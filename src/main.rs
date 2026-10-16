use rand::RngExt;
use ratatui::crossterm::event::{self, Event, KeyCode, KeyEventKind, KeyModifiers};
use ratatui::crossterm::terminal;
use ratatui::layout::{Alignment, Constraint, Layout, Rect};
use ratatui::style::{Color, Style};
use ratatui::symbols::merge::MergeStrategy;
use ratatui::widgets::{Block, Paragraph, Wrap};
use ratatui::{DefaultTerminal, Frame};
use serde::{Deserialize, Serialize};
use socket2::{Domain, Protocol, Socket, Type};
use std::env;
use std::collections::{BTreeMap, BTreeSet};
use std::f32::consts::PI;
use std::fmt;
use std::fs;
use std::io::{self, Read, Write};
use std::iter;
use std::mem;
use std::net::{Ipv4Addr, SocketAddr, TcpListener, TcpStream, UdpSocket};
use std::path::PathBuf;
use std::str;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

const DECK_SIZE: u8 = 54;
const NUM_PLAYERS: u8 = 3;
const KITTY_SIZE: u8 = 3;
const HAND_SIZE: usize = ((DECK_SIZE - KITTY_SIZE) / NUM_PLAYERS) as usize;
// used until a player sets a name, and for joined players whose names haven't arrived yet
const DEFAULT_PLAYER_NAME: &str = "Player";
const MAX_NAME_LEN: usize = 16;
const SETTINGS_FILE: &str = "settings.toml";

const POLL_INTERVAL: Duration = Duration::from_millis(100);
const DISCOVERY_PORT: u16 = 47474;
const ANNOUNCE_INTERVAL: Duration = Duration::from_secs(1);
const LOBBY_TIMEOUT: Duration = Duration::from_secs(3);

// A new card leaves the deck every DEAL_INTERVAL and takes DEAL_FLIGHT to land,
// so several are in the air at once; the whole deal takes about 1.5 seconds.
const DEAL_INTERVAL: Duration = Duration::from_millis(25);
const DEAL_FLIGHT: Duration = Duration::from_millis(180);
const DEAL_COUNT: usize = HAND_SIZE * NUM_PLAYERS as usize;
const FRAME_INTERVAL: Duration = Duration::from_millis(16);
// the kitty stays face up long enough to read, then slides to the landlord
const KITTY_REVEAL: Duration = Duration::from_millis(2500);
const KITTY_SLIDE: Duration = Duration::from_millis(300);
// two columns inside the border fit "10"; the suit goes on the line below the rank
// how long a cleared table takes to sweep off the top of the screen
const SWEEP: Duration = Duration::from_millis(300);
// A nuke's mushroom cloud flashes, rises, sends a ring rolling out along
// the ground, then peels away over NUKE_CLOUD, revealing the jokers, which sit
// on the table for NUKE_REVEAL before sweeping off like any cleared table.
// Times within the cloud, in seconds from the blast:
const NUKE_CLOUD: Duration = Duration::from_millis(4500);
const NUKE_REVEAL: Duration = Duration::from_millis(1000);
// the fireball, before the cloud starts to climb
const NUKE_FLASH: f32 = 0.15;
// how long the cap takes to reach full height
const NUKE_RISE: f32 = 0.6;
// when it starts peeling; the jokers show through from then on
const NUKE_FADE_START: f32 = 1.8;
// the ring at the base: when it bursts out, how long it lasts, and how far
// it rolls, in lines
const NUKE_RING_START: f32 = 0.75;
const NUKE_RING_LIFE: f32 = 1.8;
const NUKE_RING_REACH: f32 = 22.0;
// The ring is seen in perspective, from a viewer this many lines above the
// ground and this far from the stem, so its near side sweeps down the screen
// and past us while its far side flattens toward the horizon.
const NUKE_EYE_HEIGHT: f32 = 4.0;
const NUKE_EYE_DISTANCE: f32 = 30.0;
// how tall the full cloud is, in lines, before it's shrunk to fit the screen
const NUKE_HEIGHT: f32 = 17.0;
// A bomb's blast flashes, bursts outward and then thins away over BOMB_BLAST,
// clearing to show the bomb, which stays on the table to be beaten. Times
// within the blast, in seconds:
const BOMB_BLAST: Duration = Duration::from_millis(1300);
const BOMB_FLASH: f32 = 0.1;
// how long it takes to reach full size
const BOMB_GROW: f32 = 0.4;
// when it starts thinning; the bomb shows through from then on
const BOMB_FADE_START: f32 = 0.7;
// the shockwave's full radius, in lines; the long beams reach a third further
const BOMB_RADIUS: f32 = 8.0;
// An airplane flies across above the table, right to left, over AIRPLANE_FLIGHT,
// rolling back and forth AIRPLANE_ROLLS times; the played cards appear on the
// table once its nose passes the middle of the screen.
const AIRPLANE_FLIGHT: Duration = Duration::from_millis(1200);
const AIRPLANE_ROLLS: f32 = 2.0;
// Seen side-on with the nose to the left, at roll -1, -0.5, 0, 0.5 and 1.
// Level wings are edge-on; rolling, they show above and below the fuselage,
// the near wing as || and the far one, behind it, as ::. Spaces are see-through.
const AIRPLANE: [[&str; 5]; 5] = [
    [
        "     ::     ",
        "     ::     ",
        " <===##===<|",
        "     ||     ",
        "     ||     ",
    ],
    [
        "            ",
        "     ::     ",
        " <===##===<|",
        "     ||     ",
        "            ",
    ],
    [
        "            ",
        "            ",
        " <===##===<|",
        "            ",
        "            ",
    ],
    [
        "            ",
        "     ||     ",
        " <===##===<|",
        "     ::     ",
        "            ",
    ],
    [
        "     ||     ",
        "     ||     ",
        " <===##===<|",
        "     ::     ",
        "     ::     ",
    ],
];
// smoke from thin to thick; a blank cell lets the table show through
const SMOKE: [&str; 5] = [" ", "░", "▒", "▓", "█"];
// Ordered dithering: each cell's offset nudges where it steps between shades,
// so a fading cloud breaks up evenly instead of in rings.
const BAYER: [[f32; 4]; 4] = [
    [0.0, 8.0, 2.0, 10.0],
    [12.0, 4.0, 14.0, 6.0],
    [3.0, 11.0, 1.0, 9.0],
    [15.0, 7.0, 13.0, 5.0],
];
const CARD_WIDTH: u16 = 4;
const CARD_HEIGHT: u16 = 4;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
enum Suit {
    Clubs,
    Diamonds,
    Hearts,
    Spades,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
enum JokerColor {
    Black,
    Red,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
enum Rank {
    Three = 3,
    Four,
    Five,
    Six,
    Seven,
    Eight,
    Nine,
    Ten,
    Jack,
    Queen,
    King,
    Ace,
    Two,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
enum Card {
    Standard { rank: Rank, suit: Suit },
    Joker(JokerColor),
}

impl Suit {
    const ALL: [Suit; 4] = [Suit::Clubs, Suit::Diamonds, Suit::Hearts, Suit::Spades];
}
impl Rank {
    const ALL: [Rank; 13] = [
        Rank::Three,
        Rank::Four,
        Rank::Five,
        Rank::Six,
        Rank::Seven,
        Rank::Eight,
        Rank::Nine,
        Rank::Ten,
        Rank::Jack,
        Rank::Queen,
        Rank::King,
        Rank::Ace,
        Rank::Two,
    ];
}

impl fmt::Display for Suit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
            Suit::Clubs => "♣",
            Suit::Diamonds => "♦",
            Suit::Hearts => "♥",
            Suit::Spades => "♠",
        })
    }
}

impl fmt::Display for Rank {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Rank::Jack => f.write_str("J"),
            Rank::Queen => f.write_str("Q"),
            Rank::King => f.write_str("K"),
            Rank::Ace => f.write_str("A"),
            Rank::Two => f.write_str("2"), // discriminant is 15 so it outranks Ace
            r => write!(f, "{}", *r as u8), // 3..=10 via the discriminant
        }
    }
}

impl Card {
    // What's printed inside a face-up card: the rank, with the suit
    // underneath. Jokers are 大王 and 小王, the big and small kings, read top
    // to bottom, unless gweilo mode has them as playing-card emoji.
    fn face(&self, gweilo: bool) -> String {
        match (self, gweilo) {
            (Card::Standard { rank, suit }, _) => format!("{rank}\n{suit}"),
            (Card::Joker(JokerColor::Red), false) => "大\n王".to_string(),
            (Card::Joker(JokerColor::Black), false) => "小\n王".to_string(),
            (Card::Joker(JokerColor::Red), true) => "🃏\nR".to_string(),
            (Card::Joker(JokerColor::Black), true) => "🃏\nB".to_string(),
        }
    }

    fn value(&self) -> Value {
        match self {
            Card::Standard { rank, .. } => Value::Rank(*rank),
            Card::Joker(JokerColor::Black) => Value::BlackJoker,
            Card::Joker(JokerColor::Red) => Value::RedJoker,
        }
    }
}

// How strong a card is on its own. Suits never matter in Dou Dizhu.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
enum Value {
    Rank(Rank),
    BlackJoker,
    RedJoker,
}

// The kind of combination a set of cards forms, with whatever decides which of
// two of the same kind is stronger: the rank of its main cards (the highest
// one for sequences), and for sequences their length, which a reply has to match.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
enum Combo {
    Single(Value),
    Pair(Rank),
    // `pairs` consecutive pairs, at least 3, ending at `high`
    ChainedPairs { high: Rank, pairs: usize },
    // `len` consecutive singles, at least 5, ending at `high`
    Straight { high: Rank, len: usize },
    Triple(Rank),
    TripleWithSingle(Rank),
    TripleWithPair(Rank),
    // `len` consecutive triples, at least 2, ending at `high`
    Airplane { high: Rank, len: usize },
    // an airplane with one single kicker per triple
    SmallWingedAirplane { high: Rank, len: usize },
    // an airplane with one pair per triple
    LargeWingedAirplane { high: Rank, len: usize },
    QuadWithPair(Rank),
    Bomb(Rank),
    Nuke,
}

#[derive(Clone, Copy)]
enum Wings {
    None,
    Small,
    Large,
}

impl Combo {
    // Every combination `cards` could be read as, most natural first; empty if
    // they don't form one. Most sets have one reading, settled early by how
    // many cards there are. Only airplanes can have several, e.g. 333 444 555
    // 666 is an airplane of four, or an airplane of three with 333 or 666 as
    // kickers.
    //
    // Kickers follow these rules:
    // - a kicker can be any rank except that of its own triple or quad, which
    //   counting cards by rank enforces: a match would make four of a kind
    // - at most one joker can be among the kickers, and only as a single
    // - two jokers are never a pair, and a bomb is never two pairs
    fn readings(cards: &[Card]) -> Vec<Combo> {
        let n = cards.len();
        if n == 1 {
            return vec![Combo::Single(cards[0].value())];
        }
        let mut counts: BTreeMap<Value, usize> = BTreeMap::new();
        for card in cards {
            *counts.entry(card.value()).or_default() += 1;
        }
        let jokers = counts
            .iter()
            .filter(|(value, _)| !matches!(value, Value::Rank(_)))
            .count();
        if n == 2 && jokers == 2 {
            return vec![Combo::Nuke];
        }
        let groups: Vec<(Rank, usize)> = counts
            .iter()
            .filter_map(|(value, &count)| match value {
                Value::Rank(rank) => Some((*rank, count)),
                _ => None,
            })
            .collect();
        // ranks appearing exactly `n` times, lowest first
        let with_count = |n: usize| -> Vec<Rank> {
            groups
                .iter()
                .filter(|&&(_, count)| count == n)
                .map(|&(rank, _)| rank)
                .collect()
        };
        let quads = with_count(4);
        let triples = with_count(3);
        let pairs = with_count(2);
        let singles = with_count(1);

        // the one place a joker can go other than alone or in the nuke
        if n == 4 && triples.len() == 1 {
            return vec![Combo::TripleWithSingle(triples[0])];
        }
        if jokers == 0 {
            let combo = match (quads.len(), triples.len(), pairs.len(), singles.len()) {
                (0, 0, 1, 0) => Some(Combo::Pair(pairs[0])),
                (0, 1, 0, 0) => Some(Combo::Triple(triples[0])),
                (1, 0, 0, 0) => Some(Combo::Bomb(quads[0])),
                (0, 1, 1, 0) => Some(Combo::TripleWithPair(triples[0])),
                (1, 0, 1, 0) => Some(Combo::QuadWithPair(quads[0])),
                (0, 0, n, 0) if n >= 3 && consecutive(&pairs) => Some(Combo::ChainedPairs {
                    high: pairs[n - 1],
                    pairs: n,
                }),
                (0, 0, 0, n) if n >= 5 && consecutive(&singles) => Some(Combo::Straight {
                    high: singles[n - 1],
                    len: n,
                }),
                _ => None,
            };
            if let Some(combo) = combo {
                return vec![combo];
            }
        }
        [Wings::None, Wings::Small, Wings::Large]
            .into_iter()
            .flat_map(|wings| airplanes(&counts, &triples, n, wings))
            .collect()
    }

    // Reads `cards` so that they can follow `table`, if any reading can.
    // With the table free, the most natural reading is taken.
    fn fit(cards: &[Card], table: Option<&Combo>) -> Result<Combo, MoveError> {
        let readings = Combo::readings(cards);
        let Some(&first) = readings.first() else {
            return Err(MoveError::NotACombination);
        };
        let Some(table) = table else {
            return Ok(first);
        };
        if let Some(&combo) = readings.iter().find(|combo| combo.beats(table)) {
            Ok(combo)
        } else if readings.iter().any(|combo| combo.same_shape(table)) {
            Err(MoveError::DoesNotBeat)
        } else {
            Err(MoveError::WrongShape)
        }
    }

    // Whether two combinations are the same kind, so one could follow the
    // other: the same type and, for sequences, the same length.
    fn same_shape(&self, other: &Combo) -> bool {
        use Combo::*;
        match (self, other) {
            (ChainedPairs { pairs: m, .. }, ChainedPairs { pairs: n, .. })
            | (Straight { len: m, .. }, Straight { len: n, .. })
            | (Airplane { len: m, .. }, Airplane { len: n, .. })
            | (SmallWingedAirplane { len: m, .. }, SmallWingedAirplane { len: n, .. })
            | (LargeWingedAirplane { len: m, .. }, LargeWingedAirplane { len: n, .. }) => m == n,
            _ => mem::discriminant(self) == mem::discriminant(other),
        }
    }

    // What the table shows under a combination: its name from the combo
    // sheet, in Chinese unless gweilo mode wants English, with its length if
    // it's a sequence.
    fn name(&self, gweilo: bool) -> String {
        use Combo::*;
        let (entry, length) = match *self {
            Single(_) => (0, None),
            Pair(_) => (1, None),
            ChainedPairs { pairs, .. } => (2, Some(pairs)),
            Straight { len, .. } => (3, Some(len)),
            Triple(_) => (4, None),
            TripleWithSingle(_) => (5, None),
            TripleWithPair(_) => (6, None),
            Airplane { len, .. } => (7, Some(len)),
            SmallWingedAirplane { len, .. } => (8, Some(len)),
            LargeWingedAirplane { len, .. } => (9, Some(len)),
            QuadWithPair(_) => (10, None),
            Bomb(_) => (11, None),
            Nuke => (12, None),
        };
        let name = COMBO_SHEET[entry].name(gweilo);
        match length {
            Some(n) => format!("{name} ({n})"),
            None => name.to_string(),
        }
    }

    // what decides between two combinations of the same shape
    fn strength(&self) -> Value {
        use Combo::*;
        match *self {
            Single(value) => value,
            Pair(rank)
            | Triple(rank)
            | TripleWithSingle(rank)
            | TripleWithPair(rank)
            | QuadWithPair(rank)
            | Bomb(rank)
            | ChainedPairs { high: rank, .. }
            | Straight { high: rank, .. }
            | Airplane { high: rank, .. }
            | SmallWingedAirplane { high: rank, .. }
            | LargeWingedAirplane { high: rank, .. } => Value::Rank(rank),
            Nuke => Value::RedJoker,
        }
    }

    // Whether this can be played on top of `other`.
    fn beats(&self, other: &Combo) -> bool {
        use Combo::*;
        match (self, other) {
            (Nuke, _) => true,
            (_, Nuke) => false,
            (Bomb(_), Bomb(_)) => self.strength() > other.strength(),
            (Bomb(_), _) => true,
            _ => self.same_shape(other) && self.strength() > other.strength(),
        }
    }
}

// Every way `cards` (n of them, counted by value) can be read as an airplane
// with the given wings, highest first, as the highest triple decides strength.
// The body is a run of ranks held exactly three times each: a fourth card of a
// run rank would be a kicker matching its triple.
fn airplanes(
    counts: &BTreeMap<Value, usize>,
    triples: &[Rank],
    n: usize,
    wings: Wings,
) -> Vec<Combo> {
    let per_triple = match wings {
        Wings::None => 3,
        Wings::Small => 4,
        Wings::Large => 5,
    };
    if n % per_triple != 0 || n / per_triple < 2 {
        return Vec::new();
    }
    let len = n / per_triple;
    triples.windows(len).rev().filter_map(|run| {
        if !consecutive(run) {
            return None;
        }
        let high = run[len - 1];
        // whatever isn't in the run is the wings
        let mut rest = counts.clone();
        for rank in run {
            rest.remove(&Value::Rank(*rank));
        }
        let jokers = rest
            .keys()
            .filter(|value| !matches!(value, Value::Rank(_)))
            .count();
        match wings {
            Wings::None => rest.is_empty().then_some(Combo::Airplane { high, len }),
            Wings::Small => (jokers <= 1).then_some(Combo::SmallWingedAirplane { high, len }),
            // jokers never pair, and exactly two of a rank keeps out bombs
            Wings::Large => (jokers == 0 && rest.values().all(|&count| count == 2))
                .then_some(Combo::LargeWingedAirplane { high, len }),
        }
    })
    .collect()
}

// Whether sorted ranks run one after another. 2 sits right above Ace in rank
// order but can't be part of any sequence.
fn consecutive(ranks: &[Rank]) -> bool {
    !ranks.contains(&Rank::Two)
        && ranks
            .windows(2)
            .all(|pair| pair[1] as u8 == pair[0] as u8 + 1)
}

struct Deck {
    cards: Vec<Card>,
}

struct Hand {
    cards: Vec<Card>,
}

impl Deck {
    fn new() -> Deck {
        let cards = Suit::ALL
            .iter()
            .flat_map(|&suit| {
                Rank::ALL
                    .iter()
                    .map(move |&rank| Card::Standard { rank, suit })
            })
            .chain([Card::Joker(JokerColor::Black), Card::Joker(JokerColor::Red)])
            .collect();
        Deck { cards }
    }

    fn shuffle(&mut self) {
        let mut rng = rand::rng();
        for end in (1..self.cards.len()).rev() {
            let choice = rng.random_range(0..=end);
            self.cards.swap(choice, end);
        }
    }

    fn draw(&mut self) -> Option<Card> {
        self.cards.pop()
    }

    // one card at a time, clockwise starting from `first`, leaving the kitty in the deck
    fn deal(&mut self, hands: &mut [Hand; NUM_PLAYERS as usize], first: usize) {
        for n in 0..DEAL_COUNT {
            hands[(first + n) % NUM_PLAYERS as usize].add(self.draw().unwrap());
        }
    }
}

impl Hand {
    fn new() -> Hand {
        Hand { cards: Vec::new() }
    }

    fn add(&mut self, card: Card) {
        self.cards.push(card);
    }

    fn contains_all(&self, cards: &[Card]) -> bool {
        cards.iter().all(|card| self.cards.contains(card))
    }

    fn remove_all(&mut self, cards: &[Card]) {
        self.cards.retain(|card| !cards.contains(card));
    }
}

enum MenuChoice {
    Host,
    Join,
    Settings,
    // the hidden practice table that :debug opens
    Playground,
}

// `notice` explains why the player was sent back here, e.g. the host ended the game.
fn run_menu(
    terminal: &mut DefaultTerminal,
    theme: Theme,
    notice: Option<&str>,
) -> io::Result<Option<MenuChoice>> {
    let mut confirm_quit = false;
    let mut command: Option<CommandLine> = None;
    loop {
        draw_themed(terminal, theme, |frame| {
            draw_menu(frame, notice);
            if confirm_quit {
                draw_quit_prompt(frame, "Press [Esc] again to quit");
            }
            if let Some(text) = &command {
                draw_command_line(frame, &text.text);
            }
        })?;
        if let Event::Key(key) = read_event()? {
            if key.kind != KeyEventKind::Press {
                continue;
            }
            match command_key(&mut command, key.code) {
                CommandInput::NotMine => {}
                CommandInput::Typing => continue,
                CommandInput::Entered(text) => {
                    if matches!(parse_command(&text), Command::Debug) {
                        return Ok(Some(MenuChoice::Playground));
                    }
                    continue;
                }
            }
            if confirm_quit_key(&mut confirm_quit, key.code) {
                return Ok(None);
            }
            match key.code {
                KeyCode::Char('h') => return Ok(Some(MenuChoice::Host)),
                KeyCode::Char('j') => return Ok(Some(MenuChoice::Join)),
                KeyCode::Char('s') => return Ok(Some(MenuChoice::Settings)),
                _ => {}
            }
        }
    }
}

// 春天, shown when the landlord wins before either peasant has played, drawn
// like the title but from the font at 16 pixels a character.
const SPRING: [&str; 8] = [
    "      ▄▄            ▄▄▄▄▄▄▄▄▄▄  ",
    " ▀▀▀▀▀█▀▀▀▀▀▀       ▀▀▀▀██▀▀▀▀  ",
    "  ▀▀▀██▀▀▀▀▀            ██      ",
    " ██▄███▄▄▄▄██     ▀▀▀▀▀███▀▀▀▀▀▀",
    " ▄▄██▄▄▄▄██▄▄▄         ██▀█     ",
    "▀▀▀██▄▄▄▄▄█ ▀▀        ██  ▀█▄   ",
    "   ██▄▄▄▄▄█       ▄▄██▀     ▀██ ",
    "   ▀▀▀▀▀▀▀▀        ▀            ",
];

// 鬥地主 for the title, drawn from the STHeiti Medium font at 22 pixels a
// character. Each cell is two pixels stacked, using half blocks, so the
// pixels come out about square. Every line is the same width so the
// characters stay lined up.
const TITLE: [&str; 11] = [
    "▄▄              ▄▄                  ▄▄                              ",
    "████████ ██████▀██        ██        ██                   ▀██▄       ",
    "██  ██     ██   ██        ██    ██  ██   ▄         ▄▄▄▄▄▄▄██▄▄▄▄▄▄▄ ",
    "██▀▀██▀▀ ▀▀██▀▀ ██      ▄▄██▄▄  ██  ██▄███         ▀▀▀▀▀▀▀██▀▀▀▀▀▀▀ ",
    "██ ▄██▄▄  ▄██ ▄ ██      ▀▀██▀▀▄▄██████▀ ██                ██        ",
    "██▀▀▀▀▀▀ ▀▀▀▀▀▀ ██        ██  ▀▀██  ██  ██          ▄▄▄▄▄▄██▄▄▄▄▄▄  ",
    "██              ██        ██    ██  ██ ▄██          ▀▀▀▀▀▀██▀▀▀▀▀▀  ",
    "██              ██        ██ ▄▄ ██  ██ ▀▀▀                ██        ",
    "██              ██      ▄▄███▀▀ ██  ▀▀   ▄█▄              ██        ",
    "██            ███▀       ▀▀     ██▄▄▄▄▄▄▄██       ██████████████████",
    "▀▀            ▀▀                 ▀▀▀▀▀▀▀                            ",
];

fn draw_menu(frame: &mut Frame, notice: Option<&str>) {
    let full = frame.area();
    // the title, a gap, three buttons, and a line for any notice: 24 lines,
    // which is the smallest the screen gets
    let title_height = TITLE.len() as u16;
    let column = full.centered_vertically(Constraint::Length(title_height + 13));
    let [title, _, menu, notice_line] = Layout::vertical([
        Constraint::Length(title_height),
        Constraint::Length(1),
        Constraint::Length(11),
        Constraint::Length(1),
    ])
    .areas(column);

    let title_width = TITLE[0].chars().count() as u16;
    let title_x = full.x + full.width.saturating_sub(title_width) / 2;
    draw_art(frame, &TITLE, title_x as i32, title.y as i32);

    let buttons: [Rect; 3] = Layout::vertical([Constraint::Length(3); 3])
        .spacing(1)
        .areas(menu.centered_horizontally(Constraint::Length(20)));
    for (label, rect) in ["[h]ost", "[j]oin", "[s]ettings"].into_iter().zip(buttons) {
        let button = Paragraph::new(label)
            .alignment(Alignment::Center)
            .block(Block::bordered());
        frame.render_widget(button, rect);
    }

    if let Some(msg) = notice {
        frame.render_widget(Paragraph::new(msg).alignment(Alignment::Center), notice_line);
    }

    // bottom-left, clear of the quit prompt in the bottom-right corner
    frame.render_widget(
        Paragraph::new(format!("v{VERSION}")),
        Rect::new(full.x + 1, full.bottom().saturating_sub(1), full.width, 1).intersection(full),
    );
}

const VERSION: &str = env!("CARGO_PKG_VERSION");

// Whether a host on `version` can play with us: the same major and minor
// version. Patch releases don't change how games talk to each other.
fn compatible(version: &str) -> bool {
    let major_minor = |v: &str| v.split('.').take(2).map(str::to_string).collect::<Vec<_>>();
    major_minor(version) == major_minor(VERSION)
}

// Hosts broadcast an announcement over UDP to this port; joiners listen on it.
struct Announcement {
    // the host's game version; lobbies from incompatible versions aren't listed
    version: String,
    name: String,
    port: u16,
    players: u8,
}

impl Announcement {
    fn encode(&self) -> String {
        // name goes last so it can contain spaces
        format!(
            "DDZ {} {} {} {}",
            self.version, self.port, self.players, self.name
        )
    }

    fn decode(msg: &str) -> Option<Announcement> {
        let mut parts = msg.splitn(5, ' ');
        if parts.next()? != "DDZ" {
            return None;
        }
        Some(Announcement {
            version: parts.next()?.to_string(),
            port: parts.next()?.parse().ok()?,
            players: parts.next()?.parse().ok()?,
            name: parts.next()?.to_string(),
        })
    }
}

// A combination someone put down. Dou Dizhu only cares about the latest one:
// the next play has to beat it, and if everyone else passes, its player leads.
#[derive(Clone, Serialize, Deserialize)]
struct Play {
    seat: usize,
    cards: Vec<Card>,
    // what the next play has to beat
    combo: Combo,
}

// Messages between host and joiners, sent over TCP as one JSON object per line.
#[derive(Serialize, Deserialize)]
enum Message {
    // joiner -> host, right after connecting
    Hello {
        name: String,
    },
    // host -> each joiner when the game begins; `hand` is only that player's
    // cards, in the order they were dealt
    Start {
        seat: usize,
        names: Vec<String>,
        first: usize,
        hand: Vec<Card>,
        rules: LobbySettings,
        // each seat's wins this session, once a rematch has been agreed
        wins: Option<Vec<u32>>,
    },
    // host -> a joiner filling an empty seat mid-game; they get the hand that
    // `replaced` left behind
    TakeOver {
        seat: usize,
        names: Vec<String>,
        first: usize,
        hand: Vec<Card>,
        replaced: String,
        landlord: Option<usize>,
        // empty until there's a landlord; after that everyone has seen it
        kitty: Vec<Card>,
        turn: usize,
        last_play: Option<Play>,
        // how many cards each seat has played so far
        played: Vec<usize>,
        rules: LobbySettings,
        wins: Option<Vec<u32>>,
    },
    // joiner -> host: this player pressed Space to 叫地主
    Claim,
    // host -> players: the first claim to arrive wins; `kitty` joins their hand
    Landlord {
        seat: usize,
        kitty: Vec<Card>,
    },
    // host -> players: whoever was in `seat` left, so the game is on hold
    Paused {
        seat: usize,
    },
    // host -> players: `name` has filled the empty seat and the game carries on
    Resumed {
        seat: usize,
        name: String,
        // the newcomer starts with no wins
        wins: Option<Vec<u32>>,
    },
    // host -> a joiner there's no room for, just before disconnecting them
    Full,
    // host -> joiners waiting in the lobby: its settings, on joining and
    // whenever the host saves a change
    Lobby {
        rules: LobbySettings,
    },
    // joiner -> host: the cards to play on their turn; none means pass
    Play {
        cards: Vec<Card>,
    },
    // host -> players: a play or pass went through; `turn` and `last_play`
    // are the table after it
    Moved {
        seat: usize,
        cards: Vec<Card>,
        turn: usize,
        last_play: Option<Play>,
        // the move timer ran out and the host moved for them
        timed_out: bool,
    },
    // host -> the player whose play or pass was refused
    Rejected {
        reason: String,
    },
    // host -> players: `winner` has played their last card
    GameOver {
        winner: usize,
        wins: Option<Vec<u32>>,
        // the landlord went out before either peasant played a card
        spring: bool,
    },
    // joiner -> host: whether this player wants to play again
    Vote {
        again: bool,
    },
    // host -> players: how many have said they'll play again
    Ready {
        count: usize,
    },
    // joiner -> host: a winner pressed G on the game-over screen
    Gloat,
    // host -> players: `seat` gloated
    Gloated {
        seat: usize,
    },
    // host -> players: `seat` said no to playing again, or left, so the lobby
    // is closing
    Disbanded {
        seat: usize,
        left: bool,
    },
}

struct Connection {
    stream: TcpStream,
    // bytes received but not yet terminated by a newline
    buf: Vec<u8>,
}

impl Connection {
    fn new(stream: TcpStream) -> io::Result<Connection> {
        stream.set_nonblocking(true)?;
        stream.set_nodelay(true)?;
        Ok(Connection {
            stream,
            buf: Vec::new(),
        })
    }

    fn send(&mut self, msg: &Message) -> io::Result<()> {
        let mut line = serde_json::to_vec(msg)?;
        line.push(b'\n');
        // messages are small enough that the socket buffer always has room for them
        self.stream.write_all(&line)
    }

    // Returns the complete messages that have arrived, or None once the other
    // side has hung up.
    fn receive(&mut self) -> Option<Vec<Message>> {
        let mut chunk = [0u8; 4096];
        loop {
            match self.stream.read(&mut chunk) {
                Ok(0) => return None,
                Ok(n) => self.buf.extend_from_slice(&chunk[..n]),
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => break,
                Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
                Err(_) => return None,
            }
        }
        let mut messages = Vec::new();
        while let Some(end) = self.buf.iter().position(|&b| b == b'\n') {
            let line: Vec<u8> = self.buf.drain(..=end).collect();
            // a line we can't parse is skipped rather than dropping the connection
            if let Ok(msg) = serde_json::from_slice(&line[..end]) {
                messages.push(msg);
            }
        }
        Some(messages)
    }
}

// Turns away a joiner there's no seat for, telling them why first.
fn reject(stream: TcpStream) {
    if let Ok(mut conn) = Connection::new(stream) {
        let _ = conn.send(&Message::Full);
    }
}

// A player's name as they typed it, and as everyone is shown it.
#[derive(Clone)]
struct PlayerName {
    typed: String,
    shown: String,
}

// The name someone typing `typed` is shown as, given the players already in
// the lobby. Names are compared as typed, so brackets someone typed aren't
// taken for a suffix. A clash gets the number of people sharing the name,
// counting the newcomer: the second "Player" is "Player (2)". If that's taken
// too (someone really is called "Player (2)"), the number goes up until it's free.
fn unique_name(typed: &str, others: &[PlayerName]) -> String {
    let sharing = others.iter().filter(|other| other.typed == typed).count();
    let taken = |name: &str| others.iter().any(|other| other.shown == name);
    if sharing == 0 && !taken(typed) {
        return typed.to_string();
    }
    (sharing + 1..)
        .map(|n| format!("{typed} ({n})"))
        .find(|name| !taken(name))
        .expect("some number is always free")
}

fn hello_name(messages: Vec<Message>) -> Option<String> {
    messages.into_iter().find_map(|msg| match msg {
        Message::Hello { name } => Some(name.chars().take(MAX_NAME_LEN).collect()),
        _ => None,
    })
}

// What makes a lobby joinable: a TCP listener for joiners, and UDP broadcasts
// so they can find it. It lives for the whole game so the lobby can reopen
// when someone leaves.
struct Beacon {
    name: String,
    port: u16,
    listener: TcpListener,
    broadcaster: UdpSocket,
    last_announce: Option<Instant>,
}

impl Beacon {
    fn new(name: &str) -> io::Result<Beacon> {
        // port 0 lets the OS pick a free port
        let listener = TcpListener::bind(("0.0.0.0", 0))?;
        listener.set_nonblocking(true)?;
        let broadcaster = UdpSocket::bind(("0.0.0.0", 0))?;
        broadcaster.set_broadcast(true)?;
        Ok(Beacon {
            name: name.to_string(),
            port: listener.local_addr()?.port(),
            listener,
            broadcaster,
            last_announce: None,
        })
    }

    fn announce(&mut self, players: usize) {
        if self
            .last_announce
            .is_some_and(|t| t.elapsed() < ANNOUNCE_INTERVAL)
        {
            return;
        }
        let msg = Announcement {
            version: VERSION.to_string(),
            name: self.name.clone(),
            port: self.port,
            players: players as u8,
        }
        .encode();
        // a failed send (e.g. no network) just means nobody sees us this round
        let _ = self
            .broadcaster
            .send_to(msg.as_bytes(), (Ipv4Addr::BROADCAST, DISCOVERY_PORT));
        self.last_announce = Some(Instant::now());
    }

    fn accept(&mut self) -> Option<TcpStream> {
        self.listener.accept().ok().map(|(stream, _)| stream)
    }
}

struct Peer {
    conn: Connection,
    // None until the joiner's Hello arrives
    name: Option<PlayerName>,
}

// Rules the host picks for their lobby. They last as long as the lobby does,
// and every player is sent them when a game starts.
#[derive(Clone, Copy, PartialEq, Serialize, Deserialize)]
struct LobbySettings {
    // seconds each player gets per turn; None means no timer
    move_timer: Option<u64>,
    // the host picks the landlord when the deal ends, instead of 叫地主
    random_landlord: bool,
    // extras like the nuke's mushroom cloud. They're the same for everyone,
    // since the cloud covers the table while the game carries on.
    silly_effects: bool,
}

impl LobbySettings {
    const ROWS: [LobbyRow; 3] = [
        LobbyRow::MoveTimer,
        LobbyRow::RandomLandlord,
        LobbyRow::SillyEffects,
    ];

    const DEFAULT: LobbySettings = LobbySettings {
        move_timer: None,
        random_landlord: false,
        silly_effects: true,
    };

    fn adjust(&mut self, row: LobbyRow, step: isize) {
        match row {
            // Off, then the lengths; the ends are limits and it doesn't wrap
            LobbyRow::MoveTimer => {
                let i = TIMER_CHOICES
                    .iter()
                    .position(|&choice| choice == self.move_timer)
                    .unwrap_or(0) as isize;
                let last = TIMER_CHOICES.len() as isize - 1;
                self.move_timer = TIMER_CHOICES[(i + step).clamp(0, last) as usize];
            }
            LobbyRow::RandomLandlord => self.random_landlord = !self.random_landlord,
            LobbyRow::SillyEffects => self.silly_effects = !self.silly_effects,
        }
    }

    // each setting's name and current value, as shown in lobbies
    fn summary(&self) -> String {
        let timer = match self.move_timer {
            Some(secs) => format!("{secs}s"),
            None => "Off".to_string(),
        };
        let on_off = |on: bool| if on { "On" } else { "Off" };
        format!(
            "Move timer       {timer}\nRandom landlord  {}\nSilly effects    {}",
            on_off(self.random_landlord),
            on_off(self.silly_effects)
        )
    }
}

#[derive(Clone, Copy, PartialEq)]
enum LobbyRow {
    MoveTimer,
    RandomLandlord,
    SillyEffects,
}

enum LobbyEdit {
    Browsing,
    // holds the settings as they were, restored if the choice is cancelled
    Picking(LobbySettings),
}

struct LobbySettingsScreen {
    row: LobbyRow,
    mode: LobbyEdit,
}

impl LobbySettingsScreen {
    // Handles a key. Returns false once the host has backed out.
    fn key(&mut self, settings: &mut LobbySettings, code: KeyCode) -> bool {
        match self.mode {
            LobbyEdit::Browsing => match code {
                KeyCode::Esc => return false,
                // wraps around at the top and bottom
                KeyCode::Up | KeyCode::Char('k') | KeyCode::Down | KeyCode::Char('j') => {
                    let rows = LobbySettings::ROWS;
                    let i = rows.iter().position(|&row| row == self.row).unwrap_or(0);
                    let step = if matches!(code, KeyCode::Up | KeyCode::Char('k')) {
                        rows.len() - 1
                    } else {
                        1
                    };
                    self.row = rows[(i + step) % rows.len()];
                }
                KeyCode::Enter => self.mode = LobbyEdit::Picking(*settings),
                _ => {}
            },
            LobbyEdit::Picking(saved) => match code {
                KeyCode::Left | KeyCode::Char('h') => settings.adjust(self.row, -1),
                KeyCode::Right | KeyCode::Char('l') => settings.adjust(self.row, 1),
                KeyCode::Enter => self.mode = LobbyEdit::Browsing,
                KeyCode::Esc => {
                    *settings = saved;
                    self.mode = LobbyEdit::Browsing;
                }
                _ => {}
            },
        }
        true
    }
}

struct HostLobby {
    beacon: Beacon,
    peers: Vec<Peer>,
    confirm_quit: bool,
    settings: LobbySettings,
    // Some while the host has the lobby settings open
    editing: Option<LobbySettingsScreen>,
    // the settings as joiners last heard them; previews don't count
    shared: LobbySettings,
}

impl HostLobby {
    fn new(name: &str) -> io::Result<HostLobby> {
        Ok(HostLobby {
            beacon: Beacon::new(name)?,
            peers: Vec::new(),
            confirm_quit: false,
            settings: LobbySettings::DEFAULT,
            editing: None,
            shared: LobbySettings::DEFAULT,
        })
    }

    fn update_peers(&mut self) {
        let mut i = 0;
        while i < self.peers.len() {
            let Some(messages) = self.peers[i].conn.receive() else {
                self.peers.remove(i);
                continue;
            };
            // names are settled in the order joiners say hello, against
            // everyone already named
            if let Some(typed) = hello_name(messages) {
                let others: Vec<PlayerName> = self
                    .names()
                    .into_iter()
                    .enumerate()
                    .filter(|&(seat, _)| seat != i + 1)
                    .filter_map(|(_, name)| name)
                    .collect();
                let shown = unique_name(&typed, &others);
                self.peers[i].name = Some(PlayerName { typed, shown });
            }
            i += 1;
        }

        // the host occupies one seat; joiners beyond a full table are turned away
        while let Some(stream) = self.beacon.accept() {
            if self.is_full() {
                reject(stream);
            } else if let Ok(mut conn) = Connection::new(stream) {
                let _ = conn.send(&Message::Lobby {
                    rules: self.shared,
                });
                self.peers.push(Peer { conn, name: None });
            }
        }
    }

    // Tells joiners about saved changes to the settings, if there are any.
    fn share_settings(&mut self) {
        if self.settings == self.shared {
            return;
        }
        self.shared = self.settings;
        for peer in &mut self.peers {
            // a failed send means the joiner is gone, which receive() picks up
            let _ = peer.conn.send(&Message::Lobby {
                rules: self.settings,
            });
        }
    }

    fn is_full(&self) -> bool {
        self.peers.len() + 1 >= NUM_PLAYERS as usize
    }

    // in seat order: the host first, then joiners in the order they arrived
    // Everyone's names in seat order, the host first; None for a joiner who
    // hasn't said hello yet. The host's own name always stands as typed.
    fn names(&self) -> Vec<Option<PlayerName>> {
        let host = PlayerName {
            typed: self.beacon.name.clone(),
            shown: self.beacon.name.clone(),
        };
        iter::once(Some(host))
            .chain(self.peers.iter().map(|peer| peer.name.clone()))
            .collect()
    }

    // as everyone is shown them
    fn player_names(&self) -> Vec<String> {
        self.names()
            .into_iter()
            .map(|name| name.map_or_else(|| DEFAULT_PLAYER_NAME.to_string(), |name| name.shown))
            .collect()
    }
}

// Returns a message for the home screen, if there's something to tell the player.
fn run_host(terminal: &mut DefaultTerminal, settings: &Settings) -> io::Result<Option<String>> {
    let mut lobby = HostLobby::new(&settings.player_name)?;
    loop {
        lobby.update_peers();
        lobby.beacon.announce(lobby.peers.len() + 1);
        let theme = settings.theme();
        draw_themed(terminal, theme, |frame| draw_host(frame, &lobby, theme.hints))?;
        // poll with a timeout so new connections show up without a keypress
        if !event::poll(POLL_INTERVAL)? {
            continue;
        }
        let Event::Key(key) = read_event()? else {
            continue;
        };
        if key.kind != KeyEventKind::Press {
            continue;
        }
        // the lobby keeps running while its settings are open
        if let Some(screen) = &mut lobby.editing {
            let open = screen.key(&mut lobby.settings, key.code);
            // previews aren't sent; only once a choice is saved or cancelled
            let settled = matches!(screen.mode, LobbyEdit::Browsing);
            if !open {
                lobby.editing = None;
            }
            if settled {
                lobby.share_settings();
            }
            continue;
        }
        if confirm_quit_key(&mut lobby.confirm_quit, key.code) {
            return Ok(None);
        }
        match key.code {
            KeyCode::Char('s' | 'S') => {
                lobby.editing = Some(LobbySettingsScreen {
                    row: LobbyRow::MoveTimer,
                    mode: LobbyEdit::Browsing,
                });
            }
            KeyCode::Enter if lobby.is_full() => break,
            _ => {}
        }
    }

    let rules = lobby.settings;

    let names = lobby.player_names();
    let typed_names = lobby
        .names()
        .into_iter()
        .map(|name| name.map_or_else(|| DEFAULT_PLAYER_NAME.to_string(), |name| name.typed))
        .collect();
    // the host keeps every hand; each joiner is only sent its own
    let game = Game::new();
    let mut links = Vec::new();
    for (i, mut peer) in lobby.peers.into_iter().enumerate() {
        let seat = i + 1;
        // a failed send means the player is gone, which the game screen notices
        let _ = peer.conn.send(&Message::Start {
            seat,
            names: names.clone(),
            first: game.first,
            hand: game.hands[seat].cards.clone(),
            rules,
            wins: None,
        });
        links.push(Link {
            seat,
            conn: peer.conn,
        });
    }
    let hand = game.hands[0].cards.clone();
    let view = GameView::new(0, names, game.first, hand, true, rules);
    let table = HostTable {
        game,
        view,
        beacon: lobby.beacon,
        links,
        pending: None,
        votes: vec![None; NUM_PLAYERS as usize],
        rules,
        typed_names,
        wins: vec![0; NUM_PLAYERS as usize],
        rematched: false,
    };
    run_host_game(terminal, settings.theme(), table)
}

// Everything the host juggles during a game.
struct HostTable {
    game: Game,
    view: GameView,
    // stays quiet while the table is full; announces again when a seat empties
    beacon: Beacon,
    links: Vec<Link>,
    // someone who has connected to fill the empty seat but hasn't said hello yet
    pending: Option<Connection>,
    // each seat's answer to playing again, once the game is over
    votes: Vec<Option<bool>>,
    // the lobby's rules, carried over to every game in it
    rules: LobbySettings,
    // each seat's name as typed; the names everyone is shown are in the view
    typed_names: Vec<String>,
    // each seat's wins this session, counting from the first game
    wins: Vec<u32>,
    // set once everyone has agreed to play again; wins are only shown after
    rematched: bool,
}

// What the host does after a vote to play again.
enum VoteOutcome {
    Waiting,
    Restart,
    // someone said no; the lobby closes
    Disband,
}

impl HostTable {
    fn send_all(&mut self, msg: &Message) {
        for link in &mut self.links {
            // a failed send means that player is gone, which receive() picks up
            let _ = link.conn.send(msg);
        }
    }

    fn send_to(&mut self, seat: usize, msg: &Message) {
        if let Some(link) = self.links.iter_mut().find(|link| link.seat == seat) {
            // a failed send means that player is gone, which receive() picks up
            let _ = link.conn.send(msg);
        }
    }

    // Returns the seats of players who have left, and what the others sent,
    // in the order it was read.
    fn check_links(&mut self) -> (Vec<usize>, Vec<(usize, Message)>) {
        let mut left = Vec::new();
        let mut received = Vec::new();
        self.links.retain_mut(|link| match link.conn.receive() {
            None => {
                left.push(link.seat);
                false
            }
            Some(messages) => {
                received.extend(messages.into_iter().map(|msg| (link.seat, msg)));
                true
            }
        });
        (left, received)
    }

    // Plays `cards` for `seat`, or passes if there are none, and tells
    // everyone. Returns a notice for the host's own screen, if there is one.
    fn make_move(
        &mut self,
        seat: usize,
        cards: Vec<Card>,
        timed_out: bool,
    ) -> Result<Option<String>, MoveError> {
        if self.view.vacant.is_some() {
            return Err(MoveError::OnHold);
        }
        if cards.is_empty() {
            self.game.pass(seat)?;
        } else {
            self.game.play(seat, &cards)?;
        }
        let turn = self.game.turn;
        let last_play = self.game.last_play.clone();
        self.send_all(&Message::Moved {
            seat,
            cards: cards.clone(),
            turn,
            last_play: last_play.clone(),
            timed_out,
        });
        let text = self.view.apply_move(seat, &cards, turn, last_play, timed_out);
        if let Some(winner) = self.game.winner {
            // a landlord wins alone; if a peasant goes out, both peasants win
            let landlord_won = self.game.landlord == Some(winner);
            for seat in 0..NUM_PLAYERS as usize {
                if (self.game.landlord == Some(seat)) == landlord_won {
                    self.wins[seat] += 1;
                }
            }
            let wins = self.shown_wins();
            let spring = self.game.spring();
            self.send_all(&Message::GameOver {
                winner,
                wins: wins.clone(),
                spring,
            });
            self.view.winner = Some(winner);
            self.view.wins = wins;
            self.view.spring = spring;
        }
        Ok(text)
    }

    // the session's wins, once there's been a rematch to show them for
    fn shown_wins(&self) -> Option<Vec<u32>> {
        self.rematched.then(|| self.wins.clone())
    }

    // Moves for a player whose time has run out: a pass, or their lowest card
    // if they're leading, since a leader can't pass. Returns a notice.
    fn check_timer(&mut self) -> Option<String> {
        if !self.view.time_left()?.is_zero() {
            return None;
        }
        let seat = self.game.turn;
        let cards = if self.game.last_play.is_none() {
            self.game.hands[seat].cards.iter().min().copied().into_iter().collect()
        } else {
            Vec::new()
        };
        self.make_move(seat, cards, true).ok()?
    }

    // Passes a winner's gloat on to everyone. Losers can't gloat.
    fn gloat(&mut self, seat: usize) {
        if !self.view.is_winner(seat) {
            return;
        }
        self.send_all(&Message::Gloated { seat });
        self.view.gloats[seat] = Some(Instant::now());
    }

    fn vote(&mut self, seat: usize, again: bool) -> VoteOutcome {
        if self.game.winner.is_none() {
            return VoteOutcome::Waiting;
        }
        if !again {
            return VoteOutcome::Disband;
        }
        self.votes[seat] = Some(true);
        let count = self.votes.iter().filter(|vote| **vote == Some(true)).count();
        self.send_all(&Message::Ready { count });
        self.view.ready = count;
        if count == NUM_PLAYERS as usize {
            VoteOutcome::Restart
        } else {
            VoteOutcome::Waiting
        }
    }

    // a fresh shuffle and deal for the same players in the same seats
    fn restart(&mut self) {
        self.game = Game::new();
        self.votes = vec![None; NUM_PLAYERS as usize];
        self.rematched = true;
        let wins = self.shown_wins();
        let names = self.view.names.clone();
        for link in &mut self.links {
            let _ = link.conn.send(&Message::Start {
                seat: link.seat,
                names: names.clone(),
                first: self.game.first,
                hand: self.game.hands[link.seat].cards.clone(),
                rules: self.rules,
                wins: wins.clone(),
            });
        }
        let hand = self.game.hands[self.view.seat].cards.clone();
        let (seat, first) = (self.view.seat, self.game.first);
        self.view = GameView::new(seat, names, first, hand, true, self.rules);
        self.view.wins = wins;
    }

    // Tells everyone the lobby is closing because of `seat`, and returns the
    // message for the host's home screen.
    fn disband(&mut self, seat: usize, left: bool) -> String {
        self.send_all(&Message::Disbanded { seat, left });
        disband_text(&self.view, seat, left)
    }

    // Makes `seat` the landlord if nobody is yet. Returns whether it did.
    fn crown(&mut self, seat: usize) -> bool {
        if self.game.landlord.is_some() || self.view.vacant.is_some() {
            return false;
        }
        self.game.landlord = Some(seat);
        // the landlord leads the first round
        self.game.turn = seat;
        for &card in &self.game.kitty {
            self.game.hands[seat].add(card);
        }
        let kitty = self.game.kitty.clone();
        self.send_all(&Message::Landlord {
            seat,
            kitty: kitty.clone(),
        });
        self.view.crown(seat, kitty, true);
        true
    }

    // Lets one joiner into the empty seat. Returns a notice once they've taken it.
    fn fill_seat(&mut self, seat: usize) -> Option<String> {
        self.beacon.announce(self.links.len() + 1);
        while let Some(stream) = self.beacon.accept() {
            if self.pending.is_none() {
                self.pending = Connection::new(stream).ok();
            } else {
                reject(stream);
            }
        }

        let typed = match self.pending.as_mut()?.receive() {
            None => {
                self.pending = None;
                return None;
            }
            Some(messages) => hello_name(messages)?,
        };
        let mut conn = self.pending.take()?;
        // checked against the players still at the table
        let others: Vec<PlayerName> = (0..NUM_PLAYERS as usize)
            .filter(|&other| other != seat)
            .map(|other| PlayerName {
                typed: self.typed_names[other].clone(),
                shown: self.view.names[other].clone(),
            })
            .collect();
        let name = unique_name(&typed, &others);
        self.typed_names[seat] = typed;
        // wins belong to the person, so the newcomer starts from none
        self.wins[seat] = 0;
        let wins = self.shown_wins();
        self.view.wins = wins.clone();
        let replaced = mem::replace(&mut self.view.names[seat], name.clone());
        let _ = conn.send(&Message::TakeOver {
            seat,
            names: self.view.names.clone(),
            first: self.game.first,
            hand: self.game.hands[seat].cards.clone(),
            replaced: replaced.clone(),
            landlord: self.game.landlord,
            turn: self.game.turn,
            last_play: self.game.last_play.clone(),
            played: self.game.played(),
            rules: self.rules,
            wins: wins.clone(),
            kitty: if self.game.landlord.is_some() {
                self.game.kitty.clone()
            } else {
                Vec::new()
            },
        });
        self.send_all(&Message::Resumed {
            seat,
            name: name.clone(),
            wins,
        });
        self.links.push(Link { seat, conn });
        self.view.resume();
        Some(format!("{name} took over {replaced}'s seat"))
    }
}

fn run_host_game(
    terminal: &mut DefaultTerminal,
    theme: Theme,
    mut table: HostTable,
) -> io::Result<Option<String>> {
    let mut notice: Option<Notice> = None;
    let mut confirm_quit = false;
    loop {
        let (left, received) = table.check_links();
        for seat in left {
            // a finished game can't be handed over, so leaving counts as a no
            if table.game.winner.is_some() {
                return Ok(Some(table.disband(seat, true)));
            }
            table.view.vacant = Some(seat);
            table.send_all(&Message::Paused { seat });
        }
        if table.links.is_empty() {
            return Ok(Some(
                "Everyone else left the game, so the lobby was closed".to_string(),
            ));
        }
        for (seat, msg) in received {
            match msg {
                Message::Claim => {
                    if table.crown(seat) {
                        notice = Some(Notice::new(crown_notice(&table.view, seat, theme.gweilo)));
                    }
                }
                Message::Play { cards } => match table.make_move(seat, cards, false) {
                    Ok(text) => {
                        if let Some(text) = text {
                            notice = Some(Notice::new(text));
                        }
                    }
                    Err(e) => table.send_to(
                        seat,
                        &Message::Rejected {
                            reason: e.to_string(),
                        },
                    ),
                },
                Message::Gloat => table.gloat(seat),
                Message::Vote { again } => match table.vote(seat, again) {
                    VoteOutcome::Waiting => {}
                    VoteOutcome::Restart => {
                        table.restart();
                        notice = None;
                    }
                    VoteOutcome::Disband => return Ok(Some(table.disband(seat, false))),
                },
                _ => {}
            }
        }
        if let Some(text) = table.check_timer() {
            notice = Some(Notice::new(text));
        }
        // with a random landlord, the host picks one as soon as the deal ends
        if table.rules.random_landlord && table.view.phase() == Phase::Bidding {
            let seat = rand::rng().random_range(0..NUM_PLAYERS as usize);
            if table.crown(seat) {
                notice = Some(Notice::new(crown_notice(&table.view, seat, theme.gweilo)));
            }
        }
        match table.view.vacant {
            Some(seat) => {
                if let Some(text) = table.fill_seat(seat) {
                    notice = Some(Notice::new(text));
                }
            }
            // nobody new gets in while every seat is taken
            None => {
                while let Some(stream) = table.beacon.accept() {
                    reject(stream);
                }
            }
        }
        match game_frame(terminal, theme, &mut table.view, notice.as_ref(), &mut confirm_quit)? {
            Some(GameAction::Leave) => return Ok(None),
            Some(GameAction::Claim) => {
                if table.crown(table.view.seat) {
                    notice = Some(Notice::new(crown_notice(&table.view, table.view.seat, theme.gweilo)));
                }
            }
            Some(GameAction::Submit(cards)) => match table.make_move(table.view.seat, cards, false) {
                Ok(text) => {
                    if let Some(text) = text {
                        notice = Some(Notice::new(text));
                    }
                }
                Err(e) => table.view.reject(e.to_string()),
            },
            Some(GameAction::Say(text)) => notice = Some(Notice::new(text)),
            Some(GameAction::Gloat) => table.gloat(table.view.seat),
            Some(GameAction::Vote(again)) => match table.vote(table.view.seat, again) {
                VoteOutcome::Waiting => {}
                VoteOutcome::Restart => {
                    table.restart();
                    notice = None;
                }
                VoteOutcome::Disband => {
                    let seat = table.view.seat;
                    return Ok(Some(table.disband(seat, false)));
                }
            },
            None => {}
        }
    }
}

// The first Esc arms the quit prompt and a second one confirms; any other key
// disarms it. Returns true when the user has confirmed.
fn confirm_quit_key(confirm_quit: &mut bool, code: KeyCode) -> bool {
    if code != KeyCode::Esc {
        *confirm_quit = false;
        return false;
    }
    if *confirm_quit {
        return true;
    }
    *confirm_quit = true;
    false
}

fn draw_quit_prompt(frame: &mut Frame, msg: &str) {
    let [_, bottom] =
        Layout::vertical([Constraint::Fill(1), Constraint::Length(1)]).areas(frame.area());
    frame.render_widget(Paragraph::new(msg).alignment(Alignment::Right), bottom);
}

fn draw_host(frame: &mut Frame, lobby: &HostLobby, hints: bool) {
    if let Some(screen) = &lobby.editing {
        draw_lobby_settings(frame, &lobby.settings, screen, hints);
        return;
    }
    let list_height = NUM_PLAYERS as u16 + 2;
    // one line per lobby setting, plus the border
    let options_height = LobbySettings::ROWS.len() as u16 + 2;
    let area = frame.area().centered(
        Constraint::Length(30),
        Constraint::Length(list_height + options_height + 1),
    );
    // the start line is always reserved so the panels don't shift when it appears
    let [players, options, start] = Layout::vertical([
        Constraint::Length(list_height),
        Constraint::Length(options_height),
        Constraint::Length(1),
    ])
    .areas(area);
    frame.render_widget(
        Paragraph::new(lobby.settings.summary()).block(Block::bordered().title(" [s]ettings ")),
        options,
    );

    let mut names = lobby.player_names();
    names[0].push_str(" (you)");
    let title = format!(" Players ({}/{NUM_PLAYERS}) ", names.len());
    frame.render_widget(
        Paragraph::new(names.join("\n")).block(Block::bordered().title(title)),
        players,
    );

    if names.len() == NUM_PLAYERS as usize {
        frame.render_widget(
            Paragraph::new("Press [Enter] to start").alignment(Alignment::Center),
            start,
        );
    }

    if lobby.confirm_quit {
        draw_quit_prompt(frame, "Press [Esc] again to quit to menu");
    }
}

fn draw_lobby_settings(
    frame: &mut Frame,
    settings: &LobbySettings,
    screen: &LobbySettingsScreen,
    hints: bool,
) {
    let area = frame
        .area()
        .centered(Constraint::Length(44), Constraint::Length(LobbySettings::ROWS.len() as u16 + 3));
    let [panel, hint] = Layout::vertical([
        Constraint::Length(LobbySettings::ROWS.len() as u16 + 2),
        Constraint::Length(1),
    ])
    .areas(area);

    let picking = matches!(screen.mode, LobbyEdit::Picking(_));
    let line = |row: LobbyRow, label: &str, value: String| {
        let active = screen.row == row;
        let value = if active && picking {
            format!("◀ {value} ▶")
        } else {
            value
        };
        let cursor = if active { ">" } else { " " };
        format!("{cursor} {label:<16} {value}")
    };
    let timer = match settings.move_timer {
        Some(secs) => format!("{secs}s"),
        None => "Off".to_string(),
    };
    let lines = [
        line(LobbyRow::MoveTimer, "Move timer", timer),
        line(
            LobbyRow::RandomLandlord,
            "Random landlord",
            if settings.random_landlord { "On" } else { "Off" }.to_string(),
        ),
        line(
            LobbyRow::SillyEffects,
            "Silly effects",
            if settings.silly_effects { "On" } else { "Off" }.to_string(),
        ),
    ];
    frame.render_widget(
        Paragraph::new(lines.join("\n")).block(Block::bordered().title(" Lobby settings ")),
        panel,
    );
    if hints {
        let text = if picking {
            "[←/→] choose · [Enter] save · [Esc] cancel"
        } else {
            "[↑/↓] select · [Enter] change · [Esc] back"
        };
        frame.render_widget(Paragraph::new(text).alignment(Alignment::Center), hint);
    }
}

struct LobbyEntry {
    addr: SocketAddr,
    name: String,
    players: u8,
    last_seen: Instant,
}

struct LobbyBrowser {
    socket: UdpSocket,
    lobbies: Vec<LobbyEntry>,
    selected: usize,
    status: Option<String>,
}

impl LobbyBrowser {
    fn new() -> io::Result<LobbyBrowser> {
        let socket = discovery_socket()?;
        socket.set_nonblocking(true)?;
        Ok(LobbyBrowser {
            socket,
            lobbies: Vec::new(),
            selected: 0,
            status: None,
        })
    }

    fn update(&mut self) {
        let mut buf = [0u8; 256];
        while let Ok((len, src)) = self.socket.recv_from(&mut buf) {
            let Some(ann) = str::from_utf8(&buf[..len])
                .ok()
                .and_then(Announcement::decode)
                .filter(|ann| compatible(&ann.version))
            else {
                continue;
            };
            // the lobby lives at the sender's IP, on the TCP port it announced
            let addr = SocketAddr::new(src.ip(), ann.port);
            match self.lobbies.iter_mut().find(|l| l.addr == addr) {
                Some(lobby) => {
                    lobby.name = ann.name;
                    lobby.players = ann.players;
                    lobby.last_seen = Instant::now();
                }
                None => self.lobbies.push(LobbyEntry {
                    addr,
                    name: ann.name,
                    players: ann.players,
                    last_seen: Instant::now(),
                }),
            }
        }

        // hosts that stop announcing have closed their lobby
        self.lobbies
            .retain(|l| l.last_seen.elapsed() < LOBBY_TIMEOUT);
        self.selected = self.selected.min(self.lobbies.len().saturating_sub(1));
    }
}

// Address/port reuse lets several joiners on one machine share the discovery
// port; every one of them still receives each broadcast.
fn discovery_socket() -> io::Result<UdpSocket> {
    let socket = Socket::new(Domain::IPV4, Type::DGRAM, Some(Protocol::UDP))?;
    socket.set_reuse_address(true)?;
    #[cfg(unix)]
    socket.set_reuse_port(true)?;
    socket.bind(&SocketAddr::from((Ipv4Addr::UNSPECIFIED, DISCOVERY_PORT)).into())?;
    Ok(socket.into())
}

// Returns a message for the home screen, if there's something to tell the player.
fn run_join(terminal: &mut DefaultTerminal, settings: &Settings) -> io::Result<Option<String>> {
    let theme = settings.theme();
    let mut browser = match LobbyBrowser::new() {
        Ok(browser) => browser,
        Err(e) => {
            let msg = format!("Can't listen for lobbies on port {DISCOVERY_PORT}: {e}");
            run_message(terminal, theme, &msg)?;
            return Ok(None);
        }
    };
    loop {
        browser.update();
        draw_themed(terminal, theme, |frame| draw_join(frame, &browser, theme.hints))?;
        if !event::poll(POLL_INTERVAL)? {
            continue;
        }
        let Event::Key(key) = read_event()? else {
            continue;
        };
        if key.kind != KeyEventKind::Press {
            continue;
        }
        match key.code {
            KeyCode::Esc => return Ok(None),
            KeyCode::Up | KeyCode::Char('k') => {
                browser.selected = browser.selected.saturating_sub(1);
            }
            KeyCode::Down | KeyCode::Char('j') => {
                if browser.selected + 1 < browser.lobbies.len() {
                    browser.selected += 1;
                }
            }
            KeyCode::Enter => {
                let Some(lobby) = browser.lobbies.get(browser.selected) else {
                    continue;
                };
                if lobby.players >= NUM_PLAYERS {
                    browser.status = Some(format!("{}'s Lobby is full", lobby.name));
                    continue;
                }
                let name = lobby.name.clone();
                match TcpStream::connect_timeout(&lobby.addr, Duration::from_secs(2)) {
                    Ok(stream) => match run_joined(terminal, settings, stream, &name)? {
                        Leave::ToBrowser(status) => browser.status = status,
                        Leave::ToMenu(notice) => return Ok(notice),
                    },
                    Err(e) => browser.status = Some(format!("Couldn't join: {e}")),
                }
            }
            _ => {}
        }
    }
}

fn draw_join(frame: &mut Frame, browser: &LobbyBrowser, hints: bool) {
    let area = frame
        .area()
        .centered(Constraint::Length(40), Constraint::Length(12));
    let [list, hint, status] = Layout::vertical([
        Constraint::Length(10),
        Constraint::Length(1),
        Constraint::Length(1),
    ])
    .areas(area);

    let lines: Vec<String> = if browser.lobbies.is_empty() {
        vec!["Searching for lobbies...".to_string()]
    } else {
        browser
            .lobbies
            .iter()
            .enumerate()
            .map(|(i, lobby)| {
                let cursor = if i == browser.selected { ">" } else { " " };
                format!(
                    "{cursor} {}'s Lobby ({}/{NUM_PLAYERS})",
                    lobby.name, lobby.players
                )
            })
            .collect()
    };
    frame.render_widget(
        Paragraph::new(lines.join("\n")).block(Block::bordered().title(" Lobbies ")),
        list,
    );
    if hints {
        frame.render_widget(
            Paragraph::new("[↑/↓] select · [Enter] join · [Esc] back")
                .alignment(Alignment::Center),
            hint,
        );
    }
    if let Some(msg) = &browser.status {
        frame.render_widget(
            Paragraph::new(msg.as_str()).alignment(Alignment::Center),
            status,
        );
    }
}

// Where a joiner goes after leaving a lobby or game, with any message to show there.
enum Leave {
    ToBrowser(Option<String>),
    ToMenu(Option<String>),
}

fn run_joined(
    terminal: &mut DefaultTerminal,
    settings: &Settings,
    stream: TcpStream,
    lobby_name: &str,
) -> io::Result<Leave> {
    let theme = settings.theme();
    let mut conn = Connection::new(stream)?;
    let hello = Message::Hello {
        name: settings.player_name.clone(),
    };
    if conn.send(&hello).is_err() {
        return Ok(Leave::ToBrowser(Some(format!("Couldn't join {lobby_name}'s Lobby"))));
    }
    let mut confirm_quit = false;
    // the host sends these as soon as we're in
    let mut rules: Option<LobbySettings> = None;
    loop {
        let Some(messages) = conn.receive() else {
            return Ok(Leave::ToBrowser(Some(format!("{lobby_name} closed the lobby"))));
        };
        for msg in messages {
            match msg {
                Message::Lobby { rules: latest } => rules = Some(latest),
                Message::Start {
                    seat,
                    names,
                    first,
                    hand,
                    rules,
                    wins,
                } => {
                    let mut view = GameView::new(seat, names, first, hand, true, rules);
                    view.wins = wins;
                    return run_joined_game(terminal, theme, view, conn, None);
                }
                Message::TakeOver {
                    seat,
                    names,
                    first,
                    hand,
                    replaced,
                    landlord,
                    kitty,
                    turn,
                    last_play,
                    played,
                    rules,
                    wins,
                } => {
                    // the cards were dealt long ago, so there's no animation
                    let mut view = GameView::new(seat, names, first, hand, false, rules);
                    view.wins = wins;
                    if let Some(landlord) = landlord {
                        view.crown(landlord, kitty, false);
                    }
                    view.turn = turn;
                    view.last_play = last_play;
                    view.played = played;
                    let notice = Notice::new(format!("You took over {replaced}'s seat"));
                    return run_joined_game(terminal, theme, view, conn, Some(notice));
                }
                Message::Full => {
                    return Ok(Leave::ToBrowser(Some(format!("{lobby_name}'s Lobby is full"))));
                }
                _ => {}
            }
        }
        draw_themed(terminal, theme, |frame| {
            let area = frame
                .area()
                .centered(
                    Constraint::Fill(1),
                    Constraint::Length(LobbySettings::ROWS.len() as u16 + 6),
                );
            let [text, _, panel] = Layout::vertical([
                Constraint::Length(3),
                Constraint::Length(1),
                Constraint::Length(LobbySettings::ROWS.len() as u16 + 2),
            ])
            .areas(area);
            frame.render_widget(
                Paragraph::new(format!(
                    "Joined {lobby_name}'s Lobby\n\nWaiting for the host to start"
                ))
                .alignment(Alignment::Center),
                text,
            );
            if let Some(rules) = &rules {
                frame.render_widget(
                    Paragraph::new(rules.summary())
                        .block(Block::bordered().title(" Lobby settings ")),
                    panel.centered_horizontally(Constraint::Length(30)),
                );
            }
            if confirm_quit {
                draw_quit_prompt(frame, "Press [Esc] again to leave the lobby");
            }
        })?;
        if !event::poll(POLL_INTERVAL)? {
            continue;
        }
        if let Event::Key(key) = read_event()?
            && key.kind == KeyEventKind::Press
            && confirm_quit_key(&mut confirm_quit, key.code)
        {
            return Ok(Leave::ToBrowser(None));
        }
    }
}

fn run_joined_game(
    terminal: &mut DefaultTerminal,
    theme: Theme,
    mut view: GameView,
    mut conn: Connection,
    mut notice: Option<Notice>,
) -> io::Result<Leave> {
    let mut confirm_quit = false;
    loop {
        // the host is always seat 0, and its leaving ends the game
        let Some(messages) = conn.receive() else {
            let msg = format!("{} ended the game", view.names[0]);
            return Ok(Leave::ToMenu(Some(msg)));
        };
        for msg in messages {
            match msg {
                Message::Paused { seat } => view.vacant = Some(seat),
                Message::Resumed { seat, name, wins } => {
                    view.wins = wins;
                    let replaced = mem::replace(&mut view.names[seat], name.clone());
                    view.resume();
                    // a claim sent just as the game paused is ignored, so allow another
                    view.claimed = false;
                    notice = Some(Notice::new(format!("{name} took over {replaced}'s seat")));
                }
                Message::Landlord { seat, kitty } => {
                    view.crown(seat, kitty, true);
                    notice = Some(Notice::new(crown_notice(&view, seat, theme.gweilo)));
                }
                Message::Moved {
                    seat,
                    cards,
                    turn,
                    last_play,
                    timed_out,
                } => {
                    if let Some(text) = view.apply_move(seat, &cards, turn, last_play, timed_out) {
                        notice = Some(Notice::new(text));
                    }
                }
                Message::Rejected { reason } => view.reject(reason),
                Message::GameOver {
                    winner,
                    wins,
                    spring,
                } => {
                    view.winner = Some(winner);
                    view.wins = wins;
                    view.spring = spring;
                }
                Message::Ready { count } => view.ready = count,
                Message::Gloated { seat } => view.gloats[seat] = Some(Instant::now()),
                Message::Disbanded { seat, left } => {
                    return Ok(Leave::ToMenu(Some(disband_text(&view, seat, left))));
                }
                // everyone said yes, so here's the next deal
                Message::Start {
                    seat,
                    names,
                    first,
                    hand,
                    rules,
                    wins,
                } => {
                    view = GameView::new(seat, names, first, hand, true, rules);
                    view.wins = wins;
                    notice = None;
                }
                _ => {}
            }
        }
        // a failed send means the host is gone, which receive() picks up
        match game_frame(terminal, theme, &mut view, notice.as_ref(), &mut confirm_quit)? {
            Some(GameAction::Leave) => return Ok(Leave::ToMenu(None)),
            Some(GameAction::Claim) => {
                let _ = conn.send(&Message::Claim);
            }
            Some(GameAction::Submit(cards)) => {
                let _ = conn.send(&Message::Play { cards });
            }
            Some(GameAction::Vote(again)) => {
                let _ = conn.send(&Message::Vote { again });
            }
            Some(GameAction::Say(text)) => notice = Some(Notice::new(text)),
            Some(GameAction::Gloat) => {
                let _ = conn.send(&Message::Gloat);
            }
            None => {}
        }
    }
}

// The whole deal. Only the host has one of these; players are sent their own hand.
struct Game {
    hands: [Hand; NUM_PLAYERS as usize],
    kitty: Vec<Card>,
    // the seat dealt to first
    first: usize,
    landlord: Option<usize>,
    // whose turn it is; only meaningful once there's a landlord
    turn: usize,
    // None while the table is clear and whoever has the turn leads
    last_play: Option<Play>,
    // passes in a row since the last play; two clear the table
    passes: u8,
    // whoever shed their whole hand first
    winner: Option<usize>,
    // set once a peasant plays any cards; passes don't count
    peasant_played: bool,
}

// Why a play or pass was refused.
#[derive(Debug, PartialEq)]
enum MoveError {
    NotYourTurn,
    NotInHand,
    NotACombination,
    // no reading of the cards is the same kind of combination as the table's
    WrongShape,
    DoesNotBeat,
    // with the table clear there's nothing to pass on, so the leader has to play
    MustLead,
    // a move that crossed with someone leaving
    OnHold,
}

impl fmt::Display for MoveError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
            MoveError::NotYourTurn => "It's not your turn",
            MoveError::NotInHand => "Those cards aren't in your hand",
            MoveError::NotACombination => "That isn't a valid combination",
            MoveError::WrongShape => "That doesn't match the combination on the table",
            MoveError::DoesNotBeat => "That doesn't beat what's on the table",
            MoveError::MustLead => "You're leading, so you have to play something",
            MoveError::OnHold => "The game is on hold",
        })
    }
}

// the seat after `seat`, going clockwise
fn next_seat(seat: usize) -> usize {
    (seat + 1) % NUM_PLAYERS as usize
}

impl Game {
    fn new() -> Game {
        let mut deck = Deck::new();
        deck.shuffle();
        let first = rand::rng().random_range(0..NUM_PLAYERS as usize);
        let mut hands = [Hand::new(), Hand::new(), Hand::new()];
        deck.deal(&mut hands, first);
        Game {
            hands,
            kitty: deck.cards,
            first,
            landlord: None,
            turn: first,
            last_play: None,
            passes: 0,
            winner: None,
            peasant_played: false,
        }
    }

    // A player with the turn puts down `cards`. Nobody is skipped for having
    // nothing that beats the table: bluffing with a pass is part of the game.
    fn play(&mut self, seat: usize, cards: &[Card]) -> Result<(), MoveError> {
        if seat != self.turn || self.winner.is_some() {
            return Err(MoveError::NotYourTurn);
        }
        let unique: BTreeSet<Card> = cards.iter().copied().collect();
        if unique.len() != cards.len() || !self.hands[seat].contains_all(cards) {
            return Err(MoveError::NotInHand);
        }
        let table = self.last_play.as_ref().map(|play| &play.combo);
        let combo = Combo::fit(cards, table)?;

        self.hands[seat].remove_all(cards);
        self.passes = 0;
        if combo == Combo::Nuke {
            // nothing can answer a nuke, so the other two are skipped and the
            // table clears with the turn back to whoever played it
            self.last_play = None;
        } else {
            self.last_play = Some(Play {
                seat,
                cards: cards.to_vec(),
                combo,
            });
            self.turn = next_seat(seat);
        }
        if self.landlord != Some(seat) {
            self.peasant_played = true;
        }
        if self.hands[seat].cards.is_empty() {
            self.winner = Some(seat);
        }
        Ok(())
    }

    // how many cards each seat has played so far
    // 春天: the landlord won without either peasant playing a card
    fn spring(&self) -> bool {
        self.winner.is_some() && self.winner == self.landlord && !self.peasant_played
    }

    fn played(&self) -> Vec<usize> {
        (0..NUM_PLAYERS as usize)
            .map(|seat| {
                let kitty = if self.landlord == Some(seat) {
                    self.kitty.len()
                } else {
                    0
                };
                (HAND_SIZE + kitty).saturating_sub(self.hands[seat].cards.len())
            })
            .collect()
    }

    // The player with the turn plays nothing. After two passes in a row the
    // turn is back with whoever played last, and the table clears for them.
    fn pass(&mut self, seat: usize) -> Result<(), MoveError> {
        if seat != self.turn {
            return Err(MoveError::NotYourTurn);
        }
        if self.last_play.is_none() {
            return Err(MoveError::MustLead);
        }
        self.turn = next_seat(seat);
        self.passes += 1;
        if self.passes == 2 {
            self.last_play = None;
            self.passes = 0;
        }
        Ok(())
    }
}

// A connection to another player, tagged with the seat at the other end.
struct Link {
    seat: usize,
    conn: Connection,
}

// What one player knows: everyone's names and seats, and only their own cards.
struct GameView {
    seat: usize,
    names: Vec<String>,
    first: usize,
    // our cards: the 17 in the order they were dealt, then the kitty if we're the landlord
    hand: Vec<Card>,
    deal_start: Instant,
    // the seat whose player left; the game is on hold until it's filled
    vacant: Option<usize>,
    // set once we've pressed Space, until the host names a landlord
    claimed: bool,
    landlord: Option<Crowning>,
    // which of our two hands the cursor is in, and its position there
    row: HandRow,
    cursor: usize,
    // cards moved to the split hand, which sits above the main one; purely a
    // way of arranging them, so it changes nothing about what can be played
    split: BTreeSet<Card>,
    // Picked cards are tracked by value rather than position: every card is
    // unique, and positions shift as cards leave the hand.
    selected: BTreeSet<Card>,
    // whose turn it is and what's on the table, as last told by the host
    turn: usize,
    last_play: Option<Play>,
    // how many cards each seat has played so far
    played: Vec<usize>,
    // set from pressing Enter until the host accepts or rejects the move
    submitted: bool,
    // why the host refused our last move, shown above our hand for a while
    error: Option<Notice>,
    // the play two passes just cleared, or a nuke, on its way off the table
    swept: Option<Swept>,
    // when the latest bomb went off, for its blast
    bombed: Option<Instant>,
    // when the latest airplane was played, for its flypast
    flown: Option<Instant>,
    // whoever shed their whole hand, once someone has
    winner: Option<usize>,
    // whether it was a 春天, which the game-over screen celebrates
    spring: bool,
    // our answer to playing again, and how many have said yes so far
    voted: Option<bool>,
    ready: usize,
    // how long each turn may take, if the host set a move timer, and when
    // the current turn's clock started; it can be in the future while the
    // kitty is still being revealed
    move_timer: Option<Duration>,
    turn_started: Instant,
    // the host picks the landlord, so there's no 叫地主
    random_landlord: bool,
    // whether the nuke's cloud plays, the same for everyone in the lobby
    silly_effects: bool,
    // each seat's wins this session, once there's been a rematch
    wins: Option<Vec<u32>>,
    // Some while the combo sheet is open
    sheet: Option<ComboSheet>,
    // Some while a hidden : command is being typed
    command: Option<CommandLine>,
    // when each seat last gloated, after winning
    gloats: Vec<Option<Instant>>,
}

struct ComboSheet {
    // which combination the cursor is on
    selected: usize,
    // whether its description is open
    open: bool,
}

impl ComboSheet {
    // Handles a key. Returns false once the sheet has been closed.
    fn key(&mut self, code: KeyCode) -> bool {
        let n = COMBO_SHEET.len();
        match code {
            KeyCode::Esc if self.open => self.open = false,
            KeyCode::Esc | KeyCode::Char('c' | 'C') => return false,
            KeyCode::Up | KeyCode::Char('k') if !self.open => {
                self.selected = (self.selected + n - 1) % n;
            }
            KeyCode::Down | KeyCode::Char('j') if !self.open => {
                self.selected = (self.selected + 1) % n;
            }
            KeyCode::Enter => self.open = true,
            _ => {}
        }
        true
    }
}

struct Crowning {
    seat: usize,
    kitty: Vec<Card>,
    at: Instant,
}

#[derive(Clone, Copy, PartialEq)]
enum Phase {
    Dealing,
    // waiting for someone to 叫地主
    Bidding,
    // the kitty is face up, then slides to the landlord
    Crowning,
    Playing,
    // someone has won; waiting to hear whether everyone will play again
    Over,
}

// A play leaving the table, and when it was cleared.
struct Swept {
    play: Play,
    at: Instant,
    // nukes wait on the table before they go
    nuke: bool,
}

#[derive(Clone, Copy, PartialEq)]
enum Spot {
    Bottom,
    Left,
    Right,
}

impl GameView {
    fn new(
        seat: usize,
        names: Vec<String>,
        first: usize,
        hand: Vec<Card>,
        animate: bool,
        rules: LobbySettings,
    ) -> GameView {
        let now = Instant::now();
        // backdating the start makes the deal already finished
        let deal_start = if animate {
            now
        } else {
            now.checked_sub(deal_duration()).unwrap_or(now)
        };
        GameView {
            seat,
            names,
            first,
            hand,
            deal_start,
            vacant: None,
            claimed: false,
            landlord: None,
            row: HandRow::Main,
            cursor: 0,
            split: BTreeSet::new(),
            selected: BTreeSet::new(),
            turn: first,
            last_play: None,
            played: vec![0; NUM_PLAYERS as usize],
            submitted: false,
            error: None,
            swept: None,
            bombed: None,
            flown: None,
            winner: None,
            spring: false,
            voted: None,
            ready: 0,
            move_timer: rules.move_timer.map(Duration::from_secs),
            turn_started: now,
            random_landlord: rules.random_landlord,
            silly_effects: rules.silly_effects,
            wins: None,
            sheet: None,
            command: None,
            gloats: vec![None; NUM_PLAYERS as usize],
        }
    }

    // The game carries on after a seat is filled. The turn starts over with
    // a full clock, so whoever took over isn't left with someone else's.
    fn resume(&mut self) {
        self.vacant = None;
        self.turn_started = Instant::now();
    }

    // time left on the current turn, while a move timer is running
    fn time_left(&self) -> Option<Duration> {
        let limit = self.move_timer?;
        if self.phase() != Phase::Playing || self.vacant.is_some() {
            return None;
        }
        Some(limit.saturating_sub(self.turn_started.elapsed()))
    }

    // Applies a play or pass the host accepted. Returns a notice to show, if any.
    fn apply_move(
        &mut self,
        seat: usize,
        cards: &[Card],
        turn: usize,
        last_play: Option<Play>,
        timed_out: bool,
    ) -> Option<String> {
        self.played[seat] += cards.len();
        self.turn_started = Instant::now();
        if seat == self.seat {
            self.hand.retain(|card| !cards.contains(card));
            self.selected.retain(|card| !cards.contains(card));
            self.split.retain(|card| !cards.contains(card));
            self.settle_cursor();
            self.submitted = false;
            self.error = None;
        }
        self.turn = turn;
        // a pass that leaves the table clear was the second in a row
        if cards.is_empty()
            && last_play.is_none()
            && let Some(cleared) = self.last_play.take()
        {
            self.swept = Some(Swept {
                play: cleared,
                at: Instant::now(),
                nuke: false,
            });
        }
        // A nuke clears the table straight away, so it never becomes the last
        // play. It's shown here instead, sitting on the table for a while
        // (under its cloud, if the lobby has silly effects on) before it
        // sweeps off.
        if matches!(Combo::readings(cards).as_slice(), [Combo::Bomb(_)]) {
            self.bombed = Some(Instant::now());
        }
        if matches!(Combo::readings(cards).as_slice(), [Combo::Nuke]) {
            self.swept = Some(Swept {
                play: Play {
                    seat,
                    cards: cards.to_vec(),
                    combo: Combo::Nuke,
                },
                at: Instant::now(),
                nuke: true,
            });
        }
        if last_play.as_ref().is_some_and(|play| {
            play.seat == seat
                && matches!(
                    play.combo,
                    Combo::Airplane { .. }
                        | Combo::SmallWingedAirplane { .. }
                        | Combo::LargeWingedAirplane { .. }
                )
        }) {
            self.flown = Some(Instant::now());
        }
        self.last_play = last_play;
        let who = if seat == self.seat {
            "You".to_string()
        } else {
            self.names[seat].clone()
        };
        if timed_out {
            return Some(format!("{who} ran out of time"));
        }
        cards.is_empty().then(|| format!("{who} passed"))
    }

    // How long ago the nuke went off, while its cloud is still up. There's no
    // cloud with silly effects off.
    fn cloud(&self) -> Option<Duration> {
        let swept = self
            .swept
            .as_ref()
            .filter(|swept| swept.nuke && self.silly_effects)?;
        let since = swept.at.elapsed();
        (since < NUKE_CLOUD).then_some(since)
    }

    // How long ago the latest bomb went off, while its blast is still going.
    // There's no blast with silly effects off.
    fn blast(&self) -> Option<Duration> {
        let since = self.bombed.filter(|_| self.silly_effects)?.elapsed();
        (since < BOMB_BLAST).then_some(since)
    }

    // whether the blast is still thick enough to hide the bomb on the table
    fn blast_covers_table(&self) -> bool {
        self.blast()
            .is_some_and(|since| since.as_secs_f32() < BOMB_FADE_START)
    }

    // How far the latest airplane's flypast has got, 0 to 1, while it's going.
    // There's no flypast with silly effects off.
    fn flight(&self) -> Option<f32> {
        let since = self.flown.filter(|_| self.silly_effects)?.elapsed();
        let t = since.as_secs_f32() / AIRPLANE_FLIGHT.as_secs_f32();
        (t < 1.0).then_some(t)
    }

    // Starts an effect on this screen only, for the playground.
    fn debug_anim(&mut self, anim: DebugAnim) {
        let now = Instant::now();
        match anim {
            DebugAnim::Airplane => self.flown = Some(now),
            DebugAnim::Bomb => self.bombed = Some(now),
            DebugAnim::Nuke => {
                self.swept = Some(Swept {
                    play: Play {
                        seat: self.seat,
                        cards: vec![Card::Joker(JokerColor::Black), Card::Joker(JokerColor::Red)],
                        combo: Combo::Nuke,
                    },
                    at: now,
                    nuke: true,
                });
            }
        }
    }

    // whether the cloud is still thick enough to hide the table
    fn cloud_covers_table(&self) -> bool {
        self.cloud()
            .is_some_and(|since| since.as_secs_f32() < NUKE_FADE_START)
    }

    // The cleared play and how far it has swept, 0 to 1, until it's gone. A
    // nuke waits on the table first, and longer if its cloud plays.
    fn sweep(&self) -> Option<(&Play, f32)> {
        let swept = self.swept.as_ref()?;
        let wait = match (swept.nuke, self.silly_effects) {
            (false, _) => Duration::ZERO,
            (true, true) => NUKE_CLOUD + NUKE_REVEAL,
            (true, false) => NUKE_REVEAL,
        };
        let t = swept.at.elapsed().saturating_sub(wait).as_secs_f32() / SWEEP.as_secs_f32();
        (t < 1.0).then_some((&swept.play, t))
    }

    fn reject(&mut self, reason: String) {
        self.submitted = false;
        self.error = Some(Notice::new(reason));
    }

    // `fresh` means it's happening now: play the reveal and, if it's us, add
    // the kitty to our hand. A player taking over later already has it.
    fn crown(&mut self, seat: usize, kitty: Vec<Card>, fresh: bool) {
        let now = Instant::now();
        let at = if fresh {
            now
        } else {
            now.checked_sub(KITTY_REVEAL + KITTY_SLIDE).unwrap_or(now)
        };
        if fresh && seat == self.seat {
            self.hand.extend(&kitty);
        }
        // the cursor starts under the middle card, rounding right:
        // card 9 of 17 for peasants, card 10 of 20 for the landlord
        self.row = HandRow::Main;
        self.cursor = self.hand.len().saturating_sub(1) / 2;
        self.landlord = Some(Crowning { seat, kitty, at });
        // the landlord leads the first round, and their clock starts once the
        // kitty is in their hand
        self.turn = seat;
        self.turn_started = at + KITTY_REVEAL + KITTY_SLIDE;
    }

    fn phase(&self) -> Phase {
        if cards_landed(self.deal_start.elapsed()) < DEAL_COUNT {
            return Phase::Dealing;
        }
        match &self.landlord {
            None => Phase::Bidding,
            Some(crowning) if crowning.at.elapsed() < KITTY_REVEAL + KITTY_SLIDE => {
                Phase::Crowning
            }
            Some(_) if self.winner.is_some() => Phase::Over,
            Some(_) => Phase::Playing,
        }
    }

    // whether the roles have been settled and the kitty is in the landlord's hand
    fn roles_known(&self) -> bool {
        matches!(self.phase(), Phase::Playing | Phase::Over)
    }

    // The headline for the end of the game, and whether we're on the winning
    // side. A landlord wins alone; if a peasant goes out, both peasants win.
    // We're "You", first, so the headline alone says whether we won.
    fn result(&self, gweilo: bool) -> Option<(String, bool)> {
        let winner = self.winner?;
        let landlord_won = self.is_landlord(winner);
        let mut winners: Vec<usize> = (0..NUM_PLAYERS as usize)
            .filter(|&seat| self.is_landlord(seat) == landlord_won)
            .collect();
        winners.sort_by_key(|&seat| seat != self.seat);
        let names: Vec<&str> = winners
            .iter()
            .map(|&seat| {
                if seat == self.seat {
                    "You"
                } else {
                    self.names[seat].as_str()
                }
            })
            .collect();
        let won = winners.contains(&self.seat);
        // "wins" for one other player, "win" for us or for two
        let verb = if names.len() == 1 && !won { "wins" } else { "win" };
        let headline = format!(
            "{} ({}) {verb}!",
            names.join(" and "),
            role_name(landlord_won, gweilo)
        );
        Some((headline, won))
    }

    // whether `seat` is on the winning side, once someone has won
    fn is_winner(&self, seat: usize) -> bool {
        self.winner
            .is_some_and(|winner| self.is_landlord(seat) == self.is_landlord(winner))
    }

    // the seats whose gloats are still showing, each for GLOAT_DURATION
    // after their latest
    fn gloating(&self) -> Vec<usize> {
        (0..NUM_PLAYERS as usize)
            .filter(|&seat| {
                self.gloats[seat].is_some_and(|at| at.elapsed() < GLOAT_DURATION)
            })
            .collect()
    }

    fn is_landlord(&self, seat: usize) -> bool {
        self.landlord.as_ref().is_some_and(|c| c.seat == seat)
    }

    // the seat that the n-th card off the deck goes to
    fn deal_target(&self, n: usize) -> usize {
        (self.first + n) % NUM_PLAYERS as usize
    }

    // Seats run clockwise. Seen from above with us at the bottom, clockwise goes
    // bottom -> left -> right, so the next seat sits on our left.
    fn spot(&self, seat: usize) -> Spot {
        let n = NUM_PLAYERS as usize;
        if seat == self.seat {
            Spot::Bottom
        } else if seat == (self.seat + 1) % n {
            Spot::Left
        } else {
            Spot::Right
        }
    }

    // how many cards a seat holds, as far as the animations have got
    fn held(&self, seat: usize) -> usize {
        let landed = cards_landed(self.deal_start.elapsed());
        let dealt = (0..landed).filter(|&n| self.deal_target(n) == seat).count();
        let kitty = if self.roles_known() && self.is_landlord(seat) {
            KITTY_SIZE as usize
        } else {
            0
        };
        (dealt + kitty).saturating_sub(self.played[seat])
    }

    // our cards that have arrived so far, sorted
    fn visible_hand(&self) -> Vec<Card> {
        let mut cards: Vec<Card> = self
            .hand
            .iter()
            .take(self.held(self.seat))
            .copied()
            .collect();
        cards.sort();
        cards
    }

    // our visible cards as the main hand and the split hand, each sorted
    fn rows(&self) -> (Vec<Card>, Vec<Card>) {
        let (split, main) = self
            .visible_hand()
            .into_iter()
            .partition(|card| self.split.contains(card));
        (main, split)
    }

    // keeps the cursor on a card after cards leave a hand
    fn settle_cursor(&mut self) {
        let (main, split) = self.rows();
        if self.row == HandRow::Split && split.is_empty() {
            self.row = HandRow::Main;
        }
        let len = if self.row == HandRow::Main { main.len() } else { split.len() };
        self.cursor = self.cursor.min(len.saturating_sub(1));
    }

    fn hand_key(&mut self, code: KeyCode) {
        self.settle_cursor();
        let (main, split) = self.rows();
        let (active, other) = match self.row {
            HandRow::Main => (&main, &split),
            HandRow::Split => (&split, &main),
        };
        let Some(&card) = active.get(self.cursor) else {
            return;
        };
        let n = active.len();
        let switch_to = match self.row {
            HandRow::Main => HandRow::Split,
            HandRow::Split => HandRow::Main,
        };
        match code {
            KeyCode::Left | KeyCode::Char('h') => self.cursor = (self.cursor + n - 1) % n,
            KeyCode::Right | KeyCode::Char('l') => self.cursor = (self.cursor + 1) % n,
            // up goes to the split hand above, down back to the main hand
            KeyCode::Up | KeyCode::Char('k') if self.row == HandRow::Main && !other.is_empty() => {
                self.cursor = nearest_card(self.cursor, n, other.len());
                self.row = switch_to;
            }
            KeyCode::Down | KeyCode::Char('j') if self.row == HandRow::Split => {
                self.cursor = nearest_card(self.cursor, n, other.len());
                self.row = switch_to;
            }
            KeyCode::Char(' ') => {
                if !self.selected.remove(&card) {
                    self.selected.insert(card);
                }
            }
            KeyCode::Char('s' | 'S') => {
                if !self.split.remove(&card) {
                    self.split.insert(card);
                }
                // the cursor stays put; if that emptied this hand, it follows
                // the card into the other one
                if n == 1 {
                    let (main, split) = self.rows();
                    let landed_in = if self.row == HandRow::Main { &split } else { &main };
                    self.cursor = landed_in.iter().position(|&c| c == card).unwrap_or(0);
                    self.row = switch_to;
                }
                self.settle_cursor();
            }
            _ => {}
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
enum HandRow {
    Main,
    Split,
}

// Hands are centred on screen, so a position in one doesn't line up with the
// same position in another of a different length. This finds the card in a
// hand of `to_len` that sits closest to card `i` of a hand of `from_len`.
fn nearest_card(i: usize, from_len: usize, to_len: usize) -> usize {
    let shifted = i as f32 + (from_len as f32 - to_len as f32) / 2.0;
    (shifted.round().max(0.0) as usize).min(to_len.saturating_sub(1))
}

fn disband_text(view: &GameView, seat: usize, left: bool) -> String {
    if left {
        format!("{} left, so the lobby was closed", view.names[seat])
    } else if seat == view.seat {
        "You chose not to play again, so the lobby was closed".to_string()
    } else {
        format!(
            "{} didn't want to play again, so the lobby was closed",
            view.names[seat]
        )
    }
}

// what the landlord and the peasants are called, in Chinese unless gweilo
// mode wants English
fn role_name(landlord: bool, gweilo: bool) -> &'static str {
    match (landlord, gweilo) {
        (true, false) => "地主",
        (false, false) => "農民",
        (true, true) => "Landlord",
        (false, true) => "Peasant",
    }
}

fn crown_notice(view: &GameView, seat: usize, gweilo: bool) -> String {
    let landlord = role_name(true, gweilo);
    if seat == view.seat {
        format!("You are the {landlord}")
    } else {
        format!("{} is the {landlord}", view.names[seat])
    }
}

// cards that have left the deck after `elapsed`, including those still in the air
fn cards_launched(elapsed: Duration) -> usize {
    let n = (elapsed.as_millis() / DEAL_INTERVAL.as_millis()) as usize + 1;
    n.min(DEAL_COUNT)
}

fn cards_landed(elapsed: Duration) -> usize {
    elapsed.checked_sub(DEAL_FLIGHT).map_or(0, cards_launched)
}

// from the first card leaving the deck to the last one landing
fn deal_duration() -> Duration {
    DEAL_INTERVAL * (DEAL_COUNT as u32 - 1) + DEAL_FLIGHT
}

// ease out: moves fast at first and settles into place
fn ease_out(t: f32) -> f32 {
    let t = t.clamp(0.0, 1.0);
    1.0 - (1.0 - t).powi(3)
}

fn lerp(a: u16, b: u16, t: f32) -> u16 {
    (a as f32 + (b as f32 - a as f32) * t).round() as u16
}

// the move timer's lengths, in seconds
const TIMER_CHOICES: [Option<u64>; 5] = [None, Some(30), Some(60), Some(90), Some(120)];

// One combination on the combo sheet.
struct SheetEntry {
    english: &'static str,
    chinese: &'static str,
    // what it is and what can follow it, always in English
    description: &'static str,
    example: &'static str,
}

impl SheetEntry {
    // in Chinese unless gweilo mode wants English
    fn name(&self, gweilo: bool) -> &'static str {
        if gweilo { self.english } else { self.chinese }
    }
}

// The combo sheet, in the order Combo::name refers to.
const COMBO_SHEET: [SheetEntry; 13] = [
    SheetEntry {
        english: "Single",
        chinese: "單張",
        description: "Any one card. Ranks run 3 up to A, then 2, then the black joker, then the red joker.",
        example: "A",
    },
    SheetEntry {
        english: "Pair",
        chinese: "對子",
        description: "Two cards of the same rank. The two jokers aren't a pair: together they're the Nuke.",
        example: "3 3",
    },
    SheetEntry {
        english: "Chained pairs",
        chinese: "連對",
        description: "Three or more pairs of consecutive ranks, with no 2s or jokers. A reply needs the same number of pairs.",
        example: "7 7 8 8 9 9",
    },
    SheetEntry {
        english: "Straight",
        chinese: "順子",
        description: "Five or more single cards of consecutive ranks, up to A, with no 2s or jokers. A reply needs the same length.",
        example: "5 6 7 8 9 10 J",
    },
    SheetEntry {
        english: "Three-of-a-kind",
        chinese: "三張",
        description: "Three cards of the same rank.",
        example: "9 9 9",
    },
    SheetEntry {
        english: "Three-to-one",
        chinese: "三帶一",
        description: "Three of a kind plus one kicker of any other rank, which can be a single joker. The triple decides its strength.",
        example: "9 9 9 4",
    },
    SheetEntry {
        english: "Three-to-two",
        chinese: "三帶二",
        description: "Three of a kind plus a pair of any other rank. The triple decides its strength.",
        example: "9 9 9 4 4",
    },
    SheetEntry {
        english: "Airplane",
        chinese: "飛機",
        description: "Two or more three-of-a-kinds of consecutive ranks, with no 2s. A reply needs the same number of triples.",
        example: "3 3 3 4 4 4",
    },
    SheetEntry {
        english: "Small-winged airplane",
        chinese: "飛機帶單",
        description: "An airplane plus one single kicker per triple. Kickers can be any rank but the airplane's own, with at most one joker.",
        example: "3 3 3 4 4 4 7 9",
    },
    SheetEntry {
        english: "Large-winged airplane",
        chinese: "飛機帶對",
        description: "An airplane plus one pair per triple. The pairs must be different ranks from each other and from the airplane, and can't be jokers.",
        example: "3 3 3 4 4 4 7 7 9 9",
    },
    SheetEntry {
        english: "Quad-to-two",
        chinese: "四帶二",
        description: "Four of a kind plus a pair. Unlike a bomb, it only beats a lower quad-to-two.",
        example: "6 6 6 6 8 8",
    },
    SheetEntry {
        english: "Bomb",
        chinese: "炸彈",
        description: "Four of a kind. It beats anything except a higher bomb or the Nuke, and afterwards only those can follow it.",
        example: "6 6 6 6",
    },
    SheetEntry {
        english: "Nuke",
        chinese: "王炸",
        description: "Both jokers. Nothing beats it: the table clears and the turn comes straight back to you.",
        example: "BJ RJ",
    },
];

// how long "<name> gloated" stays up; gloating again starts it over
const GLOAT_DURATION: Duration = Duration::from_secs(2);

const NOTICE_DURATION: Duration = Duration::from_secs(4);

// A message shown at the top of the game screen for a few seconds.
struct Notice {
    text: String,
    shown: Instant,
}

impl Notice {
    fn new(text: String) -> Notice {
        Notice {
            text,
            shown: Instant::now(),
        }
    }

    fn current(&self) -> Option<&str> {
        (self.shown.elapsed() < NOTICE_DURATION).then_some(self.text.as_str())
    }
}

enum GameAction {
    Leave,
    // the player pressed Space to 叫地主
    Claim,
    // the player played these cards on their turn, or passed if there are none
    Submit(Vec<Card>),
    // the player's answer to playing again
    Vote(bool),
    // something to show at the top of the screen, like a command's reply
    Say(String),
    // a winner pressed G on the game-over screen
    Gloat,
}

// Draws one frame of the game and handles a key if one arrives.
fn game_frame(
    terminal: &mut DefaultTerminal,
    theme: Theme,
    view: &mut GameView,
    notice: Option<&Notice>,
    confirm_quit: &mut bool,
) -> io::Result<Option<GameAction>> {
    draw_themed(terminal, theme, |frame| {
        draw_game(frame, view, notice.and_then(Notice::current), theme);
        draw_sheet_or_hint(frame, view, theme);
        if *confirm_quit {
            draw_quit_prompt(frame, "Press [Esc] again to leave the game");
        }
        if let Some(text) = &view.command {
            draw_command_line(frame, &text.text);
        }
    })?;
    // redraw at frame rate only while cards are moving
    let moving =
        matches!(view.phase(), Phase::Dealing | Phase::Crowning) || view.sweep().is_some()
        || view.blast().is_some()
        || view.flight().is_some();
    let wait = if moving { FRAME_INTERVAL } else { POLL_INTERVAL };
    if !event::poll(wait)? {
        return Ok(None);
    }
    let Event::Key(key) = read_event()? else {
        return Ok(None);
    };
    if key.kind != KeyEventKind::Press {
        return Ok(None);
    }
    // Debug commands stay out of real games, so what everyone sees matches;
    // :debug just says where to find them.
    match command_key(&mut view.command, key.code) {
        CommandInput::NotMine => {}
        CommandInput::Typing => return Ok(None),
        CommandInput::Entered(text) => {
            return Ok(match parse_command(&text) {
                Command::Debug => {
                    Some(GameAction::Say("Leave the game to use debug mode".to_string()))
                }
                _ => None,
            });
        }
    }
    // while the combo sheet is open, keys are for it; the game carries on
    if view.sheet.is_some() {
        sheet_key(view, key.code);
        return Ok(None);
    }
    if confirm_quit_key(confirm_quit, key.code) {
        return Ok(Some(GameAction::Leave));
    }
    if sheet_key(view, key.code) {
        return Ok(None);
    }
    // while the game is on hold, nothing else responds
    if view.vacant.is_some() {
        return Ok(None);
    }
    match view.phase() {
        Phase::Bidding
            if key.code == KeyCode::Char(' ') && !view.claimed && !view.random_landlord =>
        {
            view.claimed = true;
            return Ok(Some(GameAction::Claim));
        }
        // Only the player with the turn can play or pass; the others can still
        // pick cards. Enter never passes, so an empty selection can't throw a
        // turn away by accident.
        Phase::Playing if key.code == KeyCode::Enter => {
            if view.turn == view.seat && !view.submitted {
                if view.selected.is_empty() {
                    view.reject(if view.last_play.is_none() {
                        "You're leading, so select cards to play".to_string()
                    } else {
                        "Select cards to play, or press [P] to pass".to_string()
                    });
                } else {
                    view.submitted = true;
                    let cards = view.selected.iter().copied().collect();
                    return Ok(Some(GameAction::Submit(cards)));
                }
            }
        }
        // passing keeps the selection, so a half-built combination survives
        Phase::Playing if matches!(key.code, KeyCode::Char('p' | 'P')) => {
            if view.turn == view.seat && !view.submitted {
                view.submitted = true;
                return Ok(Some(GameAction::Submit(Vec::new())));
            }
        }
        Phase::Playing if key.code == KeyCode::Backspace => view.selected.clear(),
        // winners can gloat as often as they like, voted or not
        Phase::Over
            if matches!(key.code, KeyCode::Char('g' | 'G')) && view.is_winner(view.seat) =>
        {
            return Ok(Some(GameAction::Gloat));
        }
        Phase::Over if view.voted.is_none() => {
            let again = match key.code {
                KeyCode::Char('y' | 'Y') => true,
                KeyCode::Char('n' | 'N') => false,
                _ => return Ok(None),
            };
            view.voted = Some(again);
            return Ok(Some(GameAction::Vote(again)));
        }
        // Space is 叫地主 while bidding; once play starts it picks cards
        Phase::Playing => view.hand_key(key.code),
        _ => {}
    }
    Ok(None)
}

fn draw_game(frame: &mut Frame, view: &GameView, notice: Option<&str>, theme: Theme) {
    let Theme { hints, gweilo, .. } = theme;
    let area = frame.area();
    let elapsed = view.deal_start.elapsed();
    let launched = cards_launched(elapsed);
    let landed = cards_landed(elapsed);
    let phase = view.phase();
    let n = NUM_PLAYERS as usize;

    // From the bottom up: a line for hints and prompts, then for each of our
    // hands a line for the cursor, the cards, and a line for picked cards to
    // rise into, with the split hand (if it has cards) above the main one.
    // Above those, our name and then the turn prompt.
    let (main, split) = view.rows();
    let hand_y = area.bottom().saturating_sub(CARD_HEIGHT + 2);
    let split_y = hand_y.saturating_sub(CARD_HEIGHT + 2);
    let stack_top = if split.is_empty() { hand_y } else { split_y }.saturating_sub(1);
    let name_y = stack_top.saturating_sub(1);
    let prompt_y = stack_top.saturating_sub(2);

    let cx = area.x + area.width / 2;
    // The middle of the table sits at the middle of the screen unless our
    // hands would run into it; its lowest line is 3 below `cy`.
    let cy = (area.y + area.height / 2).min(prompt_y.saturating_sub(4));
    let side_y = cy.saturating_sub(1);
    let side_width = area.width / 3;
    // where a card sent to a seat ends up
    let destination = |seat: usize| match view.spot(seat) {
        Spot::Bottom => (cx.saturating_sub(CARD_WIDTH / 2), hand_y),
        Spot::Left => (area.x + 1, side_y),
        Spot::Right => (area.right().saturating_sub(CARD_WIDTH + 1), side_y),
    };
    let kitty_width = KITTY_SIZE as u16 * (CARD_WIDTH + 1) - 1;
    let kitty_x = |i: usize| cx.saturating_sub(kitty_width / 2) + i as u16 * (CARD_WIDTH + 1);
    let kitty_y = cy.saturating_sub(1);
    // The flypast's left edge: from just past the right of the screen to just
    // past the left. Cards it brings appear once its nose (one column in)
    // passes the middle.
    let plane_x = view.flight().map(|t| {
        let width = AIRPLANE[0][0].len() as f32;
        let start = area.right() as f32;
        let end = area.x as f32 - width;
        (start + (end - start) * t).round() as i32
    });

    if let Some(msg) = notice {
        frame.render_widget(
            Paragraph::new(msg).alignment(Alignment::Center),
            Rect::new(area.x, area.y, area.width, 1),
        );
    }

    // the deck until every card has left it, then the kitty face down until
    // there's a landlord
    if launched < DEAL_COUNT {
        // card-sized, where the dealt cards leave from
        let deck = card_rect(cx.saturating_sub(CARD_WIDTH / 2), cy.saturating_sub(1));
        draw_card_back(frame, deck);
    } else if view.landlord.is_none() {
        for i in 0..KITTY_SIZE as usize {
            draw_card_back(frame, card_rect(kitty_x(i), kitty_y));
        }
    }

    if phase == Phase::Bidding && view.vacant.is_none() && !view.random_landlord {
        let prompt = match (view.claimed, gweilo) {
            (true, false) => "叫地主!",
            (false, false) => "Press [Space] to 叫地主",
            (true, true) => "Called!",
            (false, true) => "Press [Space] to call Landlord",
        };
        frame.render_widget(
            Paragraph::new(prompt).alignment(Alignment::Center),
            Rect::new(area.x, kitty_y + CARD_HEIGHT + 1, area.width, 1).intersection(area),
        );
    }

    let role = |seat: usize| match phase {
        Phase::Playing | Phase::Over => role_name(view.is_landlord(seat), gweilo),
        _ => "",
    };
    // a player's role and session wins, whichever there are yet
    let status = |seat: usize| {
        let wins = view.wins.as_ref().map(|wins| match wins[seat] {
            1 => "1 win".to_string(),
            n => format!("{n} wins"),
        });
        [Some(role(seat).to_string()).filter(|r| !r.is_empty()), wins]
            .into_iter()
            .flatten()
            .collect::<Vec<_>>()
            .join(" · ")
    };
    let label = |seat: usize| {
        let held = view.held(seat);
        let cards = if held == 1 { "card" } else { "cards" };
        // once play starts, a player close to going out is flagged
        let alert = if view.roles_known() && held <= 2 { "!" } else { "" };
        format!(
            "{}\n{}\n{held} {cards}{alert}",
            view.names[seat],
            status(seat)
        )
    };
    let left = (view.seat + 1) % n;
    let right = (view.seat + 2) % n;
    frame.render_widget(
        Paragraph::new(label(left)),
        Rect::new(area.x + 1, side_y, side_width, 3).intersection(area),
    );
    frame.render_widget(
        Paragraph::new(label(right)).alignment(Alignment::Right),
        Rect::new(
            area.right().saturating_sub(side_width + 1),
            side_y,
            side_width,
            3,
        )
        .intersection(area),
    );

    if phase == Phase::Playing {
        let mut turn = if view.turn == view.seat {
            "Your turn".to_string()
        } else {
            format!("{}'s turn", view.names[view.turn])
        };
        if let Some(left) = view.time_left() {
            turn.push_str(&format!(" · {}s", left.as_secs_f32().ceil() as u64));
        }
        frame.render_widget(
            Paragraph::new(turn),
            Rect::new(area.x + 1, area.y, side_width, 1).intersection(area),
        );

        // the table only ever shows the latest combination
        if let Some(play) = &view.last_play
            && !view.blast_covers_table()
            && !plane_x.is_some_and(|x| x + 1 > cx as i32)
        {
            draw_play(frame, view, play, kitty_y, gweilo);
        }

        if view.turn == view.seat && view.vacant.is_none() {
            // a rejection replaces the controls until it fades, and shows even
            // with hints off
            let prompt = match view.error.as_ref().and_then(Notice::current) {
                Some(reason) => Some(reason),
                None if !hints => None,
                // leading on a free table, so there's no passing
                None if view.last_play.is_none() => Some("[Enter] play"),
                None => Some("[Enter] play · [P] pass"),
            };
            if let Some(prompt) = prompt {
                frame.render_widget(
                    Paragraph::new(prompt).alignment(Alignment::Center),
                    Rect::new(area.x, prompt_y, area.width, 1).intersection(area),
                );
            }
        }
    }

    let name = match status(view.seat) {
        status if status.is_empty() => view.names[view.seat].clone(),
        status => format!("{} · {status}", view.names[view.seat]),
    };
    frame.render_widget(
        Paragraph::new(name).alignment(Alignment::Center),
        Rect::new(area.x, name_y, area.width, 1),
    );
    // our cards appear in sorted order as they land; the cursor waits for play
    let cursor_in = |row: HandRow| (phase == Phase::Playing && view.row == row).then_some(view.cursor);
    draw_hand(frame, &main, hand_y, &view.selected, cursor_in(HandRow::Main), gweilo);
    if !split.is_empty() {
        draw_hand(frame, &split, split_y, &view.selected, cursor_in(HandRow::Split), gweilo);
    }
    if phase == Phase::Playing && hints {
        let hint = if split.is_empty() {
            "[←/→] move · [Space] select · [S] split · [Backspace] clear"
        } else {
            "[←/→] move · [↑/↓] hand · [Space] select · [S] split · [Backspace] clear"
        };
        frame.render_widget(
            Paragraph::new(hint),
            Rect::new(area.x + 1, area.bottom().saturating_sub(1), area.width, 1)
                .intersection(area),
        );
    }

    // moving cards are drawn last so they pass over everything else
    let start = (cx.saturating_sub(CARD_WIDTH / 2), cy.saturating_sub(1));
    for card in landed..launched {
        let target = destination(view.deal_target(card));
        let flown = elapsed.saturating_sub(DEAL_INTERVAL * card as u32);
        let t = ease_out(flown.as_secs_f32() / DEAL_FLIGHT.as_secs_f32());
        let rect = card_rect(lerp(start.0, target.0, t), lerp(start.1, target.1, t));
        draw_card_back(frame, rect);
    }

    // A cleared table sweeps up and off the top of the screen, speeding up as
    // it goes, rather than toward anyone's hand. Once its top edge would pass
    // the top of the screen it's gone.
    if let Some((play, t)) = view.sweep()
        && !view.cloud_covers_table()
    {
        let distance = (kitty_y + CARD_HEIGHT + 1) as f32;
        let rise = (distance * t * t).round() as u16;
        if rise <= kitty_y {
            draw_play(frame, view, play, kitty_y - rise, gweilo);
        }
    }
    if let Some(since) = view.cloud() {
        // standing on the line under the table's cards
        draw_mushroom(frame, since, cx, kitty_y + CARD_HEIGHT);
    }
    if let Some(since) = view.blast() {
        // centred on the table's cards, and kept clear of our prompt and hand
        let centre = kitty_y + CARD_HEIGHT / 2;
        draw_bomb_blast(frame, since, cx, centre, prompt_y.saturating_sub(1));
    }
    if let (Some(x), Some(t)) = (plane_x, view.flight()) {
        // rolling back and forth, snapped to the nearest frame
        let roll = (t * AIRPLANE_ROLLS * 2.0 * PI).sin();
        let frame_index = ((roll + 1.0) * 2.0).round() as usize;
        // the lower wing tip clears the line naming the table's player, just
        // above the cards
        let top = kitty_y as i32 - 1 - AIRPLANE[0].len() as i32;
        draw_art(frame, &AIRPLANE[frame_index], x, top);
    }

    // the kitty flips face up all at once, then slides to the landlord together
    if phase == Phase::Crowning
        && let Some(crowning) = &view.landlord
    {
        let slid = crowning.at.elapsed().saturating_sub(KITTY_REVEAL);
        let t = ease_out(slid.as_secs_f32() / KITTY_SLIDE.as_secs_f32());
        let target = destination(crowning.seat);
        for (i, &card) in crowning.kitty.iter().enumerate() {
            let rect = card_rect(lerp(kitty_x(i), target.0, t), lerp(kitty_y, target.1, t));
            draw_card_face(frame, rect, card, gweilo);
        }
    }

    if let Some((headline, won)) = view.result(gweilo) {
        // a 春天 gets its characters above the box, the pair centred together
        let art_height = if view.spring { SPRING.len() as u16 + 1 } else { 0 };
        let column = area.centered(Constraint::Length(46), Constraint::Length(art_height + 8));
        let rect = Rect::new(column.x, column.y + art_height, column.width, 8);
        if view.spring {
            let width = SPRING[0].chars().count() as u16;
            let x = area.x + area.width.saturating_sub(width) / 2;
            clear_rect(frame, Rect::new(x, column.y, width, SPRING.len() as u16));
            draw_art(frame, &SPRING, x as i32, column.y as i32);
        }
        clear_rect(frame, rect);
        let question = match view.voted {
            None => "Play again? [Y] yes · [N] no",
            Some(_) => "Waiting for the others...",
        };
        // Gloating is a sideshow, so it goes last. Winners can always gloat,
        // so the line stays as long as hints do.
        let gloat = if hints && won { "[G] gloat" } else { "" };
        let text = format!(
            "{headline}\n\n{question}\n{}/{NUM_PLAYERS} ready\n\n{gloat}",
            view.ready
        );
        frame.render_widget(
            Paragraph::new(text)
                .alignment(Alignment::Center)
                .block(Block::bordered().title(" Game over ")),
            rect,
        );
        // one line per gloating winner under the box, so both peasants show
        for (i, seat) in view.gloating().into_iter().enumerate() {
            let who = if seat == view.seat {
                "You".to_string()
            } else {
                view.names[seat].clone()
            };
            frame.render_widget(
                Paragraph::new(format!("{who} gloated")).alignment(Alignment::Center),
                Rect::new(area.x, rect.bottom() + i as u16, area.width, 1).intersection(area),
            );
        }
    }

    if let Some(seat) = view.vacant {
        let rect = area.centered(Constraint::Length(46), Constraint::Length(5));
        clear_rect(frame, rect);
        let text = format!(
            "{} left the game\nWaiting for someone to join the lobby...",
            view.names[seat]
        );
        frame.render_widget(
            Paragraph::new(text)
                .alignment(Alignment::Center)
                .block(Block::bordered().title(" Game on hold ")),
            rect,
        );
    }
}

// The combo sheet over the table while it's open, or else the corner hint
// for opening it.
fn draw_sheet_or_hint(frame: &mut Frame, view: &GameView, theme: Theme) {
    if let Some(sheet) = &view.sheet {
        draw_combo_sheet(frame, sheet, theme.hints, theme.gweilo);
    } else if theme.hints {
        let area = frame.area();
        frame.render_widget(
            Paragraph::new("[C] combos").alignment(Alignment::Right),
            Rect::new(area.x, area.y, area.width.saturating_sub(1), 1),
        );
    }
}

// Gives a key to the combo sheet: C opens it, and while it's open it takes
// every key. Returns whether the sheet took the key.
fn sheet_key(view: &mut GameView, code: KeyCode) -> bool {
    match &mut view.sheet {
        Some(sheet) => {
            if !sheet.key(code) {
                view.sheet = None;
            }
            true
        }
        None if matches!(code, KeyCode::Char('c' | 'C')) => {
            view.sheet = Some(ComboSheet {
                selected: 0,
                open: false,
            });
            true
        }
        None => false,
    }
}

// The list of combinations over the table, and the selected one's details
// in a box on top once it's opened.
fn draw_combo_sheet(frame: &mut Frame, sheet: &ComboSheet, hints: bool, gweilo: bool) {
    let area = frame.area();
    let list_height = COMBO_SHEET.len() as u16 + 2;
    let rect = area.centered(Constraint::Length(30), Constraint::Length(list_height + 1));
    let [list, hint] =
        Layout::vertical([Constraint::Length(list_height), Constraint::Length(1)]).areas(rect);
    clear_rect(frame, rect);
    let lines: Vec<String> = COMBO_SHEET
        .iter()
        .enumerate()
        .map(|(i, entry)| {
            let cursor = if i == sheet.selected { ">" } else { " " };
            format!("{cursor} {}", entry.name(gweilo))
        })
        .collect();
    frame.render_widget(
        Paragraph::new(lines.join("\n")).block(Block::bordered().title(" Combos ")),
        list,
    );
    if hints {
        let text = if sheet.open {
            "[Esc] back"
        } else {
            "[↑/↓] select · [Enter] open · [Esc] close"
        };
        frame.render_widget(
            Paragraph::new(text).alignment(Alignment::Center),
            Rect::new(area.x, hint.y, area.width, 1),
        );
    }

    if sheet.open {
        let entry = &COMBO_SHEET[sheet.selected];
        let rect = area.centered(Constraint::Length(48), Constraint::Length(8));
        clear_rect(frame, rect);
        frame.render_widget(
            Paragraph::new(format!("{}\n\ne.g. {}", entry.description, entry.example))
                .wrap(Wrap { trim: true })
                .block(Block::bordered().title(format!(" {} ", entry.name(gweilo)))),
            rect,
        );
    }
}

// A play on the table: its cards with whoever played them above and the kind
// of combination below.
fn draw_play(frame: &mut Frame, view: &GameView, play: &Play, y: u16, gweilo: bool) {
    let area = frame.area();
    let mut cards = play.cards.clone();
    cards.sort();
    if y > area.y {
        frame.render_widget(
            Paragraph::new(view.names[play.seat].as_str()).alignment(Alignment::Center),
            Rect::new(area.x, y - 1, area.width, 1).intersection(area),
        );
    }
    draw_hand(frame, &cards, y, &BTreeSet::new(), None, gweilo);
    frame.render_widget(
        Paragraph::new(play.combo.name(gweilo)).alignment(Alignment::Center),
        Rect::new(area.x, y + CARD_HEIGHT, area.width, 1).intersection(area),
    );
}

// How thick the nuke's smoke is, 0 to 1, at a point `ux` across from the
// middle and `uy` up from the ground, `secs` after the blast. Distances are
// in lines; a terminal cell is about twice as tall as it is wide, so callers
// halve horizontal distances to keep the shapes round.
fn smoke(ux: f32, uy: f32, secs: f32) -> f32 {
    // a fireball swelling at the ground
    if secs < NUKE_FLASH {
        let radius = 1.0 + 3.0 * secs / NUKE_FLASH;
        let distance = (ux * ux + uy * uy).sqrt();
        return (1.6 * (1.0 - distance / radius)).clamp(0.0, 1.0);
    }
    let p = ease_out((secs - NUKE_FLASH) / NUKE_RISE);
    // the cap: a wide, flat ellipse climbing and growing as it goes
    let height = 3.0 + 8.0 * p;
    let radius = 2.0 + 5.0 * p;
    let (cap_x, cap_y) = (ux / (radius * 1.7), (uy - height) / (radius * 0.7));
    let cap = 1.0 - (cap_x * cap_x + cap_y * cap_y).sqrt();
    // the stem, tapering toward the cap
    let stem = if (0.0..=height).contains(&uy) {
        let half_width = 0.9 + 0.6 * (1.0 - uy / height);
        // as thick as the cap, so the column is the last thing left
        1.0 - ux.abs() / half_width
    } else {
        0.0
    };
    // Dust rolling out along the ground. Below the ground line it's a disc
    // lying on the ground, seen in perspective like the base ring, so its
    // near edge curves down toward us and the base doesn't look cut flat.
    let spread = 1.5 + 7.0 * p;
    let skirt = if uy >= 0.0 {
        let (x, y) = (ux / spread, uy / 1.3);
        0.7 * (1.0 - (x * x + y * y).sqrt())
    } else {
        let nearness = 1.0 - uy / NUKE_EYE_HEIGHT;
        let (x, z) = (ux / nearness, NUKE_EYE_DISTANCE - NUKE_EYE_DISTANCE / nearness);
        0.7 * (1.0 - (x * x + z * z).sqrt() / spread)
    };
    let body = cap.max(stem).max(skirt);
    if body <= 0.0 {
        return 0.0;
    }
    // a slow churn through the smoke, so it billows rather than sits still
    let churn = 0.12 * (ux * 1.1 + secs * 2.5).sin() * (uy * 1.6 - secs * 1.8).cos();
    (1.8 * body + churn).clamp(0.0, 1.0)
}

// Draws a field of smoke around (cx, cy), between lines `top` and `bottom`
// and up to `reach` columns either side. `thickness` gives 0 to 1 at a point
// `ux` across and `uy` up from (cx, cy), in lines; a terminal cell is about
// twice as tall as it is wide, so `ux` counts half-columns to keep shapes
// round. `scale` shrinks the whole field to fit. Each cell's shade is
// dithered, and blank cells let whatever is underneath show through.
fn draw_smoke(
    frame: &mut Frame,
    (cx, cy): (u16, u16),
    reach: u16,
    (top, bottom): (u16, u16),
    scale: f32,
    thickness: impl Fn(f32, f32) -> f32,
) {
    let area = frame.area();
    let buf = frame.buffer_mut();
    for y in top.max(area.top())..=bottom.min(area.bottom().saturating_sub(1)) {
        let uy = (cy as f32 - y as f32) / scale;
        for x in cx.saturating_sub(reach)..=(cx + reach).min(area.right().saturating_sub(1)) {
            let ux = (x as f32 - cx as f32) / 2.0 / scale;
            let dither = (BAYER[y as usize % 4][x as usize % 4] + 0.5) / 16.0 - 0.5;
            let shade = (thickness(ux, uy) * 4.0 + dither).round().clamp(0.0, 4.0) as usize;
            if shade > 0
                && let Some(cell) = buf.cell_mut((x, y))
            {
                cell.set_symbol(SMOKE[shade]);
            }
        }
    }
}

// how far through fading a smoke effect is, 0 to 1
fn fade_progress(secs: f32, fade_start: f32, total: Duration) -> f32 {
    ((secs - fade_start) / (total.as_secs_f32() - fade_start)).clamp(0.0, 1.0)
}

// The nuke's base ring, 0 to 1, at screen point `ux` across and `uy` up
// from the foot of the stem: a ring on the ground rolling outward and
// thinning as it goes, seen in perspective. Each screen point is traced back
// to the point on the ground it would show; rows above the horizon show none.
fn nuke_ring(ux: f32, uy: f32, secs: f32) -> f32 {
    let t = (secs - NUKE_RING_START) / NUKE_RING_LIFE;
    if !(0.0..1.0).contains(&t) {
        return 0.0;
    }
    // how much nearer than the stem the ground at this row is: 1 at the
    // stem's foot, more below it, less up toward the horizon
    let nearness = 1.0 - uy / NUKE_EYE_HEIGHT;
    if nearness <= 0.05 {
        return 0.0;
    }
    // across, and toward us, on the ground
    let (x, z) = (ux / nearness, NUKE_EYE_DISTANCE - NUKE_EYE_DISTANCE / nearness);
    let radius = 2.0 + NUKE_RING_REACH * ease_out(t);
    let off_ring = ((x * x + z * z).sqrt() - radius) / (0.55 + 0.035 * radius);
    let band = (-off_ring * off_ring).exp();
    // the far side is a little dimmer than the near
    let brightness = (0.6 + 0.3 * nearness).min(1.0);
    (1.3 * band * brightness * (1.0 - t).powf(1.6)).min(1.0)
}

// One frame of the nuke's cloud, `since` it went off, centred on `cx` and
// standing on line `ground`. It drifts upward as it clears, peeling rather
// than fading evenly: the clearing eats into every cell alike, so thin outer
// wisps go first and the dense column is the last to go.
fn draw_mushroom(frame: &mut Frame, since: Duration, cx: u16, ground: u16) {
    let secs = since.as_secs_f32();
    let fade = fade_progress(secs, NUKE_FADE_START, NUKE_CLOUD);
    let drift = 1.2 * fade;
    let peel = 1.15 * fade.powf(0.8);
    // shrink the whole cloud to fit above the ground if the screen is short
    let top = frame.area().top();
    let room = ground.saturating_sub(top) as f32 + 1.0;
    let scale = (room / NUKE_HEIGHT).min(1.0);
    // the ring spreads wider than the cloud, out to the screen's edges
    let reach = frame.area().width;
    draw_smoke(frame, (cx, ground), reach, (top, ground), scale, |ux, uy| {
        let cloud = (smoke(ux, uy - drift, secs) - peel).max(0.0);
        cloud.max(nuke_ring(ux, uy, secs))
    });
    // the base's near edge and the ring's near side come toward us, down
    // over the rest of the screen
    let bottom = frame.area().bottom().saturating_sub(1);
    draw_smoke(frame, (cx, ground), reach, (ground + 1, bottom), scale, |ux, uy| {
        let base = (smoke(ux, uy - drift, secs) - peel).max(0.0);
        base.max(nuke_ring(ux, uy, secs))
    });
}

// How thick a bomb's blast is, 0 to 1, at a point `ux` across and `uy` up
// from its centre, `secs` after it went off: a fireball, a shockwave ring,
// and beams turning as they shoot out, alternately long and short.
fn bomb_blast(ux: f32, uy: f32, secs: f32) -> f32 {
    let distance = (ux * ux + uy * uy).sqrt();
    if secs < BOMB_FLASH {
        let radius = 0.5 + 2.0 * secs / BOMB_FLASH;
        return (1.6 * (1.0 - distance / radius)).clamp(0.0, 1.0);
    }
    let p = ease_out((secs - BOMB_FLASH) / BOMB_GROW);
    let radius = 2.0 + (BOMB_RADIUS - 2.0) * p;
    if distance >= 1.35 * radius + 1.0 {
        return 0.0;
    }
    let core = 1.0 - distance / (0.55 * radius);
    let angle = uy.atan2(ux) + secs * 0.8;
    let long_beam = (4.0 * angle).cos().max(0.0).powi(6) * (1.0 - distance / (1.35 * radius));
    let short_beam =
        (4.0 * angle + PI).cos().max(0.0).powi(6) * (1.0 - distance / (0.95 * radius));
    let ring = 0.8 * (-((distance - radius) / 0.9).powi(2)).exp() * (1.0 - 0.5 * p);
    let body = core.max(long_beam).max(short_beam).max(ring);
    if body <= 0.05 {
        return 0.0;
    }
    let churn = 0.1 * (ux * 1.3 + secs * 3.0).sin() * (uy * 1.7 - secs * 2.2).cos();
    (1.6 * body + churn).clamp(0.0, 1.0)
}

// One frame of a bomb's blast, `since` it went off, centred on (cx, cy).
// It's cut off at line `floor` so it never covers our hand. Like the
// mushroom cloud it thins and drifts up.
fn draw_bomb_blast(frame: &mut Frame, since: Duration, cx: u16, cy: u16, floor: u16) {
    let secs = since.as_secs_f32();
    let fade = fade_progress(secs, BOMB_FADE_START, BOMB_BLAST);
    // the long beams reach this far out, in lines
    let extent = 1.35 * BOMB_RADIUS + 1.0;
    // shrink it to fit above the centre if the screen is short; below, the
    // floor just cuts it off
    let room = cy.saturating_sub(frame.area().top()) as f32 + 1.0;
    let scale = (room / extent).min(1.0);
    let span = (extent * scale).ceil() as u16;
    draw_smoke(
        frame,
        (cx, cy),
        span * 2,
        (cy.saturating_sub(span), floor.min(cy + span)),
        scale,
        |ux, uy| bomb_blast(ux, uy - fade, secs) * (1.0 - fade),
    );
}

// Draws `art` with its top-left corner at (x, y), which can be off screen.
// Spaces are see-through, and anything past the edges is left out.
fn draw_art(frame: &mut Frame, art: &[&str], x: i32, y: i32) {
    let area = frame.area();
    let buf = frame.buffer_mut();
    for (row, line) in art.iter().enumerate() {
        let cell_y = y + row as i32;
        for (column, ch) in line.chars().enumerate() {
            let cell_x = x + column as i32;
            if ch == ' '
                || !(area.left() as i32..area.right() as i32).contains(&cell_x)
                || !(area.top() as i32..area.bottom() as i32).contains(&cell_y)
            {
                continue;
            }
            if let Some(cell) = buf.cell_mut((cell_x as u16, cell_y as u16)) {
                cell.set_char(ch);
            }
        }
    }
}

fn card_rect(x: u16, y: u16) -> Rect {
    Rect::new(x, y, CARD_WIDTH, CARD_HEIGHT)
}

// Blanks out a rectangle so whatever is drawn there next hides what was
// underneath. Unlike ratatui's Clear widget, this keeps the theme colours.
fn clear_rect(frame: &mut Frame, rect: Rect) {
    let rect = rect.intersection(frame.area());
    let buf = frame.buffer_mut();
    for y in rect.top()..rect.bottom() {
        for x in rect.left()..rect.right() {
            if let Some(cell) = buf.cell_mut((x, y)) {
                cell.set_symbol(" ");
            }
        }
    }
}

// a blank bordered rectangle that hides whatever is underneath it
fn draw_card_back(frame: &mut Frame, rect: Rect) {
    let rect = rect.intersection(frame.area());
    clear_rect(frame, rect);
    frame.render_widget(Block::bordered(), rect);
}

fn draw_card_face(frame: &mut Frame, rect: Rect, card: Card, gweilo: bool) {
    let rect = rect.intersection(frame.area());
    clear_rect(frame, rect);
    frame.render_widget(
        Paragraph::new(card.face(gweilo)).block(Block::bordered()),
        rect,
    );
}

// Face-up cards overlapping by one column, with their shared borders merged.
// Picked cards slide up a row in front of their neighbours, and the cursor
// is a ▲ under its card:
//    ┌──┐
// ┌──│10│──┐
// │3 │♦ │A │
// │♣ └──┘♠ │
// └──┘  └──┘
//     ▲
fn draw_hand(
    frame: &mut Frame,
    cards: &[Card],
    y: u16,
    selected: &BTreeSet<Card>,
    cursor: Option<usize>,
    gweilo: bool,
) {
    let area = frame.area();
    let stride = CARD_WIDTH - 1;
    let width = cards.len() as u16 * stride + 1;
    let x0 = area.x + area.width.saturating_sub(width) / 2;
    let x_of = |i: usize| x0 + i as u16 * stride;
    let picked = |i: usize| selected.contains(&cards[i]);

    for i in (0..cards.len()).filter(|&i| !picked(i)) {
        let rect = card_rect(x_of(i), y).intersection(area);
        let face = Paragraph::new(cards[i].face(gweilo))
            .block(Block::bordered().merge_borders(MergeStrategy::Exact));
        frame.render_widget(face, rect);
    }

    // Picked cards go on top with plain borders; merging them into the row
    // would join their sides to the neighbours' and make them look taller.
    let raised_y = y.saturating_sub(1);
    for i in (0..cards.len()).filter(|&i| picked(i)) {
        let rect = card_rect(x_of(i), raised_y).intersection(area);
        clear_rect(frame, rect);
        frame.render_widget(
            Paragraph::new(cards[i].face(gweilo)).block(Block::bordered()),
            rect,
        );
        // two picked neighbours share a border, so join its corners
        if i > 0 && picked(i - 1) {
            let buf = frame.buffer_mut();
            if let Some(cell) = buf.cell_mut((x_of(i), raised_y)) {
                cell.set_symbol("┬");
            }
            if let Some(cell) = buf.cell_mut((x_of(i), raised_y + CARD_HEIGHT - 1)) {
                cell.set_symbol("┴");
            }
        }
    }
    if let Some(i) = cursor.filter(|&i| i < cards.len()) {
        // under the rank, which sits in the card's first inside column
        let x = x0 + i as u16 * stride + 1;
        frame.render_widget(
            Paragraph::new("▲"),
            Rect::new(x, y + CARD_HEIGHT, 1, 1).intersection(area),
        );
    }
}

fn run_message(terminal: &mut DefaultTerminal, theme: Theme, msg: &str) -> io::Result<()> {
    loop {
        draw_themed(terminal, theme, |frame| {
            let area = frame
                .area()
                .centered(Constraint::Fill(1), Constraint::Length(3));
            frame.render_widget(
                Paragraph::new(if theme.hints {
                    format!("{msg}\n\n[Esc] to go back")
                } else {
                    msg.to_string()
                })
                .alignment(Alignment::Center),
                area,
            );
        })?;
        if let Event::Key(key) = read_event()?
            && key.kind == KeyEventKind::Press
            && key.code == KeyCode::Esc
        {
            return Ok(());
        }
    }
}

#[derive(Clone, Copy)]
struct Theme {
    fg: Color,
    bg: Color,
    // whether to show the lines that explain the controls; confirmations and
    // prompts that ask something are shown regardless
    hints: bool,
    // roles and combinations in English and jokers as emoji, for fun
    gweilo: bool,
}

// Paints every cell with the theme before rendering; widgets that don't set
// their own colours inherit it. Color::Reset means the terminal's own colour.
fn draw_themed(
    terminal: &mut DefaultTerminal,
    theme: Theme,
    render: impl FnOnce(&mut Frame),
) -> io::Result<()> {
    terminal.draw(|frame| {
        let area = frame.area();
        frame
            .buffer_mut()
            .set_style(area, Style::new().fg(theme.fg).bg(theme.bg));
        if too_small(area.width, area.height) {
            draw_too_small(frame);
        } else {
            render(frame);
        }
        // drawn last so it covers any other prompt in the same corner
        if CTRL_C_ARMED.load(Ordering::Relaxed) {
            draw_quit_prompt(frame, "Press [Ctrl+C] again to quit");
        }
    })?;
    Ok(())
}

// The smallest terminal the screens are laid out for: the landlord's 20 cards,
// a split hand and the table only just fit in 24 lines.
const MIN_WIDTH: u16 = 80;
const MIN_HEIGHT: u16 = 24;

fn too_small(width: u16, height: u16) -> bool {
    width < MIN_WIDTH || height < MIN_HEIGHT
}

// shown instead of every screen while the terminal is too small
fn draw_too_small(frame: &mut Frame) {
    let area = frame.area();
    let text = format!(
        "This terminal is too small\n\nMake it at least {MIN_WIDTH}×{MIN_HEIGHT}\n(it's {}×{} now)",
        area.width, area.height
    );
    frame.render_widget(
        Paragraph::new(text)
            .alignment(Alignment::Center)
            .wrap(Wrap { trim: true }),
        area.centered_vertically(Constraint::Length(4)),
    );
}

// set by one Ctrl+C, so that a second quits to the terminal
static CTRL_C_ARMED: AtomicBool = AtomicBool::new(false);

// The error that carries a confirmed Ctrl+C up through every screen to main.
#[derive(Debug)]
struct QuitRequested;

impl fmt::Display for QuitRequested {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("quit requested")
    }
}

impl std::error::Error for QuitRequested {}

fn is_quit(e: &io::Error) -> bool {
    e.get_ref().is_some_and(|inner| inner.is::<QuitRequested>())
}

// Every screen reads input through this, so Ctrl+C works the same anywhere:
// the first arms a prompt, the second quits, and any other key disarms it
// and goes through as normal, unless the terminal is too small to play in.
// Swallowed presses come back as a non-key event, which every screen
// ignores apart from redrawing.
fn read_event() -> io::Result<Event> {
    let event = event::read()?;
    let Event::Key(key) = &event else {
        return Ok(event);
    };
    if key.kind != KeyEventKind::Press {
        return Ok(event);
    }
    let ctrl_c =
        key.code == KeyCode::Char('c') && key.modifiers.contains(KeyModifiers::CONTROL);
    if !ctrl_c {
        CTRL_C_ARMED.store(false, Ordering::Relaxed);
        // nobody should play blind while the too-small notice is up
        let (width, height) = terminal::size()?;
        if too_small(width, height) {
            return Ok(Event::FocusGained);
        }
        return Ok(event);
    }
    if CTRL_C_ARMED.swap(true, Ordering::Relaxed) {
        return Err(io::Error::other(QuitRequested));
    }
    Ok(Event::FocusGained)
}

// the colours the settings screen cycles through, starting with the terminal default
const COLOR_CHOICES: [Color; 17] = [
    Color::Reset,
    Color::Black,
    Color::Red,
    Color::Green,
    Color::Yellow,
    Color::Blue,
    Color::Magenta,
    Color::Cyan,
    Color::Gray,
    Color::DarkGray,
    Color::LightRed,
    Color::LightGreen,
    Color::LightYellow,
    Color::LightBlue,
    Color::LightMagenta,
    Color::LightCyan,
    Color::White,
];

fn cycle_color(color: Color, step: isize) -> Color {
    // a custom colour from the file (e.g. "#1E1E2E") isn't in the list, so it restarts at Default
    let len = COLOR_CHOICES.len() as isize;
    let i = COLOR_CHOICES
        .iter()
        .position(|&c| c == color)
        .map_or(0, |i| i as isize);
    COLOR_CHOICES[(i + step).rem_euclid(len) as usize]
}

fn color_name(color: Color) -> String {
    match color {
        Color::Reset => "Default".to_string(),
        c => c.to_string(),
    }
}

// Colours are stored as "Default", a name ratatui understands ("LightBlue"),
// a 256-colour index ("42") or hex ("#1E1E2E"). Anything unparseable becomes
// Default instead of failing, so a typo doesn't discard the rest of the file.
mod color_setting {
    use super::color_name;
    use ratatui::style::Color;
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn serialize<S: Serializer>(color: &Color, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&color_name(*color))
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<Color, D::Error> {
        let text = String::deserialize(deserializer)?;
        if text.eq_ignore_ascii_case("default") {
            return Ok(Color::Reset);
        }
        Ok(text.parse().unwrap_or(Color::Reset))
    }
}

#[derive(Serialize, Deserialize)]
#[serde(default)]
struct Settings {
    player_name: String,
    #[serde(with = "color_setting")]
    foreground: Color,
    #[serde(with = "color_setting")]
    background: Color,
    show_hints: bool,
    gweilo_mode: bool,
}

impl Default for Settings {
    fn default() -> Settings {
        Settings {
            player_name: DEFAULT_PLAYER_NAME.to_string(),
            foreground: Color::Reset,
            background: Color::Reset,
            show_hints: true,
            gweilo_mode: false,
        }
    }
}

impl Settings {
    fn theme(&self) -> Theme {
        Theme {
            fg: self.foreground,
            bg: self.background,
            hints: self.show_hints,
            gweilo: self.gweilo_mode,
        }
    }

    fn save_status(&self) -> String {
        match self.save() {
            Ok(()) => "Saved".to_string(),
            Err(e) => format!("Couldn't save: {e}"),
        }
    }

    // the settings file lives next to the executable
    fn path() -> Option<PathBuf> {
        Some(env::current_exe().ok()?.parent()?.join(SETTINGS_FILE))
    }

    // a missing or unreadable file falls back to defaults; missing keys do too
    fn load() -> Settings {
        Settings::path()
            .and_then(|path| fs::read_to_string(path).ok())
            .and_then(|text| toml::from_str(&text).ok())
            .unwrap_or_default()
    }

    fn save(&self) -> io::Result<()> {
        let path = Settings::path()
            .ok_or_else(|| io::Error::other("can't find the executable's directory"))?;
        let text = toml::to_string(self).map_err(io::Error::other)?;
        fs::write(path, text)
    }
}

#[derive(Clone, Copy, PartialEq)]
enum SettingRow {
    Name,
    Foreground,
    Background,
    Hints,
    GweiloMode,
}

impl SettingRow {
    const ALL: [SettingRow; 5] = [
        SettingRow::Name,
        SettingRow::Foreground,
        SettingRow::Background,
        SettingRow::Hints,
        SettingRow::GweiloMode,
    ];

    fn label(self) -> &'static str {
        match self {
            SettingRow::Name => "Name",
            SettingRow::Foreground => "Foreground",
            SettingRow::Background => "Background",
            SettingRow::Hints => "Hints",
            SettingRow::GweiloMode => "Gweilo mode",
        }
    }
}

enum SettingsMode {
    Browsing,
    // holds the name typed so far
    EditingName(String),
    // holds the last saved colour, restored if the choice is cancelled
    PickingColor(Color),
    // holds the last saved on/off setting, restored if the choice is cancelled
    Toggling(bool),
}

fn run_settings(terminal: &mut DefaultTerminal, settings: &mut Settings) -> io::Result<()> {
    let mut selected = 0;
    let mut mode = SettingsMode::Browsing;
    let mut status: Option<String> = None;
    loop {
        // drawn with the current settings so colour choices preview immediately
        draw_themed(terminal, settings.theme(), |frame| {
            draw_settings(frame, settings, selected, &mode, status.as_deref())
        })?;
        let Event::Key(key) = read_event()? else {
            continue;
        };
        if key.kind != KeyEventKind::Press {
            continue;
        }
        let row = SettingRow::ALL[selected];
        match &mut mode {
            SettingsMode::Browsing => match key.code {
                KeyCode::Esc => return Ok(()),
                // wraps around at the top and bottom
                KeyCode::Up | KeyCode::Char('k') => {
                    selected = (selected + SettingRow::ALL.len() - 1) % SettingRow::ALL.len();
                }
                KeyCode::Down | KeyCode::Char('j') => {
                    selected = (selected + 1) % SettingRow::ALL.len();
                }
                KeyCode::Enter => {
                    status = None;
                    mode = match row {
                        SettingRow::Name => SettingsMode::EditingName(settings.player_name.clone()),
                        SettingRow::Foreground => SettingsMode::PickingColor(settings.foreground),
                        SettingRow::Background => SettingsMode::PickingColor(settings.background),
                        SettingRow::Hints => SettingsMode::Toggling(settings.show_hints),
                        SettingRow::GweiloMode => SettingsMode::Toggling(settings.gweilo_mode),
                    };
                }
                _ => {}
            },
            SettingsMode::EditingName(name) => match key.code {
                KeyCode::Esc => mode = SettingsMode::Browsing,
                KeyCode::Backspace => {
                    name.pop();
                }
                KeyCode::Char(c)
                    if !key
                        .modifiers
                        .intersects(KeyModifiers::CONTROL | KeyModifiers::ALT)
                        && name.chars().count() < MAX_NAME_LEN =>
                {
                    name.push(c);
                }
                KeyCode::Enter => {
                    let name = name.trim();
                    if name.is_empty() {
                        status = Some("Name can't be empty".to_string());
                        continue;
                    }
                    settings.player_name = name.to_string();
                    mode = SettingsMode::Browsing;
                    status = Some(settings.save_status());
                }
                _ => {}
            },
            SettingsMode::PickingColor(saved) => {
                // the colour is changed in memory as a preview; only Enter writes the file
                let color = if row == SettingRow::Foreground {
                    &mut settings.foreground
                } else {
                    &mut settings.background
                };
                match key.code {
                    KeyCode::Left | KeyCode::Char('h') => *color = cycle_color(*color, -1),
                    KeyCode::Right | KeyCode::Char('l') => *color = cycle_color(*color, 1),
                    KeyCode::Esc => {
                        *color = *saved;
                        mode = SettingsMode::Browsing;
                    }
                    KeyCode::Enter => {
                        mode = SettingsMode::Browsing;
                        status = Some(settings.save_status());
                    }
                    _ => {}
                }
            }
            // like a colour, previewed in memory until Enter saves it
            SettingsMode::Toggling(saved) => {
                let flag = if row == SettingRow::Hints {
                    &mut settings.show_hints
                } else {
                    &mut settings.gweilo_mode
                };
                match key.code {
                    KeyCode::Left | KeyCode::Char('h') | KeyCode::Right | KeyCode::Char('l') => {
                        *flag = !*flag;
                    }
                    KeyCode::Esc => {
                        *flag = *saved;
                        mode = SettingsMode::Browsing;
                    }
                    KeyCode::Enter => {
                        mode = SettingsMode::Browsing;
                        status = Some(settings.save_status());
                    }
                    _ => {}
                }
            }
        }
    }
}

fn draw_settings(
    frame: &mut Frame,
    settings: &Settings,
    selected: usize,
    mode: &SettingsMode,
    status: Option<&str>,
) {
    let area = frame
        .area()
        .centered(Constraint::Length(44), Constraint::Length(SettingRow::ALL.len() as u16 + 4));
    let [panel, hint, status_line] = Layout::vertical([
        Constraint::Length(SettingRow::ALL.len() as u16 + 2),
        Constraint::Length(1),
        Constraint::Length(1),
    ])
    .areas(area);

    let lines: Vec<String> = SettingRow::ALL
        .iter()
        .enumerate()
        .map(|(i, &row)| {
            let active = i == selected;
            let value = match (row, mode) {
                (SettingRow::Name, SettingsMode::EditingName(name)) if active => format!("{name}█"),
                (SettingRow::Name, _) => settings.player_name.clone(),
                (SettingRow::Foreground, _) => color_name(settings.foreground),
                (SettingRow::Background, _) => color_name(settings.background),
                (SettingRow::Hints, _) => {
                    if settings.show_hints { "Shown" } else { "Hidden" }.to_string()
                }
                (SettingRow::GweiloMode, _) => {
                    if settings.gweilo_mode { "On" } else { "Off" }.to_string()
                }

            };
            let value = match mode {
                SettingsMode::PickingColor(_) | SettingsMode::Toggling(_) if active => {
                    format!("◀ {value} ▶")
                }
                _ => value,
            };
            let cursor = if active { ">" } else { " " };
            format!("{cursor} {:<12} {value}", row.label())
        })
        .collect();
    frame.render_widget(
        Paragraph::new(lines.join("\n")).block(Block::bordered().title(" Settings ")),
        panel,
    );

    let hint_text = match mode {
        SettingsMode::Browsing => "[↑/↓] select · [Enter] change · [Esc] back",
        SettingsMode::EditingName(_) => "[Enter] save · [Esc] cancel",
        SettingsMode::PickingColor(_) | SettingsMode::Toggling(_) => {
            "[←/→] choose · [Enter] save · [Esc] cancel"
        }
    };
    if settings.show_hints {
        frame.render_widget(Paragraph::new(hint_text).alignment(Alignment::Center), hint);
    }
    if let Some(msg) = status {
        frame.render_widget(
            Paragraph::new(msg).alignment(Alignment::Center),
            status_line,
        );
    }
}

fn run_app(terminal: &mut DefaultTerminal) -> io::Result<()> {
    // read once at startup; the settings screen updates this copy as well as the file
    let mut settings = Settings::load();
    // why we've come back to the menu, shown until the player picks something
    let mut notice: Option<String> = None;
    loop {
        notice = match run_menu(terminal, settings.theme(), notice.as_deref())? {
            Some(MenuChoice::Host) => run_host(terminal, &settings)?,
            Some(MenuChoice::Join) => run_join(terminal, &settings)?,
            Some(MenuChoice::Settings) => {
                run_settings(terminal, &mut settings)?;
                None
            }
            Some(MenuChoice::Playground) => {
                run_playground(terminal, settings.theme())?;
                None
            }
            None => return Ok(()),
        };
    }
}

// Hidden commands, typed after a :. Nothing advertises them. :debug on the
// main menu opens the playground, a practice table where the others work;
// real games ignore them, apart from pointing :debug at the menu.
#[derive(Clone, Copy)]
enum DebugAnim {
    Airplane,
    Bomb,
    Nuke,
}

enum Command {
    Debug,
    Anim(DebugAnim),
    // jump to the game-over screen, with our side winning or losing, or the
    // landlord winning by 春天
    Finish { win: bool, spring: bool },
    // `force` puts the cards down over whatever is on the table
    Play { cards: Vec<Card>, force: bool },
    // a command that couldn't be read, and why
    Bad(String),
    Unknown,
}

fn parse_command(text: &str) -> Command {
    let words: Vec<&str> = text.split_whitespace().collect();
    match words.as_slice() {
        ["debug"] => Command::Debug,
        ["win"] => Command::Finish {
            win: true,
            spring: false,
        },
        ["lose"] => Command::Finish {
            win: false,
            spring: false,
        },
        ["spring"] => Command::Finish {
            win: false,
            spring: true,
        },
        ["anim", which] => match *which {
            "plane" => Command::Anim(DebugAnim::Airplane),
            "bomb" => Command::Anim(DebugAnim::Bomb),
            "nuke" => Command::Anim(DebugAnim::Nuke),
            _ => Command::Unknown,
        },
        [play @ ("play" | "play!"), names @ ..] => {
            let force = *play == "play!";
            if names.is_empty() {
                return Command::Bad(format!("List the cards to play, like :{play} 3S 3H"));
            }
            let mut cards = Vec::new();
            for name in names {
                let Some(card) = parse_card(name) else {
                    return Command::Bad(format!("Couldn't read {name}"));
                };
                if cards.contains(&card) {
                    return Command::Bad(format!("{name} is listed twice"));
                }
                cards.push(card);
            }
            Command::Play { cards, force }
        }
        _ => Command::Unknown,
    }
}

// Reads a card written as its rank then its suit, like 10S or QH, or BJ and
// RJ for the jokers, which have no suit. Case doesn't matter.
fn parse_card(name: &str) -> Option<Card> {
    let name = name.to_ascii_uppercase();
    match name.as_str() {
        "BJ" => return Some(Card::Joker(JokerColor::Black)),
        "RJ" => return Some(Card::Joker(JokerColor::Red)),
        _ => {}
    }
    if !name.is_ascii() || !(2..=3).contains(&name.len()) {
        return None;
    }
    let (rank, suit) = name.split_at(name.len() - 1);
    let suit = match suit {
        "S" => Suit::Spades,
        "H" => Suit::Hearts,
        "D" => Suit::Diamonds,
        "C" => Suit::Clubs,
        _ => return None,
    };
    let rank = match rank {
        "J" => Rank::Jack,
        "Q" => Rank::Queen,
        "K" => Rank::King,
        "A" => Rank::Ace,
        "2" => Rank::Two,
        number => {
            let n: usize = number.parse().ok()?;
            *Rank::ALL.get(n.checked_sub(3)?).filter(|_| n <= 10)?
        }
    };
    Some(Card::Standard { rank, suit })
}

enum CommandInput {
    // the key had nothing to do with the command line
    NotMine,
    // the command line took the key
    Typing,
    Entered(String),
}

// Commands entered this run, oldest first, shared by every command line.
static HISTORY: Mutex<Vec<String>> = Mutex::new(Vec::new());

// A command being typed after a :.
struct CommandLine {
    text: String,
    // While cycling through history: which entry is showing, and what was
    // being typed before, to come back to past the newest.
    recalled: Option<(usize, String)>,
}

// A : opens the command line; then keys type into it until Enter runs what
// was typed or Esc (or backspacing past the start) closes it. Up and Down
// cycle through earlier commands, which can be edited before Enter.
fn command_key(command: &mut Option<CommandLine>, code: KeyCode) -> CommandInput {
    let Some(line) = command else {
        if code == KeyCode::Char(':') {
            *command = Some(CommandLine {
                text: String::new(),
                recalled: None,
            });
            return CommandInput::Typing;
        }
        return CommandInput::NotMine;
    };
    let mut history = HISTORY.lock().unwrap_or_else(|e| e.into_inner());
    match code {
        KeyCode::Enter => {
            let text = command.take().map(|line| line.text).unwrap_or_default();
            // blanks and repeats of the last command aren't worth keeping
            if !text.trim().is_empty() && history.last() != Some(&text) {
                history.push(text.clone());
            }
            return CommandInput::Entered(text);
        }
        KeyCode::Esc => *command = None,
        KeyCode::Up if !history.is_empty() => {
            let (index, draft) = match line.recalled.take() {
                Some((index, draft)) => (index.saturating_sub(1), draft),
                None => (history.len() - 1, mem::take(&mut line.text)),
            };
            line.text = history[index].clone();
            line.recalled = Some((index, draft));
        }
        KeyCode::Down => {
            if let Some((index, draft)) = line.recalled.take() {
                if index + 1 < history.len() {
                    line.text = history[index + 1].clone();
                    line.recalled = Some((index + 1, draft));
                } else {
                    line.text = draft;
                }
            }
        }
        KeyCode::Backspace => {
            if line.text.pop().is_none() {
                *command = None;
            }
        }
        KeyCode::Char(c) => line.text.push(c),
        _ => {}
    }
    CommandInput::Typing
}

fn draw_command_line(frame: &mut Frame, text: &str) {
    let area = frame.area();
    let line = Rect::new(area.x, area.bottom().saturating_sub(1), area.width, 1);
    clear_rect(frame, line);
    frame.render_widget(Paragraph::new(format!(":{text}█")), line);
}

// sample cards of the given ranks, each copy of a rank in the next suit
fn sample_cards(ranks: &[Rank]) -> Vec<Card> {
    let mut copies: BTreeMap<Rank, usize> = BTreeMap::new();
    ranks
        .iter()
        .map(|&rank| {
            let n = copies.entry(rank).or_default();
            *n += 1;
            Card::Standard {
                rank,
                suit: Suit::ALL[(*n - 1) % Suit::ALL.len()],
            }
        })
        .collect()
}

// Puts a sample play on the playground table to go with an effect, then
// plays it.
fn playground_anim(view: &mut GameView, anim: DebugAnim) {
    use Rank::*;
    view.last_play = match anim {
        DebugAnim::Airplane => Some(Play {
            seat: 1,
            cards: sample_cards(&[Three, Three, Three, Four, Four, Four]),
            combo: Combo::Airplane { high: Four, len: 2 },
        }),
        DebugAnim::Bomb => Some(Play {
            seat: 2,
            cards: sample_cards(&[Seven, Seven, Seven, Seven]),
            combo: Combo::Bomb(Seven),
        }),
        // a nuke clears the table
        DebugAnim::Nuke => None,
    };
    view.debug_anim(anim);
}

// Puts `cards` on the playground table for whoever has the turn, which stays
// with them. They're checked like any play: forced, they only need to be a
// valid combination and go down over whatever is there; otherwise they have
// to beat the table, as in a real game. Their effect plays as normal.
fn playground_play(view: &mut GameView, cards: Vec<Card>, force: bool) -> Result<(), MoveError> {
    let table = if force {
        None
    } else {
        view.last_play.as_ref().map(|play| &play.combo)
    };
    let combo = Combo::fit(&cards, table)?;
    let play = Play {
        seat: view.turn,
        cards,
        combo,
    };
    match combo {
        Combo::Bomb(_) => view.debug_anim(DebugAnim::Bomb),
        Combo::Airplane { .. }
        | Combo::SmallWingedAirplane { .. }
        | Combo::LargeWingedAirplane { .. } => view.debug_anim(DebugAnim::Airplane),
        _ => {}
    }
    if combo == Combo::Nuke {
        // like a real nuke, it clears the table and is shown on its way off
        view.last_play = None;
        view.swept = Some(Swept {
            play,
            at: Instant::now(),
            nuke: true,
        });
    } else {
        view.last_play = Some(play);
    }
    Ok(())
}

// The playground: sample players and a real deal, already played to the
// first turn, to try things on without anyone else. :anim plays an effect,
// :play and :play! put cards on the table, and Esc goes back. Its lobby rules
// have silly effects on, so every effect plays.
fn run_playground(terminal: &mut DefaultTerminal, theme: Theme) -> io::Result<()> {
    let game = Game::new();
    let names = vec!["You".to_string(), "Left".to_string(), "Right".to_string()];
    let hand = game.hands[0].cards.clone();
    let mut view = GameView::new(0, names, game.first, hand, false, LobbySettings::DEFAULT);
    view.crown(1, game.kitty.clone(), false);
    let mut notice = Some(Notice::new("Playground".to_string()));
    loop {
        draw_themed(terminal, theme, |frame| {
            draw_game(frame, &view, notice.as_ref().and_then(Notice::current), theme);
            draw_sheet_or_hint(frame, &view, theme);
            if let Some(text) = &view.command {
                draw_command_line(frame, &text.text);
            }
        })?;
        let moving = view.sweep().is_some() || view.blast().is_some() || view.flight().is_some();
        if !event::poll(if moving { FRAME_INTERVAL } else { POLL_INTERVAL })? {
            continue;
        }
        let Event::Key(key) = read_event()? else {
            continue;
        };
        if key.kind != KeyEventKind::Press {
            continue;
        }
        match command_key(&mut view.command, key.code) {
            CommandInput::NotMine => {}
            CommandInput::Typing => continue,
            CommandInput::Entered(text) => {
                match parse_command(&text) {
                    // :debug leaves from the game-over screen; elsewhere
                    // we're already here
                    Command::Debug if view.winner.is_some() => return Ok(()),
                    Command::Debug | Command::Unknown => {}
                    Command::Anim(anim) => playground_anim(&mut view, anim),
                    // We're a peasant here, under Left as landlord: winning
                    // means a peasant (us) went out, losing or a 春天 that
                    // Left did.
                    Command::Finish { win, spring } => {
                        view.winner = Some(if win { view.seat } else { 1 });
                        view.spring = spring;
                        view.voted = None;
                        view.ready = 0;
                    }
                    Command::Play { cards, force } => {
                        if let Err(e) = playground_play(&mut view, cards, force) {
                            notice = Some(Notice::new(e.to_string()));
                        }
                    }
                    Command::Bad(reason) => notice = Some(Notice::new(reason)),
                }
                continue;
            }
        }
        // Esc closes the sheet first, if it's open
        if sheet_key(&mut view, key.code) {
            continue;
        }
        if key.code == KeyCode::Esc {
            return Ok(());
        }
        if view.phase() == Phase::Over {
            // The vote screen works for us, but the dummies never vote, so a
            // yes waits forever. A no goes back to the menu, as it would close
            // a real lobby.
            match key.code {
                KeyCode::Char('g' | 'G') if view.is_winner(view.seat) => {
                    view.gloats[view.seat] = Some(Instant::now());
                }
                KeyCode::Char('y' | 'Y') if view.voted.is_none() => {
                    view.voted = Some(true);
                    view.ready = 1;
                }
                KeyCode::Char('n' | 'N') if view.voted.is_none() => return Ok(()),
                _ => {}
            }
            continue;
        }
        view.hand_key(key.code);
    }
}

fn main() -> io::Result<()> {
    match ratatui::run(run_app) {
        Err(e) if is_quit(&e) => Ok(()),
        result => result,
    }
}

#[cfg(test)]
mod tests;
