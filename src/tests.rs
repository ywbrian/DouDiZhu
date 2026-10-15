use super::*;

// cards from short names like "3", "10", "A", "BJ", "RJ"; suits are
// handed out in turn so repeated ranks stay distinct cards
fn cards(names: &str) -> Vec<Card> {
    let mut used: BTreeMap<Rank, usize> = BTreeMap::new();
    names
        .split_whitespace()
        .map(|name| {
            let rank = match name {
                "BJ" => return Card::Joker(JokerColor::Black),
                "RJ" => return Card::Joker(JokerColor::Red),
                "J" => Rank::Jack,
                "Q" => Rank::Queen,
                "K" => Rank::King,
                "A" => Rank::Ace,
                "2" => Rank::Two,
                n => Rank::ALL[n.parse::<usize>().unwrap() - 3],
            };
            let n = used.entry(rank).or_default();
            *n += 1;
            Card::Standard {
                rank,
                suit: Suit::ALL[*n - 1],
            }
        })
        .collect()
}

// the reading used when leading
fn classify(names: &str) -> Option<Combo> {
    Combo::readings(&cards(names)).first().copied()
}

#[test]
fn classifies_each_combination() {
    use Combo::*;
    assert_eq!(classify("A"), Some(Single(Value::Rank(Rank::Ace))));
    assert_eq!(classify("RJ"), Some(Single(Value::RedJoker)));
    assert_eq!(classify("3 3"), Some(Pair(Rank::Three)));
    assert_eq!(
        classify("7 7 8 8 9 9"),
        Some(ChainedPairs { high: Rank::Nine, pairs: 3 })
    );
    assert_eq!(
        classify("10 10 J J Q Q K K A A"),
        Some(ChainedPairs { high: Rank::Ace, pairs: 5 })
    );
    assert_eq!(
        classify("5 6 7 8 9 10 J"),
        Some(Straight { high: Rank::Jack, len: 7 })
    );
    assert_eq!(classify("9 9 9"), Some(Triple(Rank::Nine)));
    assert_eq!(classify("9 9 9 4"), Some(TripleWithSingle(Rank::Nine)));
    assert_eq!(classify("9 9 9 4 4"), Some(TripleWithPair(Rank::Nine)));
    let four = Rank::Four;
    assert_eq!(classify("3 3 3 4 4 4"), Some(Airplane { high: four, len: 2 }));
    assert_eq!(
        classify("3 3 3 4 4 4 7 9"),
        Some(SmallWingedAirplane { high: four, len: 2 })
    );
    assert_eq!(
        classify("3 3 3 4 4 4 7 7"),
        Some(SmallWingedAirplane { high: four, len: 2 })
    );
    assert_eq!(
        classify("3 3 3 4 4 4 7 7 9 9"),
        Some(LargeWingedAirplane { high: four, len: 2 })
    );
    assert_eq!(classify("6 6 6 6 8 8"), Some(QuadWithPair(Rank::Six)));
    assert_eq!(classify("6 6 6 6"), Some(Bomb(Rank::Six)));
    assert_eq!(classify("BJ RJ"), Some(Nuke));
}

#[test]
fn rejects_invalid_sets() {
    // too short for a straight or chain
    assert_eq!(classify("3 4 5 6"), None);
    assert_eq!(classify("3 3 4 4"), None);
    // 2 can't be part of a sequence
    assert_eq!(classify("10 J Q K A 2"), None);
    assert_eq!(classify("Q Q K K A A 2 2"), None);
    assert_eq!(classify("A A A 2 2 2"), None);
    // gaps
    assert_eq!(classify("3 4 5 6 8"), None);
    assert_eq!(classify("3 3 3 5 5 5"), None);
    // two jokers are never a pair
    assert_eq!(classify("9 9 9 BJ RJ"), None);
    // a quad takes a pair, not two singles
    assert_eq!(classify("6 6 6 6 8 9"), None);
    // a kicker can't match its triple's rank
    assert_eq!(classify("3 3 3 3 4 4 4 5"), None);
    assert_eq!(classify("3 4"), None);
}

#[test]
fn kicker_rules() {
    use Combo::*;
    let (four, five) = (Rank::Four, Rank::Five);
    // any rank can be a kicker, including 2s and a single joker
    assert_eq!(classify("9 9 9 2"), Some(TripleWithSingle(Rank::Nine)));
    assert_eq!(classify("9 9 9 BJ"), Some(TripleWithSingle(Rank::Nine)));
    assert_eq!(
        classify("3 3 3 4 4 4 RJ 7"),
        Some(SmallWingedAirplane { high: four, len: 2 })
    );
    assert_eq!(
        classify("3 3 3 4 4 4 2 2"),
        Some(SmallWingedAirplane { high: four, len: 2 })
    );
    // but only one joker at a time
    assert_eq!(classify("3 3 3 4 4 4 BJ RJ"), None);
    // and never one matching its triple or quad
    assert_eq!(classify("3 3 3 3 4 4 4 5"), None);
    assert_eq!(classify("3 3 3 4 4 4 4 5"), None);
    // a bomb isn't two pairs, and two jokers aren't a pair
    assert_eq!(classify("3 3 3 4 4 4 7 7 7 7"), None);
    assert_eq!(classify("3 3 3 4 4 4 7 7 BJ RJ"), None);
    assert_eq!(classify("6 6 6 6 BJ RJ"), None);
    // the triples have to run on from each other
    assert_eq!(classify("3 3 3 4 4 4 5 5 5 9 9 9 6 7 8 10"), None);
    // when several runs fit, the highest decides the airplane's strength
    assert_eq!(
        classify("3 3 3 4 4 4 5 5 5 6 6 6 7 7 7 8"),
        Some(SmallWingedAirplane { high: Rank::Seven, len: 4 })
    );
    // with nothing extra, it's a plain airplane rather than a winged one
    assert_eq!(
        classify("3 3 3 4 4 4 5 5 5 6 6 6"),
        Some(Airplane { high: Rank::Six, len: 4 })
    );
    assert_eq!(
        classify("3 3 3 4 4 4 5 5 5 7 7 8"),
        Some(SmallWingedAirplane { high: five, len: 3 })
    );
}

#[test]
fn sequences_have_no_maximum() {
    use Combo::*;
    assert_eq!(
        classify("3 4 5 6 7 8 9 10 J Q K A"),
        Some(Straight { high: Rank::Ace, len: 12 })
    );
    assert_eq!(
        classify("3 3 4 4 5 5 6 6 7 7 8 8 9 9"),
        Some(ChainedPairs { high: Rank::Nine, pairs: 7 })
    );
    assert_eq!(
        classify("8 8 8 9 9 9 10 10 10"),
        Some(Airplane { high: Rank::Ten, len: 3 })
    );
    // jokers and 2s never join a sequence
    assert_eq!(classify("K K K A A A 2 2 2"), None);
    assert_eq!(classify("J Q K A BJ"), None);
}

#[test]
fn beats_follows_the_rules() {
    let c = |names| classify(names).unwrap();
    assert!(c("2").beats(&c("A")));
    assert!(c("BJ").beats(&c("2")));
    assert!(c("RJ").beats(&c("BJ")));
    assert!(!c("A").beats(&c("A")));
    assert!(c("4 4").beats(&c("3 3")));
    assert!(!c("4 4").beats(&c("3")));
    // sequences must match length
    assert!(c("4 5 6 7 8").beats(&c("3 4 5 6 7")));
    assert!(!c("4 5 6 7 8 9").beats(&c("3 4 5 6 7")));
    assert!(!c("4 4 5 5 6 6 7 7").beats(&c("3 3 4 4 5 5")));
    assert!(c("4 4 4 5 5 5").beats(&c("3 3 3 4 4 4")));
    assert!(!c("4 4 4 5 5 5 6 6 6").beats(&c("3 3 3 4 4 4")));
    // winged and plain airplanes don't mix
    assert!(!c("4 4 4 5 5 5 7 8").beats(&c("3 3 3 4 4 4")));
    // a quad with a pair is an ordinary combination, not a bomb
    assert!(!c("6 6 6 6 8 8").beats(&c("9 9 9 4 4")));
    // bombs beat everything but a higher bomb or the nuke
    assert!(c("3 3 3 3").beats(&c("10 J Q K A")));
    assert!(c("4 4 4 4").beats(&c("3 3 3 3")));
    assert!(!c("3 3 3 3").beats(&c("4 4 4 4")));
    assert!(c("BJ RJ").beats(&c("2 2 2 2")));
    assert!(!c("2 2 2 2").beats(&c("BJ RJ")));
}

fn test_game(hands: [&str; 3]) -> Game {
    Game {
        hands: hands.map(|names| Hand { cards: cards(names) }),
        kitty: Vec::new(),
        first: 0,
        landlord: Some(0),
        turn: 0,
        last_play: None,
        passes: 0,
        winner: None,
    }
}

#[test]
fn two_passes_clear_the_table() {
    let mut game = test_game(["3 4", "5 6", "7 8"]);
    assert_eq!(game.pass(0), Err(MoveError::MustLead));
    game.play(0, &cards("3")).unwrap();
    assert_eq!(game.turn, 1);
    game.pass(1).unwrap();
    assert!(game.last_play.is_some());
    game.pass(2).unwrap();
    // back to the player who played last, with a clear table
    assert_eq!(game.turn, 0);
    assert!(game.last_play.is_none());
}

#[test]
fn a_play_resets_the_pass_count() {
    let mut game = test_game(["3 9", "5 6", "7 8"]);
    game.play(0, &cards("3")).unwrap();
    game.pass(1).unwrap();
    game.play(2, &cards("7")).unwrap();
    game.pass(0).unwrap();
    // only one pass since 7 was played, so the table stays
    assert!(game.last_play.is_some());
    assert_eq!(game.turn, 1);
}

#[test]
fn ambiguous_sets_fit_the_table() {
    use Combo::*;
    let set = cards("3 3 3 4 4 4 5 5 5 6 6 6");
    assert_eq!(
        Combo::readings(&set),
        vec![
            Airplane { high: Rank::Six, len: 4 },
            SmallWingedAirplane { high: Rank::Six, len: 3 },
            SmallWingedAirplane { high: Rank::Five, len: 3 },
        ]
    );
    // leading, it's the plain airplane
    assert_eq!(Combo::fit(&set, None), Ok(Airplane { high: Rank::Six, len: 4 }));
    // on a winged airplane of three it's read as one, using the highest run
    let table = SmallWingedAirplane { high: Rank::Five, len: 3 };
    assert_eq!(
        Combo::fit(&set, Some(&table)),
        Ok(SmallWingedAirplane { high: Rank::Six, len: 3 })
    );
    // a reading of the right shape that's too low doesn't beat it
    let table = SmallWingedAirplane { high: Rank::Six, len: 3 };
    assert_eq!(Combo::fit(&set, Some(&table)), Err(MoveError::DoesNotBeat));
    // nor does a different kind of combination
    assert_eq!(
        Combo::fit(&cards("7 7 7"), Some(&Pair(Rank::Three))),
        Err(MoveError::WrongShape)
    );
    // but a bomb fits on anything
    assert_eq!(
        Combo::fit(&cards("3 3 3 3"), Some(&Pair(Rank::Ace))),
        Ok(Bomb(Rank::Three))
    );
}

#[test]
fn plays_are_checked() {
    let mut game = test_game(["5 9", "3 4", "7 8"]);
    assert_eq!(game.play(1, &cards("3")), Err(MoveError::NotYourTurn));
    assert_eq!(game.play(0, &cards("6")), Err(MoveError::NotInHand));
    assert_eq!(game.play(0, &cards("5 9")), Err(MoveError::NotACombination));
    game.play(0, &cards("5")).unwrap();
    assert_eq!(game.play(1, &cards("4")), Err(MoveError::DoesNotBeat));
    assert_eq!(game.play(1, &cards("3 4")), Err(MoveError::NotACombination));
    assert_eq!(game.hands[0].cards, cards("9"));
}

#[test]
fn shedding_the_last_card_wins() {
    let mut game = test_game(["3 3 9", "5 6", "7 8"]);
    game.play(0, &cards("3 3")).unwrap();
    assert_eq!(game.winner, None);
    game.pass(1).unwrap();
    game.pass(2).unwrap();
    game.play(0, &cards("9")).unwrap();
    assert_eq!(game.winner, Some(0));
    // nothing more can be played once someone has won
    assert_eq!(game.play(1, &cards("5")), Err(MoveError::NotYourTurn));
}

#[test]
fn a_nuke_returns_the_turn_at_once() {
    let mut game = test_game(["3 4", "BJ RJ 5", "7 8"]);
    game.play(0, &cards("4")).unwrap();
    game.play(1, &cards("BJ RJ")).unwrap();
    assert_eq!(game.turn, 1);
    assert!(game.last_play.is_none());
}

fn named(typed: &str, shown: &str) -> PlayerName {
    PlayerName {
        typed: typed.to_string(),
        shown: shown.to_string(),
    }
}

#[test]
fn duplicate_names_get_numbers() {
    // no clash, no suffix
    assert_eq!(unique_name("Alice", &[named("Player", "Player")]), "Alice");
    // the second and third of a name are numbered by how many share it
    assert_eq!(unique_name("Player", &[named("Player", "Player")]), "Player (2)");
    assert_eq!(
        unique_name(
            "Player",
            &[named("Player", "Player"), named("Player", "Player (2)")]
        ),
        "Player (3)"
    );
    // a typed suffix is just part of the name
    assert_eq!(
        unique_name("Player (99999)", &[named("Player (99999)", "Player (99999)")]),
        "Player (99999) (2)"
    );
    // someone really called "Player (2)" when that's taken moves up
    assert_eq!(
        unique_name(
            "Player (2)",
            &[named("Player", "Player"), named("Player", "Player (2)")]
        ),
        "Player (2) (1)"
    );
    assert_eq!(
        unique_name(
            "Player",
            &[named("Player", "Player"), named("Player (2)", "Player (2)")]
        ),
        "Player (3)"
    );
}

#[test]
fn versions_match_up_to_minor() {
    let (major, minor) = {
        let mut parts = VERSION.split('.');
        (parts.next().unwrap(), parts.next().unwrap())
    };
    assert!(compatible(VERSION));
    assert!(compatible(&format!("{major}.{minor}.999")));
    assert!(!compatible(&format!("{major}.{minor}9.0")));
    assert!(!compatible(&format!("9{major}.{minor}.0")));
    assert!(!compatible("garbage"));
}
