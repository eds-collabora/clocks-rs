use chrono::{DateTime, Utc};
use clocks::Clock;

struct Prod {
    clock: Clock<Utc>,
}

impl Prod {
    pub fn new() -> Self {
        Self::new_with_clock(Clock::new())
    }

    pub fn new_with_clock(clock: Clock<Utc>) -> Self {
        Self { clock }
    }

    pub fn get_time(&self) -> String {
        self.clock.now().to_rfc2822()
    }
}

fn main() {
    let p = Prod::new();
    println!("{}", p.get_time());
}

#[test]
fn test_basic() {
    let start = DateTime::parse_from_rfc2822("Sun, 18 Sep 2022 20:53:00 GMT")
        .unwrap()
        .with_timezone(&Utc);
    let c = Clock::new_fake(start.clone());
    let p = Prod::new_with_clock(c);
    assert_eq!(p.get_time(), "Sun, 18 Sep 2022 20:53:00 +0000");
}
