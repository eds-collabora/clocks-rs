# clocks - a testable source of time

This crate provides a
[`Clock`](https://docs.rs/django-query/latest/clocks/struct.Clock.html)
type that can be used as a source of time. By using a clock in your
code, you make it possible to replace the time source during
testing. This can allow you to more simply test things like expiry
times.

Example usage:
```rust
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
```

## License

This code is made available under either an
[Apache-2.0](https://opensource.org/licenses/Apache-2.0) or an [MIT
license](https://opensource.org/licenses/MIT).
