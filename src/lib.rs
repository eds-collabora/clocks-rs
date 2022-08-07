//! # clocks - testable time
//!
//! This crate provides a way of making code that depends on time
//! testable. In your code, instead of calling out to
//! [`Utc::now`](chrono::Utc::now) or similar, you instead use
//! [`Clock::now`].  When your program is running normally in
//! production, it will behave just the same as without using this
//! crate.
//!
//! # Basic usage
//!
//! When you need to run tests on your program, you can replace the
//! clock object with a fake clock that lets you control the passage
//! of time. This can be very helpful if you have logic that depends
//! on the passage of time (e.g. if you expect to time things out after
//! minutes or days, and want to test that works).
//!
//! The mechanism for this is the [`Clock`] struct, which can be
//! either a wall clock or a fake clock, and has an associated
//! timezone. Your production code needs to be able to accept a clock
//! so that tests can override the default wall clock.
//!
//! Example:
//! ```rust
//! use clocks::Clock;
//! use chrono::Utc;
//!
//! pub fn production() {
//!    production_with_clock(Default::default())
//! }
//!
//! pub(crate) fn production_with_clock(clock: Clock<Utc>) {
//!    let start = clock.now();
//!    // ...
//! }
//!
//! #[test]
//! fn test_basic() {
//!    let c = Clock::new_fake(Utc::now());
//!    production_with_clock(c.clone());
//! }
//! ```
//!
//! ## Sleeping
//!
//! This crate can also help you test sleep loops, where you want in
//! your test to synchronise with code that sleeps regularly. This is
//! much less hit and miss than injecting sleeps into your test to try
//! to match the sleeping pattern of the code under test, but it can
//! take some effort to get right.
//!
//! It works only when you have multiple threads or tasks. Give each
//! thread or task that needs to sleep a "split" of the clock using
//! [`Clock::split`]. The test thread needs its own split also. Now
//! [`Clock::advance`] will wait for all other splits to be blocking
//! in [`Clock::sleep`].
//!
//! It is easier to make mistakes than would be ideal, but your
//! production code will be unaffected by using this functionality in
//! your tests. Your tests may fail due to errors in usage here, but
//! none of the test code has any effect in production. The most
//! likely error is failing to call [`Clock::split`] instead of
//! [`Clock::clone`] in some place where you intend to hand the clone
//! to some other thread.
//!
//! Effectively, we end up needing the clock to be properly split
//! for each thread, and we can neither find out when our clock was transferred
//! to another thread or task, nor is there any equivalent of [`Send`] for async code
//! meaning we cannot prevent clones being shared.
//!
//! Example:
//! ```rust
//! use clocks::Clock;
//! use chrono::{Duration, Utc};
//!
//! pub fn production() {
//!    production_with_clock(Default::default())
//! }
//!
//! pub fn production_with_clock(mut clock: Clock<Utc>) {
//!    let time = clock.now();
//!    clock.sleep_blocking(Duration::seconds(10));
//!    assert_eq!(clock.now(), time + Duration::seconds(10));
//! }
//!
//! #[test]
//! fn test_sleep() {
//!    let mut c = Clock::new_fake(Utc::now());
//!    let c2 = c.split();
//!    std::thread_spawn(|| production_with_clock(c2));
//!    c.advance(Duration::secs(10));
//! }
//! ```
use chrono::{offset::TimeZone, DateTime, Duration, Utc};
use either::Either;
use priq::PriorityQueue;
use std::sync::{Arc, Mutex, MutexGuard};
use tokio::sync::oneshot::{channel, Receiver, Sender};

/// A testable source of time
///
/// By using a [`Clock`] as the source of time in your code, you can
/// choose in testing to replace it with a fake. Your test harness can
/// then control how your production code sees time passing.
#[derive(Clone, Debug)]
pub struct Clock<Tz: TimeZone> {
    inner: ClockInner<Tz>,
    timezone: Tz,
}

impl Clock<Utc> {
    /// Create a new UTC clock that matches wall-clock time
    pub fn new() -> Self {
        Self::new_with_timezone(Utc)
    }
}

impl<Tz: TimeZone> Clock<Tz>
where
    <Tz as TimeZone>::Offset: core::fmt::Display,
{
    /// Create a new clock in this [`TimeZone`]
    pub fn new_with_timezone(timezone: Tz) -> Self {
        Self {
            inner: ClockInner::Wall,
            timezone,
        }
    }

    /// Create a new fake clock in this ['TimeZone'].
    ///
    /// Note that the time reported by this clock will not change from `start` until
    /// the clock is advanced using [`Clock::advance()`].
    pub fn new_fake(start: DateTime<Tz>) -> Self {
        Self {
            timezone: start.timezone(),
            inner: ClockInner::Fake(FakeClock::new(start)),
        }
    }

    /// Get the current time
    pub fn now(&self) -> DateTime<Tz> {
        match &self.inner {
            ClockInner::Wall => Utc::now().with_timezone(&self.timezone),
            ClockInner::Fake(f) => f.now(),
        }
    }

    /// Check whether the clock is fake
    ///
    /// Using this in production code defeats the point, but you may
    /// wish to use it in utilities that could be called from either
    /// production or test code.
    pub fn is_fake(&self) -> bool {
        match &self.inner {
            ClockInner::Wall => false,
            ClockInner::Fake(_) => true,
        }
    }

    /// Divide this clock
    ///
    /// This is equivalent to [`Clone`] when using the default, wall
    /// clock. The following discussion pertains only to the fake
    /// clock case which is intended to be used in testing; in that
    /// sense, getting it wrong is likely to be caught by the tests
    /// themselves.
    ///
    /// When using the fake clock, things become more complicated
    /// to enable testing. Clones of the same clock are divided into
    /// groups. When you call clone, you get a new clock in the same
    /// group as the clock you clone. If you want a [`Clock`] in a new group
    /// of its own, you must call `Clock::split`.
    ///
    /// For the clock to advance, all groups must either be sleeping
    /// or advancing - that means someone must have called either
    /// sleep or advance on exactly one instance in each group. So you
    /// can think of a group as being the clocks in one execution
    /// context (task/thread).
    pub fn split(&self) -> Clock<Tz> {
        Self {
            inner: self.inner.split(),
            timezone: self.timezone.clone(),
        }
    }

    /// Move a fake clock forward by some duration
    ///
    /// This will panic if called on a wall clock.
    pub async fn advance(&mut self, duration: Duration) -> (DateTime<Tz>, Duration) {
        match &mut self.inner {
            ClockInner::Wall => panic!("Attempted to advance system clock"),
            ClockInner::Fake(f) => f.advance(duration).await,
        }
    }

    /// Move a fake clock forward by some duration
    ///
    /// This will panic if called on a wall clock.
    pub fn advance_blocking(&mut self, duration: Duration) -> (DateTime<Tz>, Duration) {
        let r = match &mut self.inner {
            ClockInner::Wall => panic!("Attempted to advance system clock"),
            ClockInner::Fake(f) => f.advance_blocking(duration),
        };
        r
    }

    /// Sleep for some duration
    pub async fn sleep(&mut self, duration: Duration) {
        match &mut self.inner {
            ClockInner::Wall => tokio::time::sleep(duration.to_std().unwrap()).await,
            ClockInner::Fake(f) => f.sleep(duration).await,
        }
    }

    /// Sleep for some duration
    ///
    /// This should not be called from an async context.
    pub fn sleep_blocking(&mut self, duration: Duration) {
        match &mut self.inner {
            ClockInner::Wall => std::thread::sleep(duration.to_std().unwrap()),
            ClockInner::Fake(f) => f.sleep_blocking(duration),
        }
    }
}

impl Default for Clock<Utc> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Debug)]
enum ClockInner<Tz: TimeZone> {
    Wall,
    Fake(FakeClock<Tz>),
}

impl<Tz: TimeZone> ClockInner<Tz>
where
    <Tz as TimeZone>::Offset: core::fmt::Display,
{
    pub fn split(&self) -> Self {
        match &self {
            Self::Wall => Self::Wall,
            Self::Fake(f) => Self::Fake(f.split()),
        }
    }
}

#[derive(Debug)]
struct FakeInner<Tz: TimeZone> {
    now: DateTime<Tz>,
    sleepers: PriorityQueue<DateTime<Tz>, Sender<()>>,
    advancer: Option<Sender<()>>,
    threads: usize,
}

#[derive(Debug)]
struct FakeGroup<Tz: TimeZone> {
    inner: Arc<Mutex<FakeInner<Tz>>>,
}

impl<Tz: TimeZone> Clone for FakeGroup<Tz> {
    fn clone(&self) -> Self {
        let mut v = self.inner.lock().unwrap();
        v.threads += 1;

        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<Tz: TimeZone> Drop for FakeGroup<Tz> {
    fn drop(&mut self) {
        let mut v = self.inner.lock().unwrap();
        v.threads -= 1;
        if v.sleepers.len() + 1 == v.threads {
            if let Some(advancer) = v.advancer.take() {
                advancer.send(()).unwrap();
            }
        }
    }
}

#[derive(Clone, Debug)]
struct FakeClock<Tz: TimeZone> {
    group: Arc<FakeGroup<Tz>>,
}

impl<Tz: TimeZone> FakeClock<Tz>
where
    <Tz as TimeZone>::Offset: core::fmt::Display,
{
    pub(crate) fn new(start: DateTime<Tz>) -> Self {
        Self {
            group: Arc::new(FakeGroup {
                inner: Arc::new(Mutex::new(FakeInner {
                    now: start,
                    sleepers: Default::default(),
                    advancer: None,
                    threads: 1,
                })),
            }),
        }
    }

    pub(crate) fn split(&self) -> Self {
        Self {
            group: Arc::new(FakeGroup::clone(&self.group)),
        }
    }

    pub(crate) fn now(&self) -> DateTime<Tz> {
        self.group.inner.lock().unwrap().now.clone()
    }

    fn do_advance(
        &self,
        mut v: MutexGuard<FakeInner<Tz>>,
        duration: Duration,
    ) -> (DateTime<Tz>, Duration) {
        let start = v.now.clone();
        let mut end = start.clone() + duration;
        while let Some((time, _)) = v.sleepers.peek() {
            if time <= &end {
                let (time, sleeper) = v.sleepers.pop().unwrap();
                sleeper.send(()).expect("Failed to wake sleeper");
                end = time.clone();
            } else {
                break;
            }
        }
        v.now = end.clone();
        (end.clone(), end - start)
    }

    fn pre_advance(&self, duration: Duration) -> Either<(DateTime<Tz>, Duration), Receiver<()>> {
        let mut v = self.group.inner.lock().unwrap();
        if v.advancer.is_some() {
            panic!("Cannot advance from two threads simultaneously");
        }

        match v.sleepers.len() + 1 {
            x if x < v.threads => {
                let (tx, rx) = channel();
                v.advancer = Some(tx);
                Either::Right(rx)
            }
            x if x == v.threads => Either::Left(self.do_advance(v, duration)),
            _ => panic!("Too many threads"),
        }
    }

    pub(crate) async fn advance(&self, duration: Duration) -> (DateTime<Tz>, Duration) {
        let rx = match self.pre_advance(duration) {
            Either::Left(d) => {
                return d;
            }
            Either::Right(rx) => rx,
        };
        rx.await.unwrap();
        let v = self.group.inner.lock().unwrap();
        self.do_advance(v, duration)
    }

    pub(crate) fn advance_blocking(&self, duration: Duration) -> (DateTime<Tz>, Duration) {
        let rx = match self.pre_advance(duration) {
            Either::Left(d) => {
                return d;
            }
            Either::Right(rx) => rx,
        };
        rx.blocking_recv().unwrap();
        let v = self.group.inner.lock().unwrap();
        self.do_advance(v, duration)
    }

    fn sleep_common(&mut self, duration: Duration) -> Receiver<()> {
        let mut v = self.group.inner.lock().unwrap();
        let (tx, rx) = channel();
        let wake_time = v.now.clone() + duration;
        v.sleepers.put(wake_time, tx);
        if v.sleepers.len() + 1 == v.threads {
            if let Some(advancer) = v.advancer.take() {
                advancer.send(()).unwrap();
            }
        }
        rx
    }

    pub(crate) fn sleep_blocking(&mut self, duration: Duration) {
        let rx = self.sleep_common(duration);
        rx.blocking_recv().expect("Failed to wake up")
    }

    pub(crate) async fn sleep(&mut self, duration: Duration) {
        let rx = self.sleep_common(duration);
        rx.await.expect("Failed to wake up")
    }
}

#[cfg(test)]
mod test {
    use super::Clock;
    use chrono::{DateTime, Duration, Utc};

    #[test]
    fn test_sync_wall_sleep() {
        let mut c = Clock::new();

        let start = c.now();
        c.sleep_blocking(Duration::seconds(5));
        let end = c.now();

        let ns = ((end - start) - Duration::seconds(5))
            .num_nanoseconds()
            .unwrap();
        assert!(
            ns.abs() < 250_000,
            "Slept for {} nanoseconds too many (duration {})",
            ns,
            (end - start)
        );
    }

    #[tokio::test]
    async fn test_async_wall_sleep() {
        let mut c = Clock::new();

        let start = c.now();
        c.sleep(Duration::seconds(5)).await;
        let end = c.now();

        let ns = ((end - start) - Duration::seconds(5))
            .num_nanoseconds()
            .unwrap();
        assert!(
            ns.abs() < 2_000_000,
            "Slept for {} nanoseconds too many (duration {})",
            ns,
            (end - start)
        );
    }

    #[test]
    fn test_sync_fake_sleep() {
        let start = DateTime::parse_from_rfc2822("Mon, 8 Aug 2022 15:21:00 GMT")
            .unwrap()
            .with_timezone(&Utc);
        let mut c = Clock::new_fake(start);

        let mut cs = c.split();
        std::thread::spawn(move || {
            cs.sleep_blocking(Duration::seconds(5));
            let end = cs.now();
            assert_eq!(start + Duration::seconds(5), end);
        });

        assert_eq!(
            c.advance_blocking(Duration::seconds(1)),
            (
                DateTime::parse_from_rfc2822("Mon, 8 Aug 2022 15:21:01 GMT")
                    .unwrap()
                    .with_timezone(&Utc),
                Duration::seconds(1)
            )
        );

        assert_eq!(
            c.advance_blocking(Duration::seconds(5)),
            (
                DateTime::parse_from_rfc2822("Mon, 8 Aug 2022 15:21:05 GMT")
                    .unwrap()
                    .with_timezone(&Utc),
                Duration::seconds(4)
            )
        );

        assert_eq!(
            c.advance_blocking(Duration::seconds(10)),
            (
                DateTime::parse_from_rfc2822("Mon, 8 Aug 2022 15:21:15 GMT")
                    .unwrap()
                    .with_timezone(&Utc),
                Duration::seconds(10)
            )
        );
    }

    #[tokio::test]
    async fn test_async_fake_sleep() {
        let start = DateTime::parse_from_rfc2822("Mon, 8 Aug 2022 15:21:00 GMT")
            .unwrap()
            .with_timezone(&Utc);
        let mut c = Clock::new_fake(start);

        let mut cs = c.split();
        tokio::spawn(async move {
            cs.sleep(Duration::seconds(5)).await;
            let end = cs.now();
            assert_eq!(start + Duration::seconds(5), end);
        });

        assert_eq!(
            c.advance(Duration::seconds(1)).await,
            (
                DateTime::parse_from_rfc2822("Mon, 8 Aug 2022 15:21:01 GMT")
                    .unwrap()
                    .with_timezone(&Utc),
                Duration::seconds(1)
            )
        );

        assert_eq!(
            c.advance(Duration::seconds(5)).await,
            (
                DateTime::parse_from_rfc2822("Mon, 8 Aug 2022 15:21:05 GMT")
                    .unwrap()
                    .with_timezone(&Utc),
                Duration::seconds(4)
            )
        );

        assert_eq!(
            c.advance(Duration::seconds(10)).await,
            (
                DateTime::parse_from_rfc2822("Mon, 8 Aug 2022 15:21:15 GMT")
                    .unwrap()
                    .with_timezone(&Utc),
                Duration::seconds(10)
            )
        );
    }
}
