/* ┌────────────────────────────────────────────────────────────────────────────────────────────┐ *\
 * │                                                                                            │ *
 * │ This Source Code Form is subject to the terms of the Mozilla Public                        │ *
 * │ License, v. 2.0. If a copy of the MPL was not distributed with this                        │ *
 * │ file, You can obtain one at http://mozilla.org/MPL/2.0/.                                   │ *
 * │                                                                                            │ *
\* └────────────────────────────────────────────────────────────────────────────────────────────┘ */

/* ┌────────────────────────────────────────────────────────────────────────────────────────────┐ *\
 * │                                       Configuration                                        │ *
\* └────────────────────────────────────────────────────────────────────────────────────────────┘ */

// This is completely useless: due to this library depends async-io (it is not optional), and async-io uses std. so the final generated native code is still linked to std.
//#![no_std]

/* ┌────────────────────────────────────────────────────────────────────────────────────────────┐ *\
 * │                                       Documentation                                        │ *
\* └────────────────────────────────────────────────────────────────────────────────────────────┘ */

//! A way to poll a future until it or a timer completes.
//!
//! ## Example
//! see [`TimeoutExt::timeout`] and [`TimeoutExt::deadline`].

/* ┌────────────────────────────────────────────────────────────────────────────────────────────┐ *\
 * │                                          Imports                                           │ *
\* └────────────────────────────────────────────────────────────────────────────────────────────┘ */

use async_io::Timer;
use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll};
use std::time::{Instant, Duration};
use pin_project_lite::pin_project;

/* ┌────────────────────────────────────────────────────────────────────────────────────────────┐ *\
 * │                                    struct Timed<Fut>                                     │ *
\* └────────────────────────────────────────────────────────────────────────────────────────────┘ */

pin_project! {
    /// A helper that polling both inner Future, and a [`Timer`] that will complete after a specified
    /// timeout or deadline.
    ///
    /// ## Example
    /// see [`TimeoutExt::timeout`] and [`TimeoutExt::deadline`].
    #[derive(Debug)]
    pub struct Timed<Fut: Future> {
        #[pin]
        future: Fut,
        #[pin]
        timer: Timer,
    }
}

/* ┌────────────────────────────────────────────────────────────────────────────────────────────┐ *\
 * │                                  trait TimeoutExt: Future                                  │ *
\* └────────────────────────────────────────────────────────────────────────────────────────────┘ */

/// An extension trait for [`Future`]s that provides a way to create [`Timeout`]s.
pub trait TimedExt: Future {
    /// Given a [`Duration`], creates and returns a new [`Timed`] that will poll both the Future, and a [`Timer`] that will complete after the provided duration.
    /// * first polling the Future, returns it's output if any.
    /// * then polling the Timer, and fallback to [`None`] if the Timer completes.
    ///
    /// ## Example
    ///
    /// ```rust
    /// use async_io::Timer;
    /// # use futures_lite::future;
    /// use smoltimeout::TimeoutExt;
    /// use std::time::Duration;
    ///
    /// # future::block_on(async {
    /// #
    /// let mut timer = Timer::after(Duration::from_millis(250));
    /// let foo = async {
    ///     timer.await;
    ///     24
    /// }.timeout(Duration::from_millis(100));
    /// assert_eq!(foo.await, None);
    ///
    /// timer = Timer::after(Duration::from_millis(100));
    /// let bar = async move {
    ///     timer.await;
    ///     42
    /// }.timeout(Duration::from_millis(250));
    /// assert_eq!(bar.await, Some(42));
    ///
    /// timer = Timer::after(Duration::from_millis(50));
    /// let mod_of_delta4 = async move {
    ///     timer.await;
    ///     (21*2) as f64
    /// }.timeout(Duration::from_millis(0));
    /// Timer::after(Duration::from_millis(100)).await;
    /// assert_eq!(mod_of_delta4.await, Some(42.0));
    /// #
    /// # })
    /// ```
    fn timeout(self, after: Duration) -> Timed<Self>
    where
        Self: Sized,
    {
        Timed {
            future: self,
            timer: Timer::after(after),
        }
    }

    /// Given a [`Instant`], creates and returns a new [`Timed`] that will poll both the Future
    /// and a [`Timer`] that will complete after the provided deadline.
    /// * first polling the Future, returns it's output if any.
    /// * then polling the Timer, and fallback to [`None`] if the Timer completes.
    ///
    /// ## Example
    ///
    /// ```rust
    /// use async_io::Timer;
    /// # use futures_lite::future;
    /// use smoltimeout::TimeoutExt;
    /// use std::time::{Instant, Duration};
    ///
    /// # future::block_on(async {
    /// #
    /// let mut timer = Timer::after(Duration::from_millis(250));
    /// let foo = async move {
    ///     timer.await;
    ///     24
    /// }.deadline(Instant::now() + Duration::from_millis(100));
    /// assert_eq!(foo.await, None);
    ///
    /// timer = Timer::after(Duration::from_millis(100));
    /// let bar = async move {
    ///     timer.await;
    ///     42
    /// }.deadline(Instant::now() + Duration::from_millis(250));
    /// assert_eq!(bar.await, Some(42));
    ///
    /// timer = Timer::after(Duration::from_millis(50));
    /// let mod_of_delta4 = async move {
    ///     timer.await;
    ///     (21*2) as f64
    /// }.deadline(Instant::now());
    /// Timer::after(Duration::from_millis(100)).await;
    /// assert_eq!(mod_of_delta4.await, Some(42.0));
    /// #
    /// # })
    /// ```
    fn deadline(self, deadline: Instant) -> Timed<Self>
    where
        Self: Sized,
    {
        Timed {
            future: self,
            timer: Timer::at(deadline),
        }
    }
}

impl<Fut: Future> TimedExt for Fut {}

/// for provide compatibly to older versions.
pub use {
    TimedExt as TimeoutExt,
    Timed as Timeout,
};

/* ┌────────────────────────────────────────────────────────────────────────────────────────────┐ *\
 * │                                impl Future for Timeout<Fut>                                │ *
\* └────────────────────────────────────────────────────────────────────────────────────────────┘ */

impl<Fut: Future> Future for Timed<Fut> {
    type Output = Option<Fut::Output>;

    fn poll(self: Pin<&mut Self>, ctx: &mut Context) -> Poll<Self::Output> {
        let this = self.project();

        if let Poll::Ready(output) = this.future.poll(ctx) {
            return Poll::Ready(Some(output));
        }

        if this.timer.poll(ctx).is_ready() {
            return Poll::Ready(None);
        }

        Poll::Pending
    }
}
