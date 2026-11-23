// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::VecDeque;
use std::time::Duration;

use tokio::time::Instant;

const BEHIND: u16 = 0x8000;

struct Held<T> {
    len: usize,
    item: T,
}

pub(super) struct Reorder<T> {
    max_packets: usize,
    max_bytes: usize,
    max_delay: Duration,
    next: Option<u16>,

    /// `slots[k]` holds the packet with sequence number `next + k`.
    slots: VecDeque<Option<Held<T>>>,
    held: usize,
    held_bytes: usize,

    /// Sequence numbers of held packets in arrival order, some already
    /// released; see [`Self::deadline`].
    arrivals: VecDeque<(Instant, u16)>,
    ready: VecDeque<T>,
}

impl<T> Reorder<T> {
    pub(super) fn new(max_packets: usize, max_bytes: usize, max_delay: Duration) -> Self {
        Self {
            max_packets,
            max_bytes,
            max_delay,
            next: None,
            slots: VecDeque::new(),
            held: 0,
            held_bytes: 0,
            arrivals: VecDeque::new(),
            ready: VecDeque::new(),
        }
    }

    pub(super) fn start_at(&mut self, sequence_number: u16) {
        self.next = Some(sequence_number);
    }

    pub(super) fn enabled(&self) -> bool {
        self.max_packets > 0
    }

    pub(super) fn push(&mut self, sequence_number: u16, len: usize, arrived: Instant, item: T) {
        let next = *self.next.get_or_insert(sequence_number);
        if sequence_number.wrapping_sub(next) >= BEHIND {
            self.ready.push_back(item);
            return;
        }
        if usize::from(sequence_number.wrapping_sub(next)) >= self.max_packets {
            self.release_all();
            self.next = Some(sequence_number);
        }
        let ahead = usize::from(sequence_number.wrapping_sub(self.next.unwrap_or(next)));
        if self.slots.len() <= ahead {
            self.slots.resize_with(ahead + 1, || None);
        }
        if self.slots[ahead].is_some() {
            return;
        }
        self.slots[ahead] = Some(Held { len, item });
        self.held += 1;
        self.held_bytes += len;
        self.arrivals.push_back((arrived, sequence_number));
        self.release_run();
        while self.held_bytes > self.max_bytes {
            self.skip_gap();
        }
    }

    pub(super) fn expire(&mut self, now: Instant) {
        while self.deadline().is_some_and(|deadline| deadline <= now) {
            self.skip_gap();
        }
    }

    /// Returns when the packet held longest must be released.
    pub(super) fn deadline(&mut self) -> Option<Instant> {
        while let Some(&(_, sequence_number)) = self.arrivals.front()
            && !self.holds(sequence_number)
        {
            self.arrivals.pop_front();
        }
        self.arrivals
            .front()
            .map(|&(arrived, _)| arrived + self.max_delay)
    }

    pub(super) fn pop(&mut self) -> Option<T> {
        self.ready.pop_front()
    }

    fn holds(&self, sequence_number: u16) -> bool {
        self.next.is_some_and(|next| {
            self.slots
                .get(usize::from(sequence_number.wrapping_sub(next)))
                .is_some_and(Option::is_some)
        })
    }

    fn release_run(&mut self) {
        while let Some(Some(_)) = self.slots.front() {
            self.release_front();
        }
        if self.held == 0 {
            self.slots.clear();
            self.arrivals.clear();
        }
    }

    fn release_front(&mut self) {
        if let Some(held) = self.slots.pop_front().flatten() {
            self.held -= 1;
            self.held_bytes -= held.len;
            self.ready.push_back(held.item);
        }
        self.next = self.next.map(|next| next.wrapping_add(1));
    }

    fn skip_gap(&mut self) {
        if self.held == 0 {
            return;
        }
        while let Some(None) = self.slots.front() {
            self.release_front();
        }
        self.release_run();
    }

    fn release_all(&mut self) {
        while self.held > 0 {
            self.skip_gap();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const DELAY: Duration = Duration::from_millis(20);
    const LEN: usize = 100;

    fn window(packets: usize) -> Reorder<u16> {
        Reorder::new(packets, usize::MAX, DELAY)
    }

    fn drained(reorder: &mut Reorder<u16>) -> Vec<u16> {
        std::iter::from_fn(|| reorder.pop()).collect()
    }

    fn pushed(reorder: &mut Reorder<u16>, at: Instant, sequence_numbers: &[u16]) -> Vec<u16> {
        sequence_numbers
            .iter()
            .for_each(|&sequence_number| reorder.push(sequence_number, LEN, at, sequence_number));
        drained(reorder)
    }

    #[test]
    fn packets_swapped_on_the_way_come_out_in_order() {
        let now = Instant::now();
        let mut reorder = window(8);
        assert_eq!(
            pushed(&mut reorder, now, &[10, 12, 11, 13]),
            [10, 11, 12, 13]
        );
        assert_eq!(reorder.deadline(), None);
    }

    #[test]
    fn a_lost_packet_holds_the_ones_after_it_only_until_the_delay_or_the_window_runs_out() {
        let now = Instant::now();
        let mut reorder = window(4);
        assert_eq!(pushed(&mut reorder, now, &[1, 3, 4]), [1]);
        assert_eq!(reorder.deadline(), Some(now + DELAY));
        reorder.expire(now + DELAY / 2);
        assert!(drained(&mut reorder).is_empty());
        reorder.expire(now + DELAY);
        assert_eq!(drained(&mut reorder), [3, 4]);

        assert_eq!(pushed(&mut reorder, now, &[6, 7, 8]), Vec::<u16>::new());
        assert_eq!(
            pushed(&mut reorder, now, &[9]),
            [6, 7, 8, 9],
            "a packet past the window gives up on the lost one without waiting"
        );
    }

    #[test]
    fn the_packet_held_longest_sets_the_deadline_whatever_its_sequence_number() {
        let now = Instant::now();
        let mut reorder = window(8);
        reorder.start_at(1);
        reorder.push(5, LEN, now, 5);
        reorder.push(3, LEN, now + DELAY / 2, 3);
        assert_eq!(reorder.deadline(), Some(now + DELAY));
        reorder.expire(now + DELAY);
        assert_eq!(
            drained(&mut reorder),
            [3, 5],
            "releasing the oldest packet releases the lower ones held with it"
        );
        assert_eq!(reorder.deadline(), None);
    }

    #[test]
    fn a_full_byte_budget_gives_up_on_the_missing_packet() {
        let now = Instant::now();
        let mut reorder = Reorder::new(8, 2 * LEN, DELAY);
        assert_eq!(pushed(&mut reorder, now, &[1, 3, 4]), [1]);
        assert_eq!(pushed(&mut reorder, now, &[5]), [3, 4, 5]);
    }

    #[test]
    fn late_duplicate_and_far_ahead_packets_are_passed_on_as_the_in_order_parser_expects() {
        let now = Instant::now();
        let mut reorder = window(8);
        assert_eq!(pushed(&mut reorder, now, &[100, 101]), [100, 101]);
        assert_eq!(
            pushed(&mut reorder, now, &[99]),
            [99],
            "a late packet is not held; the parser skips it"
        );
        assert_eq!(pushed(&mut reorder, now, &[103, 103]), Vec::<u16>::new());
        assert_eq!(
            pushed(&mut reorder, now, &[5000]),
            [103, 5000],
            "a jump past the window releases what is held and starts over"
        );
        assert_eq!(pushed(&mut reorder, now, &[5001]), [5001]);
    }

    #[test]
    fn the_first_packets_are_reordered_when_the_starting_sequence_number_is_known() {
        let now = Instant::now();
        let mut reorder = window(8);
        reorder.start_at(40);
        assert_eq!(pushed(&mut reorder, now, &[41, 40]), [40, 41]);
    }

    #[test]
    fn sequence_numbers_wrap() {
        let now = Instant::now();
        let mut reorder = window(8);
        assert_eq!(
            pushed(&mut reorder, now, &[0xfffe, 0x0000, 0xffff, 0x0001]),
            [0xfffe, 0xffff, 0x0000, 0x0001]
        );
    }

    #[test]
    fn a_large_window_reverses_a_long_run() {
        let now = Instant::now();
        let mut reorder = window(10_000);
        reorder.start_at(0);
        let reversed: Vec<u16> = (0..9_000).rev().collect();
        assert_eq!(
            pushed(&mut reorder, now, &reversed),
            (0..9_000).collect::<Vec<u16>>()
        );
    }

    #[test]
    fn disabled_with_no_window() {
        assert!(!window(0).enabled());
        assert!(window(1).enabled());
    }
}
