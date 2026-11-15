use std::collections::VecDeque;
use std::time::Duration;

use tokio::time::Instant;

const BEHIND: u16 = 0x8000;

struct Held<T> {
    sequence_number: u16,
    arrived: Instant,
    item: T,
}

pub(super) struct Reorder<T> {
    max_packets: usize,
    max_delay: Duration,
    next: Option<u16>,
    held: Vec<Held<T>>,
    ready: VecDeque<T>,
}

impl<T> Reorder<T> {
    pub(super) fn new(max_packets: usize, max_delay: Duration) -> Self {
        Self {
            max_packets,
            max_delay,
            next: None,
            held: Vec::new(),
            ready: VecDeque::new(),
        }
    }

    pub(super) fn enabled(&self) -> bool {
        self.max_packets > 0
    }

    pub(super) fn push(&mut self, sequence_number: u16, arrived: Instant, item: T) {
        let next = *self.next.get_or_insert(sequence_number);
        let ahead = sequence_number.wrapping_sub(next);
        if ahead >= BEHIND {
            self.ready.push_back(item);
            return;
        }
        if self
            .held
            .iter()
            .any(|held| held.sequence_number == sequence_number)
        {
            return;
        }
        if usize::from(ahead) >= self.max_packets {
            self.release_all();
            self.next = Some(sequence_number);
        }
        self.held.push(Held {
            sequence_number,
            arrived,
            item,
        });
        self.release_run();
    }

    pub(super) fn expire(&mut self, now: Instant) {
        while self.deadline().is_some_and(|deadline| deadline <= now) {
            self.skip_gap();
        }
    }

    pub(super) fn deadline(&self) -> Option<Instant> {
        self.held
            .iter()
            .map(|held| held.arrived)
            .min()
            .map(|arrived| arrived + self.max_delay)
    }

    pub(super) fn pop(&mut self) -> Option<T> {
        self.ready.pop_front()
    }

    fn release_run(&mut self) {
        while let Some(next) = self.next
            && let Some(i) = self
                .held
                .iter()
                .position(|held| held.sequence_number == next)
        {
            self.ready.push_back(self.held.swap_remove(i).item);
            self.next = Some(next.wrapping_add(1));
        }
    }

    fn skip_gap(&mut self) {
        let Some(next) = self.next else {
            return;
        };
        self.next = self
            .held
            .iter()
            .map(|held| held.sequence_number)
            .min_by_key(|sequence_number| sequence_number.wrapping_sub(next))
            .or(self.next);
        self.release_run();
    }

    fn release_all(&mut self) {
        while !self.held.is_empty() {
            self.skip_gap();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const DELAY: Duration = Duration::from_millis(20);

    fn drained(reorder: &mut Reorder<u16>) -> Vec<u16> {
        std::iter::from_fn(|| reorder.pop()).collect()
    }

    fn pushed(reorder: &mut Reorder<u16>, at: Instant, sequence_numbers: &[u16]) -> Vec<u16> {
        sequence_numbers
            .iter()
            .for_each(|&sequence_number| reorder.push(sequence_number, at, sequence_number));
        drained(reorder)
    }

    #[test]
    fn packets_swapped_on_the_way_come_out_in_order() {
        let now = Instant::now();
        let mut reorder = Reorder::new(8, DELAY);
        assert_eq!(
            pushed(&mut reorder, now, &[10, 12, 11, 13]),
            [10, 11, 12, 13]
        );
        assert_eq!(reorder.deadline(), None);
    }

    #[test]
    fn a_lost_packet_holds_the_ones_after_it_only_until_the_delay_or_the_window_runs_out() {
        let now = Instant::now();
        let mut reorder = Reorder::new(4, DELAY);
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
    fn late_duplicate_and_far_ahead_packets_are_passed_on_as_the_in_order_parser_expects() {
        let now = Instant::now();
        let mut reorder = Reorder::new(8, DELAY);
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
    fn sequence_numbers_wrap() {
        let now = Instant::now();
        let mut reorder = Reorder::new(8, DELAY);
        assert_eq!(
            pushed(&mut reorder, now, &[0xfffe, 0x0000, 0xffff, 0x0001]),
            [0xfffe, 0xffff, 0x0000, 0x0001]
        );
    }

    #[test]
    fn disabled_with_no_window() {
        assert!(!Reorder::<u16>::new(0, DELAY).enabled());
        assert!(Reorder::<u16>::new(1, DELAY).enabled());
    }
}
