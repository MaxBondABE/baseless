use std::collections::VecDeque;

use crate::Digit;

pub fn reverse(mut v: VecDeque<Digit>) -> VecDeque<Digit> {
    let half = v.len()/2;
    for (a, b) in (0..half).zip((half..v.len()).into_iter().rev()) {
        v.swap(a, b);
    }
    v
}

// TODO make ExactSizeIterator
/// Iterator which calculates each digit required to represent a native integer
/// as 
pub struct ConversionFromUsize {
    integer: usize,
    base: usize,
    power: u32,
    done: bool
}
impl ConversionFromUsize {
    pub fn new(integer: usize, base: usize) -> Self {
        let power = (integer as f64).log(base as f64).floor() as u32;
        Self {
            integer,
            base,
            power,
            done: false
        }
    }
}
impl Iterator for ConversionFromUsize {
    type Item = Digit;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        let place = self.base.pow(self.power);
        let mut digit = 0;
        while self.integer >= place {
            digit += 1;
            self.integer -= place;
        }
        if self.power > 0 {
            self.power -= 1;
        } else {
            self.done = true;
        }
        Some(digit)
    }
}

/// Iterator which converts a number from any base to any other base
pub struct BaseConversion {
}

#[cfg(test)]
pub mod test {
    use super::*;

    #[test]
    fn conversion_from_usize() {
        assert_eq!(
            ConversionFromUsize::new(123, 10).collect::<Vec<_>>(),
            vec!(1, 2, 3)
        );
    }

    #[test]
    fn reverse_even_list() {
        let v = reverse((1..=4).collect::<VecDeque<Digit>>());
        assert_eq!(v, vec!(4, 3, 2, 1));
    }

    #[test]
    fn reverse_odd_list() {
        let v = reverse((1..=5).collect::<VecDeque<Digit>>());
        assert_eq!(v, vec!(5, 4, 3, 2, 1));
    }
}
