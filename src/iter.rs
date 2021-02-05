use std::collections::vec_deque::Iter;
use std::ops::Range;
use std::iter::Map;

use crate::{Number, Digit};

pub struct DigitAndPowerIter<'number> {
    digit_iter: Map<Iter<'number, Digit>, fn(&Digit) -> Digit>,
    power_iter: Range<isize>
}
impl<'number> DigitAndPowerIter<'number> {
    pub fn new(number: &'number Number) -> Self {
        Self {
            digit_iter: number.digit_iter(),
            power_iter: number.power_iter()
        }
    }
}
impl<'number> Iterator for DigitAndPowerIter<'number> {
    type Item = (Digit, isize);

    fn next(&mut self) -> Option<Self::Item> {
        let power = self.power_iter.next()?;
        let digit = self.digit_iter.next().unwrap_or_default();
        Some((digit, power))
    }
}

