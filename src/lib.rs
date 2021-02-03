#![allow(dead_code)]

pub mod util;
pub mod iter;

use std::collections::{VecDeque, vec_deque::Iter};
use std::convert::TryFrom;
use std::ops::{Shl, Shr, Range};
use std::iter::Map;
use std::fmt::Debug;

use util::*;
use iter::*;

pub type Digit = u8;
pub type Pair = (Digit, Digit);

pub struct Base {
    base: usize,
    addition_table: Vec<Pair>,
    multiplication_table: Vec<Pair>,
}
impl Base {
    pub fn new(base: usize) -> Self {
        let mut addition_table = Vec::new(); // TODO capacity
        let mut multiplication_table = Vec::new();
        for (add, mul) in ArithmeticPrecomputation::new(base) {
            addition_table.push(add);
            multiplication_table.push(mul);
        }
        Self {
            base,
            addition_table,
            multiplication_table,
        }
    }

    /// Given two digits, returns the digits of their sum in the form of (first_digit,
    /// carry_digit).
    pub fn addition_lookup(&self, a: Digit, b: Digit) -> Pair {
        *self.addition_table.get(pair_index((a, b), self.base)).unwrap()
    }
    /// Given two digits, returns the digits of their product in the form of (first_digit,
    /// carry_digit).
    pub fn multiplication_lookup(&self, a: Digit, b: Digit) -> Pair {
        *self.multiplication_table.get(pair_index((a, b), self.base)).unwrap()
    }
}
impl Debug for Base {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Base").field("base", &self.base).finish()
        // Don't print precomputation tables, as they can be very long & aren't
        // normally interesting
    }
}

#[derive(Debug)]
pub struct Number<'base> {
    digits: VecDeque<Digit>,
    power: isize,
    sign: Sign,
    base: &'base Base
}
impl<'base> Number<'base> {
    pub fn new(base: &'base Base) -> Self {
        Self {
            digits: VecDeque::new(),
            power: 0,
            sign: Sign::Positive,
            base
        }
    }
    pub fn with_capacity(base: &'base Base, digits: usize) -> Self {
        Self {
            digits: VecDeque::with_capacity(digits),
            power: 0,
            sign: Sign::Positive,
            base
        }
    }
    pub fn from_usize(base: &'base Base, integer: usize) -> Self {
        let digits = reverse(ConversionFromUsize::new(integer, base.base).collect::<VecDeque<_>>());
        Self {
            digits,
            power: 0,
            sign: Sign::Positive,
            base
        }
    }
    pub fn from_isize(base: &'base Base, integer: isize) -> Self {
        let digits = reverse(ConversionFromUsize::new(isize::abs(integer) as usize, base.base).collect::<VecDeque<_>>());
        let sign = if integer >= 0 { Sign::Positive } else { Sign::Negative };
        Self {
            digits,
            power: 0,
            sign,
            base
        }
    }

    pub fn digits(&self) -> usize {
        self.digits.len()
    }
    pub fn power(&self) -> isize {
        self.power
    }
    pub fn sign(&self) -> Sign {
        self.sign
    }
    pub fn positive(&self) -> bool {
        self.sign == Sign::Positive
    }
    pub fn negative(&self) -> bool {
        self.sign == Sign::Negative
    }
    pub fn is_integer(&self) -> bool {
        self.digits.len() == 0 || self.power >= 0
    }

    /// Vector API

    pub fn get(&self, idx: usize) -> Option<Digit> {
        self.digits.get(idx).map(|d| *d)
    }
    pub fn set(&mut self, idx: usize, digit: Digit) {
        if idx > self.digits.len() {
            panic!("Attempted to set inaccessible digit.");
            // TODO make consistent with vec panic msg
        }
        if idx == self.digits.len() {
            self.push_high(digit);
            return;
        }
        self.digits[idx] = digit;
    }
    /// Adds a new digit to the highest-order position
    pub fn push_high(&mut self, digit: Digit) {
        self.digits.push_back(digit);
    }
    /// Removes the digit from the highest order position, and returns it (if it
    /// exists)
    pub fn pop_high(&mut self) -> Option<Digit> {
        self.digits.pop_back()
    }
    /// Adds a new digit to the lowest-order position
    pub fn push_low(&mut self, digit: Digit) {
        self.digits.push_front(digit);
    }
    /// Removes the digit from the lowest order position, and returns it (if it
    /// exists)
    pub fn pop_low(&mut self) -> Option<Digit> {
        self.digits.pop_front()
    }

    fn pad_digits_high(&mut self, digits: usize) {
        for _ in 0..digits {
            self.push_high(0);
        }
        // TODO optimize
    }
    fn pad_digits_low(&mut self, digits: usize) {
        for _ in 0..digits {
            self.push_low(0);
            // TODO optimize
        }
        self.power -= isize::try_from(digits).expect("Overflowed isize while adding low-order digits.");
    }

    /// Arithmetic

    /// Returns the index of the digit representing a certain power, if it exists.
    /// Otherwise returns an error containing the number of digits required, to which side, and
    /// what the index will be after they are added.
    fn power_idx(&self, power: isize) -> Result<usize, PowerIndexError> {
        if self.digits.len() == 0 {
            if power == 0 {
                return Err(PowerIndexError::InsufficientDigitsHigh(1));
            } else if power > 0 {
                return Err(PowerIndexError::InsufficientDigitsHigh(power as usize));
            } else {
                return Err(PowerIndexError::InsufficientDigitsLow(-power as usize));
            }
        }

        let highest_digit = self.power + isize::try_from(self.digits.len() - 1).expect("Couldn't convert digit count to isize");
        // We can safely subtract 1 from self.digits because we've already determined it is not 0
        // Below our arithmetic is always nonnegative, and so the casting to usize is safe
        if power > highest_digit {
            return Err(PowerIndexError::InsufficientDigitsHigh((power - highest_digit) as usize));
        } else if power < self.power {
            return Err(PowerIndexError::InsufficientDigitsLow((self.power - power) as usize));
        }

        Ok((power - self.power) as usize)
    }

    // TODO better name
    pub fn arithmetic_setup(&mut self, power: isize) -> Result<usize, usize> {
        match self.power_idx(power) {
            Ok(idx) => Ok(idx), // We have a digit in this power - return it
            Err(PowerIndexError::InsufficientDigitsLow(needed)) => {
                self.pad_digits_low(needed);
                Err(0)
                // We didn't have a digit in this power & needed more low-order
                // digits - the 0th digit is now at this power
            },
            Err(PowerIndexError::InsufficientDigitsHigh(needed)) => {
                let idx = (self.digits.len() - 1) + needed;
                self.pad_digits_high(needed);
                Err(idx)
                // We didn't have a digit in this power & needed more high-order
                // digits - the index is the number of digits we added past the
                // previous last digit
            }
        }
    }

    pub fn add_digit(&mut self, digit: Digit, power: isize) {
        // TODO add asserts
        if self.digits.len() == 0 {
            self.push_high(digit);
            self.power = power;
            return;
        }
        
        match self.arithmetic_setup(power) {
            Err(idx) => self.digits[idx] = digit, // We had to allocate - eg, digit is 0
            Ok(mut idx) => {
                let first_digit = self.digits[idx];
                let (new_digit, mut carry) = self.base.addition_lookup(first_digit, digit);
                self.digits[idx] = new_digit;
                idx += 1;
                while idx < self.digits.len() && carry != 0 {
                    // TODO when destucturing is supported in assignment, change this :(
                    let (new_digit, new_carry) = self.base.addition_lookup(carry, self.digits[idx]);
                    carry = new_carry;
                    self.digits[idx] = new_digit;
                    idx += 1;
                }
                if carry != 0 {
                    self.push_high(carry);
                }
            }
        }
    }
//     pub fn sub_digit(&mut self, digit: Digit, power: usize) {
// 
//     }

    pub fn negate(&mut self) {
        self.sign = match self.sign {
            Sign::Positive => Sign::Negative,
            Sign::Negative => Sign::Positive
        }
    }

    pub fn digit_iter(&self) -> Map<Iter<'_, Digit>, fn(&u8) -> u8> {
        self.digits.iter().map(|d| *d)
    }

    pub fn power_iter(&self) -> Range<isize> {
        let low_power = self.power;
        let high_power = isize::try_from(self.digits.len()).expect("Failed to convert usize to isize") + self.power;
        low_power..high_power
    }

    pub fn digit_and_power_iter(&self) -> DigitAndPowerIter {
        DigitAndPowerIter::new(self)
    }

    pub fn as_isize(&self) -> isize {
        if !self.is_integer() {
            panic!("Unable to convert to isize: number is not an integer");
        }
        let mut n = 0;
        let base = self.base.base as isize;
        for (digit, power) in self.digit_and_power_iter() {
            // TODO make power i32?
            n += base.pow(power as u32) * (digit as isize);
        }
        if self.negative() {
            n = -n
        }
        n
    }
}

impl Shl<usize> for Number<'_> {
    type Output = Self;

    fn shl(mut self, rhs: usize) -> Self::Output {
        self.power += isize::try_from(rhs).expect("Failed to convert into isize during left shift.");
        self
    }
}

impl Shr<usize> for Number<'_> {
    type Output = Self;

    fn shr(mut self, rhs: usize) -> Self::Output {
        self.power -= isize::try_from(rhs).expect("Failed to convert into isize during right shift.");
        self
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Sign {
    Positive,
    Negative
}

enum PowerIndexError {
    InsufficientDigitsHigh(usize),
    InsufficientDigitsLow(usize)
}

#[cfg(test)]
pub mod test {
    use super::*;

    /// Number Vector API

    #[test]
    fn push_high_puts_digit_on_left() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_high(5);
        n.push_high(1);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(1, 5));
    }

    #[test]
    fn push_low_puts_digit_on_right() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_low(1);
        n.push_low(5);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(1, 5));
    }

    #[test]
    fn pop_high_takes_digits_from_right() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_high(5);
        n.push_high(1);
        assert_eq!(n.pop_high(), Some(1));
        assert_eq!(n.pop_high(), Some(5));
        assert_eq!(n.pop_high(), None);
    }

    #[test]
    fn pop_low_takes_digits_from_left() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_low(1);
        n.push_low(5);
        assert_eq!(n.pop_low(), Some(5));
        assert_eq!(n.pop_low(), Some(1));
        assert_eq!(n.pop_low(), None);
    }

    #[test]
    fn push_high_and_pop_high_are_inverse() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_high(5);
        n.push_high(1);
        assert_eq!(n.pop_high(), Some(1));
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(5));
    }

    #[test]
    fn push_low_and_pop_low_are_inverse() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_low(5);
        n.push_low(1);
        assert_eq!(n.pop_low(), Some(1));
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(5));
    }

    #[test]
    fn pushing_increases_digits() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_high(5);
        assert_eq!(n.digits(), 1);
        n.push_low(1);
        assert_eq!(n.digits(), 2);
    }

    #[test]
    fn popping_reduces_digits() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_high(5);
        n.push_low(1);
        n.pop_high();
        assert_eq!(n.digits(), 1);
        n.pop_low();
        assert_eq!(n.digits(), 0);
    }

    #[test]
    fn alternating_pushing_high_and_low() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_high(1);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(1));
        n.push_low(2);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(1, 2));
        n.push_high(3);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(3, 1, 2));
        n.push_low(4);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(3, 1, 2, 4));
    }

    #[test]
    fn alternating_popping_high_and_low() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        for i in 1..=9 {
            n.push_low(i);
        }
        assert_eq!(n.pop_high(), Some(1));
        assert_eq!(n.pop_low(), Some(9));
        assert_eq!(n.pop_high(), Some(2));
        assert_eq!(n.pop_low(), Some(8));
        assert_eq!(n.pop_high(), Some(3));
        assert_eq!(n.pop_low(), Some(7));
        assert_eq!(n.pop_high(), Some(4));
        assert_eq!(n.pop_low(), Some(6));
        assert_eq!(n.pop_high(), Some(5));

        assert_eq!(n.pop_high(), None);
        assert_eq!(n.pop_low(), None);
    }

    #[test]
    fn get_returns_correct_digit() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        for i in 1..=9 {
            n.push_high(i);
        }
        for i in 0..8 {
            assert_eq!(n.get(i), Some((i+1) as Digit));
        }
    }

    #[test]
    fn set_alters_correct_digit() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        for i in 0..9 {
            n.push_high(i);
        }
        for i in (0..9).into_iter().rev() {
            n.set(i, (i+1) as Digit);
        }
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(9, 8, 7, 6, 5, 4, 3, 2, 1));
    }

    #[test]
    fn set_can_alter_1_digit_past_last_digit() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        for i in 0..9 {
            n.push_high(i);
        }
        n.set(9, 9);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(9, 8, 7, 6, 5, 4, 3, 2, 1, 0));
    }

    /// Arithmetic

    #[test]
    fn single_digit_addition() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_high(1);
        n.add_digit(1, 0);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(2));
    }

    #[test]
    fn single_digit_addition_with_carry() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        for _ in 0..3 {
            n.push_high(9);
        }
        n.add_digit(1, 0);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(1,0,0,0));
    }

    #[test]
    fn single_digit_addition_with_carry_that_does_not_travel_all_the_way() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_high(8);
        n.push_high(9);
        n.push_high(9);
        n.push_high(1);
        n.add_digit(2, 0);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(2, 0, 0, 0));
    }

    #[test]
    fn single_digit_addition_with_new_digit_high() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_high(1);
        n.add_digit(2, 1);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(2, 1));
    }

    #[test]
    fn single_digit_addition_with_new_digit_low() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_high(1);
        n.add_digit(2, -1);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(1, 2));
    }

    #[test]
    fn shift_left_increases_power() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n = n << 1;
        assert_eq!(n.power(), 1);
    }

    #[test]
    fn shift_right_decreases_power() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n = n >> 1;
        assert_eq!(n.power(), -1);
    }

//     proptest!(
//         #[test]
//         fn add_arbitrary_digit(digit in 
//     )

    /// Conversion

    #[test]
    fn conversion_from_usize() {
        let b = Base::new(10);
        let n = Number::from_usize(&b, 123);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(3, 2, 1));
    }

    #[test]
    fn conversion_from_positive_isize() {
        let b = Base::new(10);
        let n = Number::from_isize(&b, 123);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(3, 2, 1));
        assert!(n.positive());
    }

    #[test]
    fn conversion_from_negative_isize() {
        let b = Base::new(10);
        let n = Number::from_isize(&b, -123);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(3, 2, 1));
        assert!(n.negative());
    }

    #[test]
    fn iter_digits_and_powers() {
        let b = Base::new(10);
        let n = Number::from_isize(&b, 123);
        assert_eq!(n.digit_and_power_iter().collect::<Vec<_>>(), vec!((3, 0), (2, 1), (1, 2)));
    }

    #[test]
    fn conversion_to_isize_positive() {
        let b = Base::new(10);
        let n = Number::from_isize(&b, 123);
        assert_eq!(n.as_isize(), 123);
    }

    #[test]
    fn conversion_to_isize_negative() {
        let b = Base::new(10);
        let n = Number::from_isize(&b, -123);
        assert_eq!(n.as_isize(), -123);
    }
}
