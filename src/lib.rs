#![allow(dead_code)]

pub mod util;
pub mod iter;

use std::collections::VecDeque;
use std::convert::TryFrom;
use std::ops::{Shl, Shr};
use util::*;
use iter::BorrowedNumberIter;

pub type Digit = u8;
pub type Pair = (Digit, Digit);
pub type Bucket = usize;

#[derive(Debug)]
pub struct Base {
    base: u32,
    addition_table: Vec<Pair>,
    multiplication_table: Vec<Pair>,
    digit_width: usize,
    digits_per_bucket: usize,
    digit_bitmask: usize,
}
impl Base {
    pub fn new(base: u32) -> Self {
        let mut addition_table = Vec::new(); // TODO capacity
        let mut multiplication_table = Vec::new();
        for (add, mul) in ArithmeticPrecomputation::new(base) {
            addition_table.push(add);
            multiplication_table.push(mul);
        }
        let (digit_width, digits_per_bucket, digit_bitmask) = bitwise_parameters(base);
        Self {
            base,
            addition_table,
            multiplication_table,
            digit_width,
            digits_per_bucket,
            digit_bitmask
        }
    }

    /// Given two digits, returns the digits of their sum in the form of (first_digit,
    /// carry_digit).
    pub fn add_digits(&self, a: Digit, b: Digit) -> Pair {
        *self.addition_table.get(pair_index((a, b), self.base)).unwrap()
    }
    /// Given two digits, returns the digits of their product in the form of (first_digit,
    /// carry_digit).
    pub fn multiply_digits(&self, a: Digit, b: Digit) -> Pair {
        *self.multiplication_table.get(pair_index((a, b), self.base)).unwrap()
    }

    pub fn digits_per_bucket(&self) -> usize {
        self.digits_per_bucket
    }
    pub fn digit_width(&self) -> usize {
        self.digit_width
    }
    pub fn digit_bitmask(&self) -> usize {
        self.digit_bitmask
    }

    /// Returns the index of a bucket within a vector of buckets, given the index
    /// of a digit
    pub fn bucket_index(&self, idx: usize) -> usize {
        idx / self.digits_per_bucket
    }
    /// Returns the index of a digit within it's respective bucket, given the index
    /// of a digit
    pub fn digit_index(&self, idx: usize) -> usize {
        idx % self.digits_per_bucket
    }
    /// Given the index of a particular digit, returns the index of it's bucket
    /// within the vector of buckets, and it's index within that bucket.
    pub fn indexes(&self, idx: usize) -> (usize, usize) {
        (self.bucket_index(idx), self.digit_index(idx))
    }
}

#[derive(Debug)]
pub struct Number<'base> {
    buckets: VecDeque<Bucket>,
    digits: usize,
    power: isize,
    sign: Sign,
    base: &'base Base
}
impl<'base> Number<'base> {
    pub fn new(base: &'base Base) -> Self {
        Self {
            buckets: VecDeque::new(),
            digits: 0,
            power: 0,
            sign: Sign::Positive,
            base
        }
    }
    pub fn with_capacity(base: &'base Base, digits: usize) -> Self {
        let mut buckets = digits / base.digits_per_bucket();
        if digits % base.digits_per_bucket() != 0 {
            buckets += 1;
        }
        Self {
            buckets: VecDeque::with_capacity(buckets),
            digits: 0,
            power: 0,
            sign: Sign::Positive,
            base
        }
    }

    pub fn digits(&self) -> usize {
        self.digits
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

    /// Vector API

    pub fn get(&self, idx: usize) -> Option<Digit> {
        if idx > self.digits || self.digits == 0 {
            return None;
        }
        let (bucket_idx, digit_idx) = self.base.indexes(idx);
        Some(self.get_digit(bucket_idx, digit_idx))
    }
    pub fn set(&mut self, idx: usize, digit: Digit) {
        if idx > self.digits {
            panic!("Attempted to set inaccessible digit.");
            // TODO make consistent with vec panic msg
        }
        if idx == self.digits {
            self.push_high(digit);
            return;
        }
        let (bucket_idx, digit_idx) = self.base.indexes(idx);
        self.set_digit(bucket_idx, digit_idx, digit);
    }
    /// Adds a new digit to the highest-order position
    pub fn push_high(&mut self, digit: Digit) {
        let (bucket_idx, digit_idx) = self.base.indexes(self.digits);
        if digit_idx == 0 { // New bucket
            self.buckets.push_back(digit as Bucket)
        } else {
            self.set_digit(bucket_idx, digit_idx, digit)
        }
        self.digits += 1;
    }
    /// Removes the digit from the highest order position, and returns it (if it
    /// exists)
    pub fn pop_high(&mut self) -> Option<Digit> {
        if self.digits == 0 {
            return None;
        }
        let (bucket_idx, digit_idx) = self.base.indexes(self.digits - 1);
        let digit = self.get_digit(bucket_idx, digit_idx);
        self.digits -= 1;
        if digit_idx == 0 {
            self.buckets.pop_back();
        }
        Some(digit)
    }
    /// Adds a new digit to the lowest-order position
    pub fn push_low(&mut self, digit: Digit) {
        let (bucket_idx, digit_idx) = (0, 0);
        // push_low always pushes to (0, 0) - no need to call indexes() 
        if self.digits == 0 || self.base.digit_index(self.digits - 1) == self.base.digits_per_bucket - 1 { // New bucket
            self.buckets.push_back(0)
        }
        self.shift_digits_high(1);
        self.set_digit(bucket_idx, digit_idx, digit);
        self.digits += 1;
    }
    /// Removes the digit from the lowest order position, and returns it (if it
    /// exists)
    pub fn pop_low(&mut self) -> Option<Digit> {
        if self.digits == 0 {
            return None;
        }
        let (bucket_idx, digit_idx) = (0, 0);
        let digit = self.get_digit(bucket_idx, digit_idx);
        self.shift_digits_low(1);
        self.digits -= 1;
        Some(digit)
    }
//     fn pad_high(&mut self, zeroes: usize) {
//     }
//     fn pad_low(&mut self, zeroes: usize) {
//     }

    /// Bucket Management

    fn set_digit(&mut self, bucket_idx: usize, digit_idx: usize, digit: Digit) {
        let bucket = self.buckets.get_mut(bucket_idx).expect("Attempted to set digit in uninitialzed bucket");
        let shift = self.base.digit_width() * digit_idx;
        *bucket = (*bucket & !(self.base.digit_bitmask() << shift)) | ((digit as usize) << shift);
    }
    fn get_digit(&self, bucket_idx: usize, digit_idx: usize) -> Digit {
        let bucket = self.buckets.get(bucket_idx).expect("Attempted to fetch digit from uninitialzed bucket.");
        let shift = self.base.digit_width() * digit_idx;
        ((bucket & (self.base.digit_bitmask() << shift)) >> shift) as Digit
    }
    /// Assumes caller has allocated space as necessary.
    fn shift_digits_high(&mut self, shift: usize) {
        // TODO use bit shifts rather than set_digit to do an entire bucket at once
        if self.digits == 0 {
            return;
        }
        for _ in 0..shift {
            for idx in (0..self.digits).into_iter().rev() {
                let (current_bucket_idx, current_digit_idx) = self.base.indexes(idx);
                let digit = self.get_digit(current_bucket_idx, current_digit_idx);
                let (new_bucket_idx, new_digit_idx) = self.base.indexes(idx + 1);
                self.set_digit(new_bucket_idx, new_digit_idx, digit);

            }
        }
    }
    /// Assumes caller has allocated space as necessary.
    /// First digit is is overwritten
    fn shift_digits_low(&mut self, shift: usize) {
        // TODO use bit shifts rather than set_digit to do an entire bucket at once
        if self.digits == 0 {
            return;
        }
        for _ in 0..shift {
            for idx in 1..self.digits {
                let (current_bucket_idx, current_digit_idx) = self.base.indexes(idx);
                let digit = self.get_digit(current_bucket_idx, current_digit_idx);
                let (new_bucket_idx, new_digit_idx) = self.base.indexes(idx - 1);
                self.set_digit(new_bucket_idx, new_digit_idx, digit);
            }
        }
    }
    fn add_buckets_high(&mut self, buckets: usize) {
        self.buckets.reserve(buckets);
        for _bucket in 0..buckets {
            self.buckets.push_front(0);
        }
    }
    fn add_buckets_low(&mut self, buckets: usize) {
        self.buckets.reserve(buckets);
        for _bucket in 0..buckets {
            self.buckets.push_back(0);
        }
    }
    fn pad_digits_high(&mut self, digits: usize) {
        for _ in 0..self.digits {
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
        if self.digits == 0 {
            if power == 0 {
                return Err(PowerIndexError::InsufficientDigitsHigh(1));
            } else if power > 0 {
                return Err(PowerIndexError::InsufficientDigitsHigh(power as usize));
            } else {
                return Err(PowerIndexError::InsufficientDigitsLow(-power as usize));
            }
        }

        let highest_digit = self.power + isize::try_from(self.digits - 1).expect("Couldn't convert digit count to isize");
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
    fn arithmetic_setup(&mut self, power: isize) -> usize {
        match self.power_idx(power) {
            Ok(idx) => idx,
            Err(PowerIndexError::InsufficientDigitsLow(digits_needed)) => {
                self.pad_digits_low(digits_needed);
                0 // If we need low order, then our index will always be 0
                  // (eg the first digit)
            },
            Err(PowerIndexError::InsufficientDigitsHigh(digits_needed)) => {
                let idx = (self.digits - 1) + digits_needed;
                // If we need high order digits, then our index will always be
                // the number of added digits past the highest digit
                // -1 for zero indexing
                self.pad_digits_high(digits_needed);
                idx
            }
        }
    }

    pub fn add_digit(&mut self, digit: Digit, power: isize) {
        // TODO add asserts
        let mut idx = self.arithmetic_setup(power);
        let (bucket_idx, digit_idx) = self.base.indexes(idx);
        let (new_digit, mut carry) = self.base.add_digits(digit, self.get_digit(bucket_idx, digit_idx));
        self.set_digit(bucket_idx, digit_idx, new_digit);
        idx += 1;

        while idx < self.digits && carry != 0 {
            let (bucket_idx, digit_idx) = self.base.indexes(idx);
            // TODO when destucturing is supported in assignment, change this :(
            let (new_digit, new_carry) = self.base.add_digits(carry, self.get_digit(bucket_idx, digit_idx));
            carry = new_carry;
            self.set_digit(bucket_idx, digit_idx, new_digit);
            idx += 1;
        }
        if carry != 0 {
            self.push_high(carry);
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

    pub fn iter(&self) -> BorrowedNumberIter {
        BorrowedNumberIter::new(self)
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

fn bitwise_parameters(base: u32) -> (usize, usize, usize) {
    let base = base as usize;
    let highest_digit = base - 1;
    // TODO move to usize::BITS when the feature lands in stable
    let usize_bits = 0usize.leading_zeros();

    let digits_width = usize_bits - highest_digit.leading_zeros();
    let digits_per_bucket = usize_bits / digits_width;
    let mask = !(usize::MAX << digits_width as usize);

    (digits_width as usize, digits_per_bucket as usize, mask)
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
        assert_eq!(n.iter().collect::<Vec<_>>(), vec!(1, 5));
    }

    #[test]
    fn push_low_puts_digit_on_right() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_low(1);
        n.push_low(5);
        assert_eq!(n.iter().collect::<Vec<_>>(), vec!(1, 5));
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
        assert_eq!(n.iter().collect::<Vec<_>>(), vec!(5));
    }

    #[test]
    fn push_low_and_pop_low_are_inverse() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_low(5);
        n.push_low(1);
        assert_eq!(n.pop_low(), Some(1));
        assert_eq!(n.iter().collect::<Vec<_>>(), vec!(5));
    }

    #[test]
    fn pushing_increases_digits() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_high(5);
        assert_eq!(n.digits, 1);
        n.push_low(1);
        assert_eq!(n.digits, 2);
    }

    #[test]
    fn popping_reduces_digits() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_high(5);
        n.push_low(1);
        n.pop_high();
        assert_eq!(n.digits, 1);
        n.pop_low();
        assert_eq!(n.digits, 0);
    }

    #[test]
    fn alternating_pushing_high_and_low() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_high(1);
        assert_eq!(n.iter().collect::<Vec<_>>(), vec!(1));
        n.push_low(2);
        assert_eq!(n.iter().collect::<Vec<_>>(), vec!(1, 2));
        n.push_high(3);
        assert_eq!(n.iter().collect::<Vec<_>>(), vec!(3, 1, 2));
        n.push_low(4);
        assert_eq!(n.iter().collect::<Vec<_>>(), vec!(3, 1, 2, 4));
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
    fn pushing_high_past_bucket_boundary() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        for _ in 0..(b.digits_per_bucket() + 1) {
            n.push_high(1);
        }
        assert_eq!(
            n.iter().collect::<Vec<_>>(),
            (0..b.digits_per_bucket() + 1).map(|_| 1).collect::<Vec<_>>()
        );
    }

    #[test]
    fn pushing_low_past_bucket_boundary() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        for _ in 0..(b.digits_per_bucket() + 1) {
            n.push_low(1);
        }
        assert_eq!(
            n.iter().collect::<Vec<_>>(),
            (0..b.digits_per_bucket() + 1).map(|_| 1).collect::<Vec<_>>()
        );
    }

    #[test]
    fn popping_high_past_bucket_boundary() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        for _ in 0..(b.digits_per_bucket() + 1) {
            n.push_high(1);
        }
        for _ in 0..(b.digits_per_bucket() + 1) {
            assert_eq!(n.pop_high(), Some(1));
        }
        assert_eq!(n.pop_high(), None);
    }

    #[test]
    fn popping_low_past_bucket_boundary() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        for _ in 0..(b.digits_per_bucket() + 1) {
            n.push_high(1);
        }
        for _ in 0..(b.digits_per_bucket() + 1) {
            assert_eq!(n.pop_low(), Some(1));
        }
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
        assert_eq!(n.iter().collect::<Vec<_>>(), vec!(9, 8, 7, 6, 5, 4, 3, 2, 1));
    }

    #[test]
    fn set_can_alter_1_digit_past_last_digit() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        for i in 0..9 {
            n.push_high(i);
        }
        n.set(9, 9);
        assert_eq!(n.iter().collect::<Vec<_>>(), vec!(9, 8, 7, 6, 5, 4, 3, 2, 1, 0));
        // TODO iter weirdness
    }

    /// Arithmetic

    #[test]
    fn single_digit_addition() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_high(1);
        n.add_digit(1, 0);
        assert_eq!(n.iter().collect::<Vec<_>>(), vec!(2));
    }

    #[test]
    fn single_digit_addition_with_carry() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        for _ in 0..3 {
            n.push_high(9);
        }
        n.add_digit(1, 0);
        assert_eq!(n.iter().collect::<Vec<_>>(), vec!(1,0,0,0));
    }

    #[test]
    fn single_digit_addition_with_carry_across_bucket_boundary() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        for _ in 0..b.digits_per_bucket() {
            n.push_high(9);
        }
        n.add_digit(1, 0);
        let mut expected = Vec::new();
        expected.push(1);
        for _ in 0..b.digits_per_bucket() {
            expected.push(0);
        }
        assert_eq!(n.iter().collect::<Vec<_>>(), expected);
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
        assert_eq!(n.iter().collect::<Vec<_>>(), vec!(2, 0, 0, 0));
    }

    #[test]
    fn single_digit_addition_with_new_digit_high() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_high(1);
        n.add_digit(2, 1);
        assert_eq!(n.iter().collect::<Vec<_>>(), vec!(2, 1));
    }

    #[test]
    fn single_digit_addition_with_new_digit_low() {
        let b = Base::new(10);
        let mut n = Number::new(&b);
        n.push_high(1);
        n.add_digit(2, -1);
        assert_eq!(n.iter().collect::<Vec<_>>(), vec!(1, 2));
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
}
