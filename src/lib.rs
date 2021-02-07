#![allow(dead_code)]
#![feature(deque_range)]

pub mod util;
pub mod iter;

use std::collections::{VecDeque, vec_deque::Iter as VecIter, vec_deque::IntoIter as VecIntoIter};
use std::convert::TryFrom;
use std::ops::{
    Range,
    Neg, Shl, Shr, Add, Sub, Mul,
    ShlAssign, ShrAssign, AddAssign, SubAssign, MulAssign
};
use std::iter::{Map, Zip};
use std::cmp::Ordering;

use util::*;
use iter::*;

pub type Digit = u8;

#[derive(Debug, Clone)]
pub struct Number {
    digits: VecDeque<Digit>,
    power: isize,
    sign: Sign,
    base: usize
}
impl Number {

    /// Initialization

    pub fn new(base: usize) -> Self {
        Self {
            digits: VecDeque::new(),
            power: 0,
            sign: Sign::Positive,
            base
        }
    }
    pub fn with_capacity(base: usize, digits: usize) -> Self {
        Self {
            digits: VecDeque::with_capacity(digits),
            power: 0,
            sign: Sign::Positive,
            base
        }
    }
    pub fn from_usize(base: usize, integer: usize) -> Self {
        let digits = reverse(ConversionFromUsize::new(integer, base).collect::<VecDeque<_>>());
        Self {
            digits,
            power: 0,
            sign: Sign::Positive,
            base
        }
    }
    pub fn from_isize(base: usize, integer: isize) -> Self {
        let abs = if integer != isize::MIN {
            isize::abs(integer) as usize
        } else {
            (isize::MAX as usize) + 1
            // abs() would overflow
        };
        let digits = reverse(ConversionFromUsize::new(abs, base).collect::<VecDeque<_>>());
        let sign = if integer >= 0 { Sign::Positive } else { Sign::Negative };
        Self {
            digits,
            power: 0,
            sign,
            base
        }
    }

    /// Informational

    pub fn digits(&self) -> usize {
        self.digits.len()
        // TODO rename to significant_digits(), make new function that takes power
        // into account for digits()
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
        self.digits.len() == 0 || self.power >= 0 ||
            self.fraction_digits().unwrap().all(|d| *d == 0)
    }

    // FP API

    pub fn fraction_digits(&self) -> Option<VecIter<Digit>> {
        if self.power >= 0 {
            None
        } else {
            let start = 0;
            let end = isize::abs(self.power) as usize;
            Some(self.digits.range(start..end))
        }
    }
    pub fn floor(&mut self) {
        todo!()
    }
    pub fn ceil(&mut self) {
        todo!()
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
    }
    fn pad_digits_low(&mut self, digits: usize) {
        for _ in 0..digits {
            self.push_low(0);
        }
        self.power -= isize::try_from(digits).expect("Overflowed isize while adding low-order digits.");
    }
    fn trim_zeroes_high(&mut self) {
        while self.digits.back() == Some(&0) {
            self.digits.pop_back();
        }
    }
    fn trim_zeroes_low(&mut self) {
        while self.digits.front() == Some(&0) {
            self.digits.pop_front();
            self.power += 1;
        }
    }
    pub fn simplify(&mut self) {
        self.trim_zeroes_high();
        self.trim_zeroes_low();
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

    fn get_power(&mut self, power: isize) -> usize {
        match self.power_idx(power) {
            Ok(idx) => idx, // We have a digit in this power - return it
            Err(PowerIndexError::InsufficientDigitsLow(needed)) => {
                self.pad_digits_low(needed);
                0
                // We didn't have a digit in this power & needed more low-order
                // digits - the 0th digit is now at this power
            },
            Err(PowerIndexError::InsufficientDigitsHigh(needed)) => {
                let idx = (self.digits.len() - 1) + needed;
                self.pad_digits_high(needed);
                idx
                // We didn't have a digit in this power & needed more high-order
                // digits - the index is the number of digits we added past the
                // previous last digit
            }
        }
    }

    fn add_digit(&mut self, digit: Digit, power: isize, propogate_carry: bool) {
        let mut carry = digit as usize;
        for idx in self.get_power(power)..self.digits.len() {
            let sum = (self.digits[idx] as usize) + carry;
            let (new_digit, new_carry) = self.carry(sum);
            carry = new_carry;
            self.digits[idx] = new_digit as Digit;
            if carry == 0 {
                break;
            }
        }
        if carry != 0 && propogate_carry {
            self.push_high(carry as Digit)
        }
    }

    fn add_digits_from_number(&mut self, other: Self, propogate_carry: bool) {
        for (digit, power) in other {
            self.add_digit(digit, power, propogate_carry);
        }
    }

    fn match_digits_and_powers(&mut self, other: &mut Self) {
        // Match powers & number of digits - complement only works w/
        // same number of digits, same number of digits only meaningful
        // w/ same power
        // TODO overflow issues
        if self.power > other.power {
            self.pad_digits_low(isize::abs(self.power - other.power) as usize)
        } else if other.power > self.power {
            other.pad_digits_low(isize::abs(other.power - self.power) as usize)
        }
        if self.digits.len() > other.digits.len() {
            other.pad_digits_high(self.digits.len() - other.digits.len())
        } else if other.digits.len() > self.digits.len() {
            self.pad_digits_high(other.digits.len() - self.digits.len())
        }
    }

    /// Must be equal in length & power
    fn compare_abs(&mut self, other: &mut Self) -> Ordering {
        let mut gt_idx = self.digits.len()-1;
        while gt_idx > 0 && (self.digits[gt_idx] == other.digits[gt_idx]) {
            gt_idx -= 1;
        }
        if self.digits[gt_idx] == other.digits[gt_idx] {
            Ordering::Equal
        } else if self.digits[gt_idx] > other.digits[gt_idx] {
            Ordering::Greater
        } else {
            Ordering::Less
        }
    }

    fn mul_digit(&self, mul_digit: Digit, power: isize) -> Self {
        let mul_digit = mul_digit as usize;
        let mut output = self.clone();
        let mut carry = 0;
        for digit in output.digits.iter_mut() {
            let product = ((*digit as usize) * mul_digit) + carry;
            let (new_digit, new_carry) = self.carry(product);
            carry = new_carry;
            *digit = new_digit as Digit;
        }
        if carry != 0 {
            output.push_high(carry as Digit);
        }
        output <<= power;
        output
    }

    fn carry(&self, calculation: usize) -> (usize, usize) {
        let carry_digit = calculation / self.base;
        let new_digit = calculation - (carry_digit * self.base);
        (new_digit, carry_digit)
    }

    fn set_sign_for_mul_div(&mut self, other_sign: Sign) {
        match (self.sign, other_sign) {
            (Sign::Positive, Sign::Positive)
            | (Sign::Negative, Sign::Positive) => {}
            (Sign::Negative, Sign::Negative) => { self.sign = Sign::Positive; }
            (Sign::Positive, Sign::Negative) => { self.sign = Sign::Negative; }
        }
    }

    /// Takes the radix complement of the number
    pub fn complement(&mut self) {
        if self.digits.len() == 0 {
            return;
        }
        let mut nonzero_idx = 0;
        while nonzero_idx < self.digits.len() && self.digits[nonzero_idx] == 0 {
            nonzero_idx += 1;
        }
        for idx in nonzero_idx..self.digits.len() {
            let carry = if idx == nonzero_idx { 0 } else { 1 };
            let new_digit = (self.base - ((self.digits[idx] + carry) as usize)) % self.base;
            self.digits[idx] = new_digit as Digit;
        }
    }

    pub fn negate(&mut self) {
        self.sign = match self.sign {
            Sign::Positive => Sign::Negative,
            Sign::Negative => Sign::Positive
        }
    }

    /// Iteration

    pub fn digit_iter(&self) -> Map<VecIter<'_, Digit>, fn(&u8) -> u8> {
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

    /// Conversion

    pub fn as_isize(&self) -> isize {
        if !self.is_integer() {
            panic!("Unable to convert to isize: number is not an integer");
        }
        let mut n = 0;
        for (digit, power) in self.digit_and_power_iter().filter(|(_, power)| *power >= 0) {
            n += self.base.pow(power as u32) * (digit as usize);
        }
        if self.negative() {
            if n == (isize::MAX as usize) + 1 {
                isize::MIN
            } else {
                -(n as isize)
            }
        } else {
            n as isize
        }
    }

    pub fn as_usize(&self) -> usize {
        if !self.is_integer() {
            panic!("Unable to convert to usize: number is not an integer");
        }
        if !self.positive() {
            panic!("Unable to convert to usize: number is negative");
        }
        let mut n = 0;
        for (digit, power) in self.digit_and_power_iter().filter(|(_, power)| *power >= 0) {
            n += self.base.pow(power as u32) * (digit as usize);
        }
        n
    }

    pub fn as_u128(&self) -> u128 {
        if !self.is_integer() {
            panic!("Unable to convert to u128: number is not an integer");
        }
        if !self.positive() {
            panic!("Unable to convert to u128: number is negative");
        }
        let mut n = 0;
        let base = self.base as u128;
        for (digit, power) in self.digit_and_power_iter().filter(|(_, power)| *power >= 0) {
            n += base.pow(power as u32) * (digit as u128);
        }
        n
    }

    pub fn as_i128(&self) -> i128 {
        if !self.is_integer() {
            panic!("Unable to convert to i128: number is not an integer");
        }
        let mut n = 0;
        let base = self.base as u128;
        for (digit, power) in self.digit_and_power_iter().filter(|(_, power)| *power >= 0) {
            n += base.pow(power as u32) * (digit as u128);
        }
        if self.negative() {
            if n == (i128::MAX as u128) + 1 {
                i128::MIN
            } else {
                -(n as i128)
            }
        } else {
            n as i128
        }
    }
}

impl IntoIterator for Number {
    type Item = (Digit, isize);

    type IntoIter = Zip<VecIntoIter<Digit>, Range<isize>>;

    fn into_iter(self) -> Self::IntoIter {
        let powers = self.power_iter();
        self.digits.into_iter().zip(powers)
    }
}

impl Neg for &mut Number {
    type Output = Self;
    fn neg(self) -> Self::Output {
        self.negate();
        self
    }
}
impl Neg for Number {
    type Output = Self;
    fn neg(mut self) -> Self::Output {
        let _ = (&mut self).neg();
        self
    }
}

impl AddAssign<Number> for &mut Number {
    fn add_assign(&mut self, mut rhs: Number) {
        if self.sign == rhs.sign {
            self.add_digits_from_number(rhs, true);
        } else {
            self.match_digits_and_powers(&mut rhs);
            let overflow;
            match self.compare_abs(&mut rhs) {
                Ordering::Equal => {
                    self.digits.truncate(0);
                    return;
                }
                Ordering::Greater => { overflow = false; }
                Ordering::Less => { overflow = true; }
            }
            if self.negative() { self.complement() } else { rhs.complement() }
            self.add_digits_from_number(rhs, false);
            if overflow {
                self.negate();
            }
            if self.negative() {
                self.complement()
            }
        }
    }
}
impl AddAssign<Number> for Number {
    fn add_assign(&mut self, rhs: Number) {
        // Pass the buck to the &mut Number implementation
        let mut x = self;
        x += rhs;
    }
}
impl Add<Number> for Number {
    type Output = Self;

    fn add(mut self, rhs: Number) -> Self::Output {
        self += rhs;
        self
    }
}
impl Add<usize> for Number {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        let rhs = Number::from_usize(self.base, rhs);
        self + rhs
    }
}
impl Add<isize> for Number {
    type Output = Self;

    fn add(self, rhs: isize) -> Self::Output {
        let rhs = Number::from_isize(self.base, rhs);
        self + rhs
    }
}

impl SubAssign<Number> for &mut Number {
    fn sub_assign(&mut self, rhs: Number) {
        *self += -rhs;
    }
}
impl SubAssign<Number> for Number {
    fn sub_assign(&mut self, rhs: Number) {
        let mut x = self;
        x -= rhs;
    }
}
impl Sub<Number> for Number {
    type Output = Self;

    fn sub(self, rhs: Number) -> Self::Output {
        self + -rhs
    }
}
impl Sub<usize> for Number {
    type Output = Self;

    fn sub(self, rhs: usize) -> Self::Output {
        let rhs = Number::from_usize(self.base, rhs);
        self + -rhs
    }
}
impl Sub<isize> for Number {
    type Output = Self;

    fn sub(self, rhs: isize) -> Self::Output {
        let rhs = Number::from_isize(self.base, rhs);
        self + -rhs
    }
}

impl MulAssign<Number> for &mut Number {
    fn mul_assign(&mut self, rhs: Number) {
        self.set_sign_for_mul_div(rhs.sign);
        self.power += rhs.power;
        // TODO There's room for optimization to reduce allocations, here
        // Could truncate & use self instead of a new number, for instance
        let output = rhs.into_iter()
            .map(|(digit, power)| self.mul_digit(digit, power))
            .fold(
                Number::from_usize(self.base, 0),
                |mut a, b| {
                    a.add_digits_from_number(b, true);
                    a
                }
            );
            // TODO Sum
        self.digits = output.digits;
    }
}
impl Mul<Number> for &mut Number {
    type Output = Self;

    fn mul(mut self, rhs: Number) -> Self::Output {
        self *= rhs;
        self
    }
}
impl MulAssign<Number> for Number {
    fn mul_assign(&mut self, rhs: Number) {
        let mut x = self;
        x *= rhs;
    }
}
impl Mul<Number> for Number {
    type Output = Self;

    fn mul(mut self, rhs: Number) -> Self::Output {
        self *= rhs;
        self
    }
}
impl MulAssign<usize> for Number {
    fn mul_assign(&mut self, rhs: usize) {
        let rhs = Number::from_usize(self.base, rhs);
        let mut x = self;
        x *= rhs;
    }
}
impl MulAssign<isize> for Number {
    fn mul_assign(&mut self, rhs: isize) {
        let rhs = Number::from_isize(self.base, rhs);
        let mut x = self;
        x *= rhs;
    }
}
impl Mul<usize> for Number {
    type Output = Self;

    fn mul(self, rhs: usize) -> Self::Output {
        let rhs = Number::from_usize(self.base, rhs);
        self * rhs
    }
}
impl Mul<isize> for Number {
    type Output = Self;

    fn mul(self, rhs: isize) -> Self::Output {
        let rhs = Number::from_isize(self.base, rhs);
        self * rhs
    }
}

impl ShrAssign<usize> for Number {
    fn shr_assign(&mut self, rhs: usize) {
        self.power -= isize::try_from(rhs).expect("Failed to convert usize into isize during right shift.");
    }
}
impl ShrAssign<isize> for Number {
    fn shr_assign(&mut self, rhs: isize) {
        self.power -= rhs
    }
}
impl Shr<usize> for Number {
    type Output = Self;

    fn shr(mut self, rhs: usize) -> Self::Output {
        self.power -= isize::try_from(rhs).expect("Failed to convert usize into isize during right shift.");
        self
    }
}
impl Shr<isize> for Number {
    type Output = Self;

    fn shr(mut self, rhs: isize) -> Self::Output {
        self.power -= rhs;
        self
    }
}

impl ShlAssign<usize> for Number {
    fn shl_assign(&mut self, rhs: usize) {
        self.power -= isize::try_from(rhs).expect("Failed to convert usize into isize during left shift.");
    }
}
impl ShlAssign<isize> for Number {
    fn shl_assign(&mut self, rhs: isize) {        
        self.power += rhs;
    }
}
impl Shl<usize> for Number {
    type Output = Self;

    fn shl(mut self, rhs: usize) -> Self::Output {
        self.power += isize::try_from(rhs).expect("Failed to convert usize into isize during left shift.");
        self
    }
}
impl Shl<isize> for Number {
    type Output = Self;

    fn shl(mut self, rhs: isize) -> Self::Output {
        self.power += rhs;
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
        let mut n = Number::new(10);
        n.push_high(5);
        n.push_high(1);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(1, 5));
    }

    #[test]
    fn push_low_puts_digit_on_right() {
        let mut n = Number::new(10);
        n.push_low(1);
        n.push_low(5);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(1, 5));
    }

    #[test]
    fn pop_high_takes_digits_from_right() {
        let mut n = Number::new(10);
        n.push_high(5);
        n.push_high(1);
        assert_eq!(n.pop_high(), Some(1));
        assert_eq!(n.pop_high(), Some(5));
        assert_eq!(n.pop_high(), None);
    }

    #[test]
    fn pop_low_takes_digits_from_left() {
        let mut n = Number::new(10);
        n.push_low(1);
        n.push_low(5);
        assert_eq!(n.pop_low(), Some(5));
        assert_eq!(n.pop_low(), Some(1));
        assert_eq!(n.pop_low(), None);
    }

    #[test]
    fn push_high_and_pop_high_are_inverse() {
        let mut n = Number::new(10);
        n.push_high(5);
        n.push_high(1);
        assert_eq!(n.pop_high(), Some(1));
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(5));
    }

    #[test]
    fn push_low_and_pop_low_are_inverse() {
        let mut n = Number::new(10);
        n.push_low(5);
        n.push_low(1);
        assert_eq!(n.pop_low(), Some(1));
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(5));
    }

    #[test]
    fn pushing_increases_digits() {
        let mut n = Number::new(10);
        n.push_high(5);
        assert_eq!(n.digits(), 1);
        n.push_low(1);
        assert_eq!(n.digits(), 2);
    }

    #[test]
    fn popping_reduces_digits() {
        let mut n = Number::new(10);
        n.push_high(5);
        n.push_low(1);
        n.pop_high();
        assert_eq!(n.digits(), 1);
        n.pop_low();
        assert_eq!(n.digits(), 0);
    }

    #[test]
    fn alternating_pushing_high_and_low() {
        let mut n = Number::new(10);
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
        let mut n = Number::new(10);
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
        let mut n = Number::new(10);
        for i in 1..=9 {
            n.push_high(i);
        }
        for i in 0..8 {
            assert_eq!(n.get(i), Some((i+1) as Digit));
        }
    }

    #[test]
    fn set_alters_correct_digit() {
        let mut n = Number::new(10);
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
        let mut n = Number::new(10);
        for i in 0..9 {
            n.push_high(i);
        }
        n.set(9, 9);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(9, 8, 7, 6, 5, 4, 3, 2, 1, 0));
    }

    /// Arithmetic

    #[test]
    fn shift_left_increases_power() {
        let mut n = Number::new(10);
        n = n << 1isize;
        assert_eq!(n.power(), 1);

        let mut n = Number::new(10);
        n <<= 1isize;
        assert_eq!(n.power(), 1);
    }

    #[test]
    fn shift_right_decreases_power() {
        let mut n = Number::new(10);
        n = n >> 1isize;
        assert_eq!(n.power(), -1);
    }

    #[test]
    fn complement() {
        let mut n = Number::from_isize(10, 123);
        n.complement();
        assert_eq!(n.as_usize(), 877);
    }

    #[test]
    fn complement_of_1_is_highest_digit() {

        let mut n = Number::from_isize(10, 1);
        n.complement();
        assert_eq!(n.as_usize(), 9);
    }

    #[test]
    fn complement_of_zero_is_zero() {
        let mut n = Number::from_isize(10, 0);
        n.complement();
        assert_eq!(n.as_usize(), 0);
    }

    #[test]
    fn complement_with_zero_digit() {
        let mut n = Number::from_isize(10, 1203);
        n.complement();
        assert_eq!(n.as_usize(), 8797);
    }

    #[test]
    fn complement_with_many_zeros() {
        let mut n = Number::from_isize(10, 1200003);
        n.complement();
        assert_eq!(n.as_usize(), 8799997);
    }

    #[test]
    fn complement_with_low_order_zeroes() {
        let mut n = Number::from_isize(10, 101000);
        n.complement();
        assert_eq!(n.as_usize(), 899000);
    }

    #[test]
    fn add_positive_single_digit_number_to_many_digit_positive_number() {
        let mut n = Number::from_usize(10, 100);
        n = n + 1isize;
        assert_eq!(n.as_usize(), 101);
    }

    #[test]
    fn add_negative_single_digit_number_to_many_digit_positive_number() {
        let mut n = Number::from_usize(10, 100);
        n = n + -1isize;
        assert_eq!(n.as_usize(), 99);
    }

    #[test]
    fn add_negative_single_digit_number_positive_single_digit_number() {
        let mut n = Number::from_usize(10, 1);
        n = n + -1isize;
        assert_eq!(n.as_usize(), 0);
    }

    #[test]
    fn add_negative_single_digit_number_negative_single_digit_number() {
        let mut n = Number::from_isize(10, -1);
        n = n + -1isize;
        assert_eq!(n.as_isize(), -2);
    }

    #[test]
    fn add_to_negative_number_with_change_of_sign() {
        let mut n = Number::from_isize(10, -9);
        n = n + 10isize;
        assert_eq!(n.as_isize(), 1)
    }
    
    #[test]
    fn add_to_positive_number_with_change_of_sign() {
        let mut n = Number::from_isize(10, 9);
        n = n + -10isize;
        assert_eq!(n.as_isize(), -1)
    }

    #[test]
    fn multiply_single_digits() {
        let n = Number::from_usize(10, 5);
        let m = Number::from_usize(10, 3);
        let x = m * n;
        assert_eq!(x.as_isize(), 15);
    }

    #[test]
    fn multiply_many_digits_with_simple_values() {
        let n = Number::from_usize(10, 100);
        let m = Number::from_usize(10, 100);
        let x = m * n;
        assert_eq!(x.as_isize(), 10000);
    }

    #[test]
    fn multiply_many_digits_with_complicated_values() {
        // "Complicated" used here because this example has more complexity,
        // but I didn't want to cannote sqrt(-1)
        let n = Number::from_usize(10, 123);
        let m = Number::from_usize(10, 456);
        let x = m * n;
        assert_eq!(x.as_isize(), 56088);
    }

    #[test]
    fn multiply_by_zero() {
        let n = Number::from_usize(10, 100);
        let m = Number::from_usize(10, 0);
        let x = m * n;
        assert_eq!(x.as_isize(), 0);
    }

    #[test]
    fn multiply_positive_by_negative_one() {
        let base = 10;
        let a = Number::from_isize(base, 100);
        let b = Number::from_isize(base, -1);
        let x = a * b;
        assert_eq!(x.as_isize(), -100); 
    }

    #[test]
    fn multply_negative_by_negative_one() {
        let base = 10;
        let a = Number::from_isize(base, -100);
        let b = Number::from_isize(base, -1);
        let x = a * b;
        assert_eq!(x.as_isize(), 100); 
    }

    /// Conversion

    #[test]
    fn conversion_from_usize() {
        let n = Number::from_isize(10, 123);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(1, 2, 3));
    }

    #[test]
    fn conversion_from_usize_max_does_not_overflow() {
        let n = Number::from_usize(10, usize::MAX);
        n.as_usize();
    }

    #[test]
    fn conversion_from_isize_max_does_not_overflow() {
        let n = Number::from_isize(10, isize::MAX);
        n.as_isize();
    }

    #[test]
    fn conversion_from_isize_min_does_not_overflow() {
        let n = Number::from_isize(10, isize::MIN);
        n.as_isize();
    }

    #[test]
    fn conversion_from_positive_isize() {
        let n = Number::from_isize(10, 123);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(1, 2, 3));
        assert!(n.positive());
    }

    #[test]
    fn conversion_from_negative_isize() {
        let n = Number::from_isize(10, -123);
        assert_eq!(n.digit_iter().rev().collect::<Vec<_>>(), vec!(1, 2, 3));
        assert!(n.negative());
    }

    #[test]
    fn iter_digits_and_powers() {
        let n = Number::from_isize(10, 123);
        assert_eq!(n.digit_and_power_iter().collect::<Vec<_>>(), vec!((3, 0), (2, 1), (1, 2)));
    }

    #[test]
    fn conversion_to_isize_positive() {
        let n = Number::from_isize(10, 123);
        assert_eq!(n.as_isize(), 123);
    }

    #[test]
    fn conversion_to_isize_negative() {
        let n = Number::from_isize(10, -123);
        assert_eq!(n.as_isize(), -123);
    }

}

#[cfg(test)]
pub mod property_tests {
    use super::*;
    use proptest::prelude::*;

    proptest!(
        #[test]
        fn from_usize_and_as_usize_are_inverse((base, number) in (arbitrary_base(), any::<usize>())) {
            let n = Number::from_usize(base, number);
            prop_assert!(n.as_usize() == number);
        }

        #[test]
        fn from_isize_and_as_isize_are_inverse((base, number) in (arbitrary_base(), any::<isize>())) {
            let n = Number::from_isize(base, number);
            prop_assert!(n.as_isize() == number);
        }

        #[test]
        fn arbitrary_complements((base, number) in (arbitrary_base(), any::<usize>())) {
            let mut n = Number::from_usize(base, number);
            n.complement();
            let digits = ((number as f64).log(base as f64).floor() + 1.0) as u32;
            let expected = (base as u128).pow(digits) - (number as u128);
            // No guarentee that the complement of a usize will fit in a usize
            prop_assert!(n.as_u128() == expected)
        }

        #[test]
        fn arbitrary_integer_addition((base, a, b) in (arbitrary_base(), any::<isize>(), any::<isize>())) {
            let expected = (a as i128) + (b as i128);
            let mut a = Number::from_isize(base, a);
            let b = Number::from_isize(base, b);
            a = a + b;
            prop_assert!(a.as_i128() == expected);
        }

        #[test]
        fn any_integer_plus_its_negative_is_zero(number in arbitray_integer()) {
            let mut a = number;
            let mut b = a.clone();
            b.negate();
            a = a + b;
            prop_assert!(a.as_isize() == 0);
        }

        #[test]
        fn sum_of_many_integers((base, numbers) in (arbitrary_base(), proptest::collection::vec(any::<isize>(), 3..10))) {
            let mut native_accumulator = 0i128;
            let mut number_accumulator = Number::from_usize(base, 0);
            for number in numbers {
                native_accumulator += number as i128;
                number_accumulator = number_accumulator + Number::from_isize(base, number);
                prop_assert!(number_accumulator.as_i128() == native_accumulator);
            }
        }

    
        #[test]
        fn arbitrary_integer_subtraction((base, a, b) in (arbitrary_base(), any::<isize>(), any::<isize>())) {
            let expected = (a as i128) - (b as i128);
            let mut a = Number::from_isize(base, a);
            let b = Number::from_isize(base, b);
            a = a - b;
            prop_assert!(a.as_i128() == expected);
        }

        #[test]
        fn difference_of_many_integers((base, numbers) in (arbitrary_base(), proptest::collection::vec(any::<isize>(), 3..10))) {
            let mut native_accumulator = 0i128;
            let mut number_accumulator = Number::from_usize(base, 0);
            for number in numbers {
                native_accumulator -= number as i128;
                number_accumulator = number_accumulator - Number::from_isize(base, number);
                prop_assert!(number_accumulator.as_i128() == native_accumulator);
            }
        }

        #[test]
        fn arbitrary_integer_multiplication((base, a, b) in (arbitrary_base(), any::<isize>(), any::<isize>())) {
            prop_assume!(a == 0 || i128::MAX / i128::abs(a as i128) > b as i128);
            let expected = (a as i128) * (b as i128);
            let a = Number::from_isize(base, a);
            let b = Number::from_isize(base, b);
            let observed = a * b;
            prop_assert!(observed.as_i128() == expected);
        }

        #[test]
        fn product_of_many_integers((base, numbers) in (arbitrary_base(), proptest::collection::vec(any::<i8>(), 3..10))) {
            // TODO make a strategy for testing larger integers - currently using i8s to avoid
            // overflow
            let mut native_accumulator = 1i128;
            for number in numbers.iter() {
                let x = native_accumulator.checked_mul(*number as i128);
                prop_assume!(!x.is_none()); // Don't overflow
                native_accumulator = x.unwrap();
            }

            let mut native_accumulator = 1i128;
            let mut number_accumulator = Number::from_usize(base, 1);
            for number in numbers {
                number_accumulator = number_accumulator * Number::from_isize(base, number as isize);
                native_accumulator *= number as i128;
                prop_assert!(number_accumulator.as_i128() == native_accumulator);
            }
        }

    );

    /// Strategies

    fn arbitrary_base() -> impl Strategy<Value=usize> {
        any::<u8>()
        .prop_filter(
            "Base must be > 1",
            |base| *base > 1
        )
        .prop_map(|base| base as usize)
    }

    fn arbitray_positive_integer() -> impl Strategy<Value=Number> {
        (arbitrary_base(), any::<usize>())
        .prop_map(|(base, number)| Number::from_usize(base, number))
    }

    fn arbitray_integer() -> impl Strategy<Value=Number> {
        (arbitrary_base(), any::<isize>())
        .prop_map(|(base, number)| Number::from_isize(base, number))
    }
}
