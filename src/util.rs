use std::cmp::{min,max};
use std::ops::Range;

use crate::Pair;

pub fn normalize_pair(pair: Pair) -> Pair {
    return (min(pair.0, pair.1), max(pair.0, pair.1))
}

/// Returns the index of a given pair in a precomputation table
pub fn pair_index(pair: Pair, base: u32) -> usize {
    let pair = normalize_pair(pair);
    let base = base as usize;
    let lower = pair.0 as usize;
    let upper = pair.1 as usize;

    ((base - lower + 1)..(base+1)).sum::<usize>() + (upper - lower)
}

fn carry_digits(computed: usize, base: usize) -> Pair {
    let carry = computed / base;
    let result = computed - (carry * base);
    (result as u8, carry as u8)
}

/// Iterator used to build precomputation tables for addition and subtraction.
pub struct ArithmeticPrecomputation {
    base: usize,
    lower: Range<usize>,
    upper: Range<usize>,
    current_lower: usize
}

impl ArithmeticPrecomputation {
    pub fn new(base: u32) -> Self {
        let base = base as usize;
        let mut lower = 0..base;
        let upper = 0..base;
        let current_lower = lower.next().unwrap();
        Self { base, lower, upper, current_lower }
    }

}

// Iterator which calculates each digit required to represent a native integer
// as 
pub struct ConversionFromNativeInteger {
    integer: usize,
    base: usize
}

// Iterator which converts a number from any base to any other base
pub struct BaseConversion {
}

impl Iterator for ArithmeticPrecomputation {
    type Item = (Pair, Pair);

    fn next(&mut self) -> Option<Self::Item> {
        let mut upper = self.upper.next();
        if upper.is_none() {
            self.current_lower = self.lower.next()?;
            self.upper = self.current_lower..self.base;
            upper = self.upper.next();
        }
        let upper = upper.unwrap();
        let addition = self.current_lower + upper;
        let multiplication = self.current_lower * upper;
        Some((
            carry_digits(addition, self.base),
            carry_digits(multiplication, self.base)
        ))
    }
}

#[cfg(test)]
pub mod test {
    use super::*;

    #[test]
    fn generates_valid_precomputation_tables() {
        assert_eq!(
            ArithmeticPrecomputation::new(3).collect::<Vec<(Pair, Pair)>>(),
            vec!(
                // 0 0
                ((0, 0), (0, 0)),
                // 0 1
                ((1, 0), (0, 0)),
                // 0 2
                ((2, 0), (0, 0)),
               
                // 1 1
                ((2, 0), (1, 0)),
                // 1 2
                ((0, 1), (2, 0)),

                // 2 2
                ((1, 1), (1, 1)),
            )
        );
    }

}
