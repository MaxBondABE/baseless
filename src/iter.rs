use crate::{Number, Digit};

pub struct BorrowedNumberIter<'number> {
    number: &'number Number<'number>,
    digit: usize
}

impl<'number> BorrowedNumberIter<'number> {
    pub fn new(number: &'number Number) -> Self {
        Self {
            number,
            digit: number.digits()
        }
    }
}
impl Iterator for BorrowedNumberIter<'_> {
    type Item = Digit;
    fn next(&mut self) -> Option<Self::Item> {
        if self.digit == 0 {
            return None;
        }
        self.digit -= 1;
        self.number.get(self.digit)
    }
}
