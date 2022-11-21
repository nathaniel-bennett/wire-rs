// #![feature(array_try_from_fn)]


mod reader;

#[derive(Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum WireError {
    InsufficientBytes,
    ExtraBytes,
    InvalidData(String),
    Internal,
}

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
