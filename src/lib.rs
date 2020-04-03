
pub fn foo() -> i32 {
    42
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn it_doesnt_work() {
        assert_eq!(5, foo());
    }
}
