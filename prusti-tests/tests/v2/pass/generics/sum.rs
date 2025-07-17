use prusti_contracts::*;

#[requires(n > 0)]
#[requires(n*(n-1)/2 <= 2147483647 - n)]
fn sum(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        n + sum(n - 1)
    }
}

fn main() {}
