use prusti_contracts::*;

#[ensures((old(*x) == 10) ==> *x == 9)]
fn sub_one(mut x: &mut i32) {
    if *x > 0 {
        *x -= 1
    }
    // reassign x here
}

#[ensures(result == 9)]
fn client() -> i32 {
    let mut x = &mut 10;
    // *x = 9;
    sub_one(x);
    *x
}

fn main() {}
