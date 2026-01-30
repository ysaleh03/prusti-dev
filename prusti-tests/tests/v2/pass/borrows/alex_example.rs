use prusti_contracts::*;

// example from 2025-10-08 meeting

// we know the value of p.1 does not change
#[after_expiry(sum(*p) == before_expiry(*result) + old(p.1))]
fn foo<'a>(p: &'a mut (u32, u32)) -> &'a mut u32 {
    p.0 += 10;
    &mut p.0
}

#[pure]
fn sum(p: (u32, u32)) -> u32 {
    p.0 + p.1
}

fn client() {
    let mut p = (10, 20);
    let result = foo(&mut p);
    // we can no longer access p.1,
    // but we *can* change the value of result
    *result += 10;
    // borrow expires
    assert!(sum(p) == 30 + p.1);
}

fn main() {}
