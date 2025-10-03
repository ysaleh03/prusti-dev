use prusti_contracts::*;

#[ensures(*x == 19)]
fn f<'a: 'b, 'b: 'a>(mut x: &'a mut u32, y: &'b mut u32) {
    *x = 17;
    *x += 2;
    let x = &mut *y;
}

#[ensures(result == 19)]
fn client() -> u32 {
    let mut x = 4;
    let mut y = 10;
    f(&mut x, &mut y);
    x
}

fn main() {}
