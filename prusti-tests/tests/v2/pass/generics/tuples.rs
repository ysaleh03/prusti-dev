use prusti_contracts::*;

#[pure]
fn fst<S, T, U>(tpl: (S, T, U)) -> S {
    tpl.0
}

#[pure]
fn foo(tpl: (i32, i32, i32)) -> i32 {
    fst(tpl)
}

#[pure]
fn bar(tpl: ((i32, i32, i32), i32, i32)) -> (i32, i32, i32) {
    fst(tpl)
}

#[pure]
#[ensures(result == foo(bar(tpl)))]
fn foobar(tpl: ((i32, i32, i32), i32, i32)) -> i32 {
    fst(fst(tpl))
}

fn main() {}
