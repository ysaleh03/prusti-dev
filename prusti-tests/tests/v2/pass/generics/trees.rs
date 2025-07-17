use prusti_contracts::*;

enum BinarySearchTree<T> {
    Nil,
    Node(T, Box<BinarySearchTree<T>>, Box<BinarySearchTree<T>>),
}

#[trusted]
#[pure]
fn is_some_pure<T>(opt: Option<T>) -> bool {
    opt.is_some()
}

#[pure]
fn is_none_pure<T>(opt: Option<T>) -> bool {
    !is_some_pure(opt)
}

#[trusted]
#[pure]
#[requires(is_some_pure(opt))]
fn unwrap_pure<T>(opt: Option<T>) -> T {
    opt.unwrap()
}

impl<T> BinarySearchTree<T> {
    fn nil() -> Self {
        BinarySearchTree::Nil
    }

    fn new(value: T, left: Self, right: Self) -> Self {
        BinarySearchTree::Node(value, Box::new(left), Box::new(right))
    }

    #[pure]
    // #[ensures(self.is_node() == is_some_pure(result))]
    fn value(self) -> Option<T> {
        match self {
            BinarySearchTree::Nil => None,
            BinarySearchTree::Node(value, _, _) => Some(value),
        }
    }

    #[pure]
    fn left(self) -> Option<Self> {
        match self {
            BinarySearchTree::Nil => None,
            BinarySearchTree::Node(_, left, _) => Some(*left),
        }
    }

    #[pure]
    fn right(self) -> Option<Self> {
        match self {
            BinarySearchTree::Nil => None,
            BinarySearchTree::Node(_, _, right) => Some(*right),
        }
    }

    #[pure]
    fn is_node(self) -> bool {
        match self {
            BinarySearchTree::Nil => false,
            BinarySearchTree::Node(..) => true,
        }
    }

    #[pure]
    fn is_nil(self) -> bool {
        !self.is_node()
    }
}

impl BinarySearchTree<i32> {
    #[ensures(result.is_node())]
    // #[ensures(if self.is_nil() {unwrap_pure(result.value()) == new_value} else {true} )]
    fn insert(self, new_value: i32) -> Self {
        match self {
            BinarySearchTree::Nil => BinarySearchTree::Node(
                new_value,
                Box::new(BinarySearchTree::nil()),
                Box::new(BinarySearchTree::nil()),
            ),
            BinarySearchTree::Node(value, left, right) => {
                if new_value < value {
                    left.insert(new_value)
                } else {
                    right.insert(new_value)
                }
            }
        }
    }

    fn dfs(self, target: i32) -> bool {
        match self {
            BinarySearchTree::Nil => false,
            BinarySearchTree::Node(value, left, right) => {
                if value == target {
                    return true;
                }
                if left.dfs(target) {
                    true
                } else {
                    right.dfs(target)
                }
            }
        }
    }
}

fn main() {
    let left_child = BinarySearchTree::new(10, BinarySearchTree::nil(), BinarySearchTree::nil());
    let right_child = BinarySearchTree::new(20, BinarySearchTree::nil(), BinarySearchTree::nil());
    let tree = BinarySearchTree::new(15, left_child, right_child);
    let target = 20;
}
