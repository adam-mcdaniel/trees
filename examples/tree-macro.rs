
use trees::{tree, Tree};

fn main() {
    let tree = tree! {
        "head-node";
        "child-1";
        "child-2";
        #[
            "subtree-head-node";
            "subtree-child-1";
            "subtree-child-2";
        ];
    };

    println!("{}", tree);
}