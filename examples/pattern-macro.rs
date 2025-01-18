
use trees::*;

fn main() {
    let tree = tree! {
        "head node";
        "child 1";
        "child 2";
        #[
            "subtree head node";
            "subtree child 1";
            "subtree child 2";
        ];
    };

    let pattern = pattern! {
        "head node";
        @first_child;
        ..
    };

    let matches = tree.does_match_pattern(&pattern);
    println!("Does \"{pattern}\" match? -> {matches:?}");

    let pattern2 = pattern! {
        "this won't match";
        ..
    };

    let matches2 = tree.does_match_pattern(&pattern2);
    println!("Does \"{pattern2}\" match? -> {matches2:?}");
}