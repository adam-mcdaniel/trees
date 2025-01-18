use std::fmt::Display;
use trees::*;

// The atoms of the expression tree for a simple calculator
#[derive(Clone, Debug, PartialEq)]
enum Atom {
    Add,
    Mul,
    Sub,
    Div,
    Num(i32),
}

impl Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Atom::*;
        match self {
            Add => write!(f, "+"),
            Mul => write!(f, "*"),
            Sub => write!(f, "-"),
            Div => write!(f, "/"),
            Num(n) => write!(f, "{}", n),
        }
    }
}

type Expr = Tree<Atom>;

fn commutative(expr: Expr) -> Expr {
    use Atom::*;
    // Apply the commutative property for Add and Mul operations
    let expr = rewrite!(
        expr,
        // Bind the matched subtree to `this` in the pattern
        this = pattern![
            // If the operation (head node) is Add or Mul
            @op if matches!(op, Add | Mul);
            // Bind the first child node to @a
            @a;
            // Bind the second child node to @b
            @b;
        ] => {
            // Print the matched subtree
            println!("Matched subtree: {}", this);
            // Return a new tree with the head node and children swapped
            tree![
                op.clone();
                b.clone();
                a.clone();
            ]
        // List the bound variables we want to use in the replacement expression.
        // To capture the bound variables as Trees, we use the `@` sigil.
        // To just grab their node value (Atom), we just use the plain identifier.
        } using op, @a, @b
        // ^ grabs the node value of `op`, and the `@a` and `@b` subtrees.
    );

    expr
}


fn main() {
    use Atom::*;
    // Create a tree representing the expression: 1 + (2 - 3) * 4
    let expr = tree![
        Add;
        Num(1);
        #[
            Mul;
            #[
                Sub;
                Num(2);
                Num(3);
            ];
            Num(4);
        ]
    ];

    // Apply the commutative property to the expression
    println!("Before commutative property: {}", expr);
    let expr = commutative(expr);
    println!("After commutative property: {}", expr);
}
