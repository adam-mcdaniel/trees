use trees::*;
use std::path::Path;
use std::fmt::{Display, Formatter, Result as FmtResult};

#[derive(Debug, Clone, Copy, PartialEq)]
enum ExprType {
    Add,
    Sub,
    Mul,
    Div,
    Num(i32),
}

impl Display for ExprType {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            ExprType::Add => write!(f, "+"),
            ExprType::Sub => write!(f, "-"),
            ExprType::Mul => write!(f, "*"),
            ExprType::Div => write!(f, "/"),
            ExprType::Num(n) => write!(f, "{}", n),
        }
    }
}
type Expr = Tree<ExprType>;

fn precedence(op: ExprType) -> i32 {
    match op {
        ExprType::Add | ExprType::Sub => 1,
        ExprType::Mul | ExprType::Div => 2,
        _ => 0,
    }
}

fn parse_expr(s: &str) -> Expr {
    use ExprType::*;
    // First, convert infix to postfix
    let mut postfix = vec![];
    let mut stack = vec![];
    let mut current_n = None;
    for c in s.chars() {
        if !c.is_digit(10) {
            if let Some(n) = current_n {
                postfix.push(ExprType::Num(n));
            }
            current_n = None;
        }
        match c {
            '0'..='9' => {
                // postfix.push(ExprType::Num(c.to_digit(10).unwrap() as i32))
                // current_n = current_n * 10 + c.to_digit(10).unwrap() as i32;
                current_n = Some(current_n.unwrap_or(0) * 10 + c.to_digit(10).unwrap() as i32);
            }
            '+' | '-' | '*' | '/' => {
                let op = match c {
                    '+' => ExprType::Add,
                    '-' => ExprType::Sub,
                    '*' => ExprType::Mul,
                    '/' => ExprType::Div,
                    _ => unreachable!(),
                };
                while let Some(&top) = stack.last() {
                    if top == ExprType::Num(0) {
                        break;
                    }
                    if precedence(top) >= precedence(op) {
                        postfix.push(stack.pop().unwrap());
                    } else {
                        break;
                    }
                }
                stack.push(op);
            }
            _ => {}
        }
    }
    if let Some(n) = current_n {
        postfix.push(ExprType::Num(n));
    }

    while let Some(op) = stack.pop() {
        postfix.push(op);
    }

    // Then, convert postfix to tree
    let mut stack = vec![];
    for token in postfix {
        match token {
            ExprType::Num(n) => stack.push(tree![Num(n)]),
            ExprType::Add | ExprType::Sub | ExprType::Mul | ExprType::Div => {
                let right = stack.pop().unwrap();
                let left = stack.pop().unwrap();
                stack.push(tree![token; left; right]);
            }
        }
    }

    stack.pop().unwrap()
}

/// Reduce the expression by applying the given operator.
fn reduce(expr: Expr, op: ExprType) -> Expr {
    use ExprType::*;
    let pat = pattern![
        op; // Make sure the operator is the same as the one we're looking for (`op`).
        @x if matches!(x, Num(_)); // Make sure the first child is a number.
        @y if matches!(y, Num(_)); // Make sure the second child is a number.
    ];
    // Rewrite the expression tree according to the given pattern.
    expr.graphviz_matches(&pat).save_png(&Path::new(&format!("./math-{}.png", expr.size())));

    let result = rewrite!(
        expr,
        // Our pattern is the operator, with two children that are numbers.
        // (This is a macro to make it easier to write patterns.)
        pat => {
            // Based on the operator, do the correct arithmetic operation on
            // the two numbers.
            match op {
                Add => Num(x + y),
                Sub => Num(x - y),
                Mul => Num(x * y),
                Div => Num(x / y),
                _ => unreachable!(),
            }
        } * 1, using Num(x)=x, // <- This just gets the values of x and y
                     Num(y)=y  //    from the pattern.
    );
    // Save the intermediate result to a PNG file.
    // result.save_png(format!("./math-{}.png", result.size())).unwrap();
    // Return the rewritten expression.
    result
}

fn main() {
    use ExprType::*;
    
    // Parse the math expression into a tree of operators and numbers.
    let mut tree = parse_expr("2 * 3 * 4 + 5 * 6 * 7");
    tree.save_png("./math.png").unwrap();

    // While the tree has more than one level of depth, reduce it.
    while tree.depth() > 1 {
        // Reduce the tree by applying the four operators in order of precedence.
        tree = reduce(tree, Add);
        tree = reduce(tree, Sub);
        tree = reduce(tree, Mul);
        tree = reduce(tree, Div);
    }
    // Print the final result.
    println!("Result: {}", tree);
}
