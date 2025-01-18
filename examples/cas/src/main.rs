use trees::*;
use std::collections::{VecDeque, BTreeMap, BTreeSet};
use std::iter;
use std::sync::Mutex;
use std::hash::Hash;
use std::io::Write;
use std::path::Path;
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::f64::consts::PI;
use tracing::*;
use clap::{Parser, ValueEnum};
use lazy_static::lazy_static;

const INTRO: &str = r#"Welcome to...
  ___      _                 _     
 / _ \    | |               ( )    
/ /_\ \ __| | __ _ _ __ ___ |/ ___ 
|  _  |/ _` |/ _` | '_ ` _ \  / __|
| | | | (_| | (_| | | | | | | \__ \
\_| |_/\__,_|\__,_|_| |_| |_| |___/
                                   
                                   
 _____    ___    _____             
/  __ \  / _ \  /  ___|            
| /  \/ / /_\ \ \ `--.             
| |     |  _  |  `--. \            
| \__/\_| | | |_/\__/ /            
 \____(_)_| |_(_)____(_)           
                                   
                                   "#;


#[derive(Parser, Debug, Default, Clone)]
#[command(version, about, long_about = None)]
pub struct Config {
    input: String,

    /// The number of iterations to run the optimizer for
    /// before giving up when the expression is not improving
    #[arg(short, long, default_value = "1000")]
    bail_after_no_improvement_for: usize,
    /// The maximum number of iterations to run the optimizer for.
    #[arg(short, long, default_value = "1000")]
    max_iterations: usize,

    /// The number of iterations to run before ordering the expressions
    /// by their fitness in the queue.
    #[arg(short, long, default_value = "50")]
    fitness_reevaluate_after: usize,

    /// Whether to check the solution after the optimizer has finished
    /// If the -v flag is provided, the solution will be checked
    #[arg(short, long)]
    verify: bool,

    /// How to select the roots for quadratic and cubic equations
    /// The options are: "random", "first", "last", "middle"
    /// The default is "random"
    #[arg(value_enum)]
    root_selection: Option<RootSelection>,

    /// Render equation images
    /// If the --render flag is provided, the equations will be rendered
    #[arg(long)]
    render: bool,
}

#[derive(Default, Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum RootSelection {
    Random,
    First,
    Last,
    #[default]
    Middle,
}

lazy_static! {
    static ref CONFIG: Mutex<Config> = Mutex::new(Config::default());
}

fn select_root(roots: &[f64]) -> f64 {
    use rand::seq::SliceRandom;
    let root_selection = CONFIG.lock().unwrap().root_selection;
    match root_selection.unwrap_or_default() {
        RootSelection::Random => *roots.choose(&mut rand::thread_rng()).unwrap(),
        RootSelection::First => roots[0],
        RootSelection::Last => roots[roots.len() - 1],
        RootSelection::Middle => roots[roots.len() / 2],
    }
}

pub const EPSILON: f64 = 1e-6;

#[derive(Debug, Clone, PartialOrd)]
pub enum Atom {
    Constant(f64),
    Var(String),
    
    Add,
    Sub,
    Mul,
    Div,
    Pow,
    Neg,

    Equals,
}

impl Ord for Atom {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap_or(std::cmp::Ordering::Equal)
    }
}
impl Eq for Atom {}

impl PartialEq for Atom {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Constant(a), Self::Constant(b)) => (a - b).abs() < EPSILON,
            (Self::Var(a), Self::Var(b)) => a == b,
            (Self::Add, Self::Add)
            | (Self::Sub, Self::Sub)
            | (Self::Mul, Self::Mul)
            | (Self::Div, Self::Div)
            | (Self::Pow, Self::Pow)
            | (Self::Neg, Self::Neg)
            | (Self::Equals, Self::Equals) => true,
            _ => false,
        }
    }
}

impl Hash for Atom {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::Constant(c) => c.to_bits().hash(state),
            Self::Var(v) => v.hash(state),
            Self::Add => 0.hash(state),
            Self::Sub => 1.hash(state),
            Self::Mul => 2.hash(state),
            Self::Div => 3.hash(state),
            Self::Pow => 4.hash(state),
            Self::Neg => 5.hash(state),
            Self::Equals => 6.hash(state),
        }
    }
}

impl Atom {
    fn is_binary_operator(&self) -> bool {
        match self {
            Self::Add | Self::Sub | Self::Mul | Self::Div | Self::Pow => true,
            _ => false,
        }
    }

    fn is_reversible_binary_operator(&self) -> bool {
        match self {
            Self::Add | Self::Sub | Self::Mul | Self::Div => true,
            _ => false,
        }
    }

    fn is_unary_operator(&self) -> bool {
        match self {
            Self::Neg => true,
            _ => false,
        }
    }

    fn opposite(&self) -> Self {
        match self {
            Self::Add => Self::Sub,
            Self::Sub => Self::Add,
            Self::Mul => Self::Div,
            Self::Div => Self::Mul,
            _ => unimplemented!()
        }
    }
}

impl Display for Atom {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self {
            Self::Constant(c) => write!(f, "{}", c),
            Self::Var(v) => write!(f, "{}", v),
            Self::Add => write!(f, "+"),
            Self::Sub => write!(f, "-"),
            Self::Mul => write!(f, "*"),
            Self::Div => write!(f, "/"),
            Self::Pow => write!(f, "^"),
            Self::Neg => write!(f, "-"),
            Self::Equals => write!(f, "="),
        }
    }
}

type Expr = Tree<Atom>;

fn is_irreducible(expr: &Expr) -> bool {
    use Atom::*;
    // if matches!(expr.value(), Constant(_)) {
    //     return true;
    // }
    /*
    // Get the unique variables
    let mut vars = BTreeSet::new();

    let mut var_appearances = BTreeMap::new();
    rewrite!(expr, 
        this = pattern![
            @var if matches!(var, Var(_));
        ] => {
            vars.insert(var.clone());
            var_appearances.entry(var.clone()).and_modify(|e| *e += 1).or_insert(1);
            this.clone()
        } using Var(var) = var
    );

    // If there are no variables, then the expression is irreducible
    if vars.is_empty() {
        return true;
    }

    // If the number of variable appearances is greater than 1, then the expression is reducible
    for (_, appearances) in var_appearances {
        if appearances > 1 {
            return false;
        }
    }

    // If the expression is a constant, then it is irreducible
    if matches!(expr.value(), Constant(_)) {
        return true;
    }

    // If the expression is an operator with a variable and a constant, then it is reducible
    if matches!(expr.value(), Add | Sub | Mul | Div | Pow) {
        if matches!(expr[0].value(), Constant(_)) && is_irreducible(&expr[1]) {
            return true;
        }
        if matches!(expr[1].value(), Constant(_)) && is_irreducible(&expr[0]) {
            return true;
        }
    }
    */
    // println!("Checking irreducibility of {:?}", expr);
    // println!("Is binary: {}", expr.is_binary());
    // println!("Length: {}", expr.len());
    // println!("Depth: {}", expr.depth());

    // let result = expr.does_match_pattern(&pattern![
    //     Equals;
    //     @a if is_irreducible(a);
    //     @b if is_irreducible(b);
    // ]) || 
    // expr.does_match_pattern(&pattern![
    //     Equals;
    //     @a if matches!(a, Var(_));
    //     @b if is_irreducible(b);
    // ]) ||
    // expr.does_match_pattern(&pattern![
    //     Equals;
    //     @a if is_irreducible(a);
    //     @b if matches!(b, Var(_));
    // ]);

    match expr.value() {
        Equals => {
            (matches!(expr[0].value(), Var(_)) && is_irreducible(&expr[1]))
                || (is_irreducible(&expr[0]) && matches!(expr[1].value(), Var(_)))
                || is_irreducible(&expr[0]) && is_irreducible(&expr[1])
            /*
            if matches!(expr[0].value(), Var(_)) && matches!(expr[1].value(), Constant(_)) {
                return true;
            }

            if matches!(expr[1].value(), Var(_)) && matches!(expr[0].value(), Constant(_)) {
                return true;
            }

            false
             */
        }
        Mul | Add | Sub | Div => {
            if matches!(expr[0].value(), Constant(_)) && is_irreducible(&expr[1]) {
                return true;
            }
            if matches!(expr[1].value(), Constant(_)) && is_irreducible(&expr[0]) {
                return true;
            }
            false
        }
        Constant(_) => true,
        _ => false,
    }
}

fn constant_folding(mut expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;

    let mut i = 0;
    let mut old_expr = tree![Constant(0.0)];
    while i < 10 && expr != old_expr {
        old_expr = expr.clone();
        i += 1;

        // Fold negatives
        expr = rewrite!(
            expr,
            pattern![
                Neg;
                @a if matches!(a, Constant(_));
            ] => {
                Constant(-a)
            } using Constant(a)=a
        );

        expr = rewrite!(expr, pattern![ Neg; #[Neg;@a] ] => {a.clone()} using @a);
        expr = rewrite!(expr, pattern![ Neg; @a; ] => {
            tree![
                Mul;
                a.clone();
                Constant(-1.0);
            ]
        } using @a);

        expr = subtract_to_sum(expr);
        
        expr = rewrite!(
            expr,
            pattern![
                @op if op.is_binary_operator(), where op: &Atom;
                @a if matches!(a, Constant(_));
                @b if matches!(b, Constant(_));
            ] => {
                Constant(match op {
                    Add => a + b,
                    Sub => a - b,
                    Mul => a * b,
                    Div => a / b,
                    Pow => a.powf(*b),
                    _ => unreachable!(),
                })
            } using op, Constant(a)=a, Constant(b)=b
        );

        expr = rewrite!(expr, pattern![ Mul; @a; @b if *b == Constant(1.0); ] => {a.clone()} using @a);
        expr = rewrite!(expr, pattern![ Mul; @a if *a == Constant(1.0); @b; ] => {b.clone()} using @b);
        expr = rewrite!(expr, pattern![ Div; @a; @b if *b == Constant(1.0); ] => {a.clone()} using @a);
        
        expr = rewrite!(expr, pattern![ Mul; @a; @b if *b == Constant(0.0); ] => {tree![Constant(0.0)]});
        expr = rewrite!(expr, pattern![ Mul; @a if *a == Constant(0.0); @b; ] => {tree![Constant(0.0)]});
        expr = rewrite!(expr, pattern![ Div; @a if *a == Constant(0.0); @b; ] => {tree![Constant(0.0)]});
        expr = rewrite!(expr, this = pattern![
            Mul;
            #[
                Div;
                @a;
                @b;
            ];
            @c
        ] => {
            if b == c {
                a.clone()
            } else {
                this.clone()
            }
        } using @a, @b, @c);
        expr = rewrite!(expr, this = pattern![
            Mul;
            @a;
            #[
                Div;
                @b;
                @c;
            ];
        ] => {
            if a == c {
                b.clone()
            } else {
                this.clone()
            }
        } using @a, @b, @c);
        
        expr = rewrite!(expr, this = pattern![
            Add;
            @a if matches!(a, Constant(_));
            #[
                Add;
                @b if matches!(b, Constant(_));
                @c;
            ];
        ] => {
            tree![
                Add;
                Constant(a + b);
                c.clone();
            ]
        } using Constant(a)=a, Constant(b)=b, @c);
            
        expr = rewrite!(expr, this = pattern![
            Add;
            @a if matches!(a, Constant(_));
            #[
                Add;
                @c;
                @b if matches!(b, Constant(_));
            ];
        ] => {
            tree![
                Add;
                Constant(a + b);
                c.clone();
            ]
        } using Constant(a)=a, Constant(b)=b, @c);

        expr = rewrite!(expr, this = pattern![
            Add;
            #[
                Add;
                @b if matches!(b, Constant(_));
                @c;
            ];
            @a if matches!(a, Constant(_));
        ] => {
            tree![
                Add;
                Constant(a + b);
                c.clone();
            ]
        } using Constant(a)=a, Constant(b)=b, @c);
            
        expr = rewrite!(expr, this = pattern![
            Add;
            #[
                Add;
                @c;
                @b if matches!(b, Constant(_));
            ];
            @a if matches!(a, Constant(_));
        ] => {
            tree![
                Add;
                Constant(a + b);
                c.clone();
            ]
        } using Constant(a)=a, Constant(b)=b, @c);

        expr = rewrite!(expr, this = pattern![
            Mul;
            @a if matches!(a, Constant(_));
            #[
                Mul;
                @b if matches!(b, Constant(_));
                @c;
            ];
        ] => {
            tree![
                Mul;
                Constant(a * b);
                c.clone();
            ]
        } using Constant(a)=a, Constant(b)=b, @c);

        expr = rewrite!(expr, this = pattern![
            Mul;
            @a if matches!(a, Constant(_));
            #[
                Mul;
                @c;
                @b if matches!(b, Constant(_));
            ];
        ] => {
            tree![
                Mul;
                Constant(a * b);
                c.clone();
            ]
        } using Constant(a)=a, Constant(b)=b, @c);

        expr = rewrite!(expr, this = pattern![
            Mul;
            #[
                Mul;
                @b if matches!(b, Constant(_));
                @c;
            ];
            @a if matches!(a, Constant(_));
        ] => {
            tree![
                Mul;
                Constant(a * b);
                c.clone();
            ]
        } using Constant(a)=a, Constant(b)=b, @c);

        expr = rewrite!(expr, this = pattern![
            Mul;
            #[
                Mul;
                @c;
                @b if matches!(b, Constant(_));
            ];
            @a if matches!(a, Constant(_));
        ] => {
            tree![
                Mul;
                Constant(a * b);
                c.clone();
            ]
        } using Constant(a)=a, Constant(b)=b, @c);

        expr = rewrite!(expr, pattern![ Div; @a; @b if matches!(b, Constant(_)); ] => {
            tree![
                Mul;
                a.clone();
                Constant(1.0 / b)
            ]
        } using @a, Constant(b)=b);

        expr = consolidate_muls(expr);
        expr = consolidate_powers(expr);
        expr = eliminate_ones(expr);
        expr = eliminate_zeros(expr);
        expr = combine_like_terms(expr);
        // expr = commutative(rewrite!(
        //     expr,
        //     pattern![
        //         @op if op.is_reversible_binary_operator(), where op: &Atom;
        //         @a;
        //         @b;
        //     ] => {
        //         tree![
        //             op.clone();
        //             commutative(a.clone());
        //             b.clone();
        //         ]
        //     } using op, @a, @b
        // ));
    }

    expr
}


fn balance_to_left_equation(expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;
    let expr = rewrite!(
        expr,
        pattern![
            Equals;
            // Get an expression on the right side of the equation
            @b if matches!(b, Constant(_)) && *b != Constant(0.0);
            // Get an expression on the left side of the equation
            @a;
        ] => {
            // Undo the operation on the left side of the equation
            tree![
                Equals;
                #[
                    Sub;
                    a.clone();
                    b.clone();
                ];
                Constant(0.0);
            ]
        } using @a, @b
    );
    let expr = rewrite!(
        expr,
        pattern![
            Equals;
            // Get an expression on the left side of the equation
            @a;
            // Get an expression on the right side of the equation
            @b if matches!(b, Constant(_)) && *b != Constant(0.0);
        ] => {
            // Undo the operation on the left side of the equation
            tree![
                Equals;
                #[
                    Sub;
                    a.clone();
                    b.clone();
                ];
                Constant(0.0);
            ]
        } using @a, @b
    );

    let expr = rewrite!(
        expr,
        this=pattern![
            Equals;
            // Get an expression on the left side of the equation
            #[
                @op if op.is_reversible_binary_operator(), where op: &Atom;
                @a;
                @b;
            ];
            // Get an expression on the right side of the equation
            @c;
        ] => {
            if matches!(op, Div | Mul) && *c.value() == Constant(0.0) {
                return this.clone();
            }

            // Undo the operation on the left side of the equation
            tree![
                Equals;
                a.clone();
                // Move the constant to the right side of the equation
                #[
                    op.opposite();
                    c.clone();
                    b.clone();
                ];
            ]
        } using op, @a, @b, @c
    );

    // If one side is negative, multiply both sides by -1
    let expr = rewrite!(
        expr,
        pattern![
            Equals;
            #[
                Neg;
                @a;
            ];
            #[
                Neg;
                @b;
            ];
        ] => {
            tree![
                Equals;
                a.clone();
                b.clone();
            ]
        } using @a, @b
    );

    // If one side is negative, multiply both sides by -1
    let expr = rewrite!(
        expr,
        pattern![
            Equals;
            #[
                Neg;
                @a;
            ];
            @b
        ] => {
            tree![
                Equals;
                a.clone();
                #[
                    Neg;
                    b.clone();
                ]
            ]
        } using @a, @b
    );

    expr
}

fn balance_to_right_equation(expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;

    let expr = rewrite!(
        expr,
        pattern![
            Equals;
            // Get an expression on the right side of the equation
            @b if matches!(b, Constant(_)) && *b != Constant(0.0);
            // Get an expression on the left side of the equation
            @a;
        ] => {
            // Undo the operation on the left side of the equation
            tree![
                Equals;
                #[
                    Sub;
                    a.clone();
                    b.clone();
                ];
                Constant(0.0);
            ]
        } using @a, @b
    );
    let expr = rewrite!(
        expr,
        pattern![
            Equals;
            // Get an expression on the left side of the equation
            @a;
            // Get an expression on the right side of the equation
            @b if matches!(b, Constant(_)) && *b != Constant(0.0);
        ] => {
            // Undo the operation on the left side of the equation
            tree![
                Equals;
                #[
                    Sub;
                    a.clone();
                    b.clone();
                ];
                Constant(0.0);
            ]
        } using @a, @b
    );

    let expr = rewrite!(
        expr,
        this = pattern![
            Equals;
            // Get an expression on the right side of the equation
            @a;
            // Get an expression on the left side of the equation
            #[
                @op if op.is_reversible_binary_operator(), where op: &Atom;
                @b;
                @c;
            ];
        ] => {
            if matches!(op, Div | Mul) && *a.value() == Constant(0.0) {
                return this.clone();
            }

            // Undo the operation on the left side of the equation
            let result = tree![
                Equals;
                // Move the constant to the right side of the equation
                #[
                    op.opposite();
                    a.clone();
                    c.clone();
                ];
                b.clone();
            ];
            assert!(result.is_binary());
            result
        } using op, @a, @b, @c
    );
    assert!(expr.is_binary());

    // If one side is negative, multiply both sides by -1
    let expr = rewrite!(
        expr,
        pattern![
            Equals;
            #[
                Neg;
                @a;
            ];
            #[
                Neg;
                @b;
            ];
        ] => {
            tree![
                Equals;
                a.clone();
                b.clone();
            ]
        } using @a, @b
    );

    // If one side is negative, multiply both sides by -1
    let expr = rewrite!(
        expr,
        pattern![
            Equals;
            @a;
            #[
                Neg;
                @b;
            ];
        ] => {
            tree![
                Equals;
                #[
                    Neg;
                    a.clone();
                ];
                b.clone();
            ]
        } using @a, @b
    );
    expr
}

fn distribute(expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;
    let expr = rewrite!(
        expr,
        pattern![
            Mul;
            // Get an expression on the left side of the multiplication
            #[
                @op if matches!(op, Add | Sub);
                @a;
                @b;
            ];
            // Get an expression on the right side of the multiplication
            @c;
        ] => {
            tree![
                op.clone();
                #[
                    Mul;
                    a.clone();
                    c.clone();
                ];
                #[
                    Mul;
                    b.clone();
                    c.clone();
                ];
            ]
        } using op, @a, @b, @c
    );
    let expr = rewrite!(
        expr,
        pattern![
            Mul;
            // Get an expression on the right side of the multiplication
            @a;
            // Get an expression on the left side of the multiplication
            #[
                @op if matches!(op, Add | Sub);
                @b;
                @c;
            ];
        ] => {
            tree![
                op.clone();
                #[
                    Mul;
                    a.clone();
                    b.clone();
                ];
                #[
                    Mul;
                    a.clone();
                    c.clone();
                ];
            ]
        } using op, @a, @b, @c
    );
    assert!(expr.is_binary());

    let expr = rewrite!(
        expr,
        pattern![
            Div;
            // Get an expression on the top side of the division
            #[
                @op if matches!(op, Add | Sub);
                @a;
                @b;
            ];
            // Get an expression on the bottom side of the division
            @c;
        ] => {
            // Distribute the division
            tree![
                op.clone();
                #[
                    Div;
                    a.clone();
                    c.clone();
                ];
                #[
                    Div;
                    b.clone();
                    c.clone();
                ];
            ]
        } using op, @a, @b, @c
    );

    assert!(expr.is_binary());
    expr
}

fn factor(expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;
    let expr = rewrite!(
        expr,
        this = pattern![
            Add;
            #[
                Mul;
                @a;
                @b;
            ];
            #[
                Mul;
                @c;
                @d;
            ];
        ] => {
            // Factor the expression
            if a == c {
                tree![
                    Mul;
                    a.clone();
                    #[
                        Add;
                        b.clone();
                        d.clone();
                    ];
                ]
            } else if a == d {
                tree![
                    Mul;
                    a.clone();
                    #[
                        Add;
                        b.clone();
                        c.clone();
                    ];
                ]
            } else if b == c {
                tree![
                    Mul;
                    b.clone();
                    #[
                        Add;
                        a.clone();
                        d.clone();
                    ];
                ]
            } else if b == d {
                tree![
                    Mul;
                    b.clone();
                    #[
                        Add;
                        a.clone();
                        c.clone();
                    ];
                ]
            } else {
                this.clone()
            }
        } using @a, @b, @c, @d
    );

    let expr = rewrite!(
        expr,
        this = pattern![
            Sub;
            #[
                Mul;
                @a;
                @b;
            ];
            #[
                Mul;
                @c;
                @d;
            ];
        ] => {
            // Factor the expression
            if a == c {
                tree![
                    Mul;
                    a.clone();
                    #[
                        Sub;
                        b.clone();
                        d.clone();
                    ];
                ]
            } else if a == d {
                tree![
                    Mul;
                    a.clone();
                    #[
                        Sub;
                        b.clone();
                        c.clone();
                    ];
                ]
            } else if b == c {
                tree![
                    Mul;
                    b.clone();
                    #[
                        Sub;
                        a.clone();
                        d.clone();
                    ];
                ]
            } else if b == d {
                tree![
                    Mul;
                    b.clone();
                    #[
                        Sub;
                        a.clone();
                        c.clone();
                    ];
                ]
            } else {
                this.clone()
            }
        } using @a, @b, @c, @d
    );

    let expr = rewrite!(
        expr,
        pattern![
            Pow;
            @x;
            @a if matches!(a, Constant(_));
        ] => {
            let mut result = x.clone();
            for _ in 1..(*a as i32) {
                result = tree![
                    Mul;
                    result;
                    x.clone();
                ];
            }
            result
        } using @x, Constant(a)=a
    );

    // Factor negatives into multiplication by -1
    // let expr = rewrite!(
    //     expr,
    //     pattern![
    //         Neg;
    //         @a;
    //     ] => {
    //         tree![
    //             Mul;
    //             a.clone();
    //             Constant(-1.0);
    //         ]
    //     } using @a
    // );

    assert!(expr.is_binary());
    expr
}

fn associative_left(expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;
    
    // a * (b * c) = (a * b) * c
    let expr = rewrite!(
        expr,
        pattern![
            Mul;
            #[
                Mul;
                @a;
                @b;
            ];
            @c;
        ] => {
            tree![
                Mul;
                a.clone();
                #[
                    Mul;
                    b.clone();
                    c.clone();
                ];
            ]
        } using @a, @b, @c
    );

    let expr = rewrite!(
        expr,
        pattern![
            Mul;
            #[
                Div;
                @a;
                @b;
            ];
            @c;
        ] => {
            tree![
                Div;
                #[
                    Mul;
                    a.clone();
                    c.clone();
                ];
                b.clone();
            ]
        } using @a, @b, @c
    );

    let expr = rewrite!(
        expr,
        pattern![
            Add;
            #[
                Add;
                @a;
                @b;
            ];
            @c;
        ] => {
            tree![
                Add;
                a.clone();
                #[
                    Add;
                    b.clone();
                    c.clone();
                ];
            ]
        } using @a, @b, @c
    );

    expr
}

fn associative_right(expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;
    
    
    // a * (b * c) = (a * b) * c
    let expr = rewrite!(
        expr,
        pattern![
            Mul;
            @a;
            #[
                Mul;
                @b;
                @c;
            ];
        ] => {
            tree![
                Mul;
                #[
                    Mul;
                    a.clone();
                    b.clone();
                ];
                c.clone();
            ]
        } using @a, @b, @c
    );

    let expr = rewrite!(
        expr,
        pattern![
            Mul;
            @a;
            #[
                Div;
                @b;
                @c;
            ];
        ] => {
            tree![
                Div;
                #[
                    Mul;
                    a.clone();
                    b.clone();
                ];
                c.clone();
            ]
        } using @a, @b, @c
    );

    let expr = rewrite!(
        expr,
        pattern![
            Add;
            @a;
            #[
                Add;
                @b;
                @c;
            ];
        ] => {
            tree![
                Add;
                #[
                    Add;
                    a.clone();
                    b.clone();
                ];
                c.clone();
            ]
        } using @a, @b, @c
    );

    expr
}

fn consolidate_powers(expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;
    let expr = rewrite!(
        expr,
        this = pattern![
            Mul;
            @x if matches!(x, Var(_));
            @y if matches!(y, Var(_));
        ] => {
            if x == y {
                tree![
                    Pow;
                    x.clone();
                    Constant(2.0);
                ]
            } else {
                this.clone()
            }
        } using x, y
    );

    let expr = rewrite!(
        expr,
        this = pattern![
            Mul;
            #[
                Pow;
                @x if matches!(x, Var(_));
                @a if matches!(a, Constant(_));
            ];
            @y if matches!(y, Var(_));
        ] => {
            if x == y {
                tree![
                    Pow;
                    x.clone();
                    #[
                        Add;
                        a.clone();
                        Constant(1.0);
                    ];
                ]
            } else {
                this.clone()
            }
        } using x, y, a
    );

    let expr = rewrite!(
        expr,
        this = pattern![
            Mul;
            #[
                Pow;
                @x if matches!(x, Var(_));
                @a if matches!(a, Constant(_));
            ];
            #[
                Pow;
                @y if matches!(y, Var(_));
                @b if matches!(b, Constant(_));
            ];
        ] => {
            if x == y {
                tree![
                    Pow;
                    x.clone();
                    #[
                        Add;
                        a.clone();
                        b.clone();
                    ];
                ]
            } else {
                this.clone()
            }
        } using x, y, a, b
    );

    // Same, but for division
    let expr = rewrite!(
        expr,
        this = pattern![
            Div;
            #[
                Pow;
                @x if matches!(x, Var(_));
                @a if matches!(a, Constant(_));
            ];
            #[
                Pow;
                @y if matches!(y, Var(_));
                @b if matches!(b, Constant(_));
            ];
        ] => {
            if x == y {
                tree![
                    Pow;
                    x.clone();
                    #[
                        Sub;
                        a.clone();
                        b.clone();
                    ];
                ]
            } else {
                this.clone()
            }
        } using x, y, a, b
    );

    let expr = rewrite!(
        expr,
        this = pattern![
            Div;
            #[
                Pow;
                @x if matches!(x, Var(_));
                @a if matches!(a, Constant(_));
            ];
            @y if matches!(y, Var(_));
        ] => {
            if x == y {
                tree![
                    Pow;
                    x.clone();
                    #[
                        Sub;
                        a.clone();
                        Constant(1.0);
                    ];
                ]
            } else {
                this.clone()
            }
        } using x, y, a
    );

    expr
}

fn consolidate_muls(expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;
    // x + (x * n) = x * (n + 1)

    let expr = rewrite!(
        expr,
        this = pattern![
            Add;
            @x;
            #[
                Mul;
                @y;
                @n if matches!(n, Constant(_));
            ];
        ] => {
            if x == y {
                tree![
                    Mul;
                    x.clone();
                    #[
                        Add;
                        n.clone();
                        Constant(1.0);
                    ];
                ]
            } else {
                this.clone()
            }
        } using @x, @y, n
    );

    let expr = rewrite!(
        expr,
        this = pattern![
            Add;
            #[
                Mul;
                @x;
                @m if matches!(m, Constant(_));
            ];
            #[
                Mul;
                @y;
                @n if matches!(n, Constant(_));
            ];
        ] => {
            if x == y {
                tree![
                    Mul;
                    x.clone();
                    #[
                        Add;
                        m.clone();
                        n.clone();
                    ];
                ]
            } else {
                this.clone()
            }
        } using @x, @y, n, m
    );


    let expr = rewrite!(
        expr,
        this = pattern![
            Add;
            #[
                Mul;
                @m if matches!(m, Constant(_));
                @x;
            ];
            #[
                Mul;
                @y;
                @n if matches!(n, Constant(_));
            ];
        ] => {
            if x == y {
                tree![
                    Mul;
                    x.clone();
                    #[
                        Add;
                        m.clone();
                        n.clone();
                    ];
                ]
            } else {
                this.clone()
            }
        } using @x, @y, n, m
    );


    expr
}

fn add_fractions(expr: Expr) -> Expr {
    use Atom::*;
    // Add fractions with different, but common denominators

    let expr = rewrite!(
        expr,
        pattern![
            Add;
            #[
                Div;
                @a;
                @b if matches!(b, Constant(_));
            ];
            #[
                Div;
                @c;
                @d if matches!(d, Constant(_));
            ];
        ] => {
            if b == d {
                tree![
                    Div;
                    #[
                        Add;
                        a.clone();
                        c.clone();
                    ];
                    Constant(*b);
                ]
            } else {
                // Multiply the numerators by the other denominator
                tree![
                    Div;
                    #[
                        Add;
                        #[
                            Mul;
                            a.clone();
                            Constant(*d);
                        ];
                        #[
                            Mul;
                            c.clone();
                            Constant(*b);
                        ];
                    ];
                    Constant(b * d)
                ]
            }
        } using @a, Constant(b)=b, @c, Constant(d)=d
    );

    // Add fractions with identical denominators
    let expr = rewrite!(
        expr,
        this=pattern![
            Add;
            #[
                Div;
                @a;
                @b;
            ];
            #[
                Div;
                @c;
                @d;
            ];
        ] => {
            if b == d {
                tree![
                    Div;
                    #[
                        Add;
                        a.clone();
                        c.clone();
                    ];
                    b.clone();
                ]
            } else {
                this.clone()
            }
        } using @a, @b, @c, @d
    );

    let expr = rewrite!(
        expr,
        pattern![
            Add;
            #[
                Div;
                @a;
                @b;
            ];
            #[
                Div;
                @c;
                @d;
            ];
        ] => {
            if b == d {
                tree![
                    Div;
                    #[
                        Add;
                        a.clone();
                        c.clone();
                    ];
                    b.clone();
                ]
            } else {
                // Multiply the numerators by the other denominator
                tree![
                    Div;
                    #[
                        Add;
                        #[
                            Mul;
                            a.clone();
                            d.clone();
                        ];
                        #[
                            Mul;
                            c.clone();
                            b.clone();
                        ];
                    ];
                    #[
                        Mul;
                        b.clone();
                        d.clone();
                    ]
                ]
            }
        } using @a, @b, @c, @d
    );


    expr
}



fn commutative(expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;
    let expr = rewrite!(
        expr,
        pattern![
            @op if matches!(op, Add | Mul);
            @a;
            @b;
        ] => {
            tree![
                op.clone();
                b.clone();
                a.clone();
            ]
        } using op, @a, @b
    );

    expr
}

fn subtract_to_sum(expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;
    let expr = rewrite!(
        expr,
        pattern![
            Sub;
            @a;
            @b;
        ] => {
            tree![
                Add;
                a.clone();
                #[
                    Neg;
                    b.clone();
                ];
            ]
        } using @a, @b
    );

    expr
}

fn eliminate_zeros(expr: Expr) -> Expr {
    use Atom::*;

    let expr = rewrite!(
        expr,
        pattern![
            Mul;
            @b;
            @a if *a == Constant(0.0);
        ] => { Constant(0.0) }
    );
    let expr = rewrite!(
        expr,
        pattern![
            Mul;
            @a if *a == Constant(0.0);
            @b;
        ] => { Constant(0.0) }
    );
    let expr = rewrite!(
        expr,
        pattern![
            Div;
            @a if *a == Constant(0.0);
            @b;
        ] => { Constant(0.0) }
    );
    
    let expr = rewrite!(
        expr,
        this = pattern![
            Sub;
            @a;
            @b;
        ] => {
            if a == b {
                tree![Constant(0.0)]
            } else {
                this.clone()
            }
        } using @a, @b
    );

    let expr = rewrite!(
        expr,
        pattern![
            Add;
            @a if *a == Constant(0.0);
            @b;
        ] => {
            b.clone()
        } using @b
    );
    
    let expr = rewrite!(
        expr,
        pattern![
            Add;
            @b;
            @a if *a == Constant(0.0);
        ] => {
            b.clone()
        } using @b
    );
    
    expr
}

fn eliminate_ones(expr: Expr) -> Expr {
    use Atom::*;

    let expr = rewrite!(
        expr,
        pattern![
            Mul;
            @a if *a == Constant(1.0);
            @b;
        ] => {
            b.clone()
        } using @b
    );

    let expr = rewrite!(
        expr,
        pattern![
            Mul;
            @b;
            @a if *a == Constant(1.0);
        ] => {
            b.clone()
        } using @b
    );

    let expr = rewrite!(
        expr,
        pattern![
            Div;
            @a;
            @b if *b == Constant(1.0);
        ] => { a.clone() } using @a
    );

    let expr = rewrite!(
        expr,
        pattern![
            Pow;
            @a;
            @b if *b == Constant(1.0);
        ] => { a.clone() } using @a
    );

    expr
}

fn double_negative_elimination(expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;
    let expr = rewrite!(
        expr,
        pattern![
            Neg;
            #[
                Neg;
                @a;
            ]
        ] => {
            a.clone()
        } using @a
    );

    let expr = rewrite!(
        expr,
        pattern![
            Mul;
            #[
                Neg;
                @a;
            ];
            #[
                Neg;
                @b;
            ]
        ] => {
            tree![
                Mul;
                a.clone();
                b.clone();
            ]
        } using @a, @b
    );
    let expr = rewrite!(
        expr,
        pattern![
            Div;
            #[
                Neg;
                @a;
            ];
            #[
                Neg;
                @b;
            ]
        ] => {
            tree![
                Div;
                a.clone();
                b.clone();
            ]
        } using @a, @b
    );
    /*
    let expr = rewrite!(
        expr,
        pattern![
            Mul;
            #[
                Mul;
                @a;
                @b if *b == Constant(-1.0);
            ];
            @c if *c == Constant(-1.0);
        ] => {
            a.clone()
        } using @a
    );

    let expr = rewrite!(
        expr,
        pattern![
            Div;
            #[
                Div;
                @a;
                @b if *b == Constant(-1.0);
            ];
            @c if *c == Constant(-1.0);
        ] => {
            a.clone()
        } using @a
    );*/
    
    let expr = rewrite!(
        expr,
        pattern![
            Mul;
            @a;
            @b if *b == Constant(1.0);
        ] => {
            a.clone()
        } using @a
    );
    let expr = rewrite!(
        expr,
        this = pattern![
            Div;
            @a;
            @b;
        ] => {
            if a == b {
                tree![Constant(1.0)]
            } else {
                this.clone()
            }
        } using @a, @b
    );


    /*
    let expr = rewrite!(
        expr,
        pattern![
            Mul;
            @a;
            @b if *b == Constant(0.0);
        ] => {
            tree![Constant(0.0)]
        }
    );

    let expr = rewrite!(
        expr,
        pattern![
            Add;
            @a if *a == Constant(0.0);
            @b;
        ] => {
            b.clone()
        } using @b
    );
     */


    expr
}


fn flip_equation(expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;
    let expr = rewrite!(
        expr,
        pattern![
            Equals;
            // Get an expression on the left side of the equation
            @a;
            // Get an expression on the right side of the equation
            @b;
        ] => {
            tree![
                Equals;
                b.clone();
                a.clone();
            ]
        } using @a, @b
    );
    expr
}

fn write_expr(buf: &mut impl Write, expr: &Expr) -> Result<(), std::io::Error> {
    assert!(expr.is_binary());
    let mut children = expr.children();

    if expr.value().is_unary_operator() {
        write!(buf, "{}", expr.value())?;
        if let Some(child) = children.next() {
            if child.depth() > 1 { write!(buf, "(")?; }
            write_expr(buf, child)?;
            if child.depth() > 1 { write!(buf, ")")?; }
        }
    } else {
        if let Some(child) = children.next() {
            if child.depth() > 1 { write!(buf, "(")?; }
            write_expr(buf, child)?;
            if child.depth() > 1 { write!(buf, ")")?; }
            write!(buf, " ")?;
        }
        
        write!(buf, "{}", expr.value())?;
        
        if let Some(child) = children.next() {
            write!(buf, " ")?;
            if child.depth() > 1 { write!(buf, "(")?; }
            write_expr(buf, child)?;
            if child.depth() > 1 { write!(buf, ")")?; }
        }
    }

    Ok(())
}

fn print_expr(expr: &Expr) {
    write_expr(&mut std::io::stdout(), expr).expect("Failed to write expression");
}

fn to_str(expr: &Expr) -> String {
    let mut buf = Vec::new();
    write_expr(&mut buf, expr).expect("Failed to create str from expression");
    String::from_utf8(buf).unwrap()
}

fn to_latex_helper(expr: &Expr) -> String {
    let mut result = String::new();
    match expr.value() {
        Atom::Equals => {
            result.push_str(&to_latex_helper(&expr[0]));
            result.push_str(" = ");
            result.push_str(&to_latex_helper(&expr[1]));
        }
        Atom::Add => {
            result.push_str(&to_latex_helper(&expr[0]));
            result.push_str(" + ");
            result.push_str(&to_latex_helper(&expr[1]));
        }
        Atom::Sub => {
            result.push_str(&to_latex_helper(&expr[0]));
            result.push_str(" - ");
            result.push_str(&to_latex_helper(&expr[1]));
        }
        Atom::Mul => {
            if !expr[0].is_leaf() && precedence(expr[0].value()) < precedence(expr.value()) {
                result.push_str("\\left(");
                result.push_str(&to_latex_helper(&expr[0]));
                result.push_str("\\right)");
            } else {
                result.push_str(&to_latex_helper(&expr[0]));
            }
            result.push_str(" \\cdot ");
            if !expr[1].is_leaf() && precedence(expr[1].value()) < precedence(expr.value()) {
                result.push_str("\\left(");
                result.push_str(&to_latex_helper(&expr[1]));
                result.push_str("\\right)");
            } else {
                result.push_str(&to_latex_helper(&expr[1]));
            }
        }
        Atom::Div => {
            result.push_str("\\frac{");
            result.push_str(&to_latex_helper(&expr[0]));
            result.push_str("}{");
            result.push_str(&to_latex_helper(&expr[1]));
            result.push_str("}");
        }
        Atom::Pow => {
            // result.push_str("{");
            // result.push_str(&to_latex_helper(&expr[0]));
            // result.push_str("}^{");
            // result.push_str(&to_latex_helper(&expr[1]));
            // result.push_str("}");

            result.push_str("{");
            if !expr[0].is_leaf() && precedence(expr[0].value()) < precedence(expr.value()) {
                result.push_str("\\left(");
                result.push_str(&to_latex_helper(&expr[0]));
                result.push_str("\\right)");
            } else {
                result.push_str(&to_latex_helper(&expr[0]));
            }
            result.push_str("}^{");
            if !expr[1].is_leaf() && precedence(expr[1].value()) < precedence(expr.value()) {
                result.push_str("\\left(");
                result.push_str(&to_latex_helper(&expr[1]));
                result.push_str("\\right)");
            } else {
                result.push_str(&to_latex_helper(&expr[1]));
            }
            result.push_str("}");
        }
        Atom::Neg => {
            result.push_str("-");
            result.push_str(&to_latex_helper(&expr[0]));
        }
        Atom::Constant(c) => {
            result.push_str(&c.to_string());
        }
        Atom::Var(v) => {
            result.push_str(&v);
        }
    }
    result
}

fn to_latex(expr: &Expr, path: &str) -> String {
    use std::fs::File;
    use std::io::Write;
    use std::path::Path;
    use std::process::Command;
    let mut result = String::new();
    let file_name = Path::new(path).file_name().unwrap().to_str().unwrap();

    // Start the math environment
    result.push_str("\\begin{equation*}\n");
    result.push_str("\\begin{aligned}\n");
    result.push_str(&to_latex_helper(expr));
    result.push_str("\n");
    result.push_str("\\end{aligned}\n");
    result.push_str("\\end{equation*}\n");

    // Create an image of the equation
    let latex_path = Path::new(file_name).with_extension("tex");
    let latex = format!(
        r#"\documentclass[varwidth=true, border=10pt, convert={{size=1200x}}]{{standalone}}
        \usepackage{{amsmath}}
        \begin{{document}}
        {}

        \end{{document}}
        "#,
        // "\\documentclass{{article}}\n\\usepackage{{amsmath}}\n\\begin{{document}}\n{}\n\\end{{document}}",
        result
    );

    let mut latex_file = File::create(&latex_path).expect("Failed to create image file");

    // Create the latex document
    latex_file.write_all(latex.as_bytes()).expect("Failed to write to image file");

    // Compile the latex document
    let output = Command::new("pdflatex")
        .arg(latex_path.display().to_string())
        .output()
        .expect("Failed to compile latex document");

    // Check if the compilation was successful
    if !output.status.success() {
        panic!("Failed to compile latex document: {}", String::from_utf8_lossy(&output.stderr));
    }

    // Convert the pdf to an image
    let pdf_path = latex_path.with_extension("pdf");

    let output = Command::new("pdftoppm")
        .arg(pdf_path.display().to_string())
        .arg("-png")
        .arg(file_name)
        .output()
        .expect("Failed to convert pdf to image");

    // Check if the conversion was successful
    if !output.status.success() {
        panic!("Failed to convert pdf to image: {}", String::from_utf8_lossy(&output.stderr));
    }

    // Clean up the files, leaving only the image
    fn remove_file(path: &Path, extension: &str) {
        let path = path.with_extension(extension);
        if path.exists() {
            let failure_msg = format!("Failed to remove file {}", path.display());
            std::fs::remove_file(path).expect(&failure_msg);
        } else {
            error!("File {} does not exist", path.display());
        }
    }

    remove_file(&latex_path, "log");
    remove_file(&latex_path, "aux");
    remove_file(&latex_path, "tex");
    remove_file(&latex_path, "pdf");
    // Move the image to the correct location
    let gen_path = format!("{}-1.png", file_name);
    let input_image_path = Path::new(&gen_path);
    let output_image_path = Path::new(path).with_extension("png");
    info!("Moving image file {} to {}", input_image_path.display(), output_image_path.display());
    std::fs::rename(input_image_path, output_image_path).expect("Failed to move image file");

    // std::fs::remove_file(pdf_path).expect("Failed to remove pdf file");
    // std::fs::remove_file(latex_path.with_extension("log")).expect("Failed to remove log file");
    // std::fs::remove_file(latex_path.with_extension("aux")).expect("Failed to remove aux file");
    // std::fs::remove_file(latex_path.with_extension("fls")).expect("Failed to remove fls file");
    // std::fs::remove_file(latex_path.with_extension("tex")).expect("Failed to remove tex file");
    // std::fs::remove_file(latex_path).expect("Failed to remove latex file");

    result
}

fn println_expr(expr: &Expr) {
    print_expr(expr);
    println!();
}

#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
struct Transformation {
    name: &'static str,
    func: fn(Expr) -> Expr,
}

impl Transformation {
    fn apply(&self, expr: Expr) -> Expr {
        (self.func)(expr)
    }
}

fn has_changed(old: &Expr, new: &Expr) -> bool {
    old != new
}

fn is_in_polynomial_form(expr: &Expr) -> bool {
    use Atom::*;

    let result = match expr.value() {
        Equals => {
            // Both sides must be in polynomial form
            is_in_polynomial_form(&expr[0]) && is_in_polynomial_form(&expr[1])
        }

        Add | Sub => {
            // Assert that the children are in polynomial form
            // The children must be either:
            // Additions/Subtractions, or Multiplications/Powers

            let mut children = expr.children();
            let first_child = children.next().unwrap();
            let second_child = children.next().unwrap();


            let first_child_is_polynomial = is_in_polynomial_form(first_child);
            let second_child_is_polynomial = is_in_polynomial_form(second_child);

            first_child_is_polynomial && second_child_is_polynomial

            // (match first_child.value() {
            //     Add | Sub => is_in_polynomial_form(first_child),
            //     Neg => is_in_polynomial_form(&first_child[0]),
            //     // If its a multiply, then the children must be constants, variables, or powers
            //     Mul => first_child.children_values().all(|a| matches!(a, Atom::Constant(_) | Atom::Var(_) | Atom::Pow)),
            //     // If its a power, then the children must be variables
            //     Pow => first_child.children_values().all(|a| matches!(a, Atom::Var(_))),
            //     _ => false
            // }) && (match second_child.value() {
            //     Add | Sub => is_in_polynomial_form(second_child),
            //     Neg => is_in_polynomial_form(&second_child[0]),
            //     // If its a multiply, then the children must be constants, variables, or powers
            //     Mul => second_child.children_values().all(|a| matches!(a, Atom::Constant(_) | Atom::Var(_) | Atom::Pow)),
            //     // If its a power, then the children must be variables
            //     Pow => second_child.children_values().all(|a| matches!(a, Atom::Var(_))),
            //     _ => false
            // })
        }

        Mul => {
            // Left child must be a constant
            // Right child must be a variable or power
            matches!(expr[0].value(), Atom::Constant(_)) && (matches!(expr[1].value(), Atom::Var(_) | Atom::Pow))
                && is_in_polynomial_form(&expr[0]) && is_in_polynomial_form(&expr[1])
        }

        Div => {
            // The first child must be a variable, and the second child must be a constant
            matches!(expr[0].value(), Atom::Var(_)) && matches!(expr[1].value(), Atom::Constant(_))
                && is_in_polynomial_form(&expr[0]) && is_in_polynomial_form(&expr[1])
        }

        Pow => {
            // The first child must be a variable, and the second child must be a constant
            matches!(expr[0].value(), Atom::Var(_)) && matches!(expr[1].value(), Atom::Constant(_))
        }

        Constant(_) | Var(_) => true,

        Neg => false,
    };

    // println!("Is {} in polynomial form: {}", to_str(expr), result);

    result
}

fn is_quadratic(expr: &Expr) -> bool {
    if !is_in_polynomial_form(expr) {
        return false;
    }

    let vars = get_variables(expr);
    if vars.len() > 1 {
        return false;
    }

    let count_divs = expr.iter().filter(|a| matches!(a, Atom::Div)).count();

    get_degree(expr, &vars.first().unwrap()) == 2
        && count_polynomial_terms(expr) <= 3 && count_divs == 0
        && count_polynomial_terms_of_degree(expr, 2) == 1
        && count_polynomial_terms_of_degree(expr, 1) <= 1
        && count_polynomial_terms_of_degree(expr, 0) <= 1
}

fn is_cubic(expr: &Expr) -> bool {
    if !is_in_polynomial_form(expr) {
        return false;
    }

    let vars = get_variables(expr);
    if vars.len() > 1 {
        return false;
    }

    let count_divs = expr.iter().filter(|a| matches!(a, Atom::Div)).count();

    get_degree(expr, &vars.first().unwrap()) == 3
        && count_polynomial_terms(expr) <= 4 && count_divs == 0
        && count_polynomial_terms_of_degree(expr, 3) == 1
        && count_polynomial_terms_of_degree(expr, 2) <= 1
        && count_polynomial_terms_of_degree(expr, 1) <= 1
        && count_polynomial_terms_of_degree(expr, 0) <= 1
}

/// Computes the real roots of a cubic equation: a*x^3 + b*x^2 + c*x + d = 0
///
/// # Arguments
///
/// * `a` - Coefficient of x^3
/// * `b` - Coefficient of x^2
/// * `c` - Coefficient of x
/// * `d` - Constant term
///
/// # Returns
///
/// A vector containing all real roots of the cubic equation.
fn roots_of_cubic(a: f64, b: f64, c: f64, d: f64) -> Vec<f64> {
    // Define a small epsilon for floating point comparisons
    let epsilon = 1e-12;
    let mut roots = Vec::new();

    if a.abs() < epsilon {
        // Degenerate to quadratic equation: b*x^2 + c*x + d = 0
        if b.abs() < epsilon {
            // Degenerate to linear equation: c*x + d = 0
            if c.abs() < epsilon {
                // Degenerate to constant equation: d = 0
                // If d is also zero, every x is a root. Here, we return an empty vector.
                // Otherwise, no roots.
                // You can modify this behavior as needed.
            } else {
                // Single root
                roots.push(-d / c);
            }
        } else {
            // Quadratic equation
            let discriminant = c * c - 4.0 * b * d;
            if discriminant > epsilon {
                let sqrt_disc = discriminant.sqrt();
                roots.push((-c + sqrt_disc) / (2.0 * b));
                roots.push((-c - sqrt_disc) / (2.0 * b));
            } else if discriminant.abs() < epsilon {
                // One real root (double root)
                roots.push(-c / (2.0 * b));
            }
            // If discriminant < 0, no real roots
        }
        return roots;
    }

    // Normalize coefficients
    let a_inv = 1.0 / a;
    let b_norm = b * a_inv;
    let c_norm = c * a_inv;
    let d_norm = d * a_inv;

    // Depressed cubic substitution: x = t - b/(3a)
    let p = (3.0 * c_norm - b_norm * b_norm) / 3.0;
    let q = (2.0 * b_norm * b_norm * b_norm - 9.0 * b_norm * c_norm + 27.0 * d_norm) / 27.0;

    // Compute the discriminant
    let discriminant = (q / 2.0).powi(2) + (p / 3.0).powi(3);

    // Compute the shift to revert back to x from t
    let shift = b_norm / 3.0;

    if discriminant > epsilon {
        // One real root
        let sqrt_disc = discriminant.sqrt();
        let u = (-q / 2.0 + sqrt_disc).cbrt();
        let v = (-q / 2.0 - sqrt_disc).cbrt();
        let t = u + v;
        let x = t - shift;
        roots.push(x);
    } else if discriminant.abs() < epsilon {
        // Multiple real roots
        if q.abs() < epsilon {
            // Triple root
            let x = -shift;
            roots.push(x);
        } else {
            // One single and one double root
            let u = (-q / 2.0).cbrt();
            let t1 = 2.0 * u;
            let t2 = -u;
            let x1 = t1 - shift;
            let x2 = t2 - shift;
            roots.push(x1);
            roots.push(x2);
        }
    } else {
        // Three distinct real roots
        let r = (-p / 3.0).sqrt();
        let phi = ( -q / (2.0 * r.powi(3)) ).acos();
        let t1 = 2.0 * r * (phi / 3.0).cos();
        let t2 = 2.0 * r * ( (phi + 2.0 * PI) / 3.0 ).cos();
        let t3 = 2.0 * r * ( (phi + 4.0 * PI) / 3.0 ).cos();
        let x1 = t1 - shift;
        let x2 = t2 - shift;
        let x3 = t3 - shift;
        roots.push(x1);
        roots.push(x2);
        roots.push(x3);
    }

    roots
}

fn get_degree(expr: &Expr, var: &str) -> usize {
    use Atom::*;
    match expr.value() {
        Add | Sub => {
            expr.children().map(|a| get_degree(a, var)).max().unwrap_or(0)
        },
        Mul => {
            expr.children().map(|a| get_degree(a, var)).sum::<usize>()
        }
        Neg => {
            get_degree(&expr[0], var)
        },
        Div => {
            get_degree(&expr[0], var) - get_degree(&expr[1], var)
        }
        Pow => {
            if let Constant(n) = expr[1].value() {
                *n as usize
            } else {
                0
            }
        },
        Constant(_) => 0,

        Var(v) => if v == var { 1 } else { 0 },

        Equals => {
            expr.children().map(|a| get_degree(a, var)).max().unwrap_or(0)
        }
    }
}

fn count_polynomial_terms(expr: &Expr) -> usize {
    use Atom::*;
    match expr.value() {
        Add | Sub => {
            expr.children().map(|a| count_polynomial_terms(a)).sum()
        },
        Mul | Div => {
            expr.children().map(|a| count_polynomial_terms(a)).product()
        }
        Neg => {
            count_polynomial_terms(&expr[0])
        },
        Pow => {
            1
        },
        Constant(_) => 1,

        Var(_) => 1,

        Equals => {
            expr.children().map(|a| count_polynomial_terms(a)).sum()
        }
    }
}
fn count_polynomial_terms_of_degree(expr: &Expr, degree: usize) -> usize {
    use Atom::*;
    let vars = get_variables(expr);
    if vars.len() == 0 {
        return 0;
    }

    match expr.value() {
        Add | Sub => {
            expr.children().map(|a| count_polynomial_terms_of_degree(a, degree)).sum()
        },
        Neg => {
            count_polynomial_terms_of_degree(&expr[0], degree)
        },
        
        Equals => {
            expr.children().map(|a| count_polynomial_terms_of_degree(a, degree)).sum()
        }

        Constant(_) => {
            if degree == 0 {
                1
            } else {
                0
            }
        },

        otherwise => {
            if get_degree(expr, &vars.first().unwrap()) == degree {
                1
            } else {
                0
            }
        }
    }
}

fn is_provably_negative(expr: &Expr) -> bool {
    // Get the current op
    use Atom::*;
    match expr.value() {
        Constant(n) => *n < 0.0,
        Neg => {
            // If the child is not negative
            !is_provably_negative(&expr[0])
        },
        Pow => {
            false
        },
        Add | Sub => {
            false
        },
        Mul | Div => {
            // If only one child is negative
            let mut negative_count = 0;
            for child in expr.children() {
                if is_provably_negative(child) {
                    negative_count += 1;
                }
            }
            negative_count == 1
        },
        Var(_) => false,
        Equals => {
            false
        }
    }
}

fn heuristic_score(expr: &Expr) -> usize {
    use Atom::*;
    // Example: Score based on depth and number of nodes
    if is_irreducible(expr) {
        return 0;
    }

    let mut undesirable_denominator_count = 1;
    map!(
        expr,
        pattern![
            Div;
            @numerator;
            @denominator;
        ] => {
            undesirable_denominator_count += denominator.iter().filter(|a| matches!(a, Var(_) | Constant(_))).count();
        } using @denominator
    );

    let mut vars_appearing_on_both_sides = 1;

    map!(
        expr,
        pattern![
            Equals;
            @left;
            @right;
        ] => {
            // If the two sides have any variables in common
            let vars_left = get_variables(left);
            let vars_right = get_variables(right);
            if vars_left.iter().any(|a| vars_right.contains(a)) {
                vars_appearing_on_both_sides += 1;
            }
        } using @left, @right
    );

    let is_in_polynomial_form = if is_in_polynomial_form(expr) {
        1
    } else {
        2
    };

    // Is one of the branches of the equal sign a zero?
    let mut zero_count = 0;
    map!(
        expr,
        pattern![
            Equals;
            @a if *a == Constant(0.0);
            @b;
        ] => {
            zero_count += 1;
        }
    );

    map!(
        expr,
        pattern![
            Equals;
            @a;
            @b if *b == Constant(0.0);
        ] => {
            zero_count += 1;
        }
    );

    let zero_score = if zero_count == 1 {
        1
    } else {
        2
    };

    // Check if both sides are negative
    let mut negative_sides = 0;
    map!(
        expr,
        pattern![
            Equals;
            @a;
            @b;
        ] => {
            if is_provably_negative(a) {
                negative_sides += 1;
            }
            if is_provably_negative(b) {
                negative_sides += 1;
            }
        } using @a, @b
    );

    negative_sides = if negative_sides > 1 { 2 } else { 1 };
    let var_usage = expr.iter().filter(|a| matches!(a, Atom::Var(_))).count() + 1;

    let mut solution_count = 3;
    map!(
        expr,
        pattern![
            Equals;
            @a;
            @b;
        ] => {
            if matches!(a, Var(_)) {
                solution_count -= 1;
            }
            if matches!(b, Var(_)) {
                solution_count -= 1;
            }
        } using a, b
    );

    solution_count * zero_score * is_in_polynomial_form * vars_appearing_on_both_sides * expr.size() * expr.depth() * var_usage * undesirable_denominator_count * negative_sides
}

fn simplify_quadratic(expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;
    let expr = rewrite!(
        expr,
        this = pattern![
            Equals;
            @solution if matches!(solution, Constant(_));
            @quadratic;
        ] => {
            if is_quadratic(quadratic) && get_variables(quadratic).len() == 1 {
                let (mut a, mut b, mut c) = (None, None, None);
                let mut var = None;

                rewrite!(
                    quadratic,
                    this = pattern![
                        Mul;
                        @coeff;
                        #[
                            Pow;
                            @var if matches!(var, Var(_));
                            @pow if *pow == Constant(2.0);
                        ]
                    ] => {
                        a = Some(*coeff);
                        var = Some(my_var.clone());
                        this.clone()
                    } using Constant(coeff)=coeff, Var(my_var)=var
                );
                if a.is_none() {
                    rewrite!(
                        quadratic,
                        this = pattern![
                            Pow;
                            @var if matches!(var, Var(_));
                            @pow if *pow == Constant(2.0);
                        ] => {
                            a = Some(1.0);
                            var = Some(my_var.clone());
                            this.clone()
                        } using Var(my_var)=var
                    );
                }

                
                rewrite!(
                    quadratic,
                    this = pattern![
                        Mul;
                        @coeff;
                        @var if matches!(var, Var(_));
                    ] => {
                        if Some(my_var) != var.as_ref() {
                            debug!("Var mismatch: {:?} != {:?}", my_var, var);
                            return this.clone();
                        } else {
                            b = Some(*coeff);
                        }
                        this.clone()
                    } using Constant(coeff)=coeff, Var(my_var) = var
                );

                if b.is_none() {
                    rewrite!(
                        quadratic,
                        this = pattern![
                            Add;
                            @var if matches!(var, Var(_));
                            @rest;
                        ] => {
                            if Some(my_var) != var.as_ref() {
                                debug!("Var mismatch: {:?} != {:?}", my_var, var);
                                return this.clone();
                            } else {
                                b = Some(1.0);
                            }
                            this.clone()
                        } using Var(my_var) = var
                    );
                    rewrite!(
                        quadratic,
                        this = pattern![
                            Add;
                            @rest;
                            @var if matches!(var, Var(_));
                        ] => {
                            if Some(my_var) != var.as_ref() {
                                debug!("Var mismatch: {:?} != {:?}", my_var, var);
                                return this.clone();
                            } else {
                                b = Some(1.0);
                            }
                            this.clone()
                        } using Var(my_var) = var
                    );

                }

                if b.is_none() {
                    b = Some(0.0);
                    debug!("No B term found, setting to zero");
                }

                
                rewrite!(
                    quadratic,
                    this = pattern![
                        Add;
                        @rest;
                        @constant if matches!(constant, Constant(_));
                    ] => {
                        c = Some(*constant - solution);
                        this.clone()
                    } using Constant(constant) = constant
                );
                rewrite!(
                    quadratic,
                    this = pattern![
                        Add;
                        @constant if matches!(constant, Constant(_));
                        @rest;
                    ] => {
                        c = Some(*constant - solution);
                        this.clone()
                    } using Constant(constant) = constant
                );

                if c.is_none() {
                    c = Some(-solution);
                    debug!("No C term found, setting to {}", -solution);
                }

                match (a, b, c, var) {
                    (Some(a), Some(b), Some(c), Some(var)) => {
                        debug!("Expr: {}", to_str(&expr));
                        debug!("   Found quadratic {a}*{var}^2 + {b}*{var} + {c} = 0");
                        // Solve the quadratic equation
                        let discriminant = b * b - 4.0 * a * c;
                        // Check if the discriminant is negative,
                        // which means the quadratic has no real solutions
                        if discriminant < 0.0 {
                            error!("Found quadratic {a}*{var}^2 + {b}*{var} + {c} = 0, but discriminant {} is negative", discriminant);
                            return this.clone();
                        }

                        let x1 = (-b + discriminant.sqrt()) / (2.0 * a);
                        let x2 = (-b - discriminant.sqrt()) / (2.0 * a);
                        
                        debug!("   Solutions: x1 = {}, x2 = {}", x1, x2);
                        let solutions = vec![x1, x2];

                        // Choose which solution to use.
                        tree![Constant(select_root(&solutions))]
                        /*
                        // Choose which solution to use.
                        // If the solutions are the same, then we can just use one of them
                        if x1 == x2 {
                            tree![Equals; Var(var); Constant(x1)]
                        } else {
                            // Choose the integer solution if possible
                            let solution = if x1.fract() == 0.0 {
                                x1
                            } else if x2.fract() == 0.0 {
                                x2
                            } else {
                                // Choose the smaller solution, preferring the positive one
                                if x1 > 0.0 && x2 > 0.0 {
                                    x1.min(x2)
                                } else if x2 > 0.0 {
                                    x2
                                } else {
                                    x1.max(x2)
                                }
                            };

                            tree![Equals; Var(var); Constant(solution)]
                        }
                         */
                    }
                    (a, b, c, var) => {
                        debug!("Could not find quadratic values for: a={a:?}, b={b:?}, c={c:?}, x={var:?}");

                        this.clone()
                    }
                }
            } else {
                this.clone()
            }
        } using Constant(solution) = solution, @quadratic
    );

    expr
}


fn simplify_cubic(expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;
    let expr = rewrite!(
        expr,
        this = pattern![
            Equals;
            @solution if matches!(solution, Constant(_));
            @cubic;
        ] => {
            if is_cubic(cubic) && get_variables(cubic).len() == 1 {
                let (mut a, mut b, mut c, mut d) = (None, None, None, None);
                let mut var = None;

                rewrite!(
                    cubic,
                    this = pattern![
                        Mul;
                        @coeff;
                        #[
                            Pow;
                            @var if matches!(var, Var(_));
                            @pow if *pow == Constant(3.0);
                        ]
                    ] => {
                        a = Some(*coeff);
                        var = Some(my_var.clone());
                        this.clone()
                    } using Constant(coeff)=coeff, Var(my_var)=var
                );
                if a.is_none() {
                    rewrite!(
                        cubic,
                        this = pattern![
                            Pow;
                            @var if matches!(var, Var(_));
                            @pow if *pow == Constant(3.0);
                        ] => {
                            a = Some(1.0);
                            var = Some(my_var.clone());
                            this.clone()
                        } using Var(my_var)=var
                    );
                }

                rewrite!(
                    cubic,
                    this = pattern![
                        Mul;
                        @coeff;
                        #[
                            Pow;
                            @var if matches!(var, Var(_));
                            @pow if *pow == Constant(2.0);
                        ]
                    ] => {
                        b = Some(*coeff);
                        var = Some(my_var.clone());
                        this.clone()
                    } using Constant(coeff)=coeff, Var(my_var)=var
                );
                if b.is_none() {
                    rewrite!(
                        cubic,
                        this = pattern![
                            Pow;
                            @var if matches!(var, Var(_));
                            @pow if *pow == Constant(2.0);
                        ] => {
                            b = Some(1.0);
                            var = Some(my_var.clone());
                            this.clone()
                        } using Var(my_var)=var
                    );
                }
                

                if b.is_none() {
                    b = Some(0.0);
                    debug!("No B term found, setting to zero");
                }

                rewrite!(
                    cubic,
                    this = pattern![
                        Mul;
                        @coeff;
                        @var if matches!(var, Var(_));
                    ] => {
                        if Some(my_var) != var.as_ref() {
                            debug!("Var mismatch: {:?} != {:?}", my_var, var);
                            return this.clone();
                        } else {
                            c = Some(*coeff);
                        }
                        this.clone()
                    } using Constant(coeff)=coeff, Var(my_var) = var
                );

                if c.is_none() {
                    rewrite!(
                        cubic,
                        this = pattern![
                            Add;
                            @var if matches!(var, Var(_));
                            @rest;
                        ] => {
                            if Some(my_var) != var.as_ref() {
                                debug!("Var mismatch: {:?} != {:?}", my_var, var);
                                return this.clone();
                            } else {
                                c = Some(1.0);
                            }
                            this.clone()
                        } using Var(my_var) = var
                    );
                    rewrite!(
                        cubic,
                        this = pattern![
                            Add;
                            @rest;
                            @var if matches!(var, Var(_));
                        ] => {
                            if Some(my_var) != var.as_ref() {
                                debug!("Var mismatch: {:?} != {:?}", my_var, var);
                                return this.clone();
                            } else {
                                c = Some(1.0);
                            }
                            this.clone()
                        } using Var(my_var) = var
                    );

                }

                if c.is_none() {
                    c = Some(0.0);
                    debug!("No C term found, setting to zero");
                }

                
                rewrite!(
                    cubic,
                    this = pattern![
                        Add;
                        @rest;
                        @constant if matches!(constant, Constant(_));
                    ] => {
                        d = Some(*constant - solution);
                        this.clone()
                    } using Constant(constant) = constant
                );
                rewrite!(
                    cubic,
                    this = pattern![
                        Add;
                        @constant if matches!(constant, Constant(_));
                        @rest;
                    ] => {
                        d = Some(*constant - solution);
                        this.clone()
                    } using Constant(constant) = constant
                );

                if d.is_none() {
                    d = Some(-solution);
                    debug!("No C term found, setting to {}", -solution);
                }

                match (a, b, c, d, var) {
                    (Some(a), Some(b), Some(c), Some(d), Some(var)) => {
                        debug!("Expr: {}", to_str(&expr));
                        debug!("   Found cubic {a}*{var}^3 + {b}*{var}^2 + {c}*{var} + {d} = 0");
                        
                        let roots = roots_of_cubic(a, b, c, d);
                        debug!("   Solutions: {:?}", roots);

                        // Choose which solution to use.
                        if roots.is_empty() {
                            return this.clone();
                        } else {
                            let root = select_root(&roots);
                            tree![Equals; Var(var); Constant(root)]
                        }
                    }
                    (a, b, c, d, var) => {
                        debug!("Could not find cubic values for: a={a:?}, b={b:?}, c={c:?}, d={d:?}, x={var:?}");

                        this.clone()
                    }
                }
            } else {
                this.clone()
            }
        } using Constant(solution) = solution, @cubic
    );

    expr
}

fn division_multiply_by_reciprocal(expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;
    let expr = rewrite!(
        expr,
        pattern![
            Div;
            @a;
            #[
                Div;
                @b;
                @c;
            ]
        ] => {
            tree![
                Mul;
                a.clone();
                #[
                    Div;
                    c.clone();
                    b.clone();
                ];
            ]
        } using @a, @b, @c
    );

    expr
}

fn evaluate(mut expr: Expr, bindings: BTreeMap<String, Expr>) -> Expr {
    // Substitute variables with their values
    use Atom::*;
    
    for (name, val) in bindings {
        expr = rewrite!(
            expr,
            pattern![@var if matches!(var, Var(var_name) if *var_name == name);] => {
                val.clone()
            }
        );
    }

    // Confirm there are no variables left
    if expr.iter().any(|a| matches!(a, Var(_))) {
        error!("Failed to evaluate expression: {}", to_str(&expr));
    }

    // Constant folding
    for i in 0..10000 {
        if i == 9999 {
            error!("Reached maximum iterations while evaluating solution: {}", to_str(&expr));
            break;
        }
        let new_expr = constant_folding(expr.clone());
        if has_nan_or_inf(&new_expr) {
            return tree![Constant(f64::NAN)];
        }

        if new_expr == expr {
            break;
        }
        expr = new_expr;
    }

    expr
}

fn has_nan_or_inf(expr: &Expr) -> bool {
    use Atom::*;
    match expr.value() {
        Constant(n) => n.is_nan() || n.is_infinite(),
        Neg => has_nan_or_inf(&expr[0]),
        Add | Sub | Mul | Div => expr.children().any(|a| has_nan_or_inf(a)),
        Pow => expr.children().any(|a| has_nan_or_inf(a)),
        Var(_) => false,
        Equals => expr.children().any(|a| has_nan_or_inf(a)),
    }
}

fn get_variables(expr: &Expr) -> BTreeSet<String> {
    let mut vars = BTreeSet::new();
    for atom in expr.iter() {
        if let Atom::Var(name) = atom {
            vars.insert(name.clone());
        }
    }
    vars
}

fn extract_bindings(expr: &Expr) -> BTreeMap<String, Expr> {
    let mut bindings = BTreeMap::new();
    use Atom::*;
    rewrite!(
        expr,
        this=pattern![
            Equals;
            @a if matches!(a, Var(_));
            @b if matches!(b, Constant(_));
        ] => {
            bindings.insert(a.to_string(), b.clone());
            this.clone()
        } using Var(a)=a, @b
    );
    rewrite!(
        expr,
        this=pattern![
            Equals;
            @b if matches!(b, Constant(_));
            @a if matches!(a, Var(_));
        ] => {
            bindings.insert(a.to_string(), b.clone());
            this.clone()
        } using Var(a)=a, @b
    );
    bindings
}

fn combine_like_terms(expr: Expr) -> Expr {
    assert!(expr.is_binary());
    use Atom::*;
    let expr = rewrite!(
        expr,
        this=pattern![
            Add;
            @a if matches!(a, Var(_));
            @b if matches!(b, Var(_));
        ] => {
            if a == b {
                tree![
                    Mul;
                    Constant(2.0);
                    a.clone();
                ]
            } else {
                this.clone()
            }
        } using @a, @b
    );

    let expr = rewrite!(
        expr,
        this=pattern![
            Add;
            #[
                Mul;
                @a if matches!(a, Constant(_));
                @b if matches!(b, Var(_));
            ];
            #[
                Mul;
                @c if matches!(c, Constant(_));
                @d if matches!(d, Var(_));
            ];
        ] => {
            if b == d {
                tree![
                    Mul;
                    #[
                        Add;
                        a.clone();
                        c.clone();
                    ];
                    b.clone();
                ]
            } else {
                this.clone()
            }
        } using @a, @b, @c, @d
    );


    let expr = rewrite!(
        expr,
        this=pattern![
            Add;
            #[
                Mul;
                @a if matches!(a, Constant(_));
                @b if matches!(b, Var(_));
            ];
            #[
                Mul;
                @c if matches!(c, Var(_));
                @d if matches!(d, Constant(_));
            ];
        ] => {
            if b == c {
                tree![
                    Mul;
                    #[
                        Add;
                        a.clone();
                        d.clone();
                    ];
                    b.clone();
                ]
            } else {
                this.clone()
            }
        } using @a, @b, @c, @d
    );

    expr
}

fn cross_multiply(expr: Expr) -> Expr {       
    use Atom::*;
    rewrite!(
        expr,
        pattern![
            Equals;
            #[
                Div;
                @a;
                @b;
            ];
            #[
                Div;
                @c;
                @d;
            ];
        ] => {
            tree![
                Equals;
                #[
                    Mul;
                    a.clone();
                    d.clone();
                ];
                #[
                    Mul;
                    b.clone();
                    c.clone();
                ];
            ]
        } using @a, @b, @c, @d
    )
}

fn verify_equals(input: &Expr, output: &Expr, transformations: &[Transformation]) -> bool {
    use Atom::*;
    let mut found_contradiction = false;

    let output_bindings = extract_bindings(output);
    debug!("Evaluating input: {}", to_str(input));
    debug!("With bindings:");
    for (name, val) in output_bindings.iter() {
        debug!("{} = {}", name, to_str(val));
    }
    let unique_variables = get_variables(input);
    if output_bindings.len() < unique_variables.len() {
        warn!("Not all variables are bound!");
        return true;
    }
    
    let evaluated1 = evaluate(input.clone(), output_bindings);
    
    if has_nan_or_inf(&evaluated1) {
        error!("Found NaN or Inf in expression: {}", to_str(&evaluated1));
        return false;
    }

    rewrite!(
        evaluated1,
        pattern![
            Equals;
            @a;
            @b;
        ] => {
            if a != b {
                found_contradiction = true;
                error!("Found contradiction in expression: {} != {}", to_str(&a), to_str(&b));
            }
            tree![Equals; a.clone(); b.clone()]
        } using @a, @b
    );

    if !found_contradiction {
        info!("Verified!");
    }
    
    !found_contradiction
}

fn reduce(expr: Expr, transformations: &[Transformation]) -> Expr {
    let config = (*CONFIG.lock().unwrap()).clone();

    let transformations = transformations.to_vec();
    let original_expr = constant_folding(expr.clone());

    // Instead, perform a DFS search on the transformations
    // lazy_static! {
    //     static ref VISITED: Mutex<BTreeSet<Expr>> = Mutex::new(BTreeSet::new());
    //     static ref PARENTS: Mutex<BTreeMap<Expr, BTreeSet<(Expr, Transformation)>>> = Mutex::new(BTreeMap::new());
    // }
    // let mut parents = PARENTS.lock().unwrap();
    // let mut visited = VISITED.lock().unwrap();
    let mut visited = BTreeSet::new();
    let mut parents = BTreeMap::new();

    use std::collections::VecDeque;
    let mut stack = VecDeque::new();
    let mut has_tried_all = true;
    let mut iteration = 0;
    
    let mut best_score = std::usize::MAX;
    let mut best_iteration = 0;
    stack.push_back((heuristic_score(&expr), original_expr.clone()));

    while let Some((score, expr)) = stack.pop_front() {
        if visited.contains(&expr) {
            trace!("Already visited expression: {}", to_str(&expr));
            continue;
        }

        trace!("Found unvisited expression: {}", to_str(&expr));
        visited.insert(expr.clone());
        has_tried_all = false;
        trace!("Search depth: {}", iteration);
        if iteration >= config.max_iterations {
            warn!("Reached maximum iterations");
            break;
        }
        if iteration - best_iteration > config.bail_after_no_improvement_for {
            warn!("No improvement for {} iterations", iteration - best_iteration);
            break;
        }

        if is_irreducible(&expr) {
            info!("Found irreducible expression: {}", to_str(&expr));
            break;
        }

        // Use rayon to parallelize the transformation application
        use rayon::prelude::*;
        let new_exprs: Vec<_> = transformations.par_iter().map(|transformation| {
            let new_expr = constant_folding(transformation.apply(expr.clone()));
            let new_score = heuristic_score(&new_expr);
            (new_score, new_expr, transformation)
        }).collect();

        for (new_score, new_expr, transformation) in new_exprs {
            if has_changed(&expr, &new_expr) {
                // Add the parent to the set of parents
                let _entry = parents.entry(new_expr.clone()).or_insert(BTreeSet::new())
                    .insert((expr.clone(), transformation.clone()));

                if new_score < best_score {
                    info!("Found new candidate at iteration {:<5} | {}", iteration, to_str(&new_expr));
                    best_score = new_score;
                    best_iteration = iteration;
                }

                stack.push_back((new_score, new_expr));
            }
        }

        // Sort the stack by heuristic score
        if iteration % config.fitness_reevaluate_after == 0 {
            stack.make_contiguous().sort_by_key(|(score, _)| *score);

            // Print the best expressions
            // let result: Tree<Atom> = visited.iter().min_by_key(|e| heuristic_score(e)).unwrap().clone();
            // info!("Best candidate at iteration {i:<4}: Score {} | {}", heuristic_score(&result), to_str(&result));
        }
        if stack.len() == 0 {
            info!("Exhausted all transformations");
        }
        iteration += 1;
    }
    trace!("Stopped on iteration {}", iteration);

    // Choose the smallest visited expression
    info!("Candidate solutions:");
    let mut results = visited.iter().map(|e| (heuristic_score(e), e.clone())).collect::<Vec<_>>();
    results.sort_by_key(|(score, _)| *score);
    for (i, (score, expr)) in results.iter().enumerate().take(3) {
        info!("   Score: {} | {}", score, to_str(expr));
    }
    let result: Tree<Atom> = visited.iter().min_by_key(|e| heuristic_score(e)).unwrap().clone();

    if has_tried_all {
        println!("No more transformations to apply");
    }

    // Trace back the parents to find the path to the original expression
    // let parents = PARENTS.lock().unwrap();

    info!("Ran for {} iterations", iteration);
    info!("Result: {}", to_str(&result));
    info!("*** END EVALUTION ***");
    let mut test = original_expr.clone();

    if !Path::new("output").exists() {
        std::fs::create_dir("output").unwrap();
    } else {
        // Remove all files in the results directory
        let _ = std::fs::remove_dir_all("output");
        std::fs::create_dir("output").unwrap();
    }

    // test.save_png("output/0.png").unwrap();
    if config.render {
        to_latex(&test, "output/0");
    }
    let path = find_path_to(&parents, &mut BTreeSet::new(), result.clone(), test.clone(), 0);
    if let Some(path) = path {
        println!("{}", "=".repeat(80));
        info!("Path for {}", to_str(&test));
        println!("{}", ".".repeat(80));
        let mut history = BTreeSet::new();
        for (i, transformation) in path.iter().enumerate() {
            test = constant_folding(transformation.apply(test));
            if !history.insert(test.clone()) {
                warn!("Redundant rule detected!");
            }
            info!("Applied {:<25} | {}", transformation.name, to_str(&test));

            // Graph the transformation
            // test.save_png(&format!("output/{}.png", i+1)).unwrap();
            if config.render {
                to_latex(&test, &format!("output/{}", i+1));
            }
        }
        if config.render {
            to_latex(&result, &format!("output/{}", path.len()));

            // Create an FFMPEG video
            let mut cmd = std::process::Command::new("ffmpeg")
                .arg("-framerate")
                .arg("3")
                .arg("-i")
                .arg("output/%d.png")
                .arg("-vf")
                .arg("scale=1920:1080:force_original_aspect_ratio=decrease,pad=1920:1080:(ow-iw)/2:(oh-ih)/2")
                .arg("-c:v")
                .arg("libx264")
                .arg("-pix_fmt")
                .arg("yuv420p")
                .arg("output/output.mp4")
                .spawn()
                .unwrap();
        }

        // Now convert to a video
        // let mut cmd = std::process::Command::new("ffmpeg")
        //     .arg("-y")
        //     .arg("-framerate")
        //     .arg("1")
        //     .arg("-i")
        //     .arg("output/%d.png")
        //     .arg("-vf")
        //     .arg("fps=25")
        //     .arg("output/output.mp4")
        //     .spawn()
        //     .unwrap();
        // ffmpeg -framerate 30 -i frame%03d.png -vf "fade=t=in:st=0:d=2,fade=t=out:st=8:d=2" -c:v libx264 -pix_fmt yuv420p output_with_fade.mp4
        /*
        let mut cmd = std::process::Command::new("ffmpeg")
            .arg("-framerate")
            .arg("10")
            .arg("-i")
            .arg("output/%d.png")
            .arg("-vf")
            .arg("scale=1920:1080:force_original_aspect_ratio=decrease,pad=1920:1080:(ow-iw)/2:(oh-ih)/2")
            .arg("-c:v")
            .arg("libx264")
            .arg("-pix_fmt")
            .arg("yuv420p")
            .arg("output/output.mp4")
            .spawn()
            .unwrap();
        cmd.wait().unwrap();
         */
        if config.verify {
            assert!(verify_equals(&expr, &result, &transformations));
            println!("{}", "=".repeat(80));
        }
    } else {
        warn!("No path found to original expression");
        if config.verify {
            assert!(verify_equals(&expr, &result, &transformations));
        }
    }

    result
}

fn find_path_to(parents: &BTreeMap<Expr, BTreeSet<(Expr, Transformation)>>, visited: &mut BTreeSet<Expr>, expr: Expr, target: Expr, i: usize) -> Option<Vec<Transformation>> {
    let mut path = Vec::new();

    if visited.contains(&expr) {
        return None;
    }

    visited.insert(expr.clone());
    // if let Some(my_parents) = parents.get(&expr) {
    //     for (my_parent, transformation) in my_parents.iter() {
    //         if my_parent == &target {
    //             path.push(transformation.clone());
    //             return Some(path);
    //         }
    //         if let Some(mut subpath) = find_path_to(parents, visited, my_parent.clone(), target.clone(), i + 1) {
    //             path.append(&mut subpath);
    //             path.push(transformation.clone());
                
    //             return Some(path);
    //         }
    //     }
    // }
    // return None;

    // Instead of finding any path, find the shortest path
    let mut shortest_path: Option<Vec<Transformation>> = None;
    if let Some(my_parents) = parents.get(&expr) {
        for (my_parent, transformation) in my_parents.iter() {
            let old_path = path.clone();
            if my_parent == &expr {
                continue;
            }
            if my_parent == &target {
                path.push(transformation.clone());

                shortest_path = Some(path.clone());
            }
            if let Some(mut subpath) = find_path_to(parents, visited, my_parent.clone(), target.clone(), i + 1) {
                path.append(&mut subpath);
                path.push(transformation.clone());
                
                if shortest_path.is_none() || path.len() < shortest_path.as_ref().unwrap().len() {
                    shortest_path = Some(path.clone());
                }
            }

            path = old_path;
        }

        if let Some(shortest_path) = shortest_path {
            return Some(shortest_path);
        }
    }
    None
}


fn precedence(op: &Atom) -> i32 {
    use Atom::*;
    match op {
        Add | Sub => 1,
        Mul | Div => 2,
        Pow => 3,
        Equals => 0,
        _ => 0,
    }
}

/*

fn parse_expr(s: &str) -> Expr {
    use Atom::*;
    // First, convert infix to postfix
    let mut postfix = vec![];
    let mut stack: Vec<Atom> = vec![];
    let mut current_n = None;
    let mut stack_index = 0;
    for c in s.chars() {
        if !c.is_digit(10) {
            if let Some(n) = current_n {
                postfix.push(Constant(n));
            }
            current_n = None;
        }
        match c {
            '0'..='9' => {
                // postfix.push(Num(c.to_digit(10).unwrap() as i32))
                // current_n = current_n * 10 + c.to_digit(10).unwrap() as i32;
                current_n = Some(current_n.unwrap_or(0.0) * 10.0 + c.to_digit(10).unwrap() as f64);
            }
            '+' | '-' | '*' | '/' | '^' | '=' => {
                let op = match c {
                    '+' => Add,
                    '-' => Sub,
                    '*' => Mul,
                    '/' => Div,
                    '^' => Pow,
                    '=' => Equals,
                    _ => unreachable!(),
                };
                while let Some(top) = stack.last() {
                    if top == &Constant(0.0) {
                        break;
                    }
                    if precedence(top.clone()) >= precedence(op.clone()) {
                        postfix.push(stack.pop().unwrap());
                    } else {
                        break;
                    }
                }
                stack.push(op.clone());
            }
            '(' => {
                stack_index = stack.len();
            }
            ')' => {
                while let Some(top) = stack.pop() {
                    postfix.push(top);
                    if stack.len() == stack_index {
                        break;
                    }
                }
            }

            'a'..='z' => {
                postfix.push(Var(c.to_string()));
            }

            _ => {}
        }
    }
    if let Some(n) = current_n {
        postfix.push(Constant(n));
    }

    while let Some(op) = stack.pop() {
        postfix.push(op);
    }

    // Then, convert postfix to tree
    let mut stack = vec![];
    for token in postfix {
        match token {
            Constant(n) => stack.push(tree![Constant(n)]),
            Add | Mul | Div | Pow | Equals => {
                let right = stack.pop().unwrap();
                let left = stack.pop().unwrap();
                stack.push(tree![token; left; right]);
            }
            Sub => {
                let right = stack.pop().unwrap();
                if stack.is_empty() {
                    stack.push(tree![Neg; right]);
                } else {
                    let left = stack.pop().unwrap();
                    stack.push(tree![Sub; left; right]);
                }
            }
            Var(name) => stack.push(tree![Var(name)]),

            _ => unimplemented!(),

        }
    }

    stack.pop().unwrap()
}
 */

// Use nom to parse the expression instead
use nom::{
    branch::alt,
    bytes::complete::tag,
    number::complete::double,
    character::complete::{char, alpha1, digit1, multispace0},
    combinator::{map, opt, cut},
    multi::{many0, many1},
    sequence::{delimited, pair, preceded, terminated},
    IResult,
};

fn parse_expr_inner(s: &str) -> IResult<&str, Expr> {
    use Atom::*;
    let (s, expr) = parse_equation(s)?;
    Ok((s, expr))
}

fn parse_equation(s: &str) -> IResult<&str, Expr> {
    let (s, first) = parse_addition(s)?;
    let (s, rest) = many0(preceded(multispace0, parse_equation_equals))(s)?;
    let mut expr = first;
    for (op, next) in rest {
        expr = tree![op; expr; next];
    }
    Ok((s, expr))
}

fn parse_equation_equals(s: &str) -> IResult<&str, (Atom, Expr)> {
    let (s, _) = char('=')(s)?;
    let (s, expr) = cut(parse_addition)(s)?;
    Ok((s, (Atom::Equals, expr)))
}


fn parse_addition(s: &str) -> IResult<&str, Expr> {
    let (s, first) = parse_multiplication(s)?;
    let (s, rest) = many0(preceded(multispace0, alt((parse_addition_plus, parse_addition_minus))))(s)?;
    let mut expr = first;
    for (op, next) in rest {
        expr = tree![op; expr; next];
    }
    Ok((s, expr))
}

fn parse_addition_plus(s: &str) -> IResult<&str, (Atom, Expr)> {
    let (s, _) = char('+')(s)?;
    let (s, expr) = cut(parse_multiplication)(s)?;
    Ok((s, (Atom::Add, expr)))
}

fn parse_addition_minus(s: &str) -> IResult<&str, (Atom, Expr)> {
    let (s, _) = char('-')(s)?;
    let (s, expr) = cut(parse_multiplication)(s)?;
    Ok((s, (Atom::Sub, expr)))
}

fn parse_multiplication(s: &str) -> IResult<&str, Expr> {
    let (s, first) = parse_power(s)?;
    let (s, rest) = many0(preceded(multispace0, alt((parse_multiplication_times, parse_multiplication_divide))))(s)?;
    let mut expr = first;
    for (op, next) in rest {
        expr = tree![op; expr; next];
    }
    Ok((s, expr))
}

fn parse_multiplication_times(s: &str) -> IResult<&str, (Atom, Expr)> {
    let (s, _) = char('*')(s)?;
    let (s, expr) = cut(parse_power)(s)?;
    Ok((s, (Atom::Mul, expr)))
}

fn parse_multiplication_divide(s: &str) -> IResult<&str, (Atom, Expr)> {
    let (s, _) = char('/')(s)?;
    let (s, expr) = cut(parse_power)(s)?;
    Ok((s, (Atom::Div, expr)))
}

fn parse_power(s: &str) -> IResult<&str, Expr> {
    let (s, first) = parse_atom(s)?;
    let (s, rest) = many0(preceded(multispace0, parse_power_inner))(s)?;
    let mut expr = first;
    for (op, next) in rest {
        expr = tree![op; expr; next];
    }
    Ok((s, expr))
}

fn parse_power_inner(s: &str) -> IResult<&str, (Atom, Expr)> {
    let (s, _) = char('^')(s)?;
    let (s, expr) = cut(parse_atom)(s)?;
    Ok((s, (Atom::Pow, expr)))
}

fn parse_atom(s: &str) -> IResult<&str, Expr> {
    let (s, _) = multispace0(s)?;
    let (s, output) = alt((
        map(parse_parentheses, |e| tree![e]),
        map(parse_number, |n| tree![Atom::Constant(n)]),
        map(parse_var, |v| tree![Atom::Var(v)]),
    ))(s)?;
    let (s, _) = multispace0(s)?;
    Ok((s, output))
}

fn parse_parentheses(s: &str) -> IResult<&str, Expr> {
    let (s, _) = multispace0(s)?;
    let (s, _) = char('(')(s)?;
    let (s, _) = multispace0(s)?;
    let (s, expr) = parse_expr_inner(s)?;
    let (s, _) = multispace0(s)?;
    let (s, _) = char(')')(s)?;
    let (s, _) = multispace0(s)?;
    Ok((s, expr))
}

fn parse_number(s: &str) -> IResult<&str, f64> {
    map(double, |n| n)(s)
}

fn parse_var(s: &str) -> IResult<&str, String> {
    map(
        alpha1,
        |chars: &str| chars.to_string(),
    )(s)
}

fn parse_expr(s: &str) -> Expr {
    let (_, expr) = parse_expr_inner(s).unwrap();
    expr
}

fn main() {
    use tracing_subscriber::{fmt, prelude::*};
    use std::fs::File;

    let input = {
        let mut config = CONFIG.lock().unwrap();
        *config = Config::parse();
        config.input.clone()
    };

    let file = File::create("output.log").expect("Failed to create log file");

    // Console layer with `INFO` level filter
    let console_layer = fmt::layer()
        .with_writer(std::io::stdout) // Write to console
        // Only write info to console
        .with_filter(tracing_subscriber::filter::LevelFilter::INFO);

    // File layer capturing all logs
    let file_layer = fmt::layer()
        // Write logs in a readable format
        .with_ansi(false)
        .with_writer(file) // Write to file
        // Write all logs to file
        .with_filter(tracing_subscriber::filter::LevelFilter::TRACE);
    
    // Combine the layers
    tracing_subscriber::registry()
        .with(console_layer)
        .with(file_layer)
        .init();
    use Atom::*;
    
    println!("{}", "~".repeat(80));
    for line in INTRO.lines() {
        info!("{}", line);
    }
    println!("{}", "~".repeat(80));

    info!("*** BEGIN EVALUATION ***");

    let input_expr = parse_expr(&input);

    // let mut expr = parse_expr("x * ((1 / 2) + (2 * 3)) = 5 / x");
    // let mut expr = parse_expr("2 * x + 5 = 15");
    // let mut expr = parse_expr("7 * x - 3 = 4 * x + 12");
    // let mut expr = parse_expr("x / 2 + x / 3 + x / 4 = 10");
    // let mut expr = parse_expr("x / 2 + x / 3 + x / 5 + x / 7 = y");
    // let mut expr = parse_expr("x^2 / 2 + x / 3 + x / 5 + x / 7 = 15");
    // let mut expr = parse_expr("x^2 / 2 + x / 3 + x / 5 + x / 7 = y");


    // let config = Config {
    //     max_iterations: 1000,
    //     bail_after_no_improvement_for: 1000,
    //     reevaluate_fitness_after: 25,
    // };

    let high_priority_transforms = vec![
        Transformation { name: "Constant folding", func: constant_folding },
        Transformation { name: "Eliminate double negative", func: double_negative_elimination },
        Transformation { name: "Eliminate zeros", func: eliminate_zeros },
        Transformation { name: "Eliminate ones", func: eliminate_ones },
        Transformation { name: "Combine like terms", func: combine_like_terms },
        Transformation { name: "Subtraction to addition", func: subtract_to_sum },
      
        Transformation { name: "Add fractions", func: add_fractions },
    ];

    let medium_priority_transforms = vec![
        Transformation { name: "Factor", func: factor },
        Transformation { name: "Associative left", func: associative_left },  
        Transformation { name: "Associative right", func: associative_right },
        Transformation { name: "Distribute", func: distribute },
    ];

    let core_equation_solving = vec![
        Transformation { name: "Multiply by reciprocal", func: division_multiply_by_reciprocal },
        Transformation { name: "Cross multiply", func: cross_multiply },
        Transformation { name: "Balance to left equation", func: balance_to_left_equation },
        Transformation { name: "Balance to right equation", func: balance_to_right_equation },
    ];

    let low_priority_transforms = vec![
        Transformation { name: "Simplify cubic", func: simplify_cubic },
        Transformation { name: "Simplify quadratic", func: simplify_quadratic },
        Transformation { name: "Commutative", func: commutative },
    ];

    let mut transformations = vec![];
    transformations.extend(high_priority_transforms);
    transformations.extend(medium_priority_transforms);
    transformations.extend(core_equation_solving);
    transformations.extend(low_priority_transforms);

    info!("Given expression: {}", to_str(&input_expr));
    info!("Starting CAS system...");
    let expr = reduce(input_expr.clone(), &transformations);

    info!("Final expression: {}", to_str(&expr));
}