use trees::*;
use std::fmt::{Display, Formatter, Result as FmtResult};

type Expr<'a> = Tree<Lambda<'a>>;

fn print_lambda(expr: &Expr) {
    // let expr = roll_applications(expr);
    match expr.value() {
        Lambda::Var(s) => print!("{}", s),
        Lambda::Let => {
            print!("let ");
            // Print all children except the last one
            for child in expr.children().take(expr.children().count() - 1) {
                print_lambda(child);
                print!(" = ");
                print_lambda(&child[0]);
            }
            // Print the last child
            // print!("{}", expr.children().last().unwrap());
            print!(" in ");
            print_lambda(expr.children().last().unwrap());
        }
        Lambda::Abs => {
            print!("λ");
            // Print all children except the last one
            for child in expr.children().take(expr.children().count() - 1) {
                // print!("{}.", child.clone().prune());
                print_lambda(child);
                print!(".");
            }
            // Print the last child
            // print!("{}", expr.children().last().unwrap());
            print_lambda(expr.children().last().unwrap());
        }
        Lambda::App => {
            // Print all children except the last one
            for child in expr.children().take(expr.children().count() - 1) {
                if child.children().count() > 1 {
                    print!("(");
                    print_lambda(child);
                    print!(")");
                } else {
                    print_lambda(child);
                }
                print!(" ");
            }
            // Print the last child
            let last = expr.children().last().unwrap();
            if last.children().count() > 1 {
                print!("(");
                print_lambda(last);
                print!(")");
            } else {
                print_lambda(last);
            }
        }
        other => print!("{other}"),
    }
}

fn println_lambda(expr: &Expr) {
    print_lambda(expr);
    println!();
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Lambda<'a> {
    EntryPoint,
    Var(&'a str),
    Let,
    Abs,
    App,
    Int(i32),
    Float(f64),
    Bool(bool),
    Nil,
    Builtin(&'static str, usize, fn(&[Expr<'a>]) -> Expr<'a>),
    Combinator(SKI),
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum SKI {
    S,
    K,
    I,
}

impl<'a> Display for Lambda<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::EntryPoint => write!(f, "ENTRY POINT"),
            Self::Var(s) => write!(f, "{}", s),
            Self::Let => write!(f, "let"),
            Self::Abs => write!(f, "λ"),
            Self::App => write!(f, "•"),
            Self::Int(n) => write!(f, "{}", n),
            Self::Float(n) => write!(f, "{}", n),
            Self::Bool(b) => write!(f, "{}", b),
            Self::Nil => write!(f, "nil"),
            Self::Builtin(name, args, _) => write!(f, "<builtin {name}>"),
            Self::Combinator(atom) => write!(f, "{:?}", atom),
        }
    }
}

static mut COUNTER: usize = 0;

fn eval<'a>(expr: &Expr<'a>) -> Expr<'a> {
    let my_count = unsafe {
        COUNTER += 1;
        COUNTER
    };
    use crate::SKI::*;
    use Lambda::*;

    let result = match expr.value() {
        Lambda::App => {
            let mut args = expr.children().map(eval).collect::<Vec<_>>();
            let func = args.remove(0);
            let result = match func.value() {
                Lambda::Builtin(_, args_count, f) if args.len() >= *args_count => f(&args),
                Lambda::Combinator(S) if args.len() >= 3 => {
                    let x = args.remove(0);
                    let y = args.remove(0);
                    let z = args.remove(0);
                    let mut result = tree![
                        App;
                        #[App; x; z.clone()];
                        #[App; y; z];
                    ];
                    if args.len() != 0 {
                        result = tree![App; result];
                        result.add_children(args);
                    }
                    eval(&result)
                }
                Lambda::Combinator(K) if args.len() >= 2 => {
                    let x = args.remove(0);
                    let _y = args.remove(0);
                    let mut result = x;
                    if args.len() != 0 {
                        result = tree![App; result];
                        result.add_children(args);
                    }
                    eval(&result)
                }
                Lambda::Combinator(I) if args.len() >= 1 => {
                    let x = args.remove(0);
                    let mut result = x;
                    if args.len() != 0 {
                        result = tree![App; result];
                        result.add_children(args);
                    }
                    eval(&result)
                }
                Lambda::App => {
                    // Join the function and the arguments
                    let mut result = func.clone();
                    result.add_children(args);
                    eval(&result)
                }

                Builtin(..) | Combinator(_) => expr.clone(),
                Var(_) | Int(_) | Float(_) | Bool(_) | Nil => func.clone(),

                _ => {
                    // Get all except the last child for the params
                    let params = func
                        .children()
                        .take(func.children().count() - 1)
                        .collect::<Vec<_>>();
                    // Get the last child for the body
                    let body = func.children().last().unwrap();
                    let mut new_body = body.clone();
                    for (param, arg) in params.iter().zip(&args) {
                        new_body.replace(param, arg);
                    }

                    if params.len() < args.len() {
                        let mut result = tree![App; new_body];
                        result.add_children(args[params.len()..].iter().cloned());
                        eval(&result)
                    } else if args.len() < params.len() {
                        // Create a new lambda with the remaining params
                        for param in params.iter().cloned().skip(args.len()).rev() {
                            new_body = tree![Abs; param.clone(); new_body];
                        }
                        eval(&new_body)
                    } else {
                        eval(&new_body)
                    }
                }
            };

            result
        }
        Lambda::Let => {
            let mut children = expr.children().collect::<Vec<_>>();
            let mut new_body = children.pop().unwrap().clone();

            for binding in children {
                let var = binding.clone().prune();
                let val = binding[0].clone();
                new_body.replace(&var, &eval(&val));
            }

            eval(&new_body)
        }
        _ => expr.clone(),
    };

    // if *expr != result {
    //     expr.save_png(format!("assets/eval_{my_count}_antes.png")).unwrap();
    //     result.save_png(format!("assets/eval_{my_count}_despues.png")).unwrap();
    // }
    result
}

fn eval_ski<'a>(expr: &Expr<'a>) -> Expr<'a> {
    use Lambda::*;
    use SKI::*;
    let mut expr = expr.clone();
    loop {
        let old_expr = expr.clone();
        expr = rewrite!(
            expr,
            pattern![App; Combinator(S); @x; @y; @z] => {
                tree![
                    App;
                    #[App; x.clone(); z.clone()];
                    #[App; y.clone(); z.clone()];
                ]
            } using @x, @y, @z
        );
        expr = rewrite!(
            expr,
            this = pattern![App; Combinator(S); @x; @y; @z; ..] => {
                tree![App;
                    #[
                        App;
                        #[App; x.clone(); z.clone()];
                        #[App; y.clone(); z.clone()];
                    ]; ..this.children().cloned().skip(4)]
            } using @x, @y, @z
        );

        expr = rewrite!(expr, pattern![App; Combinator(K); @x; @y] => {x.clone()} using @x);
        expr = rewrite!(expr, this = pattern![App; Combinator(K); @x; @y; ..] => {tree![App; x.clone(); ..this.children().cloned().skip(3)]} using @x);
        expr = rewrite!(expr, pattern![App; Combinator(I); @x] => {x.clone()} using @x);
        expr = rewrite!(expr, this = pattern![App; Combinator(I); @x; ..] => {tree![App; x.clone(); ..this.children().cloned().skip(2)]} using @x);

        expr = rewrite!(
            expr,
            this = pattern![App; @func if matches!(func, Builtin(..)); ..] => {
                let args = this.children().skip(1).map(eval_ski).collect::<Vec<_>>();
                if args.len() < *args_count || args.iter().any(|arg| matches!(arg.value(), App | Var(_))) {
                    this.clone()
                } else {
                    f(&args)
                }
            } using Builtin(_name, args_count, f) = func
        );
        expr = rewrite!(
            expr,
            this = pattern![App; #[App; ..]; ..] => {
                // Join together the arguments
                let mut args = this.children().map(eval_ski).collect::<Vec<_>>();
                eval_ski(&args.remove(0).clone().with_children(args))
            }
        );

        if expr == old_expr {
            break;
        }
    }
    expr
}

fn eval2<'a>(expr: &Expr<'a>) -> Expr<'a> {
    use Lambda::*;
    use SKI::*;
    let mut expr = expr.clone();
    loop {
        let old_expr = expr.clone();
        expr = rewrite!(
            expr,
            pattern![App; Combinator(S); @x; @y; @z] => {
                eval2(&tree![App; tree![App; x.clone(); z.clone()]; tree![App; y.clone(); z.clone()]])
            } using x, y, z
        );
        expr = rewrite!(expr, pattern![App; Combinator(K); @x; @y] => {x.clone()} using x);
        expr = rewrite!(expr, pattern![App; Combinator(I); @x] => {x.clone()} using x);

        expr = rewrite!(
            expr,
            node = pattern![App; #[Abs; ..]; ..]
            => {
                let mut args = node.children().map(eval2).collect::<Vec<_>>();
                let func = args.remove(0);

                // Get all except the last child for the params
                let params = func.children().take(func.children().count() - 1).collect::<Vec<_>>();
                // Get the last child for the body
                let body = func.children().last().unwrap();
                let mut new_body = body.clone();
                for (param, arg) in params.iter().zip(&args) {
                    new_body.replace(param, arg);
                }
                if params.len() < args.len() {
                    let mut result = tree![App; new_body];
                    result.add_children(args[params.len()..].iter().cloned());
                    eval2(&result)
                } else if args.len() < params.len() {
                    // Create a new lambda with the remaining params
                    for param in params.iter().cloned().skip(args.len()).rev() {
                        new_body = tree![Abs; param.clone(); new_body];
                    }
                    eval2(&new_body)
                } else {
                    eval2(&new_body)
                }
            }
        );

        expr = rewrite!(
            expr,
            node = pattern![
                App;
                @func if matches!(func, Builtin(..));
                ..
            ]
            => {
                let args = args.children().cloned().collect::<Vec<_>>();
                if args.iter().any(|arg| matches!(arg.value(), App | Var(_))) {
                    node.clone()
                } else if args.len() >= *args_count {
                    f(&args)
                } else {
                    node.clone()
                }
            } using Builtin(_name, args_count, f) = func, args=@dotdot
        );

        expr = rewrite!(
            expr,
            node = pattern![
                App;
                #[App; ..];
                ..
            ] => {
                let mut args = node.children().map(eval2).collect::<Vec<_>>();
                let func = args.remove(0);
                let mut result = func.clone();
                result.add_children(args);
                eval2(&result)
            }
        );

        if expr == old_expr {
            break;
        }
    }

    expr
}

fn is_var_used(var: Lambda, expr: &Expr) -> bool {
    use Lambda::*;
    // Check if a variable is used in an expression
    expr.iter().any(|atom| match (var, atom) {
        (Var(v1), Var(v2)) => v1 == *v2,
        _ => false,
    })
}

fn is_converted(expr: &Expr) -> bool {
    use Lambda::*;
    expr.iter().all(|atom| match atom {
        Var(_) | Abs => false,
        _ => true,
    })
}

fn main() {
    use Lambda::*;
    use SKI::*;
    let inc = Lambda::Builtin("inc", 1, |args: &[Expr]| {
        let arg = args[0].value();
        match arg {
            Int(n) => tree![Int(n + 1)],
            _ => panic!("Expected int, got {}", arg),
        }
    });

    let double = Lambda::Builtin("double", 1, |args: &[Expr]| {
        let arg = args[0].value();
        match arg {
            Int(n) => tree![Int(n * 2)],
            _ => panic!("Expected int, got {}", arg),
        }
    });

    let mul = Lambda::Builtin("mul", 2, |args: &[Expr]| {
        let a = args[0].value();
        let b = args[1].value();
        match (a, b) {
            (Int(x), Int(y)) => tree![Int(x * y)],
            _ => panic!("Expected int, got {} and {}", a, b),
        }
    });
    let compose = tree![
        Abs;
        Var("f");
        #[
            Abs;
            Var("g");
            #[
                Abs;
                Var("x");
                #[
                    App;
                    Var("f");
                    #[App; Var("g"); Var("x")]
                ]
            ]
        ]
    ];

    let pair = tree![
        Abs;
        Var("x");
        #[
            Abs;
            Var("y");
            #[
                Abs;
                Var("f");
                #[
                    App;
                    #[
                        App;
                        Var("f");
                        Var("x");
                    ];
                    Var("y")
                ]
            ]
        ]
    ];

    let true_ = tree![
        Abs;
        Var("x");
        #[
            Abs;
            Var("y");
            Var("x")
        ]
    ];

    let false_ = tree![
        Abs;
        Var("x");
        #[
            Abs;
            Var("y");
            Var("y")
        ]
    ];

    let fst = tree![
        Abs;
        Var("p");
        #[
            App;
            Var("p");
            true_
        ]
    ];

    let snd = tree![
        Abs;
        Var("p");
        #[
            App;
            Var("p");
            false_
        ]
    ];

    let test = tree![
        App;
        #[
            App;
            #[
                App;
                compose;
                double;
            ];
            inc;
        ];
        #[
            App;
            fst;
            #[
                App;
                #[
                    App;
                    pair;
                    Int(5);
                ];
                Int(2)
            ]
        ]
    ];
    tree![EntryPoint; test.clone()]
        .save_svg("lambda.svg")
        .unwrap();
    tree![EntryPoint; test.clone()]
        .save_png("lambda.png")
        .unwrap();
    let ski = convert_to_ski(&test);
    tree![EntryPoint; ski.clone()].save_svg("ski.svg").unwrap();
    let optimized_ski = optimize_ski(&ski);
    tree![EntryPoint; optimized_ski.clone()]
        .save_svg("optimized_ski.svg")
        .unwrap();
    println!("Unoptimized SKI:");
    println_lambda(&ski);
    println!("Optimized result:");
    println_lambda(&optimized_ski);
    // println!();
    // println_lambda(&eval(&optimized_ski));

    // unsafe {COUNTER = 0;}
    // eval(&test);
    // println!("Counter: {}", unsafe { COUNTER });
    // unsafe {COUNTER = 0;}
    // eval(&ski);
    // println!("Counter: {}", unsafe { COUNTER });
    // unsafe {COUNTER = 0;}
    println!("---------------------------------");
    println!("Testing eval");
    println_lambda(&eval(&optimized_ski));
    println!("Testing eval2");
    println_lambda(&eval2(&test));
    println!("Testing eval_ski");
    // println_lambda(&eval_ski(&tree![
    //     App;
    //     #[
    //         App;
    //         #[
    //             App;
    //             Combinator(S);
    //             Combinator(K);
    //         ];
    //         Combinator(K);
    //     ];
    //     Int(5)
    // ]));
    println_lambda(&eval_ski(&optimized_ski));
    // println!("Counter: {}", unsafe { COUNTER });
}

fn unroll_applications<'a>(expr: &Expr<'a>) -> Expr<'a> {
    // Find applications with more than 2 children, and convert them to nested applications
    use Lambda::*;
    match expr.value() {
        App => {
            let mut children = expr.children().map(unroll_applications).collect::<Vec<_>>();
            let f = children.remove(0);
            let x = children.remove(0);

            let mut result = tree![App; f; x];
            for child in children.into_iter() {
                result = tree![App; result; child];
            }
            result
        }
        // For all other nodes, just recurse
        _ => {
            let mut expr = expr.clone();
            expr.children_mut().for_each(|subexpr| {
                *subexpr = unroll_applications(subexpr);
            });
            expr
        }
    }
}

fn roll_applications<'a>(expr: &Expr<'a>) -> Expr<'a> {
    // Find nested applications and convert them to flat applications
    use Lambda::*;
    match expr.value() {
        App if expr.children().count() == 2 => {
            if *expr[0].value() == App {
                let first = &expr[0];

                roll_applications(&tree![
                    App;
                    first[0].clone();
                    first[1].clone();
                    expr[1].clone()
                ])
            } else {
                let mut children = expr.children().map(roll_applications).collect::<Vec<_>>();
                let f = children.remove(0);
                let x = children.remove(0);
                // roll_applications(&tree![App; roll_applications(&f); roll_applications(&x)])
                tree![App; roll_applications(&f); roll_applications(&x)]
            }
        }

        // For all other nodes, just recurse
        _ => {
            let mut expr = expr.clone();
            expr.children_mut().for_each(|subexpr| {
                *subexpr = roll_applications(subexpr);
            });
            expr
        }
    }
}

fn optimize_ski<'a>(expr: &Expr<'a>) -> Expr<'a> {
    // Replace S (K K) with I
    let mut original = double_k_elimination(&s_distribution(&roll_applications(expr)));
    let mut test = double_k_elimination2(&s_distribution2(&roll_applications(expr)));
    println!("Original:");
    println_lambda(&original);
    println!("Test:");
    println_lambda(&test);
    assert_eq!(original, test);
    println!("---------------------------------");

    let mut expr = original;
    use Lambda::*;
    use SKI::*;
    expr.replace(
        &tree![
            App;
            Combinator(S);
            Combinator(K);
            Combinator(K);
        ],
        &tree![Combinator(I)],
    );
    expr.replace(
        &tree![
            App;
            Combinator(S);
            Combinator(I);
            Combinator(I);
        ],
        &tree![Combinator(I)],
    );
    expr.replace(
        &tree![
            App;
            Combinator(K);
            Combinator(K);
            Combinator(I);
        ],
        &tree![Combinator(K)],
    );
    expr.replace(
        &tree![
            App;
            Combinator(S);
            Combinator(K);
            #[
                App;
                Combinator(S);
                Combinator(K);
            ]
        ],
        &tree![Combinator(K)],
    );

    expr
}

/// S(Kx)(Ky) = K(x y)
fn s_distribution<'a>(expr: &Expr<'a>) -> Expr<'a> {
    expr.transform(&mut |e| {
        use Lambda::*;
        use SKI::*;
        match *e.value() {
            App => {
                if *e[0].value() != Combinator(S) {
                    return e.clone();
                }
                if *e[1].value() != App || *e[1][0].value() != Combinator(K) {
                    return e.clone();
                }
                if *e[2].value() != App || *e[2][0].value() != Combinator(K) {
                    return e.clone();
                }
                let x = e[1][1].clone();
                let y = e[2][1].clone();
                tree![App; Combinator(K); x; y]
            }
            _ => e.clone(),
        }
    })
}

fn s_distribution2<'a>(expr: &Expr<'a>) -> Expr<'a> {
    use Lambda::*;
    use SKI::*;
    // let pat = pattern![
    //     App;
    //     Combinator(S);
    //     #[
    //         App;
    //         Combinator(K);
    //         @x
    //     ];
    //     #[
    //         App;
    //         Combinator(K);
    //         @y
    //     ];
    // ];
    // let expr = expr.rewrite(&pat, |node, bindings| {
    //     println!("Found S(Kx)(Ky)");
    //     let x = bindings["x"].clone();
    //     let y = bindings["y"].clone();
    //     tree![App; Combinator(K); x; y]
    // });

    // expr.clone()

    rewrite!(
        expr.clone(),
        pattern![App; Combinator(S); #[App; Combinator(K); @x]; #[App; Combinator(K); @y]]
        => {
            println!("Found S(Kx)(Ky)");
            tree![App; Combinator(K); x.clone(); y.clone()]
        } using x, y
    )
}

// /// S(Sx)(Ky)(Kz) = Sx(yz)
// fn nested_s_simplification<'a>(expr: &Expr<'a>) -> Expr<'a> {
//     expr.map(|e| {
//         use Lambda::*;
//         use SKI::*;
//         match *e.value() {
//             App if e.children().count() == 4 => {
//                 if *e[0].value() != Combinator(S) {
//                     return e.clone();
//                 }
//                 if *e[1].value() != App || *e[1][0].value() != Combinator(S) {
//                     return e.clone();
//                 }
//                 if *e[2].value() != App || *e[2][0].value() != Combinator(K) {
//                     return e.clone();
//                 }
//                 if *e[3].value() != App || *e[3][0].value() != Combinator(K) {
//                     return e.clone();
//                 }
//                 let x = e[1][1].clone();
//                 let y = e[2][1].clone();
//                 let z = e[3][1].clone();
//                 tree![App; x; y; z]
//             }
//             _ => e.clone(),
//         }
//     })
// }

/// S(Kx)I = x
fn double_k_elimination<'a>(expr: &Expr<'a>) -> Expr<'a> {
    expr.transform(&mut |e| {
        use Lambda::*;
        use SKI::*;
        match *e.value() {
            App if e.children().count() == 3 => {
                if *e[0].value() != Combinator(S) {
                    return e.clone();
                }
                if *e[1].value() != App || *e[1][0].value() != Combinator(K) {
                    return e.clone();
                }
                if *e[2].value() != Combinator(I) {
                    return e.clone();
                }
                let x = e[1][1].clone();
                println!("(Original) Found S(Kx)I: {x}");
                x
            }
            _ => e.clone(),
        }
    })
}

fn double_k_elimination2<'a>(expr: &Expr<'a>) -> Expr<'a> {
    use Lambda::*;
    use SKI::*;

    // let pat = pattern![
    //     App;
    //     Combinator(S);
    //     #[App; Combinator(K); @x];
    //     Combinator(I);
    // ];
    // expr.rewrite(&pat, |node, bindings| {
    //     println!("Found S(Kx)I");
    //     bindings["x"].clone()
    // })

    rewrite!(
        expr.clone(),
        pattern![App; Combinator(S); #[App; Combinator(K); @x]; Combinator(I)]
        => {
            println!("(Test) Found S(Kx)I: {x}");
            x.clone()
        } using x
    )
}

fn convert_to_ski<'a>(expr: &Expr<'a>) -> Expr<'a> {
    use Lambda::*;
    let expr = unroll_applications(expr);
    match expr.value() {
        // Convert all children of an application (f a b ...) into SKI:
        App => {
            // Convert each child into SKI, then rebuild the application node
            let converted_children: Vec<Expr<'a>> = expr.children().map(convert_to_ski).collect();
            make_app_chain(&converted_children)
        }

        // If you have a multi-argument abstraction:
        // (Abs; var1; var2; ...; body), treat it as nested λ.
        Abs => {
            let children: Vec<_> = expr.children().cloned().collect();
            // If there are at least 2 children: [var1, var2, ..., body]
            // we treat that as λ var1. λ var2. ... body
            if children.len() < 2 {
                // Malformed expression: Abs node with fewer than 2 children
                // but for safety, return as is
                expr.clone()
            } else {
                // If there are multiple vars, fold them left into nested single λ
                // e.g. λx y. E => λx. (λy. E)
                let mut current = children.last().unwrap().clone();
                // Go from right to left for the parameters
                for param in children[..children.len() - 1].iter().rev() {
                    current = convert_single_lambda(param, &current);
                }
                // Now we've made the fully transformed body
                // Then we need to do a top-level conversion on that expression
                convert_to_ski(&current)
            }
        }

        // If your AST allows `Let`, you might want to handle it
        // by recursively converting the body and the bound expressions.
        Let => {
            // The same approach as your normal Let evaluation, but call convert_to_ski
            // on each bound expression and on the final body
            let children: Vec<Expr<'a>> = expr.children().cloned().collect::<Vec<_>>();
            if children.is_empty() {
                return expr.clone();
            }

            let mut new_body = children.last().unwrap().clone();
            let bindings = &children[..children.len() - 1];

            // We do a “syntactic” transform: for each binding, replace
            // every occurrence of `var` in `body` with the SKI conversion of `value`.
            for binding in bindings {
                let var_expr = binding.clone().prune();
                let val_expr = binding[0].clone();
                let converted_val = convert_to_ski(&val_expr);
                new_body = replace_var(&new_body, &var_expr, &converted_val);
            }

            convert_to_ski(&new_body)
        }

        // For variables, builtins, booleans, integers, etc., just keep them.
        _ => expr.clone(),
    }
}

/// Convert λ(var). body into SKI form *without* peeling off additional lambdas.
/// This function presupposes that `body` hasn't already been run through
/// the top-level convert_to_ski, or you'll get double transformation of abstractions.
fn convert_single_lambda<'a>(var_expr: &Expr<'a>, body: &Expr<'a>) -> Expr<'a> {
    use crate::SKI::*;
    use Lambda::*;
    if let Lambda::Abs = body.value() {
        // If the body is a lambda, recursively convert it
        let converted_body = convert_to_ski(body);
        return convert_single_lambda(var_expr, &converted_body);
    }

    // We assume var_expr is literally `Var("x")`.
    // If it's not, handle gracefully.
    let Lambda::Var(var_name) = var_expr.value() else {
        // Fallback; if you have an unexpected pattern, just do K-body
        let converted_body = convert_to_ski(body);
        return make_app_chain(&[tree![Combinator(K)], converted_body]);
    };

    // 1) If body = x, then λx.x => I
    if let Lambda::Var(body_var_name) = body.value() {
        if body_var_name == var_name {
            return tree![Combinator(I)];
        }
    }

    // 2) If x is not used in body => K ( convert(body) )
    if !is_var_used(Var(var_name), body) {
        let converted_body = convert_to_ski(body);
        return make_app_chain(&[tree![Combinator(K)], converted_body]);
    }

    // 3) If body is an application, say (App; A; B), do S (λx.A) (λx.B)
    if body.value() == &App && body.children().count() == 2 {
        let mut children = body.children();
        let a = children.next().unwrap();
        let b = children.next().unwrap();

        // Recursively define λx.A => convert_single_lambda(var, A)
        let lambda_a = convert_single_lambda(var_expr, a);
        let lambda_b = convert_single_lambda(var_expr, b);

        return make_app_chain(&[tree![Combinator(S)], lambda_a, lambda_b]);
    }

    // 4) Otherwise => S (K (convert(body))) I
    let converted_body = convert_to_ski(body);
    make_app_chain(&[
        tree![Combinator(S)],
        make_app_chain(&[tree![Combinator(K)], converted_body]),
        tree![Combinator(I)],
    ])
}

/// Rebuild a chain of `App` nodes from a list of expressions:
/// [e0, e1, e2] => App(App(e0, e1), e2)
fn make_app_chain<'a>(exprs: &[Expr<'a>]) -> Expr<'a> {
    use Lambda::App;
    assert!(!exprs.is_empty());
    let mut iter = exprs.iter();
    let mut current = iter.next().unwrap().clone();
    for next_expr in iter {
        current = tree![App; current; next_expr.clone()];
    }
    current
}

/// Syntactically replace occurrences of one variable expression with another expression.
fn replace_var<'a>(body: &Expr<'a>, var_expr: &Expr<'a>, val_expr: &Expr<'a>) -> Expr<'a> {
    // If your code already has a function to do variable substitution,
    // you can reuse it. Otherwise, do something like:
    use Lambda::*;
    let Lambda::Var(var_name) = var_expr.value() else {
        return body.clone();
    };

    // We'll do a full tree walk:
    let mut new_tree = body.clone();
    for node in new_tree.iter_mut() {
        // If we see Var(var_name), replace with val_expr
        match node {
            Var(x) if x == var_name => {
                *node = val_expr.value().clone();
            }
            _ => {}
        }
    }
    new_tree
}
