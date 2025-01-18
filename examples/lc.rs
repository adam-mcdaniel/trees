use trees::*;
use std::fmt::{Display, Formatter, Result as FmtResult};

type Expr<'a> = Tree<Lambda<'a>>;

#[derive(Debug, Clone, Copy, PartialEq)]
enum Lambda<'a> {
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
            Self::Var(s) => write!(f, "{}", s),
            Self::Let => write!(f, "let"),
            Self::Abs => write!(f, "λ"),
            Self::App => write!(f, "•"),
            Self::Int(n) => write!(f, "{}", n),
            Self::Float(n) => write!(f, "{}", n),
            Self::Bool(b) => write!(f, "{}", b),
            Self::Nil => write!(f, "nil"),
            Self::Builtin(name, args, _) => write!(f, "<builtin {name}, {args} args>"),
            Self::Combinator(atom) => write!(f, "{:?}", atom),
        }
    }
}

fn eval<'a>(expr: &Expr<'a>) -> Expr<'a> {
    use Lambda::*;
    use SKI::*;
    // println!("Evaluating: {}", expr);
    match expr.value() {
        Lambda::App => {
            let mut args = expr.children().map(eval).collect::<Vec<_>>();
            let func = args.remove(0);

            match func.value() {
                Lambda::Builtin(_, args_count, f) => {
                    if args.len() < *args_count {
                        return expr.clone();
                    }
                    f(&args)
                }
                Lambda::Combinator(S) => {
                    if args.len() < 3 {
                        return expr.clone();
                    }
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
                Lambda::Combinator(K) => {
                    if args.len() < 2 {
                        return expr.clone();
                    }
                    let x = args.remove(0);
                    let _y = args.remove(0);
                    let mut result = x;
                    if args.len() != 0 {
                        result = tree![App; result];
                        result.add_children(args);
                    }
                    eval(&result)
                }
                Lambda::Combinator(I) => {
                    if args.len() < 1 {
                        return expr.clone();
                    }
                    let x = args.remove(0);
                    let mut result = x;
                    if args.len() != 0 {
                        result = tree![App; result];
                        result.add_children(args);
                    }
                    eval(&result)
                }

                Int(_) | Float(_) | Bool(_) | Nil => func.clone(),
                _ => {
                    // Get all except the last child for the params
                    let params = func.children().take(func.children().count() - 1);
                    // Get the last child for the body
                    let body = func.children().last().unwrap();
                    let mut new_body = body.clone();
                    for (param, arg) in params.zip(&args) {
                        new_body.replace(param, arg);
                    }
                    eval(&new_body)
                }
            }
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
    }
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
    use SKI::*;
    expr.iter().all(|atom| match atom {
        Var(_) | Abs => false,
        _ => true,
    })
}

fn main() {
    use Lambda::*;
    let inc = Lambda::Builtin("inc", 1, |args: &[Expr]| {
        let arg = args[0].value();
        match arg {
            Int(n) => tree![Int(n + 1)],
            _ => panic!("Expected int, got {}", arg),
        }
    });

    let mul = Lambda::Builtin("mul", 2, |args: &[Expr]| {
        let arg1 = args[0].value();
        let arg2 = args[1].value();
        match (arg1, arg2) {
            (Int(n1), Int(n2)) => tree![Int(n1 * n2)],
            _ => panic!("Expected int, got {} and {}", arg1, arg2),
        }
    });

    let before: Expr = tree![
        App;
        inc;
        Int(5)
    ];

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
    println!("{}", compose);
    println!("Conversion:");
    println!("{}", convert_to_ski(&compose));
    // println!("{}", eval(&convert_to_ski(&compose)));

    // Use mul to create double
    let double = tree![
        Abs;
        Var("x");
        #[App; mul; Int(2); Var("x")]
    ];

    use SKI::*;
    // let expr = tree![
    //     App;
    //     Combinator(S);
    //     Combinator(K);
    //     Combinator(K);
    //     inc.clone();
    //     Int(5)
    // ];
    // let expr = convert_to_ski(&tree![
    //     App;
    //     compose.clone();
    //     double.clone();
    //     inc.clone();
    //     Int(5)
    // ]);
    let lam_expr = tree![
            Abs;
            Var("x");
            #[App;
                Var("x");
                Int(42)
            ]
    ];
    // println!("{}", eval(&lam_expr));
    // println!("{}", eval(&convert_to_ski(&lam_expr)));

    // let after = eval(&before);
    // println!("{}", after);
    let program = tree![
        Let;
        #[Var("compose"); compose];
        #[Var("double"); double];
        #[Var("inc"); inc];
        #[
            App;
            Var("compose");
            Var("double");
            Var("inc");
            Int(5)
        ]
    ];

    println!("{}", eval(&program));
    // println!("{}", eval(&convert_to_ski(&program)));

    program.save_svg("lc.svg").unwrap();
}

fn convert_to_ski<'a>(expr: &Expr<'a>) -> Expr<'a> {
    use Lambda::*;
    match expr.value() {
        // For variables, builtins, booleans, integers, etc., just keep them.
        Var(_) | Builtin(_, _, _) | Combinator(_) | Bool(_) | Int(_) | Float(_) | Nil => {
            expr.clone()
        }

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
    }
}

/// Convert λ(var). body into SKI form *without* peeling off additional lambdas.
/// This function presupposes that `body` hasn't already been run through
/// the top-level convert_to_ski, or you'll get double transformation of abstractions.
fn convert_single_lambda<'a>(var_expr: &Expr<'a>, body: &Expr<'a>) -> Expr<'a> {
    use Lambda::*;
    // We assume var_expr is literally `Var("x")`.
    // If it's not, handle gracefully.
    let Lambda::Var(var_name) = var_expr.value() else {
        // Fallback; if you have an unexpected pattern, just do K-body
        let converted_body = convert_to_ski(body);
        return make_app_chain(&[tree![Combinator(SKI::K)], converted_body]);
    };

    // 1) If body = x, then λx.x => I
    if let Lambda::Var(body_var_name) = body.value() {
        if body_var_name == var_name {
            return tree![Combinator(SKI::I)];
        }
    }

    // 2) If x is not used in body => K ( convert(body) )
    if !is_var_used(Var(var_name), body) {
        let converted_body = convert_to_ski(body);
        return make_app_chain(&[tree![Combinator(SKI::K)], converted_body]);
    }

    // 3) If body is an application, say (App; A; B), do S (λx.A) (λx.B)
    if body.value() == &App && body.children().count() == 2 {
        let mut children = body.children();
        let a = children.next().unwrap();
        let b = children.next().unwrap();

        // Recursively define λx.A => convert_single_lambda(var, A)
        let lambda_a = convert_single_lambda(var_expr, a);
        let lambda_b = convert_single_lambda(var_expr, b);

        return make_app_chain(&[tree![Combinator(SKI::S)], lambda_a, lambda_b]);
    }

    // 4) Otherwise => S (K (convert(body))) I
    let converted_body = convert_to_ski(body);
    make_app_chain(&[
        tree![Combinator(SKI::S)],
        make_app_chain(&[tree![Combinator(SKI::K)], converted_body]),
        tree![Combinator(SKI::I)],
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

// fn convert(lam: Expr) -> Expr {
//     if is_converted(&lam) {
//         return lam;
//     }
//     println!("Converting: {}", lam);
//     use Lambda::*;
//     use SKI::*;
//     match lam.value() {
//         Abs => {
//             // If the lambda is an abstraction, gather all but the last child as the parameters
//             // and the last child as the body.
//             let vars = lam
//                 .children()
//                 .take(lam.children().count() - 1)
//                 .collect::<Vec<_>>();
//             let body = lam.children().last().unwrap().clone();

//             // Base: convert the body first (though our helper also does `convert`, but this is OK).
//             let mut result = convert(body);

//             // Each `Var(...)` in `vars` is an argument. We apply them from right to left:
//             for var_expr in vars.into_iter().rev() {
//                 match var_expr.value() {
//                     Var(vname) => {
//                         result = lambda_to_ski(vname, result);
//                     }
//                     _ => panic!("Expected a variable in lambda parameters, found: {:?}", var_expr),
//                 }
//             }

//             result
//         }
//         App => {
//             // If the lambda is an application, convert each child
//             let children = lam.children().cloned().map(convert).collect::<Vec<_>>();
//             let mut result = Tree::new(App);
//             for child in children {
//                 result.add_child(child);
//             }
//             result
//         }
//         Let => {
//             // For `let`, we also recursively convert the bound expressions
//             let mut children = lam.children().collect::<Vec<_>>();
//             let mut new_body = children.pop().unwrap().clone();

//             for binding in children {
//                 let var = binding.clone().prune();
//                 let val = binding[0].clone();
//                 new_body.replace(&var, &convert(val));
//             }

//             convert(new_body)
//         }
//         // Base cases: numbers, floats, booleans, variables, etc. remain as-is.
//         Nil | Float(_) | Int(_) | Var(_) | Combinator(_) | Bool(_) | Builtin(..) => lam,
//     }
// }

// fn lambda_to_ski<'a>(var: &'a str, body: Expr<'a>) -> Expr<'a> {
//     use Lambda::*;
//     use SKI::*;

//     // First, fully convert the body (important if there are nested lambdas).
//     let body = convert(body);

//     // 1. If the body is just the variable `x`, that's `I`.
//     if let Var(name) = body.value() {
//         if *name == var {
//             return tree![Combinator(I)];
//         }
//     }

//     // 2. If `var` is not used in the body, use `K body`.
//     if !is_var_used(Var(var), &body) {
//         return tree![App; Combinator(K); body];
//     }

//     // 3. If the body is an application, apply the S rule:
//     //    λx. (M N) => S (λx. M) (λx. N).
//     if let Lambda::App = body.value() {
//         // Collect children. If there are more than 2, treat them left-associatively
//         // as ( (f x) y ), etc.
//         let children = body.children().collect::<Vec<_>>();
//         if children.len() == 2 {
//             // Exactly 2 children: M, N
//             let m = children[0].clone();
//             let n = children[1].clone();
//             let mut s_node = tree![App; Combinator(S)];
//             s_node.add_child(lambda_to_ski(var, m));
//             s_node.add_child(lambda_to_ski(var, n));
//             return s_node;
//         } else if children.len() > 2 {
//             // If you have something like (f x y), interpret it as ((f x) y).
//             // You can convert them pairwise. A simple approach is to fold from the left.
//             let mut iter = children.into_iter();
//             let first = iter.next().unwrap();
//             let second = iter.next().unwrap();
//             // Start with converting λx. (first second)
//             let mut partial = {
//                 let mut tmp_app = tree![App];
//                 tmp_app.add_child(first.clone());
//                 tmp_app.add_child(second.clone());
//                 lambda_to_ski(var, tmp_app)
//             };
//             // Then fold the rest
//             for child in iter {
//                 let mut tmp_app = tree![App];
//                 tmp_app.add_child(partial);
//                 tmp_app.add_child(child.clone());
//                 partial = lambda_to_ski(var, tmp_app);
//             }
//             return partial;
//         }
//     }

//     // 4. If the body is not an application, but `x` is used somewhere inside:
//     //    λx. M => S( λx. M ) (K I )
//     //    This ensures we still handle the presence of x in M, but M is not an App.
//     let s_node = tree![
//         App;
//         Combinator(S);
//         // #[Abs; Var(var); body];
//         lambda_to_ski(var, body);
//         #[App; Combinator(K); Combinator(I)]
//     ];

//     // let mut s_node = tree![Combinator(S)];
//     // // left = convert(λx. body) => we rec call in case there's a partial
//     // s_node.add_child(lambda_to_ski(var, body));
//     // // right = K I
//     // let mut k_node = tree![Combinator(K)];
//     // k_node.add_child(tree![Combinator(I)]);
//     // s_node.add_child(k_node);

//     s_node
// }
