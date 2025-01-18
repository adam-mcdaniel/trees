use crate::{tree, Tree};
use graph::Graph;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::{
    collections::HashMap,
    io::{Read, Write},
    sync::Arc,
};

type Predicate<T> = dyn Fn(&T) -> bool;

#[derive(Clone)]
pub enum PatternParam<T> {
    Wildcard,
    Value(T),
    Variable(String),
    Alt(Vec<PatternParam<T>>),
    Complement(Box<PatternParam<T>>),
    Predicate(Arc<Predicate<T>>),
    PredicateVar(String, Arc<Predicate<T>>),
    DotDotDot,
}

impl<T> PatternParam<T> {
    pub fn alt(patterns: impl IntoIterator<Item = PatternParam<T>>) -> Self {
        PatternParam::Alt(patterns.into_iter().collect())
    }

    pub fn var(name: impl ToString) -> Self {
        PatternParam::Variable(name.to_string())
    }

    pub fn not(self) -> Self {
        PatternParam::Complement(Box::new(self))
    }

    pub fn pred(predicate: impl Fn(&T) -> bool + 'static) -> Self {
        PatternParam::Predicate(Arc::new(predicate))
    }

    pub fn pred_var(name: impl ToString, predicate: impl Fn(&T) -> bool + 'static) -> Self {
        PatternParam::PredicateVar(name.to_string(), Arc::new(predicate))
    }
}

impl<T> From<T> for PatternParam<T> {
    fn from(value: T) -> Self {
        PatternParam::Value(value)
    }
}

pub trait PatternMatch<T>
where
    T: PartialEq + Clone,
{
    fn rewrite(
        &self,
        pattern: &Pattern<T>,
        transform: impl FnMut(&Tree<T>, &HashMap<String, Tree<T>>) -> Tree<T>,
        limit: Option<usize>,
    ) -> Tree<T>;
    fn map_pattern(
        &self,
        pattern: &Pattern<T>,
        transform: impl FnMut(&Tree<T>, &HashMap<String, Tree<T>>),
        limit: Option<usize>,
    );
    fn does_match_pattern(&self, pattern: &Pattern<T>) -> bool;
    fn graphviz_matches(&self, pattern: &Pattern<T>) -> Graph where T: Display;
    fn to_svg_matches(&self, pattern: &Pattern<T>) -> Result<String, std::io::Error> where T: Display {
        let dot = self.graphviz_matches(pattern).to_dot();
        // Use the `dot` command to convert the DOT code to SVG
        let process = std::process::Command::new("dot")
            .arg("-Tsvg")
            .arg("-o")
            .arg("/dev/stdout")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .expect("Failed to execute dot");

        process
            .stdin
            .expect("Failed to open stdin")
            .write_all(dot.as_bytes())
            .expect("Failed to write to stdin");

        let mut svg = String::new();
        process
            .stdout
            .expect("Failed to open stdout")
            .read_to_string(&mut svg)
            .expect("Failed to read from stdout");

        Ok(svg)
    }

    fn save_svg_matches(&self, pattern: &Pattern<T>, path: &str) -> Result<(), std::io::Error> where T: Display {
        let svg = self.to_svg_matches(pattern)?;
        std::fs::write(path, svg)
    }

    fn save_graphviz_matches(
        &self,
        pattern: &Pattern<T>,
        path: &str,
    ) -> Result<(), std::io::Error> where T: Display {
        let dot = self.graphviz_matches(pattern).to_dot();
        std::fs::write(path, dot)
    }
}

fn rewrite_helper<T>(
    value: &Tree<T>,
    pattern: &Pattern<T>,
    transform: &mut impl FnMut(&Tree<T>, &HashMap<String, Tree<T>>) -> Tree<T>,
    limit: Option<usize>,
    count: &mut usize,
) -> Tree<T>
where
    T: PartialEq + Clone,
{

    let mut bindings = HashMap::new();
    let mut new_tree = value.clone();

    new_tree.children_mut().for_each(|child| {
        *child = rewrite_helper(child, pattern, transform, limit, count);
    });
    if let Some(limit) = limit {
        if *count >= limit {
            return new_tree;
        }
    }
    if match_pattern_internal(pattern, &new_tree, &mut bindings, &mut 0) {
        *count += 1;
        transform(&new_tree, &bindings)
    } else {
        new_tree
    }
}

fn map_helper<T>(
    value: &Tree<T>,
    pattern: &Pattern<T>,
    transform: &mut impl FnMut(&Tree<T>, &HashMap<String, Tree<T>>),
    limit: Option<usize>,
    count: &mut usize,
)
where
    T: PartialEq + Clone,
{
    if let Some(limit) = limit {
        if *count >= limit {
            return;
        }
    }

    let mut bindings = HashMap::new();

    value.children().for_each(|child| {
        map_helper(child, pattern, transform, limit, count);
    });
    if match_pattern_internal(pattern, value, &mut bindings, &mut 0) {
        *count += 1;
        transform(value, &bindings)
    }
}

impl<T> PatternMatch<T> for Tree<T>
where
    T: PartialEq + Clone + Debug,
{
    fn rewrite(
        &self,
        pattern: &Pattern<T>,
        mut transform: impl FnMut(&Tree<T>, &HashMap<String, Tree<T>>) -> Tree<T>,
        limit: Option<usize>,
    ) -> Tree<T> {
        rewrite_helper(self, pattern, &mut transform, limit, &mut 0)
    }

    fn map_pattern(
        &self,
        pattern: &Pattern<T>,
        mut transform: impl FnMut(&Tree<T>, &HashMap<String, Tree<T>>),
        limit: Option<usize>,
    ) {
        map_helper(self, pattern, &mut transform, limit, &mut 0)
    }

    fn does_match_pattern(&self, pattern: &Pattern<T>) -> bool {
        does_match_pattern(pattern, self)
    }

    fn graphviz_matches(&self, pattern: &Pattern<T>) -> Graph where T: Display {
        let mut graph = Graph::new();
        self.to_graph(&mut graph, &mut 0);

        // Now, go through all the nodes and see if they match the pattern
        let mut id = 0;
        {
            self.transform(&mut |node| {
                // If the node matches the pattern, highlight it
                if does_match_pattern(pattern, &node) {
                    if let Some(props) = graph.get_node_properties_mut(id) {
                        props.set("color", "lightblue");   // Highlight the node
                        props.set("style", "filled"); // Fill the node
                    }
                }
                id+=1;
                node
            });
        }
        graph
    }

    /*
    fn find_pattern<'a, 'b>(&'a self, pattern: &'b Pattern<T>) -> impl Iterator<Item=(HashMap<String, &'a Tree<T>>, Vec<&'a Tree<T>>)> where T: 'a {
        struct FindPatternIter<'a, 'b, T> where T: PartialEq + Clone {
            stack: Vec<(&'a Tree<T>, HashMap<String, &'a Tree<T>>)>,
            pattern: &'b Pattern<T>,
        }

        impl<'a, 'b, T> Iterator for FindPatternIter<'a, 'b, T> where T: PartialEq + Clone {
            type Item = (HashMap<String, &'a Tree<T>>, Vec<&'a Tree<T>>);

            fn next(&mut self) -> Option<Self::Item> {
                while let Some((node, mut bindings)) = self.stack.pop() {
                    if let Some((new_bindings, remaining)) = node.match_pattern(self.pattern) {
                        bindings.extend(new_bindings);
                        self.stack.push((node, bindings.clone()));
                        self.stack.extend(remaining.clone().into_iter().map(|node| (node, bindings.clone())));
                        return Some((bindings, remaining));
                    }
                }

                None
            }
        }

        let mut stack = Vec::new();
        stack.push((self, HashMap::new()));
        FindPatternIter::<'a, 'b, T> { stack, pattern }
    }

    fn match_pattern(&self, pattern: &Pattern<T>) -> Option<(HashMap<String, &Tree<T>>, Vec<&Tree<T>>)> {
        match_pattern(pattern, self)
    }
    */
}

type Pattern<T> = Tree<PatternParam<T>>;

fn match_pattern<'a, T>(
    pattern: &Pattern<T>,
    value: &'a Tree<T>,
) -> Option<HashMap<String, Tree<T>>>
where
    T: PartialEq + Clone,
{
    let mut bindings = HashMap::new();
    if match_pattern_internal(pattern, value, &mut bindings, &mut 0) {
        Some(bindings)
    } else {
        None
    }
}

fn does_match_pattern<T>(pattern: &Pattern<T>, value: &Tree<T>) -> bool
where
    T: PartialEq + Clone,
{
    let mut bindings = HashMap::new();
    match_pattern_internal(pattern, value, &mut bindings, &mut 0)
}

fn match_pattern_internal<'a, T>(
    pattern: &Pattern<T>,
    value: &'a Tree<T>,
    bindings: &mut HashMap<String, Tree<T>>,
    dot_depth: &mut usize,
) -> bool
where
    T: PartialEq + Clone,
{
    let matches_root = match (pattern.value(), value.value()) {
        (PatternParam::Wildcard, _) => true,
        (PatternParam::Value(p), v) => p == v,
        (PatternParam::Variable(name), _) => {
            bindings.insert(name.clone(), value.clone());
            true
        }
        (PatternParam::Alt(pats), v) => {
            // Create a new tree from the pattern
            let mut new_pattern = pattern.clone();
            for pat in pats {
                new_pattern.set_value(pat.clone());
                if match_pattern_internal(&new_pattern, value, bindings, dot_depth) {
                    return true;
                }
            }
            false
        }
        (PatternParam::Complement(pat), v) => {
            let mut new_pattern = pattern.clone();
            new_pattern.set_value(*pat.clone());
            !match_pattern_internal(&new_pattern, value, bindings, dot_depth)
        }
        (PatternParam::Predicate(pred), v) => pred(v),
        (PatternParam::PredicateVar(name, pred), v) => {
            bindings.insert(name.clone(), value.clone());
            pred(v)
        }
        (PatternParam::DotDotDot, _) => true,
    };

    if !matches_root {
        return false;
    }

    if pattern.children().count() != value.children().count() {
        // if !matches!(pattern.value(), PatternParam::Variable(_) | PatternParam::Wildcard) {
        //     // Check if the last pattern is a DotDotDot
        //     if let Some(last_pattern) = pattern.children().last() {
        //         if !matches!(*last_pattern.value(), PatternParam::DotDotDot) {
        //             // println!("Different number of children");
        //             return false;
        //         }
        //     } else {
        //         // println!("No last pattern: {} != {}", pattern.children().count(), value.children().count());
        //         return false;
        //     }
        // }

        // println!("Different number of children: {} != {}", pattern.children().count(), value.children().count());
        // println!("Pattern: {}", pattern);
        // println!("Value: {}", value);
        if !matches!(
            pattern.value(),
            PatternParam::Variable(_) | PatternParam::Wildcard | PatternParam::DotDotDot
        ) {
            // Check that the value is at MOST one fewer than the pattern
            if pattern.children().count() > value.children().count() + 1 {
                // println!("Too many children: {} != {}", pattern.children().count(), value.children().count());
                return false;
            }

            if pattern.children().count() > value.children().count()
                && !matches!(
                    pattern.children().last().map(|x| x.value()),
                    Some(PatternParam::DotDotDot)
                )
            {
                // println!("hmm");
                return false;
            }

            if pattern.children().count() < value.children().count()
                && !matches!(
                    pattern.children().last().map(|x| x.value()),
                    Some(PatternParam::DotDotDot)
                )
            {
                // println!("Too few children: {} != {}", pattern.children().count(), value.children().count());
                return false;
            }
        }

        // if let Some(last_pattern) = pattern.children().last() {
        //     if !matches!(*last_pattern.value(), PatternParam::DotDotDot) {
        //         // println!("Different number of children");
        //         return false;
        //     }
        // } else {
        //     // println!("No last pattern: {} != {}", pattern.children().count(), value.children().count());
        //     return false;
        // }
    }

    // Check children
    let pattern_children = pattern.children();
    let value_children = value.children();
    *dot_depth += 1;
    for (pattern_child, value_child) in pattern_children.zip(value_children) {
        if let PatternParam::DotDotDot = *pattern_child.value() {
            let value = tree![value_child.value().clone()]
                .with_children(value.children().cloned().skip(pattern.len() - 1));

            let mut dots = String::from(".");
            for _ in 0..*dot_depth {
                dots.push('.');
            }
            bindings.insert(dots, value.clone());

            let mut dots = String::from("dot");
            for _ in 0..*dot_depth {
                dots.push_str("dot");
            }
            bindings.insert(dots, value);
            break;
        }
        if !match_pattern_internal(pattern_child, value_child, bindings, dot_depth) {
            *dot_depth -= 1;
            return false;
        }
    }
    *dot_depth -= 1;

    true
}

impl<T> Display for PatternParam<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            PatternParam::Wildcard => write!(f, "_"),
            PatternParam::Value(value) => write!(f, "{}", value),
            PatternParam::Variable(name) => write!(f, "ref {}", name),
            PatternParam::Alt(pats) => {
                write!(f, "(")?;
                for (i, pat) in pats.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{}", pat)?;
                }
                write!(f, ")")
            }
            PatternParam::Predicate(..) => write!(f, "<predicate>"),
            PatternParam::PredicateVar(var, ..) => write!(f, "ref {var} if <predicate>"),
            PatternParam::Complement(pat) => write!(f, "!{}", pat),
            PatternParam::DotDotDot => write!(f, ".."),
        }
    }
}

impl<T> Debug for PatternParam<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            PatternParam::Wildcard => write!(f, "_"),
            PatternParam::Value(value) => write!(f, "{:?}", value),
            PatternParam::Variable(name) => write!(f, "ref {}", name),
            PatternParam::Alt(pats) => {
                write!(f, "(")?;
                for (i, pat) in pats.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{:?}", pat)?;
                }
                write!(f, ")")
            }
            PatternParam::Predicate(..) => write!(f, "<predicate>"),
            PatternParam::PredicateVar(var, ..) => write!(f, "ref {var} if <predicate>"),
            PatternParam::Complement(pat) => write!(f, "!{:?}", pat),
            PatternParam::DotDotDot => write!(f, ".."),
        }
    }
}

#[macro_export]
macro_rules! dotdot {
    () => {
        PatternParam::DotDotDot
    };
}

#[macro_export]
macro_rules! var {
    ($name:expr) => {
        PatternParam::Variable($name.to_string())
    };
}

#[macro_export]
macro_rules! pat_child {
    (@var $name:expr) => {
        PatternParam::Variable($name.to_string())
    };
    (@alt $($pat:expr),*) => {
        PatternParam::Alt(vec![$($pat.into()),*])
    };
    (@dotdot) => {
        PatternParam::DotDotDot
    };
    (@val $pat:expr) => {
        PatternParam::Value($pat)
    };
    (@not $($pat:tt)*) => {
        PatternParam::Complement(Box::new(pat_child![$($pat)*]))
    };
    (@pred $name:ident, $ty:ty, $pred:expr) => {
        PatternParam::pred_var(stringify!($name), move |$name: $ty| $pred)
    };
    (@pred $name:ident, $pred:expr) => {
        PatternParam::pred_var(stringify!($name), move |$name| $pred)
    };
}

#[macro_export]
macro_rules! alt {
    ($($pat:expr),*) => {
        PatternParam::Alt(vec![$($pat.into()),*])
    };
}

#[macro_export]
macro_rules! not {
    ($pat:expr) => {
        PatternParam::Complement(Box::new($pat))
    };
}

#[macro_export]
macro_rules! pattern {
    // --- Entry points ----------------------------------------------------

    // (not($($pat:expr)*); $($rest:tt)*) => {{
    //     let inner = pattern!($($pat)*);
    //     let mut t = Tree::from(inner.value().clone().not());
    //     pattern!(%parse_children t, $($rest)*);
    //     t
    // }};

    // (alt($($pat:expr),*); $($rest:tt)*) => {{
    //     let mut t = Tree::from(pat_child!(@alt $($pat),*));
    //     pattern!(%parse_children t, $($rest)*);
    //     t
    // }};

    (..; $($rest:tt)*) => {{
        let mut t = Tree::new(pat_child!(@dotdot));
        pattern!(%parse_children t, $($rest)*);
        t
    }};
    (..) => {
        tree![PatternParam::DotDotDot]
    };

    // A predicate pattern
    (@$name:ident if $pred:expr, where $name2:ident : $ty:ty; $($rest:tt)*) => {{
        // Create a function from the arg and body
        // assert_eq!(stringify!($name), stringify!($name2));
        // Compile time assert:
        let a = stringify!($name);
        let b = stringify!($name2);
        assert_eq!(a, b, "Variable names must match: {} != {}", a, b);

        let mut t = Tree::new(pat_child!(@pred $name, $ty, $pred));
        pattern!(%parse_children t, $($rest)*);
        t
    }};

    // A predicate pattern
    (@$name:ident if $pred:expr, where $name2:ident : $ty:ty) => {{
        // Create a function from the arg and body
        // Tree::new(pat_child!(@pred $name, $ty, $pred))
        let a = stringify!($name);
        let b = stringify!($name2);
        assert_eq!(a, b, "Variable names must match: {} != {}", a, b);

        Tree::new(pat_child!(@pred $name, $ty, $pred))
    }};

    // A predicate pattern
    (@$name:ident if $pred:expr; $($rest:tt)*) => {{
        // Create a function from the arg and body
        let f = |$name| $pred;
        let mut t = Tree::new(pat_child!(@pred $name, $pred));
        pattern!(%parse_children t, $($rest)*);
        t
    }};

    // A predicate pattern
    (@$name:ident if $pred:expr) => {{
        // Create a function from the arg and body
        Tree::new(pat_child!(@pred $name, $pred))
    }};



    // Expression with children
    ($value:expr; $($rest:tt)*) => {{
        let mut t = Tree::new(PatternParam::from($value));
        pattern!(%parse_children t, $($rest)*);
        t
    }};
    ($value:expr) => {
        Tree::new(PatternParam::from($value))
    };

    (@$name:ident; $($rest:tt)*) => {
        let mut t = Tree::new(pat_child!(@var stringify!($name)));
        pattern![%parse_children t, $($rest)*];
        t
    };
    (@$name:ident) => {
        tree![pat_child!(@var stringify!($name))]
    };

    // --- Internal rules for parsing children -----------------------------

    // No more children
    (%parse_children $tree:ident) => {};
    (%parse_children $tree:ident,) => {};



    // A nested child subtree: looks like #[ child_root ; child2 ; child3 ; ... ]
    (%parse_children $tree:ident, #[ $($subtree:tt)* ]; $($rest:tt)*) => {{
        $tree.add_child(pattern!($($subtree)*));
        pattern!(%parse_children $tree, $($rest)*);
    }};
    // Same, but no trailing semicolon
    (%parse_children $tree:ident, #[ $($subtree:tt)* ]) => {{
        $tree.add_child(pattern!($($subtree)*));
    }};

    // A single child expression with trailing siblings
    (%parse_children $tree:ident, @$name:ident if $pred:expr; $($rest:tt)*) => {{
        $tree.add_child(tree![pat_child!(@pred $name, $pred)]);
        pattern!(%parse_children $tree, $($rest)*);
    }};

    // A single child expression without trailing siblings
    (%parse_children $tree:ident, @$name:ident if $pred:expr) => {{
        $tree.add_child(tree![pat_child!(@pred $name, $pred)]);
    }};

    // A single child expression with trailing siblings
    (%parse_children $tree:ident, @$name:ident if $pred:expr, where $name2:ident : $ty:ty; $($rest:tt)*) => {{
        let a = stringify!($name);
        let b = stringify!($name2);
        assert_eq!(a, b, "Variable names must match: {} != {}", a, b);

        $tree.add_child(tree![pat_child!(@pred $name, $ty, $pred)]);
        pattern!(%parse_children $tree, $($rest)*);
    }};

    // A single child expression without trailing siblings
    (%parse_children $tree:ident, @$name:ident if $pred:expr, where $name2:ident : $ty:ty) => {{
        let a = stringify!($name);
        let b = stringify!($name2);
        assert_eq!(a, b, "Variable names must match: {} != {}", a, b);
        $tree.add_child(tree![pat_child!(@pred $name, $ty, $pred)]);
    }};


    // A single child expression with trailing siblings
    (%parse_children $tree:ident, @$name:ident; $($rest:tt)*) => {{
        $tree.add_child(pattern!(@$name));
        pattern!(%parse_children $tree, $($rest)*);
    }};

    // A single child expression without trailing siblings
    (%parse_children $tree:ident, @$name:ident) => {{
        $tree.add_child(pattern!(@$name));
    }};

    // A single child expression with trailing siblings
    (%parse_children $tree:ident, ..; $($rest:tt)*) => {{
        $tree.add_child(pattern!(..));
        pattern!(%parse_children $tree, $($rest)*);
    }};

    // A single child expression without trailing siblings
    (%parse_children $tree:ident, ..) => {{
        $tree.add_child(pattern!(..));
    }};

    // A single child expression with trailing siblings
    (%parse_children $tree:ident, $($child:expr)*; $($rest:tt)*) => {{
        $tree.add_child(pattern!($($child)*));
        pattern!(%parse_children $tree, $($rest)*);
    }};

    // A single child expression without trailing siblings
    (%parse_children $tree:ident, $($child:expr)*) => {{
        $tree.add_child(pattern!($($child)*));
    }};
}

#[macro_export]
macro_rules! rewrite_args {
    // Allow us to mix and match
    ($bindings:ident, $pat:pat_param = @$var:ident, $($rest:tt)*) => {
        // rewrite_args!($bindings, $pat = $var, $($rest)*);
        let var_name = stringify!($var);
        let $pat = $bindings.get(var_name).expect(&format!("Variable {} not found", stringify!($var))) else {panic!("Variable {} not found", stringify!($var));};
        rewrite_args!($bindings, $($rest)*);
    };
    // Allow us to mix and match
    ($bindings:ident, $pat:pat_param = $var:ident, $($rest:tt)*) => {
        // rewrite_args!($bindings, $pat = $var, $($rest)*);
        let var_name = stringify!($var);
        let $pat = $bindings.get(var_name).expect(&format!("Variable {} not found", stringify!($var))).value() else {panic!("Variable {} not found", stringify!($var));};
        rewrite_args!($bindings, $($rest)*);
    };
    ($bindings:ident, $pat:pat_param = @$var:ident) => {
        let var_name = stringify!($var);
        let $pat = $bindings.get(var_name).expect(&format!("Variable {} not found", stringify!($var))) else {panic!("Variable {} not found", stringify!($var));};
    };
    ($bindings:ident, $pat:pat_param = $var:ident) => {
        let var_name = stringify!($var);
        let $pat = $bindings.get(var_name).expect(&format!("Variable {} not found", stringify!($var))).value() else {panic!("Variable {} not found", stringify!($var));};
    };

    ($bindings:ident, @$var:ident, $($rest:tt)*) => {
        // rewrite_args!($bindings, $var, $($rest)*);
        let var_name = stringify!($var);
        let $var = $bindings.get(var_name).expect(&format!("Variable {} not found", stringify!($var)));
        rewrite_args!($bindings, $($rest)*);
    };
    ($bindings:ident, $var:ident, $($rest:tt)*) => {
        // rewrite_args!($bindings, $var, $($rest)*);
        let var_name = stringify!($var);
        let $var = $bindings.get(var_name).expect(&format!("Variable {} not found", stringify!($var))).value();
        rewrite_args!($bindings, $($rest)*);
    };
    ($bindings:ident, @$var:ident?, $($rest:tt)*) => {
        // rewrite_args!($bindings, $var, $($rest)*);
        let var_name = stringify!($var);
        let $var = $bindings.get(var_name);
        rewrite_args!($bindings, $($rest)*);
    };
    ($bindings:ident, $var:ident?, $($rest:tt)*) => {
        // rewrite_args!($bindings, $var, $($rest)*);
        let var_name = stringify!($var);
        let $var = $bindings.get(var_name).map(|node| node.value());
        rewrite_args!($bindings, $($rest)*);
    };
    ($bindings:ident, @$var:ident) => {
        let var_name = stringify!($var);
        let $var = $bindings.get(var_name).expect(&format!("Variable {} not found", stringify!($var)));
    };
    ($bindings:ident, $var:ident) => {
        let var_name = stringify!($var);
        let $var = $bindings.get(var_name).expect(&format!("Variable {} not found", stringify!($var))).value();
    };
    ($bindings:ident, @$var:ident?) => {
        let var_name = stringify!($var);
        let $var = $bindings.get(var_name);
    };
    ($bindings:ident, $var:ident?) => {
        let var_name = stringify!($var);
        let $var = $bindings.get(var_name).map(|node| node.value());
    };

    ($bindings:ident,) => {};
    ($bindings:ident) => {};
}

#[macro_export]
macro_rules! rewrite {
    ($value:expr, $node:ident = $pattern:expr => $transform:block * $count:expr, using $($rest:tt)*) => {{
        $value.rewrite(&$pattern, |$node, bindings| {
            // println!("Rewriting {} with bindings: {:?}", $node, bindings);
            rewrite_args!(bindings, $($rest)*);
            $transform.into()
        }, Some($count))
    }};
    ($value:expr, $node:ident = $pattern:expr => $transform:block using $($rest:tt)*) => {{
        $value.rewrite(&$pattern, |$node, bindings| {
            // println!("Rewriting {} with bindings: {:?}", $node, bindings);
            rewrite_args!(bindings, $($rest)*);
            $transform.into()
        }, None)
    }};
    ($value:expr, $node:ident = $pattern:expr => $transform:block * $count:expr) => {{
        rewrite!($value, $node = $pattern => $transform * $count, using)
    }};
    ($value:expr, $node:ident = $pattern:expr => $transform:block) => {{
        rewrite!($value, $node = $pattern => $transform using)
    }};
    ($value:expr, $pattern:expr => $transform:block * $count:expr, using $($rest:tt)*) => {{
        rewrite!($value, node = $pattern => $transform * $count, using $($rest)*)
    }};
    ($value:expr, $pattern:expr => $transform:block using $($rest:tt)*) => {{
        rewrite!($value, node = $pattern => $transform using $($rest)*)
    }};
    ($value:expr, $pattern:expr => $transform:block) => {{
        rewrite!($value, node = $pattern => $transform using)
    }};
}

#[macro_export]
macro_rules! map {
    ($value:expr, $node:ident = $pattern:expr => $transform:block * $count:expr, using $($rest:tt)*) => {{
        $value.map_pattern(&$pattern, |$node, bindings| {
            // println!("Rewriting {} with bindings: {:?}", $node, bindings);
            rewrite_args!(bindings, $($rest)*);
            $transform.into()
        }, Some($count))
    }};
    ($value:expr, $node:ident = $pattern:expr => $transform:block using $($rest:tt)*) => {{
        $value.map_pattern(&$pattern, |$node, bindings| {
            // println!("Rewriting {} with bindings: {:?}", $node, bindings);
            rewrite_args!(bindings, $($rest)*);
            $transform.into()
        }, None)
    }};
    ($value:expr, $node:ident = $pattern:expr => $transform:block * $count:expr) => {{
        map!($value, $node = $pattern => $transform * $count, using)
    }};
    ($value:expr, $node:ident = $pattern:expr => $transform:block) => {{
        map!($value, $node = $pattern => $transform using)
    }};
    ($value:expr, $pattern:expr => $transform:block * $count:expr, using $($rest:tt)*) => {{
        map!($value, node = $pattern => $transform * $count, using $($rest)*)
    }};
    ($value:expr, $pattern:expr => $transform:block using $($rest:tt)*) => {{
        map!($value, node = $pattern => $transform using $($rest)*)
    }};
    ($value:expr, $pattern:expr => $transform:block) => {{
        map!($value, node = $pattern => $transform using)
    }};
}

#[cfg(test)]
mod test {
    use super::*;

    use Math::*;
    impl Display for Math {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Add => write!(f, "+"),
                Mul => write!(f, "*"),
                Div => write!(f, "/"),
                Sub => write!(f, "-"),
                Num(n) => write!(f, "{}", n),
            }
        }
    }

    #[derive(PartialEq, Clone, Copy, Debug)]
    enum Math {
        Add,
        Mul,
        Div,
        Sub,
        Num(i32),
    }

    #[test]
    fn test_macro2() {
        use super::*;
        use crate::{tree, PatternParam};
        use Math::*;

        let add = pattern![
            alt!(Add, Sub);
            @x if matches!(x, Num(_));
            @y if matches!(y, Num(_));
        ];

        let mul = pattern![
            alt!(Mul, Div);
            @x if matches!(x, Num(_));
            @y if matches!(y, Num(_));
        ];

        let mut value = tree![
            Add;
            #[
                Mul;
                    #[
                        Add;
                            Num(3);
                            Num(6)
                    ];
                    Num(3)
            ];
            #[
                Mul;
                    Num(2);
                    Num(4)
            ];
        ];
        // rewrite!(
        //     tree![
        //         (1, 2, 3);
        //         (4, 5, 6);
        //         (7, 8, 9);
        //     ],

        //     pattern![
        //         @tup if tup.0 + tup.1 + tup.2 == 15,
        //                 where tup: &(i32, i32, i32)
        //     ] => {
        //         tree![(x * y * z, x + y + z, x - y - z)]
        //     } using (x, y, z) = tup
        // );
        while value.depth() > 1 {
            println!("{}", value);
            value = rewrite!(value, add => {Num(x + y)} using Num(x) = x, Num(y) = y);
            println!("{} (after add rewrite)", value);
            value = rewrite!(value, mul => {Num(x * y)} using Num(x) = x, Num(y) = y);
            println!("{} (after mul rewrite)", value);
        }
    }

    /*
       #[test]
       fn test_macro() {
           use super::*;
           use crate::{PatternParam, tree};

           let detect_bad = pattern![
               not(alt(Add, Mul, Div, Sub));
               ...
           ];

           let p = pattern![
               alt(Add, Mul, Div, Sub);
               ...
           ];
           println!("p = {}", p);

           let value = tree![
               Add;
               Num(7);
               Num(6);
               #[Mul; Num(2); Num(3); Num(4)];
           ];

           let nested_pat = pattern![
               Add;
               @x;
               @y;
               #[Mul; @a; @b; @c]
           ];

           println!("Nested pat: {}", nested_pat);

           value.rewrite(&detect_bad, |node, bindings| {
               if bindings.get("..").is_some() {
                   panic!("Found bad node: {}", node);
               }
               node.clone()
           });


           println!("{}", value);
           println!("Matches? {}", value.does_match_pattern(&p));
           value.save_graphviz_matches(&p, "matches.dot").unwrap();
           value.save_svg_matches(&p, "matches.svg").unwrap();

           let result = value.rewrite(&p, |node, bindings| {
               let dot = bindings.get("..").unwrap();

               match node.value() {
                   Add => {
                       let sum = dot.children().fold(0, |acc, child| {
                           match child.value() {
                               Num(n) => acc + n,
                               _ => acc,
                           }
                       });
                       tree![Num(sum)]
                   },
                   Mul => {
                       let product = dot.children().fold(1, |acc, child| {
                           match child.value() {
                               Num(n) => acc * n,
                               _ => acc,
                           }
                       });
                       tree![Num(product)]
                   },
                   _ => {
                       unreachable!();
                   },
               }
           });
           println!("{}", result);
       }

       #[test]
       fn test_match_pattern() {
           use crate::{Tree, tree};
           use super::*;

           let value = tree![
               Add;
               #[
                   Mul;
                   Num(2);
                   Num(3);
                   Num(4);
               ];
               #[
                   Mul;
                   Num(5);
                   Num(6);
               ];
           ];

           println!("{}", value);

           let pattern = tree![
               PatternParam::alt([
                   Math::Add.into(),
                   Math::Mul.into(),
               ]);
               PatternParam::DotDotDot;
           ];

           let value = value.rewrite(&pattern, |node, bindings| {
               let dot = bindings.get("..").unwrap();

               let result = tree![Math::Num(match node.value() {
                   Math::Mul => {
                       // Get product of the children
                       dot.children().fold(1, |acc, child| {
                           match child.value() {
                               Math::Num(n) => acc * n,
                               _ => acc,
                           }
                       })
                   },
                   Math::Add => {
                       // Get sum of the children
                       dot.children().fold(0, |acc, child| {
                           match child.value() {
                               Math::Num(n) => acc + n,
                               _ => acc,
                           }
                       })
                   },
                   _ => {
                       unreachable!();
                   },
               })];
               println!("{node} => {result}");
               result
           });
           println!("{}", value);
       }
    */
}
