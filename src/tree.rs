use graph::*;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::Hash;
use std::io::{Read, Write};
use std::ops::{Index, IndexMut};
use std::path::Path;
use std::sync::Arc;

fn sorted_list_to_bst<T>(list: &[T]) -> Tree<T>
where
    T: Ord + Clone,
{
    let mid = list.len() / 2;

    let mut root = Tree::new(list[mid].clone());
    if mid > 0 {
        let left = sorted_list_to_bst(&list[..mid]);
        root.add_child(left);
    }
    if mid + 1 < list.len() {
        let right = sorted_list_to_bst(&list[mid + 1..]);
        root.add_child(right);
    }
    root
}

pub struct Tree<T> {
    value: T,
    children: Arc<Vec<Box<Tree<T>>>>,
}

impl<T> Tree<T> {
    pub fn new(value: T) -> Self {
        Tree {
            value,
            children: Arc::new(Vec::new()),
        }
    }

    /*
     *
     * BEGIN TREE MANIPULATION METHODS
     *
     */

    pub fn to_binary(&self) -> Self
    where
        T: Ord + Clone,
    {
        // Create list of items
        let mut items = self.clone().into_iter().collect::<Vec<_>>();
        // Sort the items
        items.sort();
        // Create a new tree from the sorted items
        // let root = TreeNode {
        //     value: items[mid],
        //     left: sorted_list_to_bst(&list[..mid]), // Left half
        //     right: sorted_list_to_bst(&list[mid + 1..]), // Right half
        // };

        sorted_list_to_bst(&items)
    }

    pub fn degree(&self) -> usize {
        // Get the maximum degree of the tree
        let my_degree = self.children.len();

        self.children.iter().map(|child| child.degree()).max().unwrap_or(my_degree).max(my_degree)
    }

    pub fn is_binary(&self) -> bool {
        self.degree() <= 2
    }

    pub fn prune(mut self) -> Self
    where
        T: Clone,
    {
        self.children = Arc::new(Vec::new());
        self
    }

    pub fn set_value(&mut self, value: T) {
        self.value = value;
    }

    pub fn add_child(&mut self, child: Tree<T>)
    where
        T: Clone,
    {
        let children = Arc::make_mut(&mut self.children);
        children.push(Box::new(child));
    }

    pub fn add_children<I>(&mut self, children: I)
    where
        I: IntoIterator<Item = Tree<T>>,
        T: Clone,
    {
        let my_children = Arc::make_mut(&mut self.children);
        my_children.extend(children.into_iter().map(Box::new));
    }

    pub fn with_children<I>(mut self, children: I) -> Self
    where
        I: IntoIterator<Item = Tree<T>>,
        T: Clone,
    {
        self.add_children(children);
        self
    }

    pub fn remove_child(&mut self, index: usize) -> Tree<T>
    where
        T: Clone,
    {
        let children = Arc::make_mut(&mut self.children);
        *children.remove(index)
    }

    pub fn insert_child(&mut self, index: usize, child: Tree<T>)
    where
        T: Clone,
    {
        let children = Arc::make_mut(&mut self.children);
        children.insert(index, Box::new(child));
    }

    pub fn clear_children(&mut self)
    where
        T: Clone,
    {
        let children = Arc::make_mut(&mut self.children);
        children.clear();
    }

    pub fn map<F, U>(&self, f: F) -> Tree<U>
    where
        F: Fn(T) -> U + Clone,
        T: Clone,
        U: Clone,
    {
        let mut new_tree = Tree::new(f(self.value().clone()));
        let children = Arc::make_mut(&mut new_tree.children);
        for child in self.children.iter() {
            children.push(Box::new(child.map(f.clone())));
        }
        new_tree
    }

    pub fn transform<F>(&self, f: &mut F) -> Self
    where
        F: FnMut(Self) -> Self,
        T: Clone,
    {
        let mut new_tree = f(self.clone());
        for child in new_tree.children_mut() {
            *child = child.transform(f);
        }

        // let _ = new_tree.children_mut().map(move |child| *child = child.transform(&mut f)).collect::<Vec<_>>();
        new_tree
    }

    pub fn filter<F>(&self, f: F) -> Option<Tree<T>>
    where
        F: Fn(&Self) -> bool,
        T: Clone,
    {
        if f(self) {
            Some(Tree {
                value: self.value.clone(),
                children: Arc::new(
                    self.children
                        .iter()
                        .filter_map(|child| child.filter(&f))
                        .map(Box::new)
                        .collect(),
                ),
            })
        } else {
            None
        }
    }

    pub fn find<F>(&self, f: F) -> Option<&Tree<T>>
    where
        F: Fn(&T) -> bool,
    {
        if f(&self.value) {
            Some(self)
        } else {
            self.children.iter().find_map(|child| child.find(&f))
        }
    }

    pub fn find_mut<F>(&mut self, f: F) -> Option<&mut Tree<T>>
    where
        F: Fn(&T) -> bool,
        T: Clone,
    {
        if f(&self.value) {
            Some(self)
        } else {
            let children = Arc::make_mut(&mut self.children);
            children.iter_mut().find_map(|child| child.find_mut(&f))
        }
    }

    pub fn contains<F>(&self, f: F) -> bool
    where
        F: Fn(&T) -> bool,
    {
        f(&self.value) || self.children.iter().any(|child| child.contains(&f))
    }

    pub fn for_each<F>(&self, f: F)
    where
        F: Fn(&T),
    {
        f(&self.value);
        for child in self.children.iter() {
            child.for_each(&f);
        }
    }

    pub fn for_each_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T),
        T: Clone,
    {
        f(&mut self.value);
        let children = Arc::make_mut(&mut self.children);
        for child in children.iter_mut() {
            child.for_each_mut(&mut f);
        }
    }

    pub fn iter(&self) -> TreeIter<T> {
        TreeIter::new(self)
    }

    pub fn iter_mut(&mut self) -> TreeIterMut<T>
    where
        T: Clone,
    {
        TreeIterMut::new(self)
    }

    pub fn into_value(self) -> T {
        self.value
    }

    pub fn into_children(self) -> Vec<Tree<T>>
    where
        T: Debug,
    {
        self.into_children_box()
            .into_iter()
            .map(|child| *child)
            .collect()
    }

    pub fn into_children_box(self) -> Vec<Box<Tree<T>>>
    where
        T: Debug,
    {
        Arc::try_unwrap(self.children).unwrap()
    }

    pub fn reduce<F>(&self, f: F) -> Self
    where
        F: Fn(Self, Self) -> Self + Clone,
        T: Clone,
    {
        let mut value = self.clone();
        for child in self.children.iter() {
            let child_value = child.reduce(f.clone());
            value = f(value, child_value);
        }
        value
    }

    /// `foldr` recursively applies `f` over the tree, starting with the children
    /// from the rightmost to the leftmost, then the node itself.
    pub fn foldr<U, F>(&self, f: F, acc: U) -> U
    where
        F: Fn(&T, U) -> U + Clone,
        U: Clone,
        T: Debug,
    {
        // Fold over the children from right to left
        let acc = self
            .children
            .iter()
            .rev()
            .fold(acc, |acc, child| child.foldr::<U, F>(f.clone(), acc));

        // Apply the function to the current node's value and accumulated result
        f(&self.value, acc)
    }

    /// `foldl` recursively applies `f` over the tree, starting with the node itself,
    /// then the children from leftmost to rightmost.
    pub fn foldl<U, F>(&self, f: F, acc: U) -> U
    where
        F: Fn(&T, U) -> U + Clone,
        U: Clone,
    {
        // Apply the function to the current node's value and accumulated result
        let acc = f(&self.value, acc);

        // Fold over the children from left to right
        self.children
            .iter()
            .fold(acc, |acc, child| child.foldl(f.clone(), acc))
    }

    pub fn replace(&mut self, original: &Tree<T>, replacement: &Tree<T>)
    where
        T: Clone + PartialEq,
    {
        if self == original {
            *self = replacement.clone();
        } else {
            for child in self.children_mut() {
                child.replace(original, replacement);
            }
        }
    }

    /*
     *
     * BEGIN TREE INFORMATION METHODS
     *
     */

    /// Get the value of the tree node
    pub fn value(&self) -> &T {
        &self.value
    }

    pub fn value_mut(&mut self) -> &mut T {
        &mut self.value
    }

    /// Get the children of the tree node
    // pub fn children(&self) -> &[Box<Tree<T>>] {
    //     &self.children
    // }
    pub fn children(&self) -> impl Iterator<Item = &Tree<T>> {
        self.children.iter().map(|child| child.as_ref())
    }

    // pub fn children_mut(&mut self) -> &mut Vec<Box<Tree<T>>> where T: Clone {
    //     Arc::make_mut(&mut self.children)
    // }

    pub fn children_mut(&mut self) -> impl Iterator<Item = &mut Tree<T>>
    where
        T: Clone,
    {
        let children = Arc::make_mut(&mut self.children);
        children.iter_mut().map(|child| child.as_mut())
    }

    pub fn children_values(&self) -> impl Iterator<Item = &T> {
        self.children.iter().map(|child| child.value())
    }

    pub fn children_values_mut(&mut self) -> impl Iterator<Item = &mut T>
    where
        T: Clone,
    {
        let children = Arc::make_mut(&mut self.children);
        children.iter_mut().map(|child| child.value_mut())
    }

    /// Get the number of children of the tree node
    pub fn len(&self) -> usize {
        self.children.len()
    }

    /// Get the depth of the tree
    pub fn depth(&self) -> usize {
        if self.children.is_empty() {
            1
        } else {
            1 + self
                .children
                .iter()
                .map(|child| child.depth())
                .max()
                .unwrap()
        }
    }

    /// Get the number of nodes in the tree
    pub fn size(&self) -> usize {
        1 + self
            .children
            .iter()
            .map(|child| child.size())
            .sum::<usize>()
    }

    /// Check if the tree is a leaf node
    /// A leaf node is a node with no children
    pub fn is_leaf(&self) -> bool {
        self.is_empty()
    }

    /// Check if the tree is empty
    pub fn is_empty(&self) -> bool {
        self.children.is_empty()
    }

    /*
     *
     * BEGIN TREE VISUALIZATION METHODS
     *
     */

    pub fn to_graph(&self, graph: &mut Graph, id: &mut usize) -> Node
    where
        T: Display,
    {
        let parent_node = graph
            .new_node(*id)
            .with_property("label", format!("{}", self.value))
            .finalize();

        *id += 1;
        for child in self.children.iter() {
            let child_node = child.to_graph(graph, id);
            graph.new_edge(parent_node, child_node).finalize();
        }

        parent_node
    }

    pub fn graphviz(&self) -> String
    where
        T: Display,
    {
        let mut graph = Graph::new();
        self.to_graph(&mut graph, &mut 0);
        graph.to_dot()

        // let mut graph = String::new();
        // graph.push_str("digraph G {\n");
        // graph.push_str("  node [shape=plaintext]\n");
        // graph.push_str("  rankdir=TB\n");
        // graph.push_str("  ranksep=1\n");
        // graph.push_str("  ");
        // graph.push_str(&self.graphviz_node(&mut 0));
        // graph.push_str("}\n");
        // graph
    }

    pub fn to_svg(&self) -> Result<String, ()>
    where
        T: Display,
    {
        let dot = self.graphviz();
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

    pub fn save_png<P: AsRef<Path>>(&self, path: P) -> Result<(), ()>
    where
        T: Display,
    {
        let dot = self.graphviz();
        // Use the `dot` command to convert the DOT code to PNG
        let process = std::process::Command::new("dot")
            .arg("-Tpng")
            .arg("-o")
            .arg(path.as_ref())
            .stdin(std::process::Stdio::piped())
            .spawn()
            .expect("Failed to execute dot");

        process
            .stdin
            .expect("Failed to open stdin")
            .write_all(dot.as_bytes())
            .expect("Failed to write to stdin");

        Ok(())
    }

    pub fn save_svg<P: AsRef<Path>>(&self, path: P) -> Result<(), ()>
    where
        T: Display,
    {
        let svg = self.to_svg()?;
        std::fs::write(path, svg).map_err(|_| ())
    }

    pub fn save_graphviz<P: AsRef<Path>>(&self, path: P) -> Result<(), ()>
    where
        T: Display,
    {
        let graph = self.graphviz();
        std::fs::write(path, graph).map_err(|_| ())
    }

    fn graphviz_node(&self, id: &mut usize) -> String
    where
        T: Display,
    {
        let my_id = *id;
        let mut node = format!("node{} [label=\"{}\"];\n", id, self.value);
        for child in self.children.iter() {
            *id += 1;
            node.push_str(&format!("  node{} -> node{};\n", my_id, *id));
            node.push_str(&child.graphviz_node(id));
        }
        node
    }
}

impl<T> Clone for Tree<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Tree {
            value: self.value.clone(),
            children: self.children.clone(),
        }
    }
}

impl<T> Debug for Tree<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        f.debug_struct("Tree")
            .field("value", &self.value)
            .field("children", &self.children)
            .finish()
    }
}

impl<T> Display for Tree<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        if self.is_leaf() {
            return write!(f, "{}", self.value);
        }
        write!(f, "({}", self.value)?;
        if !self.children.is_empty() {
            for child in self.children.iter() {
                write!(f, " {}", child)?;
            }
        }
        write!(f, ")")?;
        Ok(())
    }
}

impl<T> From<T> for Tree<T> {
    fn from(value: T) -> Self {
        Tree::new(value)
    }
}

impl<T> FromIterator<T> for Tree<T>
where
    T: Clone,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut iter = iter.into_iter();
        let value = iter.next().expect("Cannot create tree from empty iterator");
        let mut tree = Tree::new(value);
        for value in iter {
            tree.add_child(Tree::new(value));
        }
        tree
    }
}

pub struct TreeIter<'a, T> {
    stack: Vec<&'a Tree<T>>,
}

impl<'a, T> TreeIter<'a, T> {
    fn new(tree: &'a Tree<T>) -> Self {
        let mut stack = Vec::new();
        stack.push(tree);
        TreeIter { stack }
    }
}

impl<'a, T> Iterator for TreeIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.stack.pop()?;
        self.stack
            .extend(node.children.iter().map(|child| child.as_ref()));
        Some(&node.value)
    }
}

pub struct TreeIterMut<'a, T> {
    stack: Vec<&'a mut Tree<T>>,
}

impl<'a, T> TreeIterMut<'a, T> {
    fn new(tree: &'a mut Tree<T>) -> Self {
        let mut stack = Vec::new();
        stack.push(tree);
        TreeIterMut { stack }
    }
}

impl<'a, T> Iterator for TreeIterMut<'a, T>
where
    T: Clone,
{
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.stack.pop()?;
        let children = Arc::make_mut(&mut node.children);
        self.stack
            .extend(children.iter_mut().map(|child| child.as_mut()));
        Some(&mut node.value)
    }
}

impl<T> Index<usize> for Tree<T> {
    type Output = Tree<T>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.children[index]
    }
}

impl<T> IndexMut<usize> for Tree<T>
where
    T: Clone,
{
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let children = Arc::make_mut(&mut self.children);
        &mut children[index]
    }
}

impl<T> AsRef<Tree<T>> for Tree<T> {
    fn as_ref(&self) -> &Tree<T> {
        self
    }
}

impl<T> AsMut<Tree<T>> for Tree<T>
where
    T: Clone,
{
    fn as_mut(&mut self) -> &mut Tree<T> {
        self
    }
}

impl<T> AsRef<T> for Tree<T> {
    fn as_ref(&self) -> &T {
        &self.value
    }
}

impl<T> AsMut<T> for Tree<T>
where
    T: Clone,
{
    fn as_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

impl<T> PartialEq for Tree<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.children == other.children
    }
}

impl<T> Eq for Tree<T> where T: Eq {}

impl<T> Default for Tree<T>
where
    T: Default,
{
    fn default() -> Self {
        Tree::new(T::default())
    }
}

impl<T> PartialOrd for Tree<T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        // Compare the values of the nodes
        match self.value.partial_cmp(&other.value) {
            Some(std::cmp::Ordering::Equal) => {
                // If the values are equal, compare the children
                self.children.partial_cmp(&other.children)
            }
            result => result,
        }
    }
}

impl<T> Ord for Tree<T>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Compare the values of the nodes
        match self.value.cmp(&other.value) {
            std::cmp::Ordering::Equal => {
                // If the values are equal, compare the children
                self.children.cmp(&other.children)
            }
            result => result,
        }
    }
}

impl<T> IntoIterator for Tree<T>
where
    T: Clone,
{
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        let mut iter = Vec::new();
        iter.push(self.value.clone());
        for child in self.children.iter() {
            iter.extend(child.clone().into_iter());
        }
        iter.into_iter()
    }
}

impl<T> Hash for Tree<T> where T: Hash {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state);
        for child in self.children.iter() {
            child.hash(state);
        }
    }
}

/*

#[macro_export]
macro_rules! tree {
    // --- Entry points ----------------------------------------------------

    // A node with children: first expression, then more tokens
    ($value:expr; $($rest:tt)*) => {{
        let mut t = Tree::from($value);
        tree!(@parse_children t, $($rest)*);
        t
    }};

    // A leaf node: just a single expression with no children
    ($value:expr) => {
        Tree::from($value)
    };

    // --- Internal rules for parsing children -----------------------------

    // No more children
    (@parse_children $tree:ident) => {};
    (@parse_children $tree:ident,) => {};

    // A nested child subtree: looks like #[ child_root ; child2 ; child3 ; ... ]
    (@parse_children $tree:ident, #[ $($subtree:tt)* ]; $($rest:tt)*) => {{
        $tree.add_child(tree!($($subtree)*));
        tree!(@parse_children $tree, $($rest)*);
    }};
    // Same, but no trailing semicolon
    (@parse_children $tree:ident, #[ $($subtree:tt)* ]) => {{
        $tree.add_child(tree!($($subtree)*));
    }};

    // A single child expression with trailing siblings
    (@parse_children $tree:ident, $child:expr; $($rest:tt)*) => {{
        $tree.add_child(tree!($child));
        tree!(@parse_children $tree, $($rest)*);
    }};
    // A single child expression without trailing siblings
    (@parse_children $tree:ident, $child:expr) => {{
        $tree.add_child(tree!($child));
    }};
}
*/
#[macro_export]
macro_rules! tree {
    // --- Entry points ----------------------------------------------------

    // A node with children: first expression, then more tokens
    ($value:expr; $($rest:tt)*) => {{
        let mut t = Tree::from($value);
        tree!(@parse_children t, $($rest)*);
        t
    }};

    // A leaf node: just a single expression with no children
    ($value:expr) => {
        Tree::from($value)
    };

    // --- Internal rules for parsing children -----------------------------

    // No more children
    (@parse_children $tree:ident) => {};
    (@parse_children $tree:ident,) => {};

    // A nested child subtree: looks like #[ child_root ; child2 ; child3 ; ... ]
    (@parse_children $tree:ident, #[ $($subtree:tt)* ]; $($rest:tt)*) => {{
        $tree.add_child(tree!($($subtree)*));
        tree!(@parse_children $tree, $($rest)*);
    }};
    // Same, but no trailing semicolon
    (@parse_children $tree:ident, #[ $($subtree:tt)* ]) => {{
        $tree.add_child(tree!($($subtree)*));
    }};

    // NEW: Multiple children from an iterator, with trailing siblings
    (@parse_children $tree:ident, .. $iter:expr; $($rest:tt)*) => {{
        for child in $iter {
            $tree.add_child(Tree::from(child));
        }
        tree!(@parse_children $tree, $($rest)*);
    }};
    // NEW: Multiple children from an iterator, no trailing siblings
    (@parse_children $tree:ident, .. $iter:expr) => {{
        for child in $iter {
            $tree.add_child(Tree::from(child));
        }
    }};

    // A single child expression with trailing siblings
    (@parse_children $tree:ident, $child:expr; $($rest:tt)*) => {{
        $tree.add_child(tree!($child));
        tree!(@parse_children $tree, $($rest)*);
    }};
    // A single child expression without trailing siblings
    (@parse_children $tree:ident, $child:expr) => {{
        $tree.add_child(tree!($child));
    }};
}

// Test the tree macro
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tree_macro() {
        let tree = tree![0; 1; 2];
        assert_eq!(format!("{}", tree), "(0 1 2)");

        let tree = tree![0; 1; 2; 3];
        assert_eq!(format!("{}", tree), "(0 1 2 3)");

        // Nested tree
        let tree = tree![0; 1; 2; #[3; 4; 5]];
        assert_eq!(format!("{}", tree), "(0 1 2 (3 4 5))");

        // Multiple nested subtrees
        let tree = tree![0; #[1; 2]; #[3; 4]; 5];
        assert_eq!(format!("{}", tree), "(0 (1 2) (3 4) 5)");

        // Using an iterator at the top level
        let extra = vec![4, 5, 6];
        let t = tree![0; 1; 2; 3; ..extra];
        assert_eq!(format!("{}", t), "(0 1 2 3 4 5 6)");

        // Using iterators nested in subtrees
        let subtree_extra = vec![30, 31];
        let outer_extra = vec![10, 11];
        let t = tree![
            0;
            #[1; 2; 3; ..subtree_extra];  // nested iterator
            4;
            ..outer_extra                // outer iterator
        ];
        // So we expect: 0 -> children = [1 -> [2 3 30 31], 4, 10, 11]
        assert_eq!(format!("{}", t), "(0 (1 2 3 30 31) 4 10 11)");
    }
}
