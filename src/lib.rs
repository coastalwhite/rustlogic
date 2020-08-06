//! Hello fellow Rustacians! RustLogic is a crate for parsing and handling simple logical expressings.
//!
//! This crate contains the basic foundation for handling stringed logical formulas.
//! If you want to want to submit an issue or a pull request,
//! please visit the [GitHub](https://github.com/coastalwhite/rustlogic) page.
//!
//! Thanks for your time and enjoy this crate!
//!
//! # Examples
//! ## 4-1 Multiplexer
//! ```
//! # use std::collections::HashMap;
//! let multiplexer_4_to_1 =
//!     rustlogic::parse(
//!         "([a]&~[x]&~[y])|([b]&~[x]&[y])|([c]&[x]&~[y])|([d]&[x]&[y])"
//!     )
//!     .expect("Failed to parse 4-1 multiplexer");
//!
//! let mut variable_map = HashMap::new();
//!
//! // Input: 1001
//! variable_map.insert("a", true);
//! variable_map.insert("b", false);
//! variable_map.insert("c", false);
//! variable_map.insert("d", true);
//!
//! // Selector: 11
//! variable_map.insert("x", true);
//! variable_map.insert("y", true);
//!
//! // Should select fourth item from bus so true
//! let value = multiplexer_4_to_1.get_value_from_variables(&variable_map).unwrap();
//! println!("{}", value); // Will print true!
//! # assert!(value);
//! # variable_map.insert("d", false);
//! # let value = multiplexer_4_to_1.get_value_from_variables(&variable_map).unwrap();
//! # assert!(!value);
//! ```
//!
//! ## Evaluating a logical string with variables and custom logical operators
//! ```
//! use rustlogic::operators;
//! use std::collections::HashMap;
//!
//! // Define the set
//! let operator_set = operators::common_sets::worded();
//!
//! let parsed = rustlogic::custom_parse("(NOT $[A] AND TRUE) OR $[B]", &operator_set);
//! # assert!(parsed.is_ok());
//!
//! // We assign the variables to their values
//! let mut hm = HashMap::new();
//! hm.insert("A", false);
//! hm.insert("B", false);
//! # assert!(parsed.unwrap().get_value_from_variables(&hm).is_ok());
//!
//! // Now contains the value of the logical expression
//! # let parsed = rustlogic::custom_parse("(NOT $[A] AND TRUE) OR $[B]", &operator_set);
//! let value = parsed.unwrap().get_value_from_variables(&hm).unwrap();
//! # assert!(value);
//! ```

mod multidimensional_logicnode;
pub mod operators;
mod util;

use operators::OperatorSet;
use std::collections::HashMap;

/// An Enum of all the possible states of a head of a logical formula
#[derive(Debug)]
pub enum LogicNode {
    /// AND operation of left and right
    And(Box<LogicNode>, Box<LogicNode>),

    /// OR operation of left and right
    Or(Box<LogicNode>, Box<LogicNode>),

    /// NOT operation of child
    Not(Box<LogicNode>),

    /// True, always returns true
    True,

    /// False, always returns false
    False,

    /// Variable, always returns value of variable passed in
    Variable(String),
}

impl LogicNode {
    /// Will retrieve the value of a [LogicNode](enum.LogicNode.html)
    /// given a [HashMap](https://doc.rust-lang.org/std/collections/struct.HashMap.html) of variables
    ///
    /// # Output
    /// Will output a result type with either the value of the [LogicNode](enum.LogicNode.html)
    /// given the [Hashmap](https://doc.rust-lang.org/std/collections/struct.HashMap.html)
    /// or will give a error with the variable missing from the 'variables' argument given.
    ///
    /// # Examples
    /// ## X-OR
    /// ```
    /// # use std::collections::HashMap;
    /// # use rustlogic::parse;
    /// let xor = parse("([a]|[b])&~([a]&[b])")
    ///     .expect("Failed to parse xor gate");
    ///
    /// let mut variable_map = HashMap::new();
    /// variable_map.insert("a", true);
    /// variable_map.insert("b", true);
    /// let value_1 = xor.get_value_from_variables(&variable_map).unwrap();
    /// println!("First value: {}!", value_1); // Will print false!
    /// # assert!(!value_1);
    ///
    /// variable_map.insert("a", false);
    /// let value_2 = xor.get_value_from_variables(&variable_map).unwrap();
    /// println!("Second value: {}!", value_1); // Will print true!
    /// # assert!(value_2);
    ///
    /// variable_map.insert("b", false);
    /// let value_3 = xor.get_value_from_variables(&variable_map).unwrap();
    /// println!("Third value: {}!", value_1); // Will print false!
    /// # assert!(!value_3);
    /// ```
    pub fn get_value_from_variables(
        &self,
        variables: &HashMap<&str, bool>,
    ) -> Result<bool, String> {
        use LogicNode::*;

        match self {
            And(left, right) => Ok(left.get_value_from_variables(variables)?
                && right.get_value_from_variables(variables)?),

            Or(left, right) => Ok(left.get_value_from_variables(variables)?
                || right.get_value_from_variables(variables)?),

            Not(child) => Ok(!child.get_value_from_variables(variables)?),

            True => Ok(true),

            False => Ok(false),

            // Fetch variable, if it cannot be found through error with name of that variable
            Variable(variable) => Ok(variables
                .get(&variable[..])
                .ok_or(variable.clone())?
                .clone()),
        }
    }

    /// Will retrieve the value of a [LogicNode](enum.LogicNode.html) given purely the formula
    ///
    /// # Output
    /// Will return a result with either the value of the [LogicNode](enum.LogicNode.html) or an error value containing
    /// the name of the (or one of the) variable contained within the [LogicNode](enum.LogicNode.html).
    ///
    /// # Examples
    /// ## Basic usage
    /// ```
    /// # use std::collections::HashMap;
    /// # use rustlogic::parse;
    /// let and_of_true_and_false = parse("0&1")
    ///     .expect("Unable to parse AND of true and false");
    /// let or_of_true_and_false = parse("0|1")
    ///     .expect("Unable to parse OR of true and false");
    ///
    /// let value_1 = and_of_true_and_false.get_value().unwrap();
    /// println!("0&1: {}", value_1); // Will return false!
    /// # assert!(!value_1);
    ///
    /// let value_2 = or_of_true_and_false.get_value().unwrap();
    /// println!("0|1: {}", value_2); // Will return true!
    /// # assert!(value_2);
    /// ```
    pub fn get_value(&self) -> Result<bool, String> {
        use LogicNode::*;

        match self {
            And(left, right) => Ok(left.get_value()? && right.get_value()?),

            Or(left, right) => Ok(left.get_value()? || right.get_value()?),

            Not(child) => Ok(!child.get_value()?),

            True => Ok(true),

            False => Ok(false),

            // Tree contains variable so return error
            Variable(variable) => Err(variable.clone()),
        }
    }

    /// Will return whether a given [LogicNode](enum.LogicNode.html) contains a variable
    ///
    /// # Examples
    /// ## Basic usage
    /// ```
    /// # use std::collections::HashMap;
    /// # use rustlogic::parse;
    /// let with_variable = parse("([a]&0)")
    ///     .expect("Unable to parse with variable");
    /// let without_variable = parse("(1&0)")
    ///     .expect("Unable to parse without variable");
    ///
    /// // Will return true!
    /// println!("First contains variable: {}", with_variable.contains_variable());
    /// # assert!(with_variable.contains_variable());
    ///
    /// // Will return false!
    /// println!("Second contains variable: {}", without_variable.contains_variable());
    /// # assert!(!without_variable.contains_variable());
    /// ```
    pub fn contains_variable(&self) -> bool {
        use LogicNode::*;

        match self {
            And(left, right) | Or(left, right) => {
                left.contains_variable() || right.contains_variable()
            }

            Not(child) => child.contains_variable(),

            True | False => false,

            Variable(_) => true,
        }
    }

    /// Returns a sorted vector of all Variables used in a LogicNode
    ///
    /// # Examples
    /// ## NOR
    /// ```
    /// # use std::collections::HashMap;
    /// # use rustlogic::parse;
    /// let nor = parse("~([a]|[b])")
    ///     .expect("Unable to parse with variable");
    ///
    /// // Will return ["a", "b"]
    /// println!("Variables in nor: {:?}", nor.get_variables());
    /// # assert_eq!(nor.get_variables(), vec!["a", "b"]);
    /// ```
    pub fn get_variables(&self) -> Vec<String> {
        let mut variables = Vec::new();

        use LogicNode::*;

        // Go through elements recurvely
        match self {
            And(left, right) | Or(left, right) => {
                variables.extend(left.get_variables().iter().cloned());
                variables.extend(right.get_variables().iter().cloned());
            }

            Not(child) => variables.extend(child.get_variables().iter().cloned()),

            True | False => (),

            Variable(var) => variables = vec![var.clone()],
        }

        // Sort the variables in preparation for the deduplication
        variables.sort();

        // Remove duplicates
        variables.dedup();

        variables
    }

    /// Inserts formula in place of variable
    ///
    /// # Examples
    /// ## Insert AND in OR
    /// ```rust
    /// # use std::collections::HashMap;
    /// # use rustlogic::parse;
    /// let or = parse("[AND]|[b]").expect("Error parsing or");
    ///
    /// # assert_eq!(or.to_string(), "( [AND] | [b] )");
    /// let and_in_or = or.insert_formula(
    ///     "AND",
    ///     &parse("[x]&[y]").expect("Error parsing AND")
    /// );
    ///
    /// println!("{}", and_in_or); // Will print ( ( [x] & [y] ) | [b] )
    /// # assert_eq!(and_in_or.to_string(), "( ( [x] & [y] ) | [b] )");
    pub fn insert_formula(&self, variable: &str, formula: &LogicNode) -> LogicNode {
        use LogicNode::*;

        match self {
            And(left, right) => And(
                Box::new(left.insert_formula(variable, formula)),
                Box::new(right.insert_formula(variable, formula)),
            ),

            Or(left, right) => Or(
                Box::new(left.insert_formula(variable, formula)),
                Box::new(right.insert_formula(variable, formula)),
            ),

            Not(child) => Not(Box::new(child.insert_formula(variable, formula))),

            Variable(var) => {
                if var == variable {
                    return formula.clone();
                }

                Variable(var.clone())
            }

            True => True,
            False => False,
        }
    }

    /// Convert a Logical node to a String using a certain Operator Set
    ///
    /// # Example
    /// ```
    /// use rustlogic::operators;
    ///
    /// // Create our logical node
    /// let parsed = rustlogic::parse("(~[A]&[B])|[C]").unwrap();
    ///
    /// // Create a string using the worded operator set
    /// let worded = parsed.to_string_using_set(&operators::common_sets::worded());
    ///
    /// // Will print "((NOT $[A] AND $[B]) OR $[C])"!
    /// println!("{}", worded);
    /// assert_eq!(worded, String::from("((NOT $[A] AND $[B]) OR $[C])"));
    /// ```
    pub fn to_string_using_set(&self, operator_set: &OperatorSet) -> String {
        multidimensional_logicnode::MultiDimensionalLogicNode::new(self)
            .to_string_using_set(operator_set)
    }
}

impl std::fmt::Display for LogicNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let multi_dim = multidimensional_logicnode::MultiDimensionalLogicNode::new(self);
        write!(f, "{}", multi_dim)
    }
}

impl std::clone::Clone for LogicNode {
    fn clone(&self) -> Self {
        use LogicNode::*;

        match self {
            And(left, right) => And(left.clone(), right.clone()),
            Or(left, right) => Or(left.clone(), right.clone()),
            Not(child) => Not(child.clone()),
            True => True,
            False => False,
            Variable(var) => Variable(var.clone()),
        }
    }
}

/// Function used to find the matching parenthesis given a string
/// and a position open a opening group symbol (taking into account depth)
/// Will return None if position given is not a bracket or
/// if no matching bracket was found
fn get_group_content(
    input_string: &str,
    position: usize,
    operator_set: &OperatorSet,
) -> Option<String> {
    use util::{multi_search, search};

    let opener = operator_set.group_open();
    let closer = operator_set.group_close();
    let var_opener = operator_set.variable_open();
    let var_closer = operator_set.variable_close();

    // Check whether input_string starts with opening symbol
    if search(&input_string[position..], opener) != Some(0) {
        return None;
    }

    let mut depth: u16 = 0;
    let mut search_location = position + opener.len();

    let multi_search_query = vec![opener, closer, var_opener];

    // Search through string for the first occurance of a opening or closing symbol
    let mut search_result = multi_search(&input_string[search_location..], &multi_search_query);
    while search_result != None {
        let unwrapped_search_result = search_result.unwrap();

        let query_index = unwrapped_search_result.0;
        let pool_index = unwrapped_search_result.1;

        match query_index {
            0 => {
                // Opening symbol found at pool_index

                depth += 1;
                search_location += pool_index + opener.len();
            }
            1 => {
                // Closing symbol found at pool_index

                if depth == 0 {
                    return Some(String::from(
                        &input_string[position + opener.len()..pool_index + search_location],
                    ));
                }

                depth -= 1;
                search_location += pool_index + closer.len();
            }
            _ => {
                // Variable open symbol found at pool_index

                let var_closer_loc = search(
                    &input_string[search_location + pool_index + var_opener.len()..],
                    var_closer,
                );

                match var_closer_loc {
                    None => {
                        return None;
                    }
                    Some(var_closer_loc) => {
                        search_location +=
                            pool_index + var_opener.len() + var_closer_loc + var_closer.len();
                    }
                }
            }
        }

        search_result = multi_search(&input_string[search_location..], &multi_search_query);
    }

    // No matching closing symbol found so return nothing
    None
}

fn get_variable_content(
    input_string: &str,
    position: usize,
    operator_set: &OperatorSet,
) -> Option<String> {
    use util::search;

    let opener = operator_set.variable_open();
    let closer = operator_set.variable_close();

    if search(&input_string[position..], opener) != Some(0) {
        return None;
    }

    let search_string = &input_string[position + opener.len()..];
    let closer_location = search(search_string, closer);

    match closer_location {
        None => None,
        Some(closer_location) => Some(String::from(&search_string[..closer_location])),
    }
}

fn easy_parse(input_string: &str, operator_set: &OperatorSet) -> Option<Result<LogicNode, usize>> {
    use LogicNode::*;

    if input_string.is_empty() {
        return Some(Err(0));
    }

    if input_string == operator_set.true_symbol() {
        return Some(Ok(True));
    }

    if input_string == operator_set.false_symbol() {
        return Some(Ok(False));
    }

    let variable_content_option = get_variable_content(input_string, 0, operator_set);
    if variable_content_option.is_some() {
        let variable_content = variable_content_option.unwrap();

        if variable_content.len()
            == input_string.len()
                - operator_set.variable_open().len()
                - operator_set.variable_close().len()
        {
            return Some(Ok(Variable(variable_content)));
        }
    }

    let group_content_option = get_group_content(input_string, 0, operator_set);
    if group_content_option.is_some() {
        let group_content = group_content_option.unwrap();

        if group_content.len()
            == input_string.len()
                - operator_set.group_open().len()
                - operator_set.group_close().len()
        {
            return Some(
                custom_parse(&group_content[..], operator_set)
                    .map_err(|err_loc| err_loc + operator_set.group_open().len()),
            );
        }
    }

    None
}

fn infix_parse(
    input_string: &str,
    position: usize,
    operator_set: &OperatorSet,
) -> Result<LogicNode, usize> {
    let symbol = if input_string[position..].starts_with(operator_set.and()) {
        operator_set.and()
    } else if input_string[position..].starts_with(operator_set.or()) {
        operator_set.or()
    } else {
        return Err(position);
    };

    let left = custom_parse(&input_string[..position], operator_set)?;
    let right = custom_parse(&input_string[position + symbol.len()..], operator_set)
        .map_err(|err_loc| position + symbol.len() + err_loc)?;

    Ok(
        match input_string[position..].starts_with(operator_set.and()) {
            true => LogicNode::And(Box::new(left), Box::new(right)),
            false => LogicNode::Or(Box::new(left), Box::new(right)),
        },
    )
}

/// Parsing of logic formulas with non-default operator symbols
/// Use the [OperatorSet](struct.OperatorSet.html) Struct
///
/// # Examples
/// ## Using a worded set
/// ```
/// use rustlogic::operators;
///
/// // Define the set
/// let operator_set = operators::common_sets::worded();
///
/// let parsed = rustlogic::custom_parse("(NOT $[A] AND $[B]) OR $[C]", &operator_set);
/// # assert!(parsed.is_ok());
///
/// // -- snipp
/// ```
///
/// ## Having a customized operator set
/// ```
/// use rustlogic::operators;
///
/// // This will be our new symbol for the AND logical function
/// let new_and_operator = "<AND>";
///
/// // Then we take the default set and adjust the AND symbol
/// let custom_operator_set = operators::common_sets::default()
///     .adjust_and(new_and_operator);
///
/// // Now we can use this set to parse logical strings
/// let parsed = rustlogic::custom_parse("([A]<AND>[B])|[C]", &custom_operator_set);
/// # assert!(parsed.is_ok());
///
/// // -- snipp
/// ```
///
/// ## Evaluating a custom logical string
/// ```
/// use rustlogic::operators;
///
/// // Define the set
/// let operator_set = operators::common_sets::worded();
///
/// let parsed = rustlogic::custom_parse("(NOT FALSE AND TRUE) OR FALSE", &operator_set);
/// # assert!(parsed.is_ok());
/// # assert!(parsed.unwrap().get_value().is_ok());
///
/// /// Now contains the value of the logical expression
/// # let parsed = rustlogic::custom_parse("(NOT FALSE AND TRUE) OR FALSE", &operator_set);
/// let value = parsed.unwrap().get_value().unwrap();
/// # assert!(value);
/// ```
///
/// ## Evaluating a custom logical string with variables
/// ```
/// use rustlogic::operators;
/// use std::collections::HashMap;
///
/// // Define the set
/// let operator_set = operators::common_sets::worded();
///
/// let parsed = rustlogic::custom_parse("(NOT $[A] AND $[B]) OR $[C]", &operator_set);
/// # assert!(parsed.is_ok());
///
/// // We assign the variables to their values
/// let mut hm = HashMap::new();
/// hm.insert("A", false);
/// hm.insert("B", true);
/// hm.insert("C", false);
/// # assert!(parsed.unwrap().get_value_from_variables(&hm).is_ok());
///
/// // Now contains the value of the logical expression
/// # let parsed = rustlogic::custom_parse("(NOT $[A] AND $[B]) OR $[C]", &operator_set);
/// let value = parsed.unwrap().get_value_from_variables(&hm).unwrap();
/// # assert!(value);
/// ```
pub fn custom_parse(input_string: &str, operator_set: &OperatorSet) -> Result<LogicNode, usize> {
    let easy_parse_option = easy_parse(input_string, operator_set);
    if easy_parse_option.is_some() {
        return easy_parse_option.unwrap();
    }

    if input_string.starts_with(operator_set.not()) {
        let easy_parse_option = easy_parse(&input_string[operator_set.not().len()..], operator_set);
        if easy_parse_option.is_some() {
            return easy_parse_option
                .unwrap()
                .map_err(|err_loc| err_loc + operator_set.not().len())
                .map(|node| LogicNode::Not(Box::new(node)));
        }
    }

    use util::multi_search;

    let multi_search_query = vec![
        operator_set.group_open(),
        operator_set.variable_open(),
        operator_set.and(),
        operator_set.or(),
    ];
    let mut ms_start = 0;
    let mut ms_result = multi_search(input_string, &multi_search_query);

    while ms_result.is_some() {
        match ms_result {
            None => return Err(input_string.len()), // Unreachable branch
            Some((0, pool_index)) => {
                let group_content =
                    get_group_content(input_string, ms_start + pool_index, operator_set);

                if group_content.is_none() {
                    return Err(ms_start + pool_index + operator_set.group_open().len());
                }

                ms_start += pool_index
                    + group_content.unwrap().len()
                    + operator_set.group_open().len()
                    + operator_set.group_close().len();
                ms_result = multi_search(&input_string[ms_start..], &multi_search_query);
            }
            Some((1, pool_index)) => {
                let variable_content =
                    get_variable_content(input_string, ms_start + pool_index, operator_set);

                if variable_content.is_none() {
                    return Err(ms_start + pool_index + operator_set.variable_open().len());
                }

                ms_start += pool_index
                    + variable_content.unwrap().len()
                    + operator_set.variable_open().len()
                    + operator_set.variable_close().len();
                ms_result = multi_search(&input_string[ms_start..], &multi_search_query);
            }
            Some((_, pool_index)) => {
                return infix_parse(input_string, ms_start + pool_index, operator_set)
            }
        };
    }

    Err(input_string.len())
}

/// Parse a formula string into in [LogicNode](enum.LogicNode.html) object
///
/// Outputs a results with an ok of the [LogicNode](enum.LogicNode.html) or the location of the error
///
/// # Examples
///
/// ## Basic usage (A pure variable)
/// ```
/// # use std::collections::HashMap;
/// # use rustlogic::parse;
/// let a_variable = parse("[a]").expect("Failed to parse variable");
///
/// let mut variable_map = HashMap::new();
/// variable_map.insert("a", true);
///
/// let value = a_variable.get_value_from_variables(&variable_map).unwrap();
/// println!("{}", value); // Will print true!
/// # assert!(value);
/// ```
///
/// ## 4-1 Multiplexer
/// ```
/// # use std::collections::HashMap;
/// # use rustlogic::parse;
/// let multiplexer_4_to_1 = parse("([a]&~[x]&~[y])|([b]&~[x]&[y])|([c]&[x]&~[y])|([d]&[x]&[y])")
///     .expect("Failed to parse 4-1 multiplexer");
///
/// let mut variable_map = HashMap::new();
///
/// // Input: 1001
/// variable_map.insert("a", true);
/// variable_map.insert("b", false);
/// variable_map.insert("c", false);
/// variable_map.insert("d", true);
///
/// // Selector: 11
/// variable_map.insert("x", true);
/// variable_map.insert("y", true);
///
/// // Should select fourth item from bus so true
/// let value = multiplexer_4_to_1.get_value_from_variables(&variable_map).unwrap();
/// println!("{}", value); // Will print true!
/// # assert!(value);
/// # variable_map.insert("d", false);
/// # let value = multiplexer_4_to_1.get_value_from_variables(&variable_map).unwrap();
/// # assert!(!value);
/// ```
pub fn parse(input_string: &str) -> Result<LogicNode, usize> {
    let operator_set = operators::common_sets::default();
    custom_parse(input_string, &operator_set)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_group_content() {
        let default_op = operators::common_sets::default();

        assert_eq!(
            get_group_content("(Hi)", 0, &default_op),
            Some(String::from("Hi"))
        );

        assert_eq!(
            get_group_content("  (before(inbetween(in)[var)test])after)", 2, &default_op),
            Some(String::from("before(inbetween(in)[var)test])after"))
        );

        let non_default_op = operators::common_sets::default()
            .adjust_group_open(" { ")
            .adjust_group_close(" } ");

        assert_eq!(
            get_group_content(
                " { before { inbetween { in } [var } test] } after } ",
                0,
                &non_default_op
            ),
            Some(String::from(
                "before { inbetween { in } [var } test] } after"
            ))
        );

        assert_eq!(
            get_group_content(
                "before { inbetween { in } [var } test] } after } ",
                0,
                &non_default_op
            ),
            None
        );

        assert_eq!(
            get_group_content(
                " { before { inbetween { in } [var } test] } after",
                0,
                &non_default_op
            ),
            None
        );
    }

    #[test]
    fn test_get_variable_content() {
        let default_op = operators::common_sets::default();

        assert_eq!(
            get_variable_content("[Hi]", 0, &default_op),
            Some(String::from("Hi"))
        );

        assert_eq!(
            get_variable_content("  [before(inbetween(in)[var)test])after]", 2, &default_op),
            Some(String::from("before(inbetween(in)[var)test"))
        );

        let non_default_op = operators::common_sets::default()
            .adjust_variable_open(" { ")
            .adjust_variable_close(" } ");

        assert_eq!(
            get_variable_content(
                " { before { inbetween { in } [var } test] } after } ",
                0,
                &non_default_op
            ),
            Some(String::from("before { inbetween { in"))
        );

        assert_eq!(
            get_group_content(
                " { before { inbetween { in [var test] after ",
                0,
                &non_default_op
            ),
            None
        );
    }

    #[test]
    fn test_operator_set() {
        let operator_set = operators::common_sets::worded();

        let mut hm = HashMap::new();

        hm.insert("A", false);
        hm.insert("B", true);
        hm.insert("C", false);

        assert!(custom_parse("(NOT $[A] AND $[B]) OR $[C]", &operator_set)
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());

        assert!(custom_parse("(($[A]) AND $[B]) OR NOT $[C]", &operator_set)
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());

        assert!(!custom_parse("($[A] AND NOT $[B]) OR $[C]", &operator_set)
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
    }

    #[test]
    fn test_parsing() {
        assert!(parse("[a]").is_ok());
        assert!(parse("~[a]").is_ok());
        assert!(parse("([a])").is_ok());
        assert!(parse("[a]|[b]").is_ok());
        assert!(parse("[a]&[b]").is_ok());
        assert!(parse("1").is_ok());
        assert!(parse("0").is_ok());
        assert!(parse("([a]&([b]|0))").is_ok());

        assert!(parse("[a]&&[b]").is_err());
        assert!(parse("[a]||[b]").is_err());
        assert!(parse("~[a]&[b]").is_ok());
    }

    #[test]
    fn test_values() {
        let mut hm = HashMap::new();

        hm.insert("a", false);
        hm.insert("b", false);

        assert!(!parse("[a]").unwrap().get_value_from_variables(&hm).unwrap());
        assert!(parse("~[a]")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(!parse("([a])")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(!parse("[a]|[b]")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(!parse("[a]&[b]")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(parse("1").unwrap().get_value_from_variables(&hm).unwrap());
        assert!(!parse("0").unwrap().get_value_from_variables(&hm).unwrap());
        assert!(!parse("([a]&([b]|0))")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(!parse("~[a]&[b]")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());

        hm.insert("a", false);
        hm.insert("b", true);
        assert!(!parse("[a]").unwrap().get_value_from_variables(&hm).unwrap());
        assert!(parse("~[a]")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(!parse("([a])")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(parse("[a]|[b]")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(!parse("[a]&[b]")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(parse("1").unwrap().get_value_from_variables(&hm).unwrap());
        assert!(!parse("0").unwrap().get_value_from_variables(&hm).unwrap());
        assert!(!parse("([a]&([b]|0))")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(parse("~[a]&[b]")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());

        hm.insert("a", true);
        hm.insert("b", false);
        assert!(parse("[a]").unwrap().get_value_from_variables(&hm).unwrap());
        assert!(!parse("~[a]")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(parse("([a])")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(parse("[a]|[b]")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(!parse("[a]&[b]")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(parse("1").unwrap().get_value_from_variables(&hm).unwrap());
        assert!(!parse("0").unwrap().get_value_from_variables(&hm).unwrap());
        assert!(!parse("([a]&([b]|0))")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(!parse("~[a]&[b]")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());

        hm.insert("a", true);
        hm.insert("b", true);
        assert!(parse("[a]").unwrap().get_value_from_variables(&hm).unwrap());
        assert!(!parse("~[a]")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(parse("([a])")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(parse("[a]|[b]")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(parse("[a]&[b]")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(parse("1").unwrap().get_value_from_variables(&hm).unwrap());
        assert!(!parse("0").unwrap().get_value_from_variables(&hm).unwrap());
        assert!(parse("([a]&([b]|0))")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
        assert!(!parse("~[a]&[b]")
            .unwrap()
            .get_value_from_variables(&hm)
            .unwrap());
    }

    #[test]
    fn test_display() {
        let three_way_and = parse("([a]&[b]&[c])").expect("Unable to parse three way and");
        assert_eq!("( [a] & [b] & [c] )", format!("{}", three_way_and));

        let three_way_and = parse("(([a]&[b])&[c])").expect("Unable to parse three way and");
        assert_eq!("( [a] & [b] & [c] )", format!("{}", three_way_and));

        let three_way_and = parse("([a]&([b]&[c]))").expect("Unable to parse three way and");
        assert_eq!("( [a] & [b] & [c] )", format!("{}", three_way_and));

        let three_way_or = parse("([a]|[b]|[c])").expect("Unable to parse three way or");
        assert_eq!("( [a] | [b] | [c] )", format!("{}", three_way_or));

        let formula = parse("(~[a]&~[b]&~[c])").expect("Unable to parse three way and");
        assert_eq!("( ~[a] & ~[b] & ~[c] )", format!("{}", formula));
    }
}
