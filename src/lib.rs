//! Hello fellow Rustacians! RustLogic is a crate for parsing and handling simple logical expressings.
//!
//! This crate contains the basic foundation for handling stringed logical formulas.
//! If you want to want to submit an issue or a pull request,
//! please visit the [GitHub](https://github.com/coastalwhite/rustlogic) page.
//!
//! Thanks for your time and enjoy this crate!
//!
//! # Example
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

mod multidimensional_logicnode;
mod util;

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

/// Returns if a character is allowed within a variable name
///
/// For now:
/// Check if a certain ASCII character in the form of a *u8*
/// falls into the alphabetic range, numeric range or is - or _
fn is_allowed_character_in_variable(character: u8) -> bool {
    (character >= b'a' && character <= b'z')
        || (character >= b'A' && character <= b'Z')
        || (character >= b'0' && character <= b'9')
        || character == b'_'
        || character == b'-'
        || character == b'$'
        || character == b':'
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
    /// # assert_eq!(or.to_string(), "([AND]|[b])");
    /// let and_in_or = or.insert_formula(
    ///     "AND",
    ///     &parse("[x]&[y]").expect("Error parsing AND")
    /// );
    ///
    /// println!("{}", and_in_or); // Will print (([x]&[y])|[b])
    /// # assert_eq!(and_in_or.to_string(), "(([x]&[y])|[b])");
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

/// The opening symbol of a priority group
/// ## Default: '\('
pub const DEFAULT_GROUP_OPEN_SYMBOL: &str = "(";
/// The closing symbol of a priority group
/// ## Default: '\)'
pub const DEFAULT_GROUP_CLOSE_SYMBOL: &str = ")";

/// The symbol used for the AND operation
/// ## Default: '&'
pub const DEFAULT_AND_SYMBOL: &str = "&";

/// The symbol used for the OR operation
/// ## Default: '|'
pub const DEFAULT_OR_SYMBOL: &str = "|";

/// The symbol used for the NOT operation
/// ## Default: '~'
pub const DEFAULT_NOT_SYMBOL: &str = "~";

/// The symbol used for true state
/// ## Default: '1'
pub const DEFAULT_TRUE_SYMBOL: &str = "1";

/// The symbol used for false state
/// ## Default: '0'
pub const DEFAULT_FALSE_SYMBOL: &str = "0";

/// The opening symbol for a variable
/// ## Default: '\['
pub const DEFAULT_VARIABLE_OPEN_SYMBOL: &str = "[";

/// The closing symbol for a variable
/// ## Default: '\]'
pub const DEFAULT_VARIABLE_CLOSE_SYMBOL: &str = "]";

/// Function used to find the matching parenthesis given a string
/// and a position open a opening group symbol (taking into account depth)
/// Will return None if position given is not a bracket or
/// if no matching bracket was found
fn matching_group_symbol(input_string: &str, position: usize) -> Option<usize> {
    // // Fetch opening character and check if
    // // this is a opening character for a priority group
    // let opening_character = input_string.as_bytes()[position];
    // if opening_character != GROUP_OPEN_SYMBOL {
    //     return None;
    // }

    // // Loop through all the characters untill a matching symbol is found
    // let mut depth: u16 = 0;
    // for (index, character) in input_string
    //     .as_bytes()
    //     .iter()
    //     .skip(position + 1)
    //     .enumerate()
    // {
    //     // Shadow character to get ownership
    //     let character = character.clone();

    //     // If character equals closing symbol for priority group
    //     if character == GROUP_CLOSE_SYMBOL {
    //         // Check if not a layer deep
    //         match depth {
    //             // If zero layers deep,
    //             // return index with correction for starting position
    //             0 => return Some(index + position + 1),

    //             // If more than zero layers deep,
    //             // go up one layer
    //             _ => {
    //                 depth -= 1;
    //             }
    //         }

    //     // If character equals opening symbol for priority group
    //     // go one layer deeper
    //     } else if character == GROUP_OPEN_SYMBOL {
    //         depth += 1;
    //     }
    // }

    // No matching closing symbol found so return nothing
    None
}

/// Function used to fetch if a input consists of a variable,
/// and ifso what this variable is
fn get_variable_name(input_string: &str, position: usize) -> Option<String> {
    // // Fetch opening character and check if
    // // this is a opening character for a variable
    // let opening_character = input_string.as_bytes()[position];
    // if opening_character != VARIABLE_OPEN_SYMBOL {
    //     return None;
    // }

    // // Loop over all characters
    // for (index, character) in input_string
    //     .as_bytes()
    //     .iter()
    //     .skip(position + 1)
    //     .enumerate()
    // {
    //     // Shadow character to take ownership
    //     let character = character.clone();

    //     // If character is the closing symbol
    //     if character == VARIABLE_CLOSE_SYMBOL {
    //         // If not the end of the string
    //         if index + position + 1 < input_string.len() - 1 {
    //             return None;
    //         }

    //         // Return variable
    //         return Some(String::from(
    //             &input_string[(position + 1)..(index + position + 1)],
    //         ));
    //     }

    //     // Check if character is allowed within variable
    //     if !is_allowed_character_in_variable(character) {
    //         return None;
    //     }
    // }

    // If no closing character was found return none
    None
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
    // use LogicNode::*;

    // // Return on empty strings
    // if input_string == "" {
    //     return Err(0);
    // }

    // // Match absolute symbols (0/1)
    // if input_string.len() == 1 {
    //     if input_string.as_bytes()[0] == FALSE_SYMBOL {
    //         return Ok(False);
    //     }
    //     if input_string.as_bytes()[0] == TRUE_SYMBOL {
    //         return Ok(True);
    //     }
    // }

    // // Match priority groups
    // match matching_group_symbol(input_string, 0) {
    //     Some(end) => {
    //         if end == input_string.len() - 1 {
    //             return parse(&input_string[1..input_string.len() - 1]).map_err(|pos| pos + 1);
    //             // Correct error for new string
    //         }
    //     }
    //     _ => (),
    // }

    // // Match variables
    // match get_variable_name(input_string, 0) {
    //     Some(variable) => {
    //         return Ok(Variable(variable));
    //     }
    //     _ => (),
    // }

    // // Match NOT operation
    // if input_string.as_bytes()[0] == NOT_SYMBOL {
    //     // Match a absolute after / or error after
    //     if input_string.len() == 2 {
    //         return Ok(Not(Box::new(
    //             parse(&input_string[1..]).map_err(|pos| pos + 1)?,
    //         )));
    //     }

    //     // Match a priority group after
    //     match matching_group_symbol(input_string, 1) {
    //         Some(end) => {
    //             if end == input_string.len() - 1 {
    //                 return Ok(Not(Box::new(
    //                     parse(&input_string[2..input_string.len() - 1]).map_err(|pos| pos + 2)?,
    //                 )));
    //             }
    //         }
    //         _ => (),
    //     }

    //     // Match a variable after
    //     match get_variable_name(input_string, 1) {
    //         Some(variable) => {
    //             return Ok(Not(Box::new(Variable(variable))));
    //         }
    //         _ => (),
    //     }
    // }

    // let mut index = 0;
    // while index < input_string.len() {
    //     let character = input_string.as_bytes()[index];

    //     match character {
    //         // Skip over priority groups
    //         GROUP_OPEN_SYMBOL => match matching_group_symbol(input_string, index) {
    //             None => return Err(index),
    //             Some(position) => {
    //                 index = position;
    //             }
    //         },

    //         // Match and symbol
    //         AND_SYMBOL => {
    //             return Ok(And(
    //                 Box::new(parse(&input_string[..index])?),
    //                 Box::new(parse(&input_string[index + 1..]).map_err(|pos| pos + index + 1)?),
    //             ));
    //         }

    //         // Match Or Symbol
    //         OR_SYMBOL => {
    //             return Ok(Or(
    //                 Box::new(parse(&input_string[..index])?),
    //                 Box::new(parse(&input_string[index + 1..]).map_err(|pos| pos + index + 1)?),
    //             ));
    //         }
    //         // Do nothing on allowed characters
    //         c if is_allowed_character_in_variable(c) => (),
    //         FALSE_SYMBOL
    //         | TRUE_SYMBOL
    //         | NOT_SYMBOL
    //         | VARIABLE_OPEN_SYMBOL
    //         | VARIABLE_CLOSE_SYMBOL => (),

    //         // Throw error on non allowed characters
    //         _ => {
    //             return Err(index);
    //         }
    //     }
    //     index += 1;
    // }

    // // If no match was found return full length
    return Err(input_string.len());
}

/// OperatorSymbols struct used to specify non-default operator symbols for custom_parse
pub struct OperatorSymbols {
    GROUP_OPEN_SYMBOL: String,
    GROUP_CLOSE_SYMBOL: String,
    AND_SYMBOL: String,
    OR_SYMBOL: String,
    NOT_SYMBOL: String,
    TRUE_SYMBOL: String,
    FALSE_SYMBOL: String,
    VARIABLE_OPEN_SYMBOL: String,
    VARIABLE_CLOSE_SYMBOL: String,
}

impl OperatorSymbols {
    pub fn new() -> OperatorSymbols {
        OperatorSymbols {
            GROUP_OPEN_SYMBOL: String::from(DEFAULT_GROUP_OPEN_SYMBOL),
            GROUP_CLOSE_SYMBOL: String::from(DEFAULT_GROUP_CLOSE_SYMBOL),
            AND_SYMBOL: String::from(DEFAULT_AND_SYMBOL),
            OR_SYMBOL: String::from(DEFAULT_OR_SYMBOL),
            NOT_SYMBOL: String::from(DEFAULT_NOT_SYMBOL),
            TRUE_SYMBOL: String::from(DEFAULT_TRUE_SYMBOL),
            FALSE_SYMBOL: String::from(DEFAULT_FALSE_SYMBOL),
            VARIABLE_OPEN_SYMBOL: String::from(DEFAULT_VARIABLE_OPEN_SYMBOL),
            VARIABLE_CLOSE_SYMBOL: String::from(DEFAULT_VARIABLE_CLOSE_SYMBOL),
        }
    }

    pub fn adjust_and(self: Self, to: &str) -> OperatorSymbols {
        self.AND_SYMBOL = String::from(to);

        self
    }

    pub fn adjust_or(self: Self, to: &str) -> OperatorSymbols {
        self.OR_SYMBOL = String::from(to);

        self
    }

    pub fn adjust_not(self: Self, to: &str) -> OperatorSymbols {
        self.NOT_SYMBOL = String::from(to);

        self
    }

    pub fn adjust_true(self: Self, to: &str) -> OperatorSymbols {
        self.TRUE_SYMBOL = String::from(to);

        self
    }

    pub fn adjust_false(self: Self, to: &str) -> OperatorSymbols {
        self.FALSE_SYMBOL = String::from(to);

        self
    }

    pub fn adjust_group_open(self: Self, to: &str) -> OperatorSymbols {
        self.GROUP_OPEN_SYMBOL = String::from(to);

        self
    }

    pub fn adjust_group_close(self: Self, to: &str) -> OperatorSymbols {
        self.GROUP_CLOSE_SYMBOL = String::from(to);

        self
    }

    pub fn adjust_variable_open(self: Self, to: &str) -> OperatorSymbols {
        self.VARIABLE_OPEN_SYMBOL = String::from(to);

        self
    }

    pub fn adjust_variable_close(self: Self, to: &str) -> OperatorSymbols {
        self.VARIABLE_CLOSE_SYMBOL = String::from(to);

        self
    }

    pub fn new_with(
        and_symbol: &str,
        or_symbol: &str,
        not_symbol: &str,
        true_symbol: &str,
        false_symbol: &str,
        group_open_symbol: &str,
        group_close_symbol: &str,
        variable_open_symbol: &str,
        variable_close_symbol: &str,
    ) -> OperatorSymbols {
        OperatorSymbols {
            GROUP_OPEN_SYMBOL: String::from(group_open_symbol),
            GROUP_CLOSE_SYMBOL: String::from(group_close_symbol),
            AND_SYMBOL: String::from(and_symbol),
            OR_SYMBOL: String::from(or_symbol),
            NOT_SYMBOL: String::from(not_symbol),
            TRUE_SYMBOL: String::from(true_symbol),
            FALSE_SYMBOL: String::from(false_symbol),
            VARIABLE_OPEN_SYMBOL: String::from(variable_open_symbol),
            VARIABLE_CLOSE_SYMBOL: String::from(variable_close_symbol),
        }
    }
}

/// Parsing of logic formulas with non-default operator symbols
/// Use the [OperatorSymbols](struct.OperatorSymbols.html) Struct
pub fn custom_parse(
    input_string: &str,
    operator_symbols: &OperatorSymbols,
) -> Result<LogicNode, usize> {
    Err(1)
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert_eq!("([a]&[b]&[c])", format!("{}", three_way_and));

        let three_way_and = parse("(([a]&[b])&[c])").expect("Unable to parse three way and");
        assert_eq!("([a]&[b]&[c])", format!("{}", three_way_and));

        let three_way_and = parse("([a]&([b]&[c]))").expect("Unable to parse three way and");
        assert_eq!("([a]&[b]&[c])", format!("{}", three_way_and));

        let three_way_or = parse("([a]|[b]|[c])").expect("Unable to parse three way or");
        assert_eq!("([a]|[b]|[c])", format!("{}", three_way_or));

        let formula = parse("(~[a]&~[b]&~[c])").expect("Unable to parse three way and");
        assert_eq!("(~[a]&~[b]&~[c])", format!("{}", formula));
    }
}
