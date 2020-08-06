//! Contains all the functionality to adjust operators when parsing

macro_rules! operator_getset {
    ($setter:ident, $getter:ident) => {
        /// Setter used to adjust operator within [OperatorSet](struct.OperatorSet.html)
        pub fn $setter(self: Self, to: &str) -> OperatorSet {
            let mut operator_clone = self.clone();
            operator_clone.$getter = String::from(to);
            operator_clone
        }

        /// Getter used to fetch operator within [OperatorSet](struct.OperatorSet.html)
        pub fn $getter(self: &Self) -> &str {
            &self.$getter[..]
        }
    };
}

/// OperatorSet struct used to specify non-default operator symbols for [custom_parse](../../fn.custom_parse.html) function
///
/// # Examples
/// ## Using the common sets
/// ```
/// use rustlogic::operators;
///
/// let mathematical_version = operators::common_sets::mathematical();
///
/// // We create a parsed logic node
/// let parse_result = rustlogic::custom_parse("(![A]*[B])+[C]", &mathematical_version);
/// # assert!(parse_result.is_some());
///
/// // -- snipp
/// ```
/// For all the common sets [click here](common_sets/index.html)
///
/// ## Defining your own sets
/// ```
/// use rustlogic::operators::OperatorSet;
///
/// // Create a operator set with words
/// let worded_version = OperatorSet::new(
///     " AND ", " OR ", "NOT ", "TRUE", "FALSE", "(", ")", "$[", "]",
/// );
///
/// // Attempt to parse a logical string
/// let parse_result = rustlogic::custom_parse("(NOT $[A] AND $[B]) OR $[C]", &worded_version);
/// # assert!(parse_result.is_some());
///
/// // -- snipp
/// ```
///
/// ## Adjusting a pre-existing set
/// ```
/// use rustlogic::operators;
///
/// // Adjust the group brackets to be curly
/// let curly_bracket_groups = operators::common_sets::default()
///      .adjust_group_open("{")
///      .adjust_group_close("}");
///
/// // We create a parsed logic node
/// let parse_result = rustlogic::custom_parse("{~[A]&[B]}|[C]", &curly_bracket_groups);
/// # assert!(parse_result.is_some());
///
/// // -- snipp
/// ```
#[derive(Clone)]
pub struct OperatorSet {
    group_open: String,
    group_close: String,
    and: String,
    or: String,
    not: String,
    true_symbol: String,
    false_symbol: String,
    variable_open: String,
    variable_close: String,
}

impl OperatorSet {
    pub fn new(
        and: &str,
        or: &str,
        not: &str,
        true_symbol: &str,
        false_symbol: &str,
        group_open: &str,
        group_close: &str,
        variable_open: &str,
        variable_close: &str,
    ) -> OperatorSet {
        OperatorSet {
            group_open: String::from(group_open),
            group_close: String::from(group_close),
            and: String::from(and),
            or: String::from(or),
            not: String::from(not),
            true_symbol: String::from(true_symbol),
            false_symbol: String::from(false_symbol),
            variable_open: String::from(variable_open),
            variable_close: String::from(variable_close),
        }
    }

    operator_getset!(adjust_and, and);
    operator_getset!(adjust_or, or);
    operator_getset!(adjust_not, not);
    operator_getset!(adjust_true_symbol, true_symbol);
    operator_getset!(adjust_false_symbol, false_symbol);
    operator_getset!(adjust_group_open, group_open);
    operator_getset!(adjust_group_close, group_close);
    operator_getset!(adjust_variable_open, variable_open);
    operator_getset!(adjust_variable_close, variable_close);
}

/// Some common operator sets used
pub mod common_sets {
    use super::OperatorSet;

    /// Returns the default set of operators used with the [parse](../../fn.parse.html) function
    ///
    /// This includes "&", "|" and "~" as logical functions,
    /// "1" and "0" as absolute values, "(" and ")" as group opener and closer
    /// and "[" and "]" as variable opener and closer.
    pub fn default() -> OperatorSet {
        OperatorSet::new("&", "|", "~", "1", "0", "(", ")", "[", "]")
    }

    /// Returns an english worded set of operators
    ///
    /// This includes " AND ", " OR " and "NOT " as logical functions,
    /// "TRUE" and "FALSE" as absolute values, "(" and ")" as group opener and closer
    /// and "$[" and "]" as variable opener and closer.
    pub fn worded() -> OperatorSet {
        OperatorSet::new(
            " AND ", " OR ", "NOT ", "TRUE", "FALSE", "(", ")", "$[", "]",
        )
    }

    /// Returns a mathematical set of operators
    ///
    /// This includes "*", "+" and "!" as logical functions,
    /// "1" and "0" as absolute values, "(" and ")" as group opener and closer
    /// and "[" and "]" as variable opener and closer.
    pub fn mathematical() -> OperatorSet {
        OperatorSet::new("*", "+", "!", "1", "0", "(", ")", "[", "]")
    }
}
