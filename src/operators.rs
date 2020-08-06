macro_rules! operator_getset {
    ($setter:ident, $getter:ident) => {
        /// Setter used to adjust operator within [OperatorSymbols](struct.OperatorSymbols.html)
        pub fn $setter(self: Self, to: &str) -> OperatorSymbols {
            let mut operator_clone = self.clone();
            operator_clone.$getter = String::from(to);
            operator_clone
        }

        /// Getter used to fetch operator within [OperatorSymbols](struct.OperatorSymbols.html)
        pub fn $getter(self: &Self) -> &str {
            &self.$getter[..]
        }
    };
}

/// OperatorSymbols struct used to specify non-default operator symbols for custom_parse
#[derive(Clone)]
pub struct OperatorSymbols {
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

impl OperatorSymbols {
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
    ) -> OperatorSymbols {
        OperatorSymbols {
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

pub mod common_sets {
    use super::OperatorSymbols;
    pub fn default() -> OperatorSymbols {
        OperatorSymbols::new("&", "|", "~", "1", "0", "(", ")", "[", "]")
    }

    pub fn worded() -> OperatorSymbols {
        OperatorSymbols::new(
            " AND ", " OR ", "NOT ", "TRUE", "FALSE", "(", ")", "$[", "]",
        )
    }

    pub fn mathetical() -> OperatorSymbols {
        OperatorSymbols::new("*", "+", "!", "1", "0", "(", ")", "[", "]")
    }
}
