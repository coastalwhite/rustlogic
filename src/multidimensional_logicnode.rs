#[derive(Debug)]
pub enum MultiDimensionalLogicNode {
    And(Vec<MultiDimensionalLogicNode>),
    Or(Vec<MultiDimensionalLogicNode>),
    Not(Box<MultiDimensionalLogicNode>),
    True,
    False,
    Variable(String),
}

impl MultiDimensionalLogicNode {
    pub fn new(logic_node: &super::LogicNode) -> MultiDimensionalLogicNode {
        match logic_node {
            super::LogicNode::And(left, right) => {
                let multi_dim_left = MultiDimensionalLogicNode::new(left);
                let multi_dim_right = MultiDimensionalLogicNode::new(right);

                let mut ands = Vec::<MultiDimensionalLogicNode>::new();

                use MultiDimensionalLogicNode::And;

                match multi_dim_left {
                    And(mut left_ands) => ands.append(&mut left_ands),
                    _ => ands.push(multi_dim_left),
                };

                match multi_dim_right {
                    And(mut right_ands) => ands.append(&mut right_ands),
                    _ => ands.push(multi_dim_right),
                };

                And(ands)
            }

            super::LogicNode::Or(left, right) => {
                let multi_dim_left = MultiDimensionalLogicNode::new(left);
                let multi_dim_right = MultiDimensionalLogicNode::new(right);

                let mut ors = Vec::<MultiDimensionalLogicNode>::new();

                use MultiDimensionalLogicNode::Or;

                match multi_dim_left {
                    Or(mut left_ors) => ors.append(&mut left_ors),
                    _ => (),
                };

                match multi_dim_right {
                    Or(mut right_ors) => ors.append(&mut right_ors),
                    _ => (),
                };

                Or(ors)
            }

            super::LogicNode::Not(child) => {
                MultiDimensionalLogicNode::Not(Box::new(MultiDimensionalLogicNode::new(child)))
            }

            super::LogicNode::True => MultiDimensionalLogicNode::True,
            super::LogicNode::False => MultiDimensionalLogicNode::False,

            super::LogicNode::Variable(var) => MultiDimensionalLogicNode::Variable(var.clone()),
        }
    }
}

impl std::fmt::Display for MultiDimensionalLogicNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use MultiDimensionalLogicNode::*;

        match self {
            And(ands) => {
                if ands.len() == 0 {
                    return write!(f, "");
                }

                let joined_strings = super::util::join(
                    ands.iter().map(|x| format!("{}", x)).collect(),
                    format!("{}", super::AND_SYMBOL as char),
                );

                write!(
                    f,
                    "{group_open}{}{group_close}",
                    joined_strings,
                    group_open = super::GROUP_OPEN_SYMBOL as char,
                    group_close = super::GROUP_CLOSE_SYMBOL as char
                )
            }
            Or(ors) => {
                if ors.len() == 0 {
                    return write!(f, "");
                }

                let joined_strings = super::util::join(
                    ors.iter().map(|x| format!("{}", x)).collect(),
                    format!("{}", super::OR_SYMBOL as char),
                );

                write!(
                    f,
                    "{group_open}{}{group_close}",
                    joined_strings,
                    group_open = super::GROUP_OPEN_SYMBOL as char,
                    group_close = super::GROUP_CLOSE_SYMBOL as char
                )
            }

            Not(child) => write!(
                f,
                "{not_symbol}{}",
                child,
                not_symbol = super::NOT_SYMBOL as char
            ),

            True => write!(f, "{}", super::TRUE_SYMBOL as char),

            False => write!(f, "{}", super::FALSE_SYMBOL as char),

            Variable(var) => write!(
                f,
                "{var_open}{}{var_close}",
                var,
                var_open = super::VARIABLE_OPEN_SYMBOL as char,
                var_close = super::VARIABLE_CLOSE_SYMBOL as char
            ),
        }
    }
}

impl std::clone::Clone for MultiDimensionalLogicNode {
    fn clone(&self) -> Self {
        use MultiDimensionalLogicNode::*;

        match self {
            And(ands) => And(ands.iter().cloned().collect()),
            Or(ors) => Or(ors.iter().cloned().collect()),
            Not(child) => Not(child.clone()),
            True => True,
            False => False,
            Variable(var) => Variable(var.clone()),
        }
    }
}
