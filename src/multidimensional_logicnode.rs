use crate::operators::OperatorSet;

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
                    _ => ors.push(multi_dim_left),
                };

                match multi_dim_right {
                    Or(mut right_ors) => ors.append(&mut right_ors),
                    _ => ors.push(multi_dim_right),
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

    pub fn to_string_using_set(&self, operator_set: &OperatorSet) -> String {
        use MultiDimensionalLogicNode::*;

        match self {
            And(ands) => {
                if ands.len() == 0 {
                    return format!("");
                }

                let joined_strings = super::util::join(
                    ands.iter()
                        .map(|x| format!("{}", x.to_string_using_set(operator_set)))
                        .collect(),
                    format!("{}", operator_set.and()),
                );

                format!(
                    "{group_open}{}{group_close}",
                    joined_strings,
                    group_open = operator_set.group_open(),
                    group_close = operator_set.group_close()
                )
            }
            Or(ors) => {
                if ors.len() == 0 {
                    return format!("");
                }

                let joined_strings = super::util::join(
                    ors.iter()
                        .map(|x| format!("{}", x.to_string_using_set(operator_set)))
                        .collect(),
                    format!("{}", operator_set.or()),
                );

                format!(
                    "{group_open}{}{group_close}",
                    joined_strings,
                    group_open = operator_set.group_open(),
                    group_close = operator_set.group_close()
                )
            }

            Not(child) => format!(
                "{not_symbol}{}",
                child.to_string_using_set(operator_set),
                not_symbol = operator_set.not()
            ),

            True => format!("{}", operator_set.true_symbol()),

            False => format!("{}", operator_set.false_symbol()),

            Variable(var) => format!(
                "{var_open}{}{var_close}",
                var,
                var_open = operator_set.variable_open(),
                var_close = operator_set.variable_close()
            ),
        }
    }
}

impl std::fmt::Display for MultiDimensionalLogicNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.to_string_using_set(&crate::operators::common_sets::display())
        )
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
