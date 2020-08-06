Hello fellow Rustacians! RustLogic is a crate for parsing and handling simple logical expressings.

# Description

This crate provides a fast way of parsing logical strings into a tree object.
Furthermore, one can insert variables into this equation for single parsing-multiple outputs.

# Examples

## 4-1 Multiplexer

```
use std::collections::HashMap;
let multiplexer_4_to_1 =
    rustlogic::parse(
        "([a]&~[x]&~[y])|([b]&~[x]&[y])|([c]&[x]&~[y])|([d]&[x]&[y])"
    )
    .expect("Failed to parse 4-1 multiplexer");

let mut variable_map = HashMap::new();

// Input: 1001
variable_map.insert("a", true);
variable_map.insert("b", false);
variable_map.insert("c", false);
variable_map.insert("d", true);

// Selector: 11
variable_map.insert("x", true);
variable_map.insert("y", true);

// Should select fourth item from bus so true
let value = multiplexer_4_to_1.get_value_from_variables(&variable_map).unwrap();
println!("{}", value); // Will print true!
```

## Evaluating a logical string with variables and custom logical operators

```
use rustlogic::operators;
use std::collections::HashMap;

// Define the set
let operator_set = operators::common_sets::worded();

let parsed = rustlogic::custom_parse("(NOT $[A] AND TRUE) OR $[B]", &operator_set);

// We assign the variables to their values
let mut hm = HashMap::new();
hm.insert("A", false);
hm.insert("B", false);

// Now contains the value of the logical expression
let value = parsed.unwrap().get_value_from_variables(&hm).unwrap();
```

# Issues

If you want to want to submit an issue or a pull request,
please visit the [GitHub](https://github.com/coastalwhite/rustlogic) page.

Thanks for your time and enjoy this crate!
