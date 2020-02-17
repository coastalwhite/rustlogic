pub fn join(strings: Vec<String>, by: String) -> String {
    let mut output = String::from("");

    if strings.len() == 0 {
        return String::from("");
    }

    for (index, string) in strings.iter().enumerate() {
        if index < strings.len() - 1 {
            output.push_str(&format!("{}{}", string, by)[..]);
        } else {
            output.push_str(&format!("{}", string)[..]);
        }
    }

    output
}
