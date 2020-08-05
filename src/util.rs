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

/// Function used to find a substring (spear) in a bigger string (pool)
/// Will return None if no match is found or if the spear is empty
pub fn search(pool: &str, spear: &str) -> Option<usize> {
    if pool.len() < spear.len() || spear.is_empty() {
        return None;
    }

    if pool.chars().next() == spear.chars().next() && pool[1..].starts_with(&spear[1..]) {
        Some(0)
    } else {
        search(&pool[1..], spear)
    }
}
