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

/// Function used to find the first occurance of a substring (spear) in a bigger string (pool)
/// Will return None if no match is found or if the spear is empty
pub fn search(pool: &str, spear: &str) -> Option<usize> {
    if pool.len() < spear.len() || spear.is_empty() {
        return None;
    }

    if pool.chars().next() == spear.chars().next() && pool[1..].starts_with(&spear[1..]) {
        Some(0)
    } else {
        match search(&pool[1..], spear) {
            Some(x) => Some(x + 1),
            None => None,
        }
    }
}

/// Function used to find first occurance of a number of substrings (spears) in a bigger string (pool)
/// Will return None if no match is found and will ignore empty spears
pub fn multi_search(pool: &str, spears: &Vec<&str>) -> Option<(usize, usize)> {
    for (spear_index, spear) in spears.iter().enumerate() {
        if pool.len() < spear.len() || spear.is_empty() {
            continue;
        }

        if pool.chars().next() == spear.chars().next() && pool[1..].starts_with(&spear[1..]) {
            return Some((spear_index, 0));
        }
    }

    if pool.len() == 1 {
        return None;
    }

    match multi_search(&pool[1..], spears) {
        Some((spear_index, x)) => Some((spear_index, x + 1)),
        None => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ut_search() {
        assert_eq!(search("hi", ""), None);
        assert_eq!(search("Hello World!", "World"), Some(6));
        assert_eq!(search("Hello Wrld!", "World"), None);
    }

    #[test]
    fn ut_multi_search() {
        let query = vec!["World", "Boy"];

        assert_eq!(multi_search("hi", &query), None);
        assert_eq!(multi_search("Hello World!", &query), Some((0, 6)));
        assert_eq!(multi_search("Hello Wrld!", &query), None);

        assert_eq!(multi_search("Hello Boy!", &query), Some((1, 6)));
    }
}
