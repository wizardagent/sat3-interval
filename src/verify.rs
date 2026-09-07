// Minimal verifier for data/sat3_values.json (no crate deps).
// Build: rustc -O src/verify.rs -o /tmp/sat3-verify && /tmp/sat3-verify data/sat3_values.json

use std::env;
use std::fs;

fn is_free(a: &[i32]) -> bool {
    let s: std::collections::HashSet<i32> = a.iter().copied().collect();
    for i in 0..a.len() {
        for j in i + 1..a.len() {
            let c = 2 * a[j] - a[i];
            if s.contains(&c) {
                return false;
            }
        }
    }
    true
}

fn completes(a: &[i32], t: i32) -> bool {
    for i in 0..a.len() {
        for j in i + 1..a.len() {
            let x = a[i];
            let y = a[j];
            if 2 * y - x == t || 2 * x - y == t || (x + y) % 2 == 0 && (x + y) / 2 == t {
                if t != x && t != y {
                    return true;
                }
            }
        }
    }
    false
}

fn is_maximal(a: &[i32], n: i32) -> bool {
    if !is_free(a) {
        return false;
    }
    for t in 1..=n {
        if a.contains(&t) {
            continue;
        }
        if !completes(a, t) {
            return false;
        }
    }
    true
}

fn main() {
    let path = env::args().nth(1).expect("json path");
    let text = fs::read_to_string(&path).expect("read");
    // Tiny extractor: find "n": N ... "sat": S ... "example": [..]
    let mut ok = 0u32;
    let mut i = 0;
    let bytes = text.as_bytes();
    while i < bytes.len() {
        if text[i..].starts_with("\"n\":") {
            let rest = &text[i + 4..];
            let n: i32 = rest
                .chars()
                .skip_while(|c| c.is_whitespace() || *c == ':')
                .take_while(|c| c.is_ascii_digit())
                .collect::<String>()
                .parse()
                .unwrap_or(0);
            if n == 0 {
                i += 1;
                continue;
            }
            // find next example array after this n
            if let Some(rel) = text[i..].find("\"example\":") {
                let after = &text[i + rel + 10..];
                if let Some(lb) = after.find('[') {
                    if let Some(rb) = after[lb..].find(']') {
                        let arr = &after[lb + 1..lb + rb];
                        let a: Vec<i32> = arr
                            .split(',')
                            .filter_map(|s| s.trim().parse().ok())
                            .collect();
                        assert!(is_maximal(&a, n), "not maximal");
                        ok += 1;
                        i += rel + lb + rb;
                        continue;
                    }
                }
            }
        }
        i += 1;
    }
    println!("verified {ok} examples");
    assert!(ok >= 40, "expected 40 examples");
}
