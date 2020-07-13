#![warn(missing_docs)]
/*!

A small library for minimizing or maximizing sets, useful for delta-debugging.

Really it's minimizing/maximizing sequences, as the oracles may rely on
candidates being a subsequence (same order) of the initial set.

# Examples
```
let set = vec![0, 1, 2, 3, 0, 1, 2, 3];
let has_one_and_three = |s: &[i32]| s.contains(&1) && s.contains(&3);
let minimal = delta_debug::minimize(set, has_one_and_three);
assert_eq!(minimal, vec![1, 3]);

let set = vec![0, 1, 2, 3, 0, 1, 2, 3];
let all_even = |s: &[i32]| s.iter().all(|i| *i % 2 == 0);
let maximal = delta_debug::maximize(set, all_even);
assert_eq!(maximal, vec![0, 2, 0, 2]);


// For non-Clone type, references work just fine
struct Foo(i32);
let set: Vec<Foo> = vec![0, 1, 2, 3, 0, 1, 2, 3].into_iter().map(Foo).collect();
let refs: Vec<&Foo> = set.iter().collect();
let all_even = |s: &[&Foo]| s.iter().all(|foo| foo.0 % 2 == 0);
let maximal = delta_debug::maximize(refs, all_even);
let ints: Vec<i32> = maximal.iter().map(|foo| foo.0).collect();
assert_eq!(ints, vec![0, 2, 0, 2]);
```

*/

/// Minimize a set given an oracle.
///
/// It consumes the given set because it uses that allocation.
pub fn minimize<T, F>(mut set: Vec<T>, mut oracle: F) -> Vec<T>
where
    T: Clone,
    F: FnMut(&[T]) -> bool,
{
    let mut times_shrunk = 0;
    let mut candidate = Vec::with_capacity(set.len());

    'outer: loop {
        for chunk_len in (0..).map(|i| set.len() / (2 << i)).take_while(|n| *n > 0) {
            debug_assert!(0 < chunk_len);
            debug_assert!(chunk_len <= set.len() / 2);

            let mut missing = 0;
            while missing + chunk_len <= set.len() {
                candidate.clear();
                candidate.extend(set[..missing].iter().cloned());
                candidate.extend(set[missing + chunk_len..].iter().cloned());
                missing += chunk_len;

                if oracle(&candidate) {
                    std::mem::swap(&mut set, &mut candidate);
                    times_shrunk += 1;
                    continue 'outer;
                }
            }
        }

        // if we got this far, see if we can go all the way to empty
        if set.len() == 1 && oracle(&[]) {
            return Vec::new();
        }

        if times_shrunk == 0 && !oracle(&set) {
            panic!("Failed to shrink, and even the input set failed the oracle!")
        }

        debug_assert!(oracle(&set));
        return set;
    }
}

/// Maximize a set given an oracle.
///
/// It consumes the given set because it uses that allocation.
pub fn maximize<T, F>(set: Vec<T>, mut oracle: F) -> Vec<T>
where
    T: Clone,
    F: FnMut(&[T]) -> bool,
{
    let build_set = |to_remove: &[usize]| {
        // list of indices to remove is sorted and distinct
        debug_assert!(to_remove.windows(2).all(|w| w[0] < w[1]));
        let mut candidate = Vec::with_capacity(set.len() - to_remove.len());
        let mut to_remove = to_remove.iter().peekable();
        for (i, t) in set.iter().enumerate() {
            if to_remove.peek().map_or(false, |r| **r == i) {
                to_remove.next();
            } else {
                candidate.push(t.clone())
            }
        }
        candidate
    };

    let indices = (0..set.len()).collect();
    let to_remove = minimize(indices, |candidate| oracle(&build_set(candidate)));
    build_set(&to_remove)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn edge_cases() {
        assert_eq!(minimize(vec![0, 1, 2, 3], |_| true), vec![]);
    }

    #[test]
    fn find_the_number() {
        assert_eq!(minimize(vec![0, 1, 2, 3], |v| v.contains(&0)), vec![0]);
        assert_eq!(minimize(vec![3, 0, 1, 2], |v| v.contains(&0)), vec![0]);
        assert_eq!(minimize(vec![2, 3, 0, 1], |v| v.contains(&0)), vec![0]);
        assert_eq!(minimize(vec![1, 2, 3, 0], |v| v.contains(&0)), vec![0]);
    }

    #[test]
    #[rustfmt::skip]
    fn keep_the_number() {
        assert_eq!(maximize(vec![0, 1, 2, 3], |v| !v.contains(&0)), vec![1, 2, 3]);
        assert_eq!(maximize(vec![3, 0, 1, 2], |v| !v.contains(&0)), vec![3, 1, 2]);
        assert_eq!(maximize(vec![2, 3, 0, 1], |v| !v.contains(&0)), vec![2, 3, 1]);
        assert_eq!(maximize(vec![1, 2, 3, 0], |v| !v.contains(&0)), vec![1, 2, 3]);
    }
}
