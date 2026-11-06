//! Iterative SCC decomposition. Edges point from a node to its dependencies;
//! returned components therefore place dependencies before their callers.
pub(crate) fn components(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut seen = vec![false; edges.len()];
    let mut order = Vec::with_capacity(edges.len());
    for root in 0..edges.len() {
        if seen[root] {
            continue;
        }
        seen[root] = true;
        let mut stack = vec![(root, 0)];
        while let Some((node, next)) = stack.last_mut() {
            if let Some(&child) = edges[*node].get(*next) {
                *next += 1;
                if !seen[child] {
                    seen[child] = true;
                    stack.push((child, 0));
                }
            } else {
                order.push(*node);
                stack.pop();
            }
        }
    }
    let mut reverse = vec![Vec::new(); edges.len()];
    for (source, targets) in edges.iter().enumerate() {
        for &target in targets {
            reverse[target].push(source);
        }
    }
    seen.fill(false);
    let mut groups = Vec::new();
    for &root in order.iter().rev() {
        if seen[root] {
            continue;
        }
        seen[root] = true;
        let mut members = Vec::new();
        let mut pending = vec![root];
        while let Some(node) = pending.pop() {
            members.push(node);
            for &parent in &reverse[node] {
                if !seen[parent] {
                    seen[parent] = true;
                    pending.push(parent);
                }
            }
        }
        members.sort_unstable();
        groups.push(members);
    }
    groups.reverse();
    groups
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn components_are_dependency_first_and_deep_graphs_do_not_use_the_host_stack() {
        let groups = components(&[vec![1], vec![2], vec![1], vec![]]);
        let mut group = [0; 4];
        for (index, members) in groups.iter().enumerate() {
            for &node in members {
                group[node] = index;
            }
        }
        assert_eq!(group[1], group[2]);
        assert!(group[1] < group[0]);
        let edges: Vec<_> = (0..10000)
            .map(|i| if i == 9999 { Vec::new() } else { vec![i + 1] })
            .collect();
        let groups = components(&edges);
        assert_eq!(groups[0], [9999]);
        assert_eq!(groups.last().unwrap(), &[0]);
    }
}
