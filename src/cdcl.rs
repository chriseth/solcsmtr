use std::{
    cmp::max,
    collections::{HashMap, HashSet},
    fmt::{self, Display},
    ops::Not,
};

use num_traits::abs;

use crate::types::{Clause, Literal, VariableID};

type ClauseIndex = usize;
type AssignmentTrailIndex = usize;
/// Index into decision_points.
type DecisionLevel = usize;

#[derive(Default)]
pub struct CDCL {
    // TODO remove string unless debug
    variables: Vec<String>,
    // List of clauses including learnt clauses.
    clauses: Vec<Clause>,
    /// These are pointers from literals to the clauses they occur in,
    /// if they occur in one of the first two places.
    watches: HashMap<Literal, Vec<ClauseIndex>>,
    // TODO better use vector?
    // If yes, need to handle "unassigned".
    assignments: HashMap<VariableID, Assignment>,
    assignment_trail: Vec<Literal>,
    /// Index into assignment_trail: All assignments starting there have not yet been propagated.
    assignment_queue_pointer: AssignmentTrailIndex,
    /// Index into assignment_trail to denote where decisions were taken.
    decision_points: Vec<AssignmentTrailIndex>,
}

struct Assignment {
    value: bool,
    level: usize,
    // TODO optimize for space?
    reason: Option<ClauseIndex>,
}

impl CDCL {
    pub fn add_variable(&mut self, name: String) -> VariableID {
        if self.variables.is_empty() {
            self.variables.push("".to_string());
        }
        self.variables.push(name);
        (self.variables.len() - 1) as VariableID
    }
    pub fn add_clause(&mut self, c: Clause) -> ClauseIndex {
        // TODO assert that the clause does not contain the same variable twice.
        assert!(!c.is_empty());
        let clause_index = self.clauses.len();
        for l in c.iter().take(2) {
            self.watches.entry(*l).or_default().push(clause_index);
        }
        self.clauses.push(c);
        clause_index
    }
    pub fn solve(&mut self) -> bool {
        loop {
            if let Some(conflict_clause) = self.propagate() {
                if self.decision_level() == 0 {
                    return false;
                }
                let (learnt_clause, backtrack_level) = self.analyze_conflict(conflict_clause);
                self.cancel_until(backtrack_level);
                let literal_to_queue = learnt_clause[0];
                let reason = self.add_clause(learnt_clause);
                self.enqueue_assignment(literal_to_queue, Some(reason));
            } else {
                if let Some(var) = self.next_decision_variable() {
                    self.decision_points.push(self.assignment_trail.len());
                    // TODO Use polarity decision heuristics
                    self.enqueue_assignment(Literal::from(var), None);
                } else {
                    return true;
                }
            }
        }
        unreachable!();
    }
    pub fn decision_level(&self) -> usize {
        self.decision_points.len()
    }
}

impl Display for CDCL {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for clause in &self.clauses {
            writeln!(f, "c {}", self.format_clause(clause))?;
        }
        Ok(())
    }
}

impl CDCL {
    fn propagate(&mut self) -> Option<Clause> {
        while self.assignment_queue_pointer < self.assignment_trail.len() {
            let literal = self.assignment_trail[self.assignment_queue_pointer];
            if let Some(conflict) = self.propagate_literal(literal) {
                self.assignment_queue_pointer = self.assignment_trail.len();
                return Some(conflict);
            }
            self.assignment_queue_pointer += 1;
        }
        None
    }

    fn propagate_literal(&mut self, to_propagate: Literal) -> Option<Clause> {
        let negated = !to_propagate;
        let old_watches = std::mem::take(self.watches.entry(negated).or_default());
        let mut watch_replacement = Vec::new();
        let mut conflict = None;
        for clause_index in &old_watches {
            let mut index_to_swap = None;
            if conflict.is_none() {
                let mut clause = std::mem::take(&mut self.clauses[*clause_index]);
                if clause[0] != negated {
                    clause.swap(0, 1);
                }
                assert_eq!(clause[0], negated);

                (index_to_swap, conflict) =
                    self.propagate_first_literal_inside_clause(*clause_index, &clause);
                if let Some(i) = index_to_swap {
                    clause.swap(0, i);
                    self.watches
                        .entry(clause[0])
                        .or_default()
                        .push(*clause_index);
                }
                self.clauses[*clause_index] = clause;
            };
            if index_to_swap.is_none() {
                watch_replacement.push(*clause_index);
            }
        }
        self.watches.insert(negated, watch_replacement);
        conflict
    }

    /// Propagates inside the clause.
    /// Returns a new literal that has been swapped in place,
    /// or the conflicting clause.
    fn propagate_first_literal_inside_clause(
        &mut self,
        clause_index: ClauseIndex,
        clause: &Clause,
    ) -> (Option<usize>, Option<Clause>) {
        if clause.len() >= 2 && self.is_assigned_true(&clause[1]) {
            // Clause is satisfied, keep the watch.
            (None, None)
        } else if let Some((i, _)) = clause
            .iter()
            .enumerate()
            .skip(2)
            .find(|(_, l)| self.is_unknown_or_assigned_true(l))
        {
            // We found another literal to swap in place.
            (Some(i), None)
        } else if clause.len() >= 2 && self.is_unassigned(clause[1].var()) {
            // The only way to satisfy the clause is to set clause[1] to true.
            self.enqueue_assignment(clause[1], Some(clause_index));
            (None, None)
        } else {
            // Clause is false!
            (None, Some(clause.clone()))
        }
    }

    fn analyze_conflict(&self, mut conflict_clause: Clause) -> (Clause, DecisionLevel) {
        let mut learnt_clause = Clause::default();
        let mut path_count = 0;
        let mut resolving_literal = None;
        let mut seen_variables = HashSet::new();
        let mut backtrack_level = 0;
        let mut trail_index = self.assignment_trail.len() - 1;
        loop {
            for literal in conflict_clause {
                if Some(literal) != resolving_literal && !seen_variables.contains(&literal.var()) {
                    seen_variables.insert(literal.var());
                    let level = self.assignments[&literal.var()].level;
                    if level == self.decision_level() {
                        path_count += 1;
                    } else {
                        learnt_clause.push(literal);
                        backtrack_level = max(backtrack_level, level);
                    }
                }
            }
            assert!(path_count > 0);
            path_count -= 1;
            while !seen_variables.contains(&self.assignment_trail[trail_index].var()) {
                trail_index -= 1;
            }
            resolving_literal = Some(self.assignment_trail[trail_index]);
            // TODO in the C++ implementation, this was done
            // unconditionally and underflowed.
            if trail_index >= 1 {
                trail_index -= 1;
            }
            seen_variables.remove(&resolving_literal.unwrap().var());

            if path_count == 0 {
                break;
            } else {
                conflict_clause = self.clauses[self.assignments[&resolving_literal.unwrap().var()]
                    .reason
                    .unwrap()]
                .clone();
            }
        }
        learnt_clause.push(!resolving_literal.unwrap());
        // Move to front so we can directly propagate.
        let idx = learnt_clause.len() - 1;
        learnt_clause.swap(0, idx);

        // TODO in the test, this returns exactly the conflict clause,
        // but we alreay know that one!
        (learnt_clause, backtrack_level)
    }

    fn cancel_until(&mut self, backtrack_level: DecisionLevel) {
        assert!(self.assignment_queue_pointer == self.assignment_trail.len());
        let assignments_to_undo =
            self.assignment_trail.len() - self.decision_points[backtrack_level];
        for _ in 0..assignments_to_undo {
            let l = self.assignment_trail.pop().unwrap();
            self.assignments.remove(&l.var());
        }

        self.decision_points.truncate(backtrack_level);
        self.assignment_queue_pointer = self.assignment_trail.len();
        assert_eq!(self.decision_level(), backtrack_level);
    }
    fn enqueue_assignment(&mut self, literal: Literal, reason: Option<ClauseIndex>) {
        assert!(self.is_unassigned(literal.var()));
        let a = Assignment {
            value: literal.polarity(),
            level: self.decision_level(),
            reason,
        };
        self.assignments.insert(literal.var(), a);
        self.assignment_trail.push(literal);
    }
    fn next_decision_variable(&self) -> Option<VariableID> {
        (1..self.variables.len())
            .map(|v| v as VariableID)
            .find(|v| self.is_unassigned(*v))
    }

    fn is_assigned_true(&self, literal: &Literal) -> bool {
        if let Some(a) = self.assignments.get(&literal.var()) {
            a.value == literal.polarity()
        } else {
            false
        }
    }
    fn is_assigned_false(&self, literal: &Literal) -> bool {
        if let Some(a) = self.assignments.get(&literal.var()) {
            a.value != literal.polarity()
        } else {
            false
        }
    }
    fn is_unknown_or_assigned_true(&self, literal: &Literal) -> bool {
        if let Some(a) = self.assignments.get(&literal.var()) {
            a.value == literal.polarity()
        } else {
            true
        }
    }
    fn is_unassigned(&self, v: VariableID) -> bool {
        !self.assignments.contains_key(&v)
    }

    pub fn format_clause(&self, c: &Clause) -> String {
        c.iter()
            .map(|l| self.format_literal(l))
            .collect::<Vec<_>>()
            .join(" ∨ ")
    }
    pub fn format_literal(&self, l: &Literal) -> String {
        format!(
            "{}{}",
            if l.polarity() { "" } else { "¬" },
            self.variables[l.var() as usize]
        )
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn setup() -> (CDCL, Literal, Literal, Literal) {
        let mut s = CDCL::default();
        let x = Literal::from(s.add_variable("x".to_string()));
        let y = Literal::from(s.add_variable("y".to_string()));
        let z = Literal::from(s.add_variable("z".to_string()));
        (s, x, y, z)
    }

    #[test]
    fn empty() {
        let mut s = CDCL::default();
        assert!(s.solve());
    }

    #[test]
    fn trivial() {
        let (mut s, x, ..) = setup();
        s.add_clause(vec![x]);
        assert!(s.solve());
    }

    #[test]
    fn conflicting() {
        let (mut s, x, ..) = setup();
        s.add_clause(vec![x]);
        s.add_clause(vec![!x]);
        assert!(!s.solve());
    }

    #[test]
    fn slightly_complex() {
        let (mut s, x, y, z, ..) = setup();
        s.add_clause(vec![!x, y]);
        s.add_clause(vec![!y, !x, z]);
        s.add_clause(vec![!z, !y]);
        assert!(s.solve());
    }

    #[test]
    fn multi_backtrack() {
        let (mut s, x, y, z, ..) = setup();
        s.add_clause(vec![!y, z]);
        s.add_clause(vec![!z]);
        assert!(s.solve());
    }
}
