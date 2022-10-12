use std::iter;

// TODO try u32 for index.

#[derive(Default)]
struct Entry<T> {
    value: T,
    row: usize,
    col: usize,
    in_col: Neighbors,
    in_row: Neighbors,
}

struct Neighbors {
    prev: usize,
    next: usize,
}
impl Default for Neighbors {
    fn default() -> Self {
        Self {
            prev: INVALID_INDEX,
            next: INVALID_INDEX,
        }
    }
}

const INVALID_INDEX: usize = usize::MAX;

pub struct SparseMatrix<T> {
    entries: Vec<Entry<T>>,
    // TODO We could model the border using actual entries that then create a loop (i.e. turning the matrix into a torus).
    // This could improve performance by removing conditional code.
    col_border: Vec<Neighbors>,
    row_border: Vec<Neighbors>,
    abandoned_indices: Vec<usize>,
}

enum RowColumn {
    Row,
    Column,
}

struct EntryIterator<'a, T> {
    index: usize,
    entries: &'a Vec<Entry<T>>,
    kind: RowColumn,
}

impl<'a, T> Iterator for EntryIterator<'a, T> {
    type Item = (usize, usize, &'a T);
    fn next(&mut self) -> Option<Self::Item> {
        let n = self.entries.get(self.index);
        if let Some(entry) = n {
            self.index = match self.kind {
                RowColumn::Row => entry.in_row.next,
                RowColumn::Column => entry.in_col.next,
            };
        }
        n.map(|e| (e.row, e.col, &e.value))
    }
}

impl<T> SparseMatrix<T>
where
    T: Clone
        + Default
        + std::ops::MulAssign
        + std::ops::Mul<T, Output = T>
        + std::ops::AddAssign
        + std::cmp::PartialEq,
{
    pub fn new() -> Self {
        Self {
            entries: vec![],
            col_border: vec![],
            row_border: vec![],
            abandoned_indices: vec![],
        }
    }
    pub fn rows(&self) -> usize {
        self.row_border.len()
    }
    pub fn columns(&self) -> usize {
        self.col_border.len()
    }
    fn iterate_row(&self, row: usize) -> EntryIterator<T> {
        EntryIterator {
            index: self.row_border.get(row).unwrap_or(&Default::default()).next,
            entries: &self.entries,
            kind: RowColumn::Row,
        }
    }
    fn iterate_column(&self, col: usize) -> EntryIterator<T> {
        EntryIterator {
            index: self.col_border.get(col).unwrap_or(&Default::default()).next,
            entries: &self.entries,
            kind: RowColumn::Column,
        }
    }

    pub fn multiply_row_by_factor(&mut self, row: usize, f: T) {
        let mut entry_id = self.row_border[row].next;
        let mut to_erase = vec![];
        while let Some(entry) = self.entries.get_mut(entry_id) {
            entry.value *= f.clone();
            if entry.value == Default::default() {
                to_erase.push(entry_id);
            }
            entry_id = entry.in_row.next;
        }
        for id in to_erase {
            self.erase(id);
        }
    }

    pub fn add_multiple_of_row(&mut self, source_row: usize, target_row: usize, factor: T) {
        let multiple = self
            .iterate_row(source_row)
            .map(|(_, c, v)| (c, v.clone() * factor.clone()))
            .filter(|(_, v)| *v != Default::default())
            .collect::<Vec<_>>();
        let mut target = self.row_border[target_row].next;
        for (col, sv) in multiple {
            while let Some(e) = self.entries.get(target).filter(|e| e.col < col) {
                target = e.in_row.next;
            }
            target = match self.entries.get_mut(target) {
                Some(e) if e.col == col => {
                    e.value += sv.clone();
                    let next = e.in_row.next;
                    if e.value == Default::default() {
                        self.erase(target)
                    }
                    next
                }
                _ => self.prepend_in_row(target, target_row, col, sv),
            }
        }
    }

    /// Ensures that the entry exists and returns a reference to its value.
    pub fn entry(&mut self, row: usize, column: usize) -> &mut T {
        self.ensure_size(row, column);

        let mut id = usize::MAX;
        // Try to find the entry or the one after it.
        if let Some(last) = self.entries.get(self.row_border[row].prev) {
            if column <= last.col {
                id = self.row_border[row].next;
                while let Some(e) = self.entries.get(id).filter(|e| e.col < column) {
                    id = e.in_col.next;
                }
            }
        }
        // TODO reduce the entries array accesses here.
        // The loop above might already hold the right index.
        if id >= self.entries.len() || self.entries[id].col > column {
            id = self.prepend_in_row(id, row, column, Default::default());
        }
        &mut self.entries[id].value
    }

    /// Append a new row given an iterater that returns pairs of columns and
    /// values. The pairs must be sorted by columns.
    pub fn append_row(&mut self, entries: impl Iterator<Item = (usize, T)>) {
        let row = self.rows();
        self.row_border.push(Default::default());
        for (col, value) in entries {
            if value != Default::default() {
                self.prepend_in_row(INVALID_INDEX, row, col, value);
            }
        }
    }
}

impl<T: Default> SparseMatrix<T> {
    /// Ensure that row and col exists.
    fn ensure_size(&mut self, row: usize, col: usize) {
        if row >= self.row_border.len() {
            self.row_border
                .extend(iter::repeat_with(Default::default).take(row + 1 - self.row_border.len()));
        }
        if col >= self.col_border.len() {
            self.col_border
                .extend(iter::repeat_with(Default::default).take(col + 1 - self.col_border.len()));
        }
    }
    fn prepend_in_row(&mut self, successor: usize, row: usize, col: usize, value: T) -> usize {
        let mut entry = Entry {
            value,
            col,
            row,
            in_col: Default::default(),
            in_row: Default::default(),
        };
        let entry_id = self.abandoned_indices.pop().unwrap_or_else(|| {
            self.entries.push(Default::default());
            self.entries.len() - 1
        });
        entry.in_row.next = successor;

        let next_prev = self.next_prev(RowColumn::Row, &entry);
        entry.in_row.prev = *next_prev;
        *next_prev = entry_id;

        *self.prev_next(RowColumn::Row, &entry) = entry_id;

        self.ensure_size(0, col);
        self.adjust_column_properties(entry_id, &mut entry);
        self.entries[entry_id] = entry;
        entry_id
    }

    fn adjust_column_properties(&mut self, entry_id: usize, entry: &mut Entry<T>) {
        let col = entry.col;
        let mut next_in_col = INVALID_INDEX;
        if let Some(border_entry) = self.entries.get(self.col_border[col].prev) {
            if entry.row < border_entry.row {
                // TODO use "iterate_col"?
                next_in_col = self.col_border[col].next;
                // TODO could choose to search from end, depending on row.
                while let Some(e) = self.entries.get(next_in_col).filter(|e| e.row < entry.row) {
                    next_in_col = e.in_col.next;
                }
            }
        }
        entry.in_col.next = next_in_col;
        let next_prev = self.next_prev(RowColumn::Column, entry);
        entry.in_col.prev = *next_prev;
        *next_prev = entry_id;

        *self.prev_next(RowColumn::Column, entry) = entry_id;
    }

    fn erase(&mut self, entry_id: usize) {
        // TODO this does not deallocate the entry.
        // We should maintain a queue of empty slots to
        // re-use for the next allocation.
        // At some point we should perform cleanup
        // and swap entries in the vector
        let entry = std::mem::take(&mut self.entries[entry_id]);
        *self.prev_next(RowColumn::Row, &entry) = entry.in_row.next;
        *self.prev_next(RowColumn::Column, &entry) = entry.in_col.next;
        *self.next_prev(RowColumn::Row, &entry) = entry.in_row.prev;
        *self.next_prev(RowColumn::Column, &entry) = entry.in_col.prev;
        self.abandoned_indices.push(entry_id);
    }

    /// Returns the prev field of the next entry (or the border).
    fn next_prev(&mut self, rc: RowColumn, entry: &Entry<T>) -> &mut usize {
        match rc {
            RowColumn::Row => {
                if let Some(next_entry) = self.entries.get_mut(entry.in_row.next) {
                    &mut next_entry.in_row.prev
                } else {
                    &mut self.row_border[entry.row].prev
                }
            }
            RowColumn::Column => {
                if let Some(next_entry) = self.entries.get_mut(entry.in_col.next) {
                    &mut next_entry.in_col.prev
                } else {
                    &mut self.col_border[entry.col].prev
                }
            }
        }
    }

    /// Returns the next field of the prev entry (or the border).
    fn prev_next(&mut self, rc: RowColumn, entry: &Entry<T>) -> &mut usize {
        match rc {
            RowColumn::Row => {
                if let Some(prev_entry) = self.entries.get_mut(entry.in_row.prev) {
                    &mut prev_entry.in_row.next
                } else {
                    &mut self.row_border[entry.row].next
                }
            }
            RowColumn::Column => {
                if let Some(prev_entry) = self.entries.get_mut(entry.in_col.prev) {
                    &mut prev_entry.in_col.next
                } else {
                    &mut self.col_border[entry.col].next
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn matrix_by_row(m: &SparseMatrix<i64>) -> Vec<Vec<i64>> {
        (0..m.rows())
            .map(|c| m.iterate_row(c).map(|(.., v)| *v).collect::<Vec<_>>())
            .collect::<Vec<_>>()
    }

    fn matrix_by_column(m: &SparseMatrix<i64>) -> Vec<Vec<i64>> {
        (0..m.columns())
            .map(|c| m.iterate_column(c).map(|(.., v)| *v).collect::<Vec<_>>())
            .collect::<Vec<_>>()
    }

    #[test]
    fn add_single_row() {
        let mut m = SparseMatrix::<i64>::new();
        assert_eq!(m.columns(), 0);
        assert_eq!(m.rows(), 0);
        assert_eq!(matrix_by_column(&m), Vec::<Vec::<i64>>::new());
        m.append_row(vec![(0, 10), (3, 5), (4, 9)].into_iter());
        assert_eq!(m.columns(), 5);
        assert_eq!(m.rows(), 1);
        assert_eq!(
            matrix_by_column(&m),
            vec![vec![10], vec![], vec![], vec![5], vec![9]]
        );
        assert_eq!(matrix_by_row(&m), vec![vec![10, 5, 9],]);
    }

    #[test]
    fn add_two_rows() {
        let mut m = SparseMatrix::<i64>::new();
        assert_eq!(m.columns(), 0);
        assert_eq!(m.rows(), 0);
        m.append_row(vec![(0, 1), (3, 2), (4, 3)].into_iter());
        m.append_row(vec![(1, 4), (3, 5), (5, 6)].into_iter());
        assert_eq!(m.columns(), 6);
        assert_eq!(m.rows(), 2);
        assert_eq!(
            matrix_by_column(&m),
            vec![vec![1], vec![4], vec![], vec![2, 5], vec![3], vec![6]]
        );
        assert_eq!(matrix_by_row(&m), vec![vec![1, 2, 3], vec![4, 5, 6]]);
    }

    #[test]
    fn multiply_by_factor() {
        let mut m = SparseMatrix::<i64>::new();
        m.append_row(vec![(0, 1), (3, 2), (4, 3)].into_iter());
        m.append_row(vec![(1, 4), (2, 5), (4, 6)].into_iter());
        m.append_row(vec![(0, 7), (2, 8), (3, 9)].into_iter());
        assert_eq!(
            matrix_by_column(&m),
            vec![vec![1, 7], vec![4], vec![5, 8], vec![2, 9], vec![3, 6]]
        );
        assert_eq!(
            matrix_by_row(&m),
            vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]
        );
        m.multiply_row_by_factor(0, 0);
        m.multiply_row_by_factor(2, 0);
        assert_eq!(
            matrix_by_column(&m),
            vec![vec![], vec![4], vec![5], vec![], vec![6]]
        );
        assert_eq!(matrix_by_row(&m), vec![vec![], vec![4, 5, 6], vec![]]);
    }

    #[test]
    fn reuse_abandoned() {
        let mut m = SparseMatrix::<i64>::new();
        m.append_row(vec![(0, 1), (3, 2), (4, 3)].into_iter());
        m.append_row(vec![(1, 4), (3, 5), (5, 6)].into_iter());
        m.multiply_row_by_factor(0, 0);
        m.append_row(vec![(0, 1), (3, 2), (4, 3)].into_iter());
        assert_eq!(m.entries.len(), 6);
        assert_eq!(
            matrix_by_row(&m),
            vec![vec![], vec![4, 5, 6], vec![1, 2, 3]]
        );
        assert_eq!(
            matrix_by_column(&m),
            vec![vec![1], vec![4], vec![], vec![5, 2], vec![3], vec![6]]
        );
    }

    #[test]
    fn entry_access() {
        let mut m = SparseMatrix::<i64>::new();
        *m.entry(0, 0) = 1;
        *m.entry(0, 4) = 2;
        *m.entry(1, 4) = 3;
        assert_eq!(matrix_by_row(&m), vec![vec![1, 2], vec![3]]);
        assert_eq!(
            matrix_by_column(&m),
            vec![vec![1], vec![], vec![], vec![], vec![2, 3]]
        );

        *m.entry(0, 0) = 4;
        *m.entry(1, 3) = 5;
        *m.entry(1, 2) = 6;
        assert_eq!(matrix_by_row(&m), vec![vec![4, 2], vec![6, 5, 3]]);
        assert_eq!(
            matrix_by_column(&m),
            vec![vec![4], vec![], vec![6], vec![5], vec![2, 3]]
        );

        assert_eq!(*m.entry(0, 0), 4);
        assert_eq!(*m.entry(1, 2), 6);
        assert_eq!(*m.entry(1, 6), 0);
        assert_eq!(*m.entry(9, 2), 0);
        assert_eq!(
            matrix_by_row(&m),
            vec![
                vec![4, 2],
                vec![6, 5, 3, 0],
                vec![],
                vec![],
                vec![],
                vec![],
                vec![],
                vec![],
                vec![],
                vec![0]
            ]
        );
        assert_eq!(
            matrix_by_column(&m),
            vec![
                vec![4],
                vec![],
                vec![6, 0],
                vec![5],
                vec![2, 3],
                vec![],
                vec![0]
            ]
        );
    }

    #[test]
    fn add_multiple() {
        let mut m = SparseMatrix::<i64>::new();
        m.append_row(vec![(0, 1), (3, 2), (5, 3), (6, 1)].into_iter());
        m.append_row(vec![(1, 4), (3, -4), (5, 6)].into_iter());
        m.add_multiple_of_row(0, 1, 2);
        assert_eq!(matrix_by_row(&m), vec![vec![1, 2, 3, 1], vec![2, 4, 12, 2]]);
        assert_eq!(
            matrix_by_column(&m),
            vec![
                vec![1, 2],
                vec![4],
                vec![],
                vec![2],
                vec![],
                vec![3, 12],
                vec![1, 2]
            ]
        );
    }
}
