use std::iter;

#[derive(Default)]
struct Entry<T> {
    value: T,
    col: Index,
    row: Index,
    adjacent_cols: Neighbors,
    adjacent_rows: Neighbors,
}

#[derive(Clone)]
struct Neighbors {
    prev: Index,
    next: Index,
}
impl Default for Neighbors {
    fn default() -> Self {
        Self {
            prev: INVALID_INDEX,
            next: INVALID_INDEX,
        }
    }
}

// TODO later, try u32
// Would be nice to have a nonzero guarantee to encode
// "unset" memory-efficiently
type Index = usize;
const INVALID_INDEX: usize = usize::MAX;

pub struct SparseMatrix<T> {
    entries: Vec<Entry<T>>,
    col_border: Vec<Neighbors>,
    row_border: Vec<Neighbors>,
}

enum RowColumn {
    Row,
    Column,
}

struct EntryIterator<'a, T> {
    index: Index,
    entries: &'a Vec<Entry<T>>,
    kind: RowColumn,
}

impl<'a, T> Iterator for EntryIterator<'a, T> {
    type Item = &'a Entry<T>;
    fn next(&mut self) -> Option<Self::Item> {
        let n = self.entries.get(self.index);
        if let Some(entry) = n {
            self.index = match self.kind {
                RowColumn::Row => entry.adjacent_rows.next,
                RowColumn::Column => entry.adjacent_cols.next,
            };
        }
        n
    }
}

impl<T> SparseMatrix<T>
where
    T: Default + Clone + std::ops::MulAssign + std::cmp::PartialEq + From<u32>,
{
    pub fn new() -> Self {
        Self {
            entries: vec![],
            col_border: vec![],
            row_border: vec![],
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

    // pub fn multiply_row_by_factor(&mut self, row: usize, f: T) {
    //     let mut entry_id = self.row_border[row].next;
    //     let mut to_erase = vec![];
    //     while let Some(entry) = self.entries.get_mut(entry_id) {
    //         entry.value *= f.clone();
    //         if entry.value == T::from(0) {
    //             to_erase.push(entry_id);
    //         }
    //         entry_id = entry.adjacent_cols.next;
    //     }
    //     for id in to_erase {
    //         self.erase(id);
    //     }
    // }

    /// Append a new row given an iterater that returns pairs of columns and
    /// values. The pairs must be sorted by columns.
    pub fn append_row(&mut self, entries: impl Iterator<Item = (usize, T)>) {
        let row = self.rows();
        self.row_border.push(Default::default());
        for (col, item) in entries {
            self.prepend_in_row(None, row, col, item);
        }
    }
}

impl<T: Default> SparseMatrix<T> {
    fn prepend_in_row(&mut self, successor: Option<usize>, row: usize, col: usize, item: T) {
        let mut entry = Entry {
            value: item,
            col,
            row,
            adjacent_cols: Default::default(),
            adjacent_rows: Default::default(),
        };
        let entry_id = self.entries.len();
        entry.adjacent_rows.next = if let Some(s) = successor { s } else { usize::MAX };
        let next_prev = self.next_prev(RowColumn::Row, &entry);
        entry.adjacent_rows.prev = *next_prev;
        *next_prev = entry_id;

        *self.prev_next(RowColumn::Row, &entry) = entry_id;

        if col >= self.col_border.len() {
            self.col_border
                .extend(iter::repeat(Default::default()).take(col + 1 - self.col_border.len()));
        }
        self.adjust_column_properties(entry_id, &mut entry);
        self.entries.push(entry);
    }

    fn adjust_column_properties(&mut self, entry_id: usize, entry: &mut Entry<T>) {
        let col = entry.col;
        let mut next_in_col = usize::MAX;
        if let Some(border_entry) = self.entries.get(self.col_border[col].prev) {
            if entry.row < border_entry.row {
                // TODO use "iterate_col"?
                next_in_col = self.col_border[col].next;
                // TODO could choose to search from end, depending on row.
                loop {
                    if let Some(e) = self.entries.get(next_in_col) {
                        if e.row < entry.row {
                            next_in_col = e.adjacent_cols.next;
                            continue;
                        }
                    }
                    break;
                }
            }
        }
        entry.adjacent_cols.next = next_in_col;
        let next_prev = self.next_prev(RowColumn::Column, entry);
        entry.adjacent_cols.prev = *next_prev;
        *next_prev = entry_id;

        *self.prev_next(RowColumn::Column, entry) = entry_id;
    }

    // fn erase(&mut self, entry_id: usize) {
    //     // TODO this does not deallocate the entry.
    //     // We should maintain a queue of empty slots to
    //     // re-use for the next allocation.
    //     // At some point we should perform cleanup
    //     // and swap entries in the vector
    //     let entry = std::mem::take(&mut self.entries[entry_id]);
    //     if let Some(p) = self.entries.get_mut(entry.adjacent_rows.prev) {
    //         p.adjacent_rows.next = entry.adjacent_rows.next;
    //     } else {
    //         self.row_border[entry.row].next = entry.adjacent_rows.next;
    //     }
    //     // if (_e.prev_in_row)
    //     //     _e.prev_in_row->next_in_row = _e.next_in_row;
    //     // else
    //     //     m_row_start[_e.row] = _e.next_in_row;
    //     // if (_e.next_in_row)
    //     //     _e.next_in_row->prev_in_row = _e.prev_in_row;
    //     // else
    //     //     m_row_end[_e.row] = _e.prev_in_row;
    //     // if (_e.prev_in_col)
    //     //     _e.prev_in_col->next_in_col = _e.next_in_col;
    //     // else
    //     //     m_col_start[_e.col] = _e.next_in_col;
    //     // if (_e.next_in_col)
    //     //     _e.next_in_col->prev_in_col = _e.prev_in_col;
    //     // else
    //     //     m_col_end[_e.col] = _e.prev_in_col;
    // }

    /// Returns the prev field of the next entry (or the border).
    fn next_prev(&mut self, rc: RowColumn, entry: &Entry<T>) -> &mut usize {
        match rc {
            RowColumn::Row => {
                if let Some(next_entry) = self.entries.get_mut(entry.adjacent_rows.next) {
                    &mut next_entry.adjacent_rows.prev
                } else {
                    &mut self.row_border[entry.row].prev
                }
            }
            RowColumn::Column => {
                if let Some(next_entry) = self.entries.get_mut(entry.adjacent_cols.next) {
                    &mut next_entry.adjacent_cols.prev
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
                if let Some(prev_entry) = self.entries.get_mut(entry.adjacent_rows.prev) {
                    &mut prev_entry.adjacent_rows.next
                } else {
                    &mut self.row_border[entry.row].next
                }
            }
            RowColumn::Column => {
                if let Some(prev_entry) = self.entries.get_mut(entry.adjacent_cols.prev) {
                    &mut prev_entry.adjacent_cols.next
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

    #[test]
    fn add_single_row() {
        let mut m = SparseMatrix::<i64>::new();
        assert_eq!(m.columns(), 0);
        assert_eq!(m.rows(), 0);
        m.append_row(vec![(0, 10), (3, 5), (4, 9)].into_iter());
        assert_eq!(m.columns(), 5);
        assert_eq!(m.rows(), 1);
        assert_eq!(
            m.iterate_column(0).map(|e| e.value).collect::<Vec<_>>(),
            vec![10]
        );
        assert_eq!(
            m.iterate_column(1).map(|e| e.value).collect::<Vec<_>>(),
            vec![]
        );
        assert_eq!(
            m.iterate_column(4).map(|e| e.value).collect::<Vec<_>>(),
            vec![9]
        );
        assert_eq!(
            m.iterate_row(0).map(|e| e.value).collect::<Vec<_>>(),
            vec![10, 5, 9]
        );
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
            m.iterate_column(0).map(|e| e.value).collect::<Vec<_>>(),
            vec![1]
        );
        assert_eq!(
            m.iterate_column(1).map(|e| e.value).collect::<Vec<_>>(),
            vec![4]
        );
        assert_eq!(
            m.iterate_column(3).map(|e| e.value).collect::<Vec<_>>(),
            vec![2, 5]
        );
        assert_eq!(
            m.iterate_column(4).map(|e| e.value).collect::<Vec<_>>(),
            vec![3]
        );
        assert_eq!(
            m.iterate_column(5).map(|e| e.value).collect::<Vec<_>>(),
            vec![6]
        );
        assert_eq!(
            m.iterate_row(0).map(|e| e.value).collect::<Vec<_>>(),
            vec![1, 2, 3]
        );
    }
}
