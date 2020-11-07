// TODO: Come up with a reasonable policy about &mut.
//       Is the internal mutability hazardous?  Not using const fn's/
//       &mut is irritating, but informative about caching behavior of struct.
#![allow(dead_code)]

use num;
use std::cell::Cell;

#[derive(Clone, Debug)]
/// Implements union-find with internal mutability
///
/// The `find` method 
struct UF<I: Copy> {
    /// invariants: 
    ///     1.  leaders[i] <= i, so whenever unioning two indices, the bigger will point to the
    ///            smaller.  This prevents (non-identity) cycles.
    leaders: Vec<Cell<I>>,
}

impl<I> PartialEq for UF<I>
where
    I: Into<usize> + Copy + num::FromPrimitive + num::Num + num::Integer,
{
    fn eq(&self, other: &Self) -> bool {
        assert!(self.leaders.len() == other.leaders.len(), 
                "Tried to compare equality on two UF with different sizes");
        for i_idx in 0..self.leaders.len() {
            let i = I::from_usize(i_idx).unwrap();
            if self.find(i) != other.find(i) {
                return false;
            }
        }
        true
    }
}

impl<I> Eq for UF<I>
where
    I: Into<usize> + Copy + num::FromPrimitive + num::Num + num::Integer,
{
}


impl<I> UF<I>
where
    I: Into<usize> + Copy + num::FromPrimitive + num::Num + num::Integer,
{
    pub fn new_reflexive(size: I) -> Self {
        let mut leaders: Vec<Cell<I>> = Vec::with_capacity(size.into());
        for i in 0..size.into() {
            leaders.push(Cell::new(I::from_usize(i).unwrap()))
        }
        UF { leaders }
    }
    pub fn max(&self) -> I {
        I::from_usize(self.leaders.len()).unwrap()
    }
    pub fn len(&self) -> usize {
        self.leaders.len()
    }
    fn const_find(&self, mut i: I) -> I {
        loop {
            let l = self.leaders[i.into()].get();
            if l == i {
                return l
            }
            i = l;
        }
    }
    /// Returns representative with minimum index from equivalence class.
    ///
    /// This method purports to immutably use `&self`, but it really uses interior mutability to
    /// implement path-compression in the safe, traditional way.  Almost every other method on `UF`
    /// delegates to `find`, so they are all lying too.
    pub fn find(&self, i: I) -> I {
        let cell = &self.leaders[i.into()];
        let l = cell.get();
        // TODO: optimize for common case
        if l == i {
            i
        } else {
            let mut prev = i;
            let mut this = l;
            loop {
                let next = self.leaders[this.into()].get();
                if this == next {
                    break;
                }
                // leave a bread crumb
                self.leaders[this.into()].set(prev);
                prev = this;
                this = next;
            }
            let res = this;
            this = prev;
            while this != i {
                let next = self.leaders[this.into()].replace(res);
                this = next;
            }
            self.leaders[i.into()].set(res);
            res
        }
    }

    /// Perform union
    ///
    /// Since this structure uses interior mutability, the `mut` attribute is not strictly
    /// necessary.  But it communicates to the user that the data structure is logically changing,
    /// so it's a worthwhiile part of the API.
    pub fn union(&mut self, i: I, j: I) {
        // The mutability here is really not necessary, but I think it is effective at
        // astonishment reduction.
        let l_i = self.find(i);
        let l_j = self.find(j);
        if l_i < l_j {
            self.leaders[l_j.into()].set(l_i);
        } else {
            self.leaders[l_i.into()].set(l_j);
        }
    }
    pub fn same_set(&self, i: I, j: I) -> bool {
        self.find(i) == self.find(j)
    }
    pub fn equivalence_union(a: &Self, b: &Self) -> Self {
        assert!(a.leaders.len() == b.leaders.len(), "Called equivalence_union on two UF of different sizes");
        let mut res = a.clone();
        for idx in 0..b.leaders.len() {
            let i = I::from_usize(idx).unwrap();
            res.union(i, b.find(i))
        }
        res
    }
    fn slow_equivalence_intersection(a: &Self, b: &Self) -> Self {
        // TODO: discover a better than O(n^2) algorithm for this.
        assert!(a.leaders.len() == b.leaders.len(), "Called equivalence_union on two UF of different sizes");
        let len = a.leaders.len();
        let max_i = I::from_usize(len).unwrap();
        let mut res = Self::new_reflexive(max_i);
        for i_idx in 0..len {
            let i = I::from_usize(i_idx).unwrap();
            for j_idx in i_idx+1..len {
                let j = I::from_usize(j_idx).unwrap();
                if a.same_set(i,j) && b.same_set(i,j) {
                    res.union(i,j);
                }
            }
        }
        res
    }
    pub fn equivalence_intersection(a: &Self, b: &Self) -> Self {
        // TODO: discover a better than O(n^2) algorithm for this.
        assert!(a.leaders.len() == b.leaders.len(), "Called equivalence_union on two UF of different sizes");
        let len = a.leaders.len();
        let max_i = I::from_usize(len).unwrap();
        let mut res = Self::new_reflexive(max_i);
        for i_idx in 0..len {
            let i = I::from_usize(i_idx).unwrap();
            for j_idx in i_idx+1..len {
                let j = I::from_usize(j_idx).unwrap();
                if a.same_set(i,j) && b.same_set(i,j) {
                    res.union(i,j);
                }
            }
        }
        res
    }

    /// Ensure all leader paths are minimal
    fn canonicalize(&self) {
        for idx in 0..self.leaders.len() {
            let i = I::from_usize(idx).unwrap();
            self.find(i);
        }
    }
    /// Creates permutation version of a UF
    ///
    /// each equivalence group corresponds to a cycle.  Every link in a cycle points downward,
    /// except for the smallest which points at the largest element in the cycle.
    fn as_permutation(&self) -> Vec<I> {
        let mut res = Vec::with_capacity(self.leaders.len().into());
        for idx in 0..self.len() {
            let i = I::from_usize(idx).unwrap();
            let j = self.find(i);
            if i == j {
                res.push(j); // identity cycle
            } else { // points to the leader
                res.push(res[j.into()]); // This cell points back at the previous max
                res[j.into()] = i;  // leader now points at this one, the new max
            }
        }
        res
    }
    #[cfg(test)]
    /// Ensures all expected invariants hold
    ///
    /// The only one I can think of is that leaders[i] <= i
    ///
    /// This is *actually* const.
    fn assert_invariants(&self) 
    where
        I: std::fmt::Display,
    {
        for idx in 0..self.leaders.len() {
            let v = self.leaders[idx].get().into();
            assert!(v <= idx, "leaders[{}] == {}, expected it to be <= {}", idx, v, idx);
        }
    }

    #[cfg(test)]
    /// Manually initialize a UF
    ///
    /// Unsafe because reslulting UF might violate invariants
    unsafe fn from_slice(slice: &[I]) -> Self {
        let leaders = slice
            .iter()
            .cloned()
            .map(|v| Cell::new(v))
            .collect();
        UF { leaders }
    }

    #[cfg(test)]
    /// compare two UF for structual equality, not logical equality
    ///
    /// Not actually unsafe, but requires understanding of internals to use properly, so it's
    /// marked as such.
    ///
    /// This is **actually** const
    unsafe fn struct_eq(&self, other: &Self) -> bool {
        self.leaders == other.leaders
    }
}



fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    type T = u16;
    use super::UF;
    use num::FromPrimitive;

    fn residue_class(len: T, m: T) -> UF<T> {
        let mut res = UF::new_reflexive(len);
        for i_idx in m.into()..len.into() {
            let i = T::from_usize(i_idx).unwrap();
            let j = i - m;
            res.union(i,j);
        }
        println!("residue_class({},{}) = {:?}", len, m, res);
        res
    }
    fn assert_is_residue_class(m: T, a: &UF<T>) {
        println!("checking if UF is residue_class {}", m);
        for i in 0..a.max() {
            for j in 0..a.max() {
                let same_res = (i % m) == (j % m);
                let same_set = a.same_set(i,j);
                assert_eq!(same_res, same_set, "m=={} i=={} j=={} same_set=={}", m, i, j, same_set);
            }
        }
    }
    #[test]
    fn try_2_3_6() {
        let x2 = residue_class(100, 2);
        assert_is_residue_class(2, &x2);
        let x3 = residue_class(100, 3);
        assert_is_residue_class(3, &x3);
        let y6a = UF::slow_equivalence_intersection(&x2, &x3);
        assert_is_residue_class(6, &y6a);
        let y6b = UF::equivalence_intersection(&x2, &x3);
        assert_is_residue_class(6, &y6b);
    }


    #[test]
    fn synthetic_find_test() {
        unsafe {
            const T_VALS: [u16; 10] = [ 0, 0, 2, 1, 3, 4, 5, 6, 7, 8 ];
            let mut t = UF::from_slice(&T_VALS[..]);
            t.assert_invariants();
            t.union(8, 9);
            const U_VALS: [u16; 10] = [ 0, 0, 2, 0, 0, 0, 0, 0, 0, 0 ];
            let u = UF::from_slice(&U_VALS[..]);
            t.assert_invariants();
            assert!(t.struct_eq(&u));
        }
    }
    #[test]
    fn permutation_test() {
        unsafe {
            const T_VALS: [u16; 10] = [ 0, 0, 2, 3, 2, 5, 6, 7, 7, 7 ];
            let t = UF::from_slice(&T_VALS[..]);
            t.assert_invariants();
            const U_VALS: [u16; 10] = [ 1, 0, 4, 3, 2, 5, 6, 9, 7, 8 ];
            let u = t.as_permutation();
            assert_eq!(&U_VALS[..], &u[..]);
        }
    }
}
