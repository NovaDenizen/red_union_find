
#![allow(dead_code)]

use num;
use std::cell::Cell;

#[derive(Clone, Debug)]
struct UF<I: Copy> {
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
    pub fn len(&self) -> I {
        I::from_usize(self.leaders.len()).unwrap()
    }
    pub fn find(&self, i: I) -> I {
        // TODO: use bread-crumb strategy to eliminate recursion
        let cell = &self.leaders[i.into()];
        let l = cell.get();
        if l == i {
            i
        } else {
            let l = self.find(l);
            cell.set(l);
            l
        }
    }
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
        for i in 0..a.len() {
            for j in 0..a.len() {
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
        let y6 = UF::equivalence_intersection(&x2, &x3);
        assert_is_residue_class(6, &y6);
    }

}
