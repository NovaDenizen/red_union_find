
//! A basic implementation of the Union-find algorithm
use num_traits:: { FromPrimitive, Num };
use num_integer::Integer;
use std::cell::Cell;

#[derive(Clone, Debug)]
/// Implements union-find
///
/// The UF structure efficiently represents a disjoint set data structure.
pub struct UF<I: Copy> {
    /// invariants: 
    ///     1.  `leaders[i] <= i`, so whenever unioning two indices, the bigger will point to the
    ///            smaller.  This prevents (non-identity) cycles.
    leaders: Vec<Cell<I>>,
}

impl<I> PartialEq for UF<I>
where
    I: Into<usize> + Copy + FromPrimitive + Num + Integer,
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
    I: Into<usize> + Copy + FromPrimitive + Num + Integer,
{
}


impl<I> UF<I>
where
    I: Into<usize> + Copy + FromPrimitive + Num + Integer,
{
    /// Creates a minimal reflexive UF structure.
    ///
    /// Each index `i` is the sole memeber of its own equivalence set.
    pub fn new_reflexive(size: I) -> Self {
        let mut leaders: Vec<Cell<I>> = Vec::with_capacity(size.into());
        for i in 0..size.into() {
            leaders.push(Cell::new(I::from_usize(i).unwrap()))
        }
        UF { leaders }
    }
    /// Returns the element beyond the largest represented in ths `UF`.
    pub fn max(&self) -> I {
        I::from_usize(self.leaders.len()).unwrap()
    }
    /// Number of indices in this `UF`
    pub fn len(&self) -> usize {
        self.leaders.len()
    }
    #[allow(dead_code)]
    fn const_find(&self, mut i: I) -> I {
        loop {
            let l = self.leaders[i.into()].get();
            if l == i {
                return l
            }
            i = l;
        }
    }
    /// Returns representative with minimum index from `i`'s equivalence set.
    ///
    /// This method purports to immutably use `&self`, but it really uses interior mutability to
    /// implement path-compression in the safe, traditional way.  Almost every other method on `UF`
    /// delegates to `find`, so they are all lying too.
    ///
    /// # Performance
    ///
    /// If you perform `n` `find()` operations on a `UF` with length `len()`, then these operations
    /// will take O(`n` + `len()`) operations.  So the performance is amortized O(1).
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

    /// Perform union of two indices
    ///
    /// Since `UF` uses interior mutability, the `mut` attribute here is not strictly necessary.
    /// But it communicates to the user that the data structure is logically changing, so it's a
    /// worthwhiile part of the API.
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
    /// Retrns true if `i` and `j` are in the same equivalence set.
    pub fn same_set(&self, i: I, j: I) -> bool {
        self.find(i) == self.find(j)
    }
    /// Creates a new UF that represents the union of the two given equivalence relations.
    ///
    /// let `c = UF::equivalence_union(&a, &b)`.  `c.same_set(i,j) == a.same_set(i,j) ||
    /// b.same_set(i,j)`.
    ///
    /// Performance: O(len())
    pub fn equivalence_union(a: &Self, b: &Self) -> Self {
        assert!(a.leaders.len() == b.leaders.len(), "Called equivalence_union on two UF of different sizes");
        let mut res = a.clone();
        for idx in 0..b.leaders.len() {
            let i = I::from_usize(idx).unwrap();
            res.union(i, b.find(i))
        }
        res
    }
    #[allow(dead_code)]
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
    /// Creates a new UF that represents the intersection of the two given equivalence relations.
    ///
    /// let `c = UF::equivalence_intersection(&a, &b)`.  `c.same_set(i,j) == a.same_set(i,j) &&
    /// b.same_set(i,j)`.
    ///
    /// # Performance
    ///
    /// I have only been able to prove that the performance is somewhere between O(`len()`) and
    /// O(`len()`^2).  But it seems pretty fast.
    /// 
    /// If either `a` or `b` is mostly pure-reflexive or mostly one big equivalence set, then the
    /// performance is almost linear.
    ///
    /// The inner loop that steps through the cycles can't do more than O(`len()`^2) operations.
    /// The worst case operation seems to be when there are large sets in both argument `UF`s, but
    /// the intersection has no non-reflexive elements.
    pub fn equivalence_intersection(a: &Self, b: &Self) -> Self {
        assert!(a.leaders.len() == b.leaders.len(), "Called equivalence_union on two UF of different sizes");
        let ap = a.as_permutation();
        let bp = b.as_permutation();
        let mut c = UF::new_reflexive(a.max());
        for i in (0..ap.len()).rev() {
            let mut ai = i;
            let mut bi = i;
            let mut anext = ap[ai].into();
            let mut bnext = bp[bi].into();
            // Follow both cycles down until we find one in common or run out of elements
            loop {
                // while a is bigger than b, advance a
                while anext < ai && anext > bnext {
                    ai = anext;
                    anext = ap[ai].into();
                }
                // if we're ad the end of the cycle, we're done
                // if a and b are equal, we're done
                if anext >= ai || anext == bnext {
                    break;
                }
                // while b is bigger than a, advance b
                while bnext < bi && bnext > anext {
                    bi = bnext;
                    bnext = bp[bi].into();
                }
                // if we're ad the end of the cycle, we're done
                // if a and b are equal, we're done
                if bnext >= bi || anext == bnext {
                    break;
                }
            }
            if anext == bnext {
                // anext is the biggest element in both the a and b cycle.
                c.union(I::from_usize(i).unwrap(), I::from_usize(anext).unwrap());
            }
        }
        c
    }

    /// Ensure all leader paths are minimal
    #[allow(dead_code)]
    fn canonicalize(&self) {
        for idx in 0..self.leaders.len() {
            let i = I::from_usize(idx).unwrap();
            self.find(i);
        }
    }
    /// Creates permutation version of a UF
    ///
    /// Each equivalence set corresponds to a cycle.  Every link in a cycle points downward,
    /// except for the smallest which points at the largest element in the cycle.
    ///
    /// This representation can be used to do neat algorithmic things with an equivalence class.
    pub fn as_permutation(&self) -> Vec<I> {
        let mut res = Vec::with_capacity(self.leaders.len().into());
        for idx in 0..self.len() {
            let i = I::from_usize(idx).unwrap();
            let j = self.find(i);
            if i == j {
                res.push(j); // identity cycle
            } else { // points to the leader
                res.push(res[j.into()]); // This cell points back at the previous max
                res[j.into()] = i;       // leader now points at this one, the new max
            }
        }
        res
    }
    /// Ensures all expected invariants hold
    ///
    /// The only one I can think of is that leaders[i] <= i
    ///
    /// This is *actually* const.
    #[allow(dead_code)]
    fn assert_invariants(&self) 
    where
        I: std::fmt::Display,
    {
        for idx in 0..self.leaders.len() {
            let v = self.leaders[idx].get().into();
            assert!(v <= idx, "leaders[{}] == {}, expected it to be <= {}", idx, v, idx);
        }
    }

    /// Manually initialize a UF
    ///
    /// Unsafe because reslulting UF might violate invariants
    ///
    /// This is useful for testing.
    #[allow(dead_code)]
    unsafe fn from_slice(slice: &[I]) -> Self {
        let leaders = slice
            .iter()
            .cloned()
            .map(|v| Cell::new(v))
            .collect();
        UF { leaders }
    }

    /// compare two UF for structual equality, not logical equality
    ///
    /// Not actually unsafe, but requires understanding of internals to use properly, so it's
    /// marked as such.
    ///
    /// This is **actually** const
    #[allow(dead_code)]
    unsafe fn struct_eq(&self, other: &Self) -> bool {
        self.leaders == other.leaders
    }

    /// Returns an iterator over group leader indexes
    pub fn leaders<'a>(&'a self) -> LeadersIter<'a, I> {
        LeadersIter { uf: self, next_i: I::zero() }
    }
}

pub struct LeadersIter<'a, I: Copy> {
    uf: &'a UF<I>,
    next_i: I,
}

impl<'a, I: Copy> Iterator for LeadersIter<'a,I>
where
    I: Into<usize> + Copy + FromPrimitive + Num + Integer,
{
    type Item = I;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.next_i >= self.uf.max() {
                return None;
            }
            let i = self.next_i;
            let l = self.uf.find(i);
            self.next_i = self.next_i + I::one();
            if i == l {
                return Some(i);
            }
        }
    }
}




#[cfg(test)]
mod tests {
    type T = u16;
    use super::UF;
    use num_traits::FromPrimitive;
    use rand::prelude::*;

    fn test_rng() -> StdRng {
        StdRng::seed_from_u64(0x0102030405060708_u64)
    }

    fn residue_class(len: T, m: T) -> UF<T> {
        let mut res = UF::new_reflexive(len);
        for i_idx in m.into()..len.into() {
            let i = T::from_usize(i_idx).unwrap();
            let j = i - m;
            res.union(i,j);
        }
        //println!("residue_class({},{}) = {:?}", len, m, res);
        res
    }
    fn assert_is_residue_class(m: T, a: &UF<T>) {
        println!("checking if UF is residue_class {}", m);
        let mut v = Vec::with_capacity(a.len());
        for i in 0..a.max() {
            v.push(i % m);
        }
        let b = unsafe { UF::from_slice(&v) };
        a.canonicalize();
        b.canonicalize();
        assert!(unsafe { a.struct_eq(&b) });
    }
    fn random_uf(size: usize, max_unions: usize, rng: &mut StdRng) -> UF<T> {
        let tsize = T::from_usize(size).unwrap();
        let mut res = UF::new_reflexive(tsize);
        let num_unions = rng.gen_range(0, max_unions);
        for _ in 0..num_unions {
            let i = rng.gen_range(0, tsize);
            let j = rng.gen_range(0, tsize);
            res.union(i, j);
        }
        res
    }
    fn test_intersections(a: &UF<T>, b: &UF<T>) {
        let c1 = UF::slow_equivalence_intersection(a, b);
        c1.canonicalize();
        {
            let c2 = UF::equivalence_intersection(a, b);
            c2.canonicalize();
            let res = unsafe { c1.struct_eq(&c2) };
            if !res {
                println!("a={:?}", a);
                println!("b={:?}", b);
                println!("c1={:?}", c1);
                println!("c2={:?}", c2);
                assert!(res);
            }
        }
        {
            let t = a;
            let a = b;
            let b = t;
            // same as before, but different order args
            let c2 = UF::slow_equivalence_intersection(a, b);
            c2.canonicalize();
            let res = unsafe { c1.struct_eq(&c2) };
            if !res {
                println!("a={:?}", a);
                println!("b={:?}", b);
                println!("c1={:?}", c1);
                println!("c2={:?}", c2);
                assert!(res);
            }
        }
    }
    fn do_iterator_test(a: &UF<T>) {
        use std::collections::BTreeSet;
        let mut s = BTreeSet::new();
        for i in 0..a.max() {
            if a.find(i) == i {
                s.insert(i);
            }
        }
        let comp: Vec<T> = s.into_iter().collect();
        let leaders: Vec<T> = a.leaders().collect();
        assert_eq!(comp, leaders, "iterator test failed for {:?}", a);
    }
    #[test]
    fn do_random_intersection_tests() {
        let mut rng = test_rng();
        let ntests = 1000;
        for _ in 0..ntests {
            let size = rng.gen_range(20, 30);
            let a = random_uf(size, 15, &mut rng);
            do_iterator_test(&a);
            let b = random_uf(size, 15, &mut rng);
            do_iterator_test(&b);
            test_intersections(&a, &b);
        }
    }
    /// Test intersection operation with two modular residue sets
    ///
    /// a and b must be relatively prime
    fn modular_residue_test(a: T, b: T, size: T) {
        use num_integer::Integer;
        println!("making xa");
        let xa = residue_class(size, a);
        println!("checking xa");
        assert_is_residue_class(a, &xa);
        println!("making xb");
        let xb = residue_class(size, b);
        println!("testing xb");
        assert_is_residue_class(b, &xb);
        println!("slowly making yca");
        let c = a * b;
        assert_eq!(a.gcd(&b), 1, "a and b are not relatively prime");
        {
            println!("quickly making ycb");
            let ycb = UF::equivalence_intersection(&xa, &xb);
            println!("testing ycb");
            assert_is_residue_class(c, &ycb);
        }
        {
            // same test, diffferent order arguments to the intersection call
            println!("quickly making ycc");
            let ycb = UF::equivalence_intersection(&xb, &xa);
            println!("testing ycb");
            assert_is_residue_class(c, &ycb);
        }

    }

    #[test]
    fn lots_of_residue_tests() {
        const PRIMES: [T; 10] = 
            [2, 3, 5, 7, 11, 13, 17, 19, 23, 29];
        for i in 0..PRIMES.len()-1 {
            for j in i+1..PRIMES.len() {
                modular_residue_test(PRIMES[i], PRIMES[j], PRIMES[i]*PRIMES[j]*4);
            }
        }
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

