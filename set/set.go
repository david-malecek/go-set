package set

type Set[K comparable] struct {
	m map[K]struct{} // empty structs occupy 0 memory
}

// New creates a new set with `0 to n` elements.
func New[K comparable](ks ...K) Set[K] {
	m := make(map[K]struct{})
	for _, k := range ks {
		m[k] = struct{}{}
	}
	return Set[K]{m}
}

// Add adds an element to this set.
func (s *Set[K]) Add(k K) {
	s.m[k] = struct{}{}
}

// Contains indicates whether the set contains a given element.
// This is Set's characteristic function.
//
// Mathematical notation is `a ∈ A`, which we read as
// `a` is _Element Of_ set `A`
// (or element `a` belongs to set `A`)
func (s *Set[K]) Contains(k K) bool {
	_, ok := s.m[k]
	return ok
}

// NotContains inidicates whether the set does not contain a given element.
//
// Mathematical notation is `b ∉ A`, which we read as
// `b` is _Not Element Of_ set `A`
// (or element `b` does not belong to set `A`).
func (s *Set[K]) NotContains(k K) bool {
	return !s.Contains(k)
}

// Empty Set, ∅.
// The set is empty if it contains no element.
//
// IsEmpty returns `true` if it is empty, `false` otherwise.
func (s Set[K]) IsEmpty() bool { return s.Cardinality() == 0 }

// Non-Empty Set
// If a set contains at least 1 element, we say the set is _Non-empty_.
//
// IsNotEmpty returns `true`, if it is not empty, `false` otherwise.
func (s Set[K]) IsNotEmpty() bool { return !s.IsEmpty() }

// Cardinality
//
// Cardinality (aka size) of a set is a measure of the number of elements of the set.
func (s Set[K]) Cardinality() int {
	return len(s.m)
}

//
// Set Relations and Operations
//

// Subset
//
// IsSubsetOf tests whether the set `s` is a subset of a set `t`.
// Set `s` is a _subset_ of a set `t` if all elements of `s` are also elements of `t`.
//
// Mathematical notation is `A ⊂ B`, and is defined as
// `A ⊂ B <=> (∀x ∈ U; x ∈ A => x ∈ B)`
func (s *Set[K]) IsSubsetOf(t Set[K]) bool {
	return s.ForAll(t.Contains)
}

// Another implementation based on mathematical Subset Properties.
// TODO: verify the definition with Matematika 1 CVUT FJFI and Teorie Mnozin books.
// https://en.wikipedia.org/wiki/Subset#Properties
// 1. A is a subset of B if and only if their intersection is equal to A.
// 2. A is a subset of B if and only if their union is equal to B.
// 3. A is a subset of B if and only if the cardinality of their intersection is equal to the cardinality A.
func (s *Set[K]) IsSubsetOf2(t Set[K]) bool {
	prop1 := s.Intersection(t).Equals(*s)
	prop2 := s.Union(t).Equals(t)
	prop3 := s.Intersection(t).Cardinality() == s.Cardinality()
	return prop1 && prop2 && prop3
}

// TODO: verify this
// IsProperSubsetOf tests whether the set `s` is a proper (or strict) subset of set `t`.
// Set `s` must be subset of `t`, but not equal (i.e. there exists at least one element
// of `t` which is not an element of `s`).
func (s *Set[K]) IsProperSubsetOf(t Set[K]) bool {
	return s.IsSubsetOf(t) && !s.Equals(t)
}

// Superset
//
// IsSuperset tests whether the set `s` is a superset of set `t`.
func (s *Set[K]) IsSupersetOf(t Set[K]) bool {
	return t.ForAll(s.Contains)
}

// TODO: Verify this
// IsProperSupersetOf tests whether the set `s` is a proper (or strict) superset of set `t`.
// Set `s` must be superset of `t`, but not equal.
func (s *Set[K]) IsProperSupersetOf(t Set[K]) bool {
	return s.IsSupersetOf(t) && !s.Equals(t)
}

// Equality
//
// Equals checks whether the two given sets are equal.
// Sets `s` and `t` are equal if every element of `s` is an element of `t`,
// and every element of `t` is an element of `s`.
//
// Mathematical definition:
// `A ⊂ B <=> (x ∈ A => x ∈ B)`
// `B ⊂ A <=> (x ∈ B => x ∈ A)`
//
// `A = B <=> A ⊂ B ∧ B ⊂ A`
// `A = B <=> (∀x ∈ U; x ∈ A <=> x ∈ B)`
func (s Set[K]) Equals(t Set[K]) bool {
	// Cardinality comparison is not part of mathematical definition,
	// but we do it for efficiency.
	if s.Cardinality() != t.Cardinality() {
		return false
	}
	// `A = B <=> (∀x ∈ U; x ∈ A <=> x ∈ B)`
	return s.ForAll(t.Contains) && t.ForAll(s.Contains)
}

// Another implementation based on mathematical definition definition of _Set Equality_:
// `A = B <=> A ⊂ B ∧ B ⊂ A`
func (s Set[K]) Equals2(t Set[K]) bool {
	return s.IsSubsetOf(t) && s.IsSubsetOf(s)
}

// Union
//
// Union, `s ∪ t`, returns the union of sets `s` and `t`,
// i.e. the set of all elements that are in `s` OR `t` (or both).
//
// Mathematical definition:
// `A ∪ B = {x ∈ U; x ∈ A ∨ x ∈ B}`
func (s *Set[K]) Union(t Set[K]) Set[K] {
	union := New[K]()
	s.ForEach(union.Add)
	t.ForEach(union.Add)
	return union
}

// Intersection
//
// Intersection, `s ∩ t`, returns the intersection of sets `s` and `t`,
// i.e. the set of all elements that are both in `s` AND `t`.
//
// Mathematical definition:
// `A ∩ B = {x ∈ U; x ∈ A ∧ x ∈ B}`
func (s *Set[K]) Intersection(t Set[K]) Set[K] {
	intersection := New[K]()
	for k := range s.m {
		if _, ok := t.m[k]; ok {
			intersection.Add(k)
		}
	}
	return intersection
}

func (s *Set[K]) Intersection2(t Set[K]) Set[K] {
	return s.Filter(t.Contains)
}

// Disjoint Sets
//
// Sets `A`, `B`, for which `A ∩ B = ∅` holds (i.e. they don't have any common element)
// are _disjoint_.
//
// IsDisjointWith tests if `s ∩ t = ∅`.
func (s *Set[K]) IsDisjointWith(t Set[K]) bool {
	return s.Intersection(t).IsEmpty()
}

// Difference
//
// Difference, `s \ t`, or `s − t`, returns the difference of sets `s` and `t`,
// i.e. the set of all elements that are in `s` (elements of `s`) but not in `t` (not elements of `t`).
//
// Mathematical definition:
// `A \ B = {x ∈ U; x ∈ A ∧ x ∉ B}`
func (s *Set[K]) Difference(t Set[K]) Set[K] {
	return s.Filter(func(k K) bool { return !t.Contains(k) })
}

// SymmetricDifference, returns the set of all elements that are a member of exatly one of `s` or `t`,
// i.e. elements which are in one of the sets, but not in both.
func (s *Set[K]) SymmetricDifference(t Set[K]) Set[K] {
	sOnly := s.Filter(func(k K) bool { return !t.Contains(k) })
	tOnly := t.Filter(func(k K) bool { return !s.Contains(k) })
	return sOnly.Union(tOnly)
}

// SymmetricDifference2 implementation based on `(A ∪ B) \ (A ∩ B)`.
func (s Set[K]) SymmetricDifference2(t Set[K]) Set[K] {
	return difference(union(s, t), intersection(s, t))
}

// SymmetricDifference3 implementation based on `(A \ B) ∪ (B \ A)`.
func (s Set[K]) SymmetricDifference3(t Set[K]) Set[K] {
	return union(difference(s, t), difference(t, s))
}
func union[K comparable](s, t Set[K]) Set[K]        { return s.Union(t) }
func intersection[K comparable](s, t Set[K]) Set[K] { return s.Intersection(t) }
func difference[K comparable](s, t Set[K]) Set[K]   { return s.Difference(t) }

// Complement
//
// When `U` is a universal set, the difference, and `A` is a subset of `U`, then
// the difference `U\A` is also called the complement of `A` in `U`.
//
// `A' = {a ∈ U | a ∉ A}`
func (s *Set[K]) Complement(u Set[K]) Set[K] {
	return u.Difference(*s)
}

// Filter returns the subset of `s` for which `p` holds.
func (s *Set[K]) Filter(p func(k K) bool) Set[K] {
	subset := New[K]()
	s.ForEach(func(k K) {
		if p(k) {
			subset.Add(k)
		}
	})
	return subset
}

// Map returns a set transformed by applying `f` to each element of `s`.
func (s *Set[K]) Map(f func(k K) K) Set[K] {
	t := New[K]()
	s.ForEach(func(k K) { t.Add(f(k)) })
	return t
}

// ForEach applies a function `f` to all elements of this set.
func (s *Set[K]) ForEach(f func(k K)) {
	for k := range s.m {
		f(k)
	}
}

func (s *Set[K]) ForAll(p func(k K) bool) bool {
	for k := range s.m {
		if !p(k) {
			return false
		}
	}
	return true
}

// ToList returns a list of all set's elements in an indeterminate order.
func (s Set[K]) ToList() []K {
	return keys(s.m)
}

// keys returns the keys of the map `m`in an indeterminate order.
func keys[M ~map[K]V, K comparable, V any](m M) []K {
	// See https://cs.opensource.google/go/x/exp/+/master:maps/maps.go.
	keys := make([]K, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	return keys
}

// Cartesian Product
//
// CartesianProduct returns all possible ordered pairs (ks, kt)
// where `ks` is a member of `s` and `kt` is a member of `t`.
func CartesianProduct[T, U comparable](s Set[T], t Set[U]) []Tuple[T, U] {
	f := func(t T, u U) Tuple[T, U] { return Tuple[T, U]{t, u} }
	return zipWith(s, t, f)
}

type Tuple[T, U comparable] struct {
	Left  T
	Right U
}

// Yet another implementation returning a list of maps instead of a list of `Tuple`s.
func CartesianProduct2[T, U comparable](s Set[T], t Set[U]) []map[T]U {
	f := func(t T, u U) map[T]U { return map[T]U{t: u} }
	return zipWith(s, t, f)
}

func zipWith[R any, T, U comparable](ts Set[T], us Set[U], f func(t T, u U) R) []R {
	z := []R{}
	ts.ForEach(func(t T) {
		us.ForEach(func(u U) {
			z = append(z, f(t, u))
		})
	})
	return z
}

// Subsets returns _all_ subsets of a given set, including:
// - an empty set, as it is a subset of any set: `∅ ⊂ X`,
// - the set itself, as any set is a subset of itself: `X ⊂ X`.
//
// In mathematics, _all_ subsets of a set is known as a _PowerSet_.
func Subsets(s []int) [][]int {
	var loop func(s []int, prev []int) [][]int
	loop = func(s []int, prev []int) [][]int {
		if len(s) == 0 {
			return append([][]int{}, prev) // prev :: Nil
		}
		head := s[0]
		tail := s[1:]
		curr := append(prev, head)                           // prev :+ head
		return append(loop(tail, prev), loop(tail, curr)...) // loop(t, prev) ++ loop(t, curr)
	}
	return loop(s, []int{})
}
