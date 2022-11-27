package funcset

// Purely functional implementation of a set.
// An exercise taken from Martin Odersky's Functional Programming Principles in Scala course.

// Not using generics to keep it simple.

// We represent a set by its characteristic function, i.e. its `contains` predicate.
// Predicate is a function which for each `x` of a set `M` assigns a proposition (výrok) `V(x)`.
type FunSet = func(elem int) bool

// Contains indicates whether a set contains a given element.
func Contains(s FunSet, elem int) bool {
	return s(elem)
}

// Empty returns an empty set.
func Empty() FunSet {
	return func(elem int) bool { return false }
}

// Singleton returns the set of the one given element.
func Singleton(elem int) FunSet {
	return func(e int) bool { return e == elem }
}

// Union returns union of the two given sets,
// the sets of all elements that are in either `s` or `t`.
func Union(s FunSet, t FunSet) FunSet {
	return func(elem int) bool {
		return Contains(s, elem) || Contains(t, elem)
	}
}

// Intersection returns the intersection of the two given sets,
// the set of all elements that are both in `s` and `t`.
func Intersection(s FunSet, t FunSet) FunSet {
	return func(elem int) bool {
		return Contains(s, elem) && Contains(t, elem)
	}
}

// Difference returns the difference of the two given sets,
// the set of all elements of `s` that are not in `t`.
func Difference(s FunSet, t FunSet) FunSet {
	return func(elem int) bool {
		return Contains(s, elem) && !Contains(t, elem)
	}
}

// Filter returns the subset of `s` for which `p` holds.
func Filter(s FunSet, p func(elem int) bool) FunSet {
	return func(elem int) bool {
		return Contains(s, elem) && p(elem)
	}
}

// Map returns a set transformed by applying `f` to each element of `s`.
func Map(s FunSet, f func(elem int) int) FunSet {
	return func(elem int) bool {
		return Contains(s, f(elem))
	}
}
