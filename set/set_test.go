package set

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestSet_Int_New(t *testing.T) {
	tests := []struct {
		s        Set[int]
		expected []int
	}{
		{New[int](), []int{}},                   // empty set
		{New(1), []int{1}},                      // singleton
		{New(1, 1, 2, 2, 3, 3), []int{1, 2, 3}}, // duplicates
		{New(1, 2, 3), []int{1, 2, 3}},
	}
	for _, test := range tests {
		assert.ElementsMatch(t, test.expected, test.s.ToList())
	}
}

func TestSet_String_New(t *testing.T) {
	tests := []struct {
		s        Set[string]
		expected []string
	}{
		{New[string](), []string{}},                                  // empty set
		{New("a"), []string{"a"}},                                    // singleton
		{New("a", "a", "b", "b", "c", "c"), []string{"a", "b", "c"}}, // duplicates
		{New("a", "b", "c"), []string{"a", "b", "c"}},
	}
	for _, test := range tests {
		assert.ElementsMatch(t, test.expected, test.s.ToList())
	}
}

func TestSet_Add(t *testing.T) {
	s := New[int]()
	assert.Equal(t, 0, len(s.m))
	assert.ElementsMatch(t, []int{}, s.ToList())
	s.Add(1)
	s.Add(2)
	s.Add(3)
	// add duplicates
	s.Add(1)
	s.Add(2)
	s.Add(3)
	assert.Equal(t, 3, len(s.m))
	assert.ElementsMatch(t, []int{1, 2, 3}, s.ToList())
}

func TestSet_ForEach(t *testing.T) {
	tests := []struct {
		s        Set[int]
		expected []int
	}{
		{New(1, 2, 3), []int{1, 2, 3}},
	}
	for _, test := range tests {
		var actual []int
		test.s.ForEach(func(k int) { actual = append(actual, k) })
		assert.ElementsMatch(t, test.expected, actual)
	}
}

func TestSet_Equals(t *testing.T) {
	tests := []struct {
		s1       Set[int]
		s2       Set[int]
		expected bool
	}{
		{New(1, 2), New(1, 1, 1, 2, 2), true},
		{New(1, 2, 3, 4), New(1, 2, 3, 4), true},
		{New(1, 2, 3, 4), New(4, 3, 2, 1), true},
		{New[int](), New[int](), true},
		{New(1, 2), New(3, 4), false},
		{New(1, 2), New(1, 2, 3), false},
	}
	for _, test := range tests {
		assert.Equal(t, test.expected, test.s1.Equals(test.s2))
		assert.Equal(t, test.expected, test.s2.Equals(test.s1))
	}
}

func TestSet_Contains(t *testing.T) {
	tests := []struct {
		s        Set[int]
		x        int
		expected bool
	}{
		{New(1, 2, 3), 1, true},
		{New(1, 2, 3), 2, true},
		{New(1, 2, 3), 3, true},
		{New(1, 2, 3), 4, false},
		{New[int](), 1, false},
	}
	for _, test := range tests {
		assert.Equal(t, test.expected, test.s.Contains(test.x))
		assert.Equal(t, !test.expected, test.s.NotContains(test.x))
	}
}

func TestSet_IsEmpty(t *testing.T) {
	tests := []struct {
		s        Set[int]
		expected bool
	}{
		{New(2, 4, 6), false},
		{New[int](), true},
	}
	for _, test := range tests {
		assert.Equal(t, test.expected, test.s.IsEmpty())
		assert.Equal(t, !test.expected, test.s.IsNotEmpty())
	}
}

func TestSet_Cardinality(t *testing.T) {
	tests := []struct {
		s        Set[int]
		expected int
	}{
		{New(2, 4, 6), 3},
		{New[int](), 0},
	}
	for _, test := range tests {
		assert.Equal(t, test.expected, test.s.Cardinality())
		assert.Equal(t, len(test.s.m), test.s.Cardinality())
	}
}

func TestSet_Union(t *testing.T) {
	tests := []struct {
		s        Set[int]
		t        Set[int]
		expected Set[int]
	}{
		{New[int](), New[int](), New[int]()},       // empty set
		{New(1), New[int](), New(1)},               // singleton
		{New(1, 2, 3), New(1, 2, 3), New(1, 2, 3)}, // equal sets
		{New(1, 2, 3), New(3, 4, 5), New(1, 2, 3, 4, 5)},
	}
	for _, test := range tests {
		assert.Equal(t, test.expected, test.s.Union(test.t))
		assert.Equal(t, test.expected, test.t.Union(test.s))
	}
}

func TestSet_Intersection(t *testing.T) {
	tests := []struct {
		s        Set[int]
		t        Set[int]
		expected Set[int]
	}{
		{New[int](), New[int](), New[int]()},       // empty set
		{New(1), New[int](), New[int]()},           // singleton
		{New(1, 2, 3), New(1, 2, 3), New(1, 2, 3)}, // equal sets
		{New(1, 2), New(3, 4), New[int]()},         // no common elements
		{New(1, 2, 3), New(3, 4, 5), New(3)},
	}
	for _, test := range tests {
		assert.Equal(t, test.expected, test.s.Intersection(test.t))
		assert.Equal(t, test.expected, test.t.Intersection(test.s))
	}
}

func TestSet_Difference(t *testing.T) {
	tests := []struct {
		s        Set[int]
		t        Set[int]
		expected Set[int]
	}{
		{New[int](), New[int](), New[int]()},     // empty set
		{New(1), New(2, 3), New(1)},              // singleton
		{New(1, 2, 3), New(1, 2, 3), New[int]()}, // equal sets
		{New(1, 2, 3), New(3, 4, 5), New(1, 2)},
	}
	for _, test := range tests {
		assert.Equal(t, test.expected, test.s.Difference(test.t))
	}
}

func TestSet_SymmetricDifference(t *testing.T) {
	tests := []struct {
		s        Set[int]
		t        Set[int]
		expected Set[int]
	}{
		{New[int](), New[int](), New[int]()}, // empty set
		{New(1), New(1), New[int]()},         // singleton
		{New(1, 2, 3), New(3, 4, 5), New(1, 2, 4, 5)},
	}
	for _, test := range tests {
		assert.Equal(t, test.expected, test.s.SymmetricDifference(test.t))
	}
}

func TestSet_SymmetricDifference2(t *testing.T) {
	tests := []struct {
		s        Set[int]
		t        Set[int]
		expected Set[int]
	}{
		{New[int](), New[int](), New[int]()}, // empty set
		{New(1), New(1), New[int]()},         // singleton
		{New(1, 2, 3), New(3, 4, 5), New(1, 2, 4, 5)},
	}
	for _, test := range tests {
		assert.Equal(t, test.expected, test.s.SymmetricDifference2(test.t))
	}
}

func TestSet_SymmetricDifference3(t *testing.T) {
	tests := []struct {
		s        Set[int]
		t        Set[int]
		expected Set[int]
	}{
		{New[int](), New[int](), New[int]()}, // empty set
		{New(1), New(1), New[int]()},         // singleton
		{New(1, 2, 3), New(3, 4, 5), New(1, 2, 4, 5)},
	}
	for _, test := range tests {
		assert.Equal(t, test.expected, test.s.SymmetricDifference3(test.t))
	}
}

func TestSet_IsSubset(t *testing.T) {
	tests := []struct {
		s        Set[int]
		t        Set[int]
		expected bool
	}{
		{New(1, 2, 3), New(1, 2, 3), true}, // A set is a subset of itself.
		{New(1, 2), New(1, 2, 3), true},
		{New(1), New(2, 3), false},
		{New(1, 4), New(1, 2, 3), false},
		{New[int](), New[int](), true},
	}
	for _, test := range tests {
		assert.Equal(t, test.expected, test.s.IsSubsetOf(test.t))
	}
}

func TestSet_IsSubset2(t *testing.T) {
	tests := []struct {
		s        Set[int]
		t        Set[int]
		expected bool
	}{
		{New(1, 2, 3), New(1, 2, 3), true}, // A set is a subset of itself.
		{New(1, 2), New(1, 2, 3), true},
		{New(1), New(2, 3), false},
		{New(1, 4), New(1, 2, 3), false},
		{New[int](), New[int](), true},
	}
	for _, test := range tests {
		assert.Equal(t, test.expected, test.s.IsSubsetOf2(test.t))
	}
}

func TestSet_IsProperSubset(t *testing.T) {
	tests := []struct {
		s        Set[int]
		t        Set[int]
		expected bool
	}{
		{New(1, 2, 3), New(1, 2, 3), false},
		{New(1, 2), New(1, 2, 3), true},
		{New(1), New(2, 3), false},
		{New(1, 4), New(1, 2, 3), false},
		{New[int](), New[int](), false},
	}
	for _, test := range tests {
		assert.Equal(t, test.expected, test.s.IsProperSubsetOf(test.t))
	}
}

func TestSet_IsSuperset(t *testing.T) {
	tests := []struct {
		s        Set[int]
		t        Set[int]
		expected bool
	}{
		{New(1, 2, 3), New(1, 2, 3), true},
		{New(1, 2, 3), New(1, 2), true},
		{New(1), New(2, 3), false},
		{New[int](), New[int](), true},
	}
	for _, test := range tests {
		assert.Equal(t, test.expected, test.s.IsSupersetOf(test.t))
	}
}

func TestSet_Filter(t *testing.T) {
	tests := []struct {
		s        Set[int]
		p        func(n int) bool
		expected Set[int]
	}{
		{
			New(1, 2, 3),
			func(n int) bool { return true },
			New(1, 2, 3),
		},
		{
			New(1, 2, 3),
			func(n int) bool { return false },
			New[int](),
		},
		{
			New(1, 2, 3),
			func(n int) bool { return n%2 != 0 },
			New(1, 3),
		},
	}
	for _, test := range tests {
		assert.Equal(t, test.expected, test.s.Filter(test.p))
	}
}

func TestSet_Map(t *testing.T) {
	tests := []struct {
		s        Set[int]
		f        func(n int) int
		expected Set[int]
	}{
		{
			New(1, 2, 3),
			func(n int) int { return n * n },
			New(1, 4, 9),
		},
	}
	for _, test := range tests {
		assert.Equal(t, test.expected, test.s.Map(test.f))
	}
}

func TestSet_CartesianProduct(t *testing.T) {
	tests := []struct {
		s        Set[int]
		t        Set[string]
		expected []Tuple[int, string]
	}{
		{
			New(1, 2, 3), New("a", "b", "c"), []Tuple[int, string]{
				{1, "a"}, {2, "a"}, {3, "a"},
				{1, "b"}, {2, "b"}, {3, "b"},
				{1, "c"}, {2, "c"}, {3, "c"},
			},
		},
		{
			New(1, 2), New("a", "b", "c"), []Tuple[int, string]{
				{1, "a"}, {2, "a"},
				{1, "b"}, {2, "b"},
				{1, "c"}, {2, "c"},
			},
		},
		{
			New(1, 2, 3), New("a", "b"), []Tuple[int, string]{
				{1, "a"}, {2, "a"}, {3, "a"},
				{1, "b"}, {2, "b"}, {3, "b"},
			},
		},
	}
	for _, test := range tests {
		assert.ElementsMatch(t, test.expected, CartesianProduct(test.s, test.t))
	}
}

func TestSet_CartesianProduct2(t *testing.T) {
	tests := []struct {
		s        Set[int]
		t        Set[string]
		expected []map[int]string
	}{
		{
			New(1, 2, 3), New("a", "b", "c"), []map[int]string{
				{1: "a"}, {2: "a"}, {3: "a"},
				{1: "b"}, {2: "b"}, {3: "b"},
				{1: "c"}, {2: "c"}, {3: "c"},
			},
		},
		{
			New(1, 2), New("a", "b", "c"), []map[int]string{
				{1: "a"}, {2: "a"},
				{1: "b"}, {2: "b"},
				{1: "c"}, {2: "c"},
			},
		},
		{
			New(1, 2, 3), New("a", "b"), []map[int]string{
				{1: "a"}, {2: "a"}, {3: "a"},
				{1: "b"}, {2: "b"}, {3: "b"},
			},
		},
	}
	for _, test := range tests {
		assert.ElementsMatch(t, test.expected, CartesianProduct2(test.s, test.t))
	}
}

func Test_Subsets(t *testing.T) {
	tests := []struct {
		s        []int
		expected [][]int
	}{
		{[]int{}, [][]int{{}}},       // empty set
		{[]int{1}, [][]int{{}, {1}}}, // singleton
		{[]int{1, 2, 3, 4}, [][]int{
			{}, {1}, {2}, {3}, {4},
			{1, 2}, {1, 3}, {1, 4}, {1, 2, 3}, {1, 2, 4}, {1, 3, 4},
			{2, 3}, {2, 4}, {2, 3, 4},
			{3, 4},
			{1, 2, 3, 4},
		}},
	}
	for _, test := range tests {
		assert.ElementsMatch(t, test.expected, Subsets(test.s))
	}
}

// An exercise from Polak's Math book.
func TestSet_PolakMathBookExercise(t *testing.T) {
	// Let's have sets `A = {a, c, e, g}`, `B = {b, c, d, e}` and an universal set `U = {a, b, c, d, e, f, g}`.
	// Then following holds:
	// `A ⊂ U`, `B ⊂ U`
	// `A ⊄ B`, `B ⊄ A`, `A != B`
	// `A ∪ B = {a, b, c, d, e, g}`
	// `A ∩ B = {c, e}`, i.e. `A ∩ B != ∅`, i.e. sets `A` and `B` are not disjoint.
	// `A \ B = {a, g}`, `B \ A = {b, d}`
	// `A' = U \ A = {b, d, f}`, `B' = U \ B = {a, f, g}`
	a := New('a', 'c', 'e', 'g')
	b := New('b', 'c', 'd', 'e')
	u := New('a', 'b', 'c', 'd', 'e', 'f', 'g')

	assert.True(t, a.IsSubsetOf(u))
	assert.True(t, b.IsSubsetOf(u))
	assert.False(t, a.IsSubsetOf(b))
	assert.False(t, b.IsSubsetOf(a))
	assert.False(t, a.Equals(b))
	assert.ElementsMatch(t, a.Union(b).ToList(), []rune{'a', 'b', 'c', 'd', 'e', 'g'})
	assert.ElementsMatch(t, a.Intersection(b).ToList(), []rune{'c', 'e'})
	assert.False(t, a.Intersection(b).IsEmpty())
	assert.False(t, a.IsDisjointWith(b))
	assert.ElementsMatch(t, a.Difference(b).ToList(), []rune{'a', 'g'})
	assert.ElementsMatch(t, b.Difference(a).ToList(), []rune{'b', 'd'})
	assert.ElementsMatch(t, a.Complement(u).ToList(), []rune{'b', 'd', 'f'})
	assert.ElementsMatch(t, b.Complement(u).ToList(), []rune{'a', 'f', 'g'})
}
