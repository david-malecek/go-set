package funcset

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestFunSet_Contains_Empty(t *testing.T) {
	s := Empty()
	assert.False(t, Contains(s, 1))
}

func TestFunSet_Contains_Singleton(t *testing.T) {
	s := Singleton(1)
	assert.True(t, Contains(s, 1))
	assert.False(t, Contains(s, 2))
}

func TestFunSet_Union(t *testing.T) {
	s1 := Singleton(1)
	s2 := Singleton(2)
	u := Union(s1, s2)
	assert.True(t, Contains(u, 1))
	assert.True(t, Contains(u, 2))
	assert.False(t, Contains(u, 3))
}

func TestFunSet_Intersection(t *testing.T) {
	s1 := Singleton(1)
	s2 := Singleton(1)
	i := Intersection(s1, s2)
	assert.True(t, Contains(i, 1))
	assert.False(t, Contains(i, 2))
}

func TestFunSet_Difference(t *testing.T) {
	s1 := Singleton(1)
	s2 := Singleton(2)
	i := Difference(s1, s2)
	assert.True(t, Contains(i, 1))
	assert.False(t, Contains(i, 2))
}

func TestFunSet_Filter(t *testing.T) {
	s := Union(Singleton(1), Singleton(2))
	isEven := func(n int) bool { return n%2 == 0 }
	actual := Filter(s, isEven)
	assert.False(t, Contains(actual, 1))
	assert.True(t, Contains(actual, 2))
}
