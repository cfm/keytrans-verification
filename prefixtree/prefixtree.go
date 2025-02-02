package main

import (
	"fmt"

	"github.com/spf13/cast"
)

type Node struct {
    hasData bool
    key int
    value int // e.g. some public key
    left *Node
    right *Node
}

/*@
type BitConversion domain {
    func GetBits(int) seq[bool]
    func GetInt(seq[bool]) int

    axiom { // bijection between int and bits
        forall i int :: { GetBits(i) } GetInt(GetBits(i)) == i
    }
}
@*/

//@ ensures acc(res)
//@ ensures len(res) == len(GetBits(key))
//@ ensures forall i int :: { res[i] } 0 <= i && i < len(res) ==> res[i] == GetBits(key)[i]
func ComputeBits(key int) (res []bool) {
	return cast.ToBoolSlice(key)
}

/*@
pred (n *Node) PrefixTree() {
    n.PrefixSubtree(seq[bool]{})
}

pred (n *Node) PrefixSubtree(prefix seq[bool]) {
    acc(n) &&
    (n.hasData ==> GetBits(n.key) == prefix && n.left == nil && n.right == nil) &&
    (n.left != nil ==> n.left.PrefixSubtree(prefix ++ seq[bool]{false})) &&
    (n.right != nil ==> n.right.PrefixSubtree(prefix ++ seq[bool]{true}))
}
@*/

func main() {
    n000 := &Node{true, 0, 42, nil, nil}
    //@ assume GetBits(0) == seq[bool]{false, false, false}
    //@ fold n000.PrefixSubtree(seq[bool]{false, false, false})

    n001 := &Node{true, 1, 0, nil, nil}
    //@ assume GetBits(1) == seq[bool]{false, false, true}
    //@ fold n001.PrefixSubtree(seq[bool]{false, false, true})

    n00 := &Node{false, -1, -1, n000, n001}
    //@ fold n00.PrefixSubtree(seq[bool]{false, false})
    
    n0 := &Node{false, -1, -1, n00, nil}
    //@ fold n0.PrefixSubtree(seq[bool]{false})

    n := &Node{false, -1, -1, n0, nil}
    //@ fold n.PrefixSubtree(seq[bool]{})
    //@ fold n.PrefixTree()

	fmt.Printf("%p: %+v\n", n, n)
	fmt.Printf("%p:   %+v\n", n0, n0)
	fmt.Printf("%p:     %+v\n", n00, n00)
	fmt.Printf("%p:       %+v\n", n000, n000)
	fmt.Printf("%p:       %+v\n", n001, n001)
}

/*@
type Hashing domain {
    func hash2(int, int) int
    func inv21(int) int
    func inv22(int) int

    axiom { // hash2 is injective
        forall i1, i2 int :: { hash2(i1, i2) } inv21(hash2(i1, i2)) == i1 && inv22(hash2(i1, i2)) == i2
    }
}
@*/

//@ trusted
//@ ensures   res == hash2(key, value)
func HashData(key, value int) (res int) {
    return key + value // just a stupid example
}

//@ preserves acc(n.PrefixSubtree(prefix), 1/2)
//@ ensures   res == unfolding acc(n.PrefixSubtree(prefix), 1/2) in hash2(n.key, n.value)
func HashNodeData(n *Node /*@, ghost prefix seq[bool] @*/) (res int) {
    //@ unfold acc(n.PrefixSubtree(prefix), 1/4)
    res = HashData(n.key, n.value)
    //@ fold acc(n.PrefixSubtree(prefix), 1/4)
	return res
}

//@ trusted
//@ ensures   res == hash2(left, right)
func CombineSubtreeHashes(left, right int) (res int) {
    return left + right // just a stupid example
}

/*@
ghost
decreases
requires acc(n.PrefixTree(), _)
pure func (n *Node) prefixTreeHash() int {
    return unfolding acc(n.PrefixTree(), _) in n.prefixSubtreeHash(seq[bool]{})
}

ghost
decreases n.PrefixSubtree(prefix)
requires acc(n.PrefixSubtree(prefix), _)
pure func (n *Node) prefixSubtreeHash(prefix seq[bool]) int {
    return unfolding acc(n.PrefixSubtree(prefix), _) in (
        n.hasData ?
            hash2(n.key, n.value) :
            hash2(
                n.left == nil ? 0 : n.left.prefixSubtreeHash(prefix ++ seq[bool]{false}),
                n.right == nil ? 0 : n.right.prefixSubtreeHash(prefix ++ seq[bool]{true})))
}

ghost
decreases
requires acc(n.PrefixTree(), _)
pure func (n *Node) prefixTreeContains(key, value int) bool {
    return unfolding acc(n.PrefixTree(), _) in n.prefixSubtreeContains(seq[bool]{}, key, value)
}

ghost
decreases n.PrefixSubtree(prefix)
requires acc(n.PrefixSubtree(prefix), _)
pure func (n *Node) prefixSubtreeContains(prefix seq[bool], key, value int) bool {
    return unfolding acc(n.PrefixSubtree(prefix), _) in (
        len(GetBits(key)) < len(prefix) ?
            false :
            len(GetBits(key)) == len(prefix) ?
                n.hasData && n.hasData :
                GetBits(key)[len(prefix)] ?
                    (n.right == nil ? false : n.right.prefixSubtreeContains(prefix ++ seq[bool]{true}, key, value)) :
                    (n.left == nil ? false : n.left.prefixSubtreeContains(prefix ++ seq[bool]{false}, key, value)))
}
@*/

// copath is sorted such that hashes for subtrees deeper in the prefix tree appear later in the slice
//@ preserves acc(copath, 1/2) && len(copath) == len(GetBits(key)) + 1
//@ preserves acc(n.PrefixTree(), 1/2) && rootHash == n.prefixTreeHash()
// ensures   res ==> n.prefixTreeContains(key, value) // TODO
func CheckInclusion(key int, value int, rootHash int, copath []int, n *Node) (res bool) {
    dataHash := HashData(key, value)
    bits := ComputeBits(key)
    var computedHash int

    //@ invariant -1 <= i && i < len(bits)
    //@ invariant acc(copath, 1/4) && acc(bits, 1/4)
    //@ invariant len(copath) == len(GetBits(key)) + 1
    //@ invariant len(bits) == len(GetBits(key))
    for i := len(bits) - 1; i >= 0; i-- {
        if bits[i] {
            computedHash = CombineSubtreeHashes(copath[i], dataHash)
        } else {
            computedHash = CombineSubtreeHashes(dataHash, copath[i])
        }
    }

    return computedHash == rootHash
}

// recursive implementation of computing the root hash using the copath
//@ requires  0 <= i && i <= len(GetBits(key))
//@ requires  len(copath) == len(GetBits(key)) + 1
//@ preserves acc(copath, 1/2)
//@ preserves acc(n.PrefixSubtree(prefix), 1/2)
func ComputePath(key int, value int, i int, copath []int, n *Node /*@, ghost prefix seq[bool] @*/) (hash int) {
    //@ unfold acc(n.PrefixSubtree(prefix), 1/2)
    bits := ComputeBits(key)
    if len(bits) == i {
        hash = HashData(key, value)
    } else if bits[i] {
        var prevHash int
        if n.right == nil {
            prevHash = 0
        } else {
            prevHash = ComputePath(key, value, i + 1, copath, n.right /*@, prefix ++ seq[bool]{ true } @*/)
        }
        hash = CombineSubtreeHashes(copath[i], prevHash)
    } else {
        var prevHash int
        if n.left == nil {
            prevHash = 0
        } else {
            prevHash = ComputePath(key, value, i + 1, copath, n.left /*@, prefix ++ seq[bool]{ false } @*/)
        }
        hash = CombineSubtreeHashes(prevHash, copath[i])
    }
    //@ fold acc(n.PrefixSubtree(prefix), 1/2)
    return
}
