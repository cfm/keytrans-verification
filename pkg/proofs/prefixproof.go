package proofs

import (
	"crypto/sha256"
	"errors"
)

/*@
pred (t *PrefixTree) Inv() {
	acc(t, _) && (t != nil ==> acc(t.InvRec(), _))
}

pred (t PrefixTree) InvRec() {
	acc(t.Value) &&
	(t.Leaf != nil ==> acc(t.Leaf, _) && acc(t.Leaf.Inv(), _)) &&
	(t.Left != nil ==> acc(t.Left, _) && acc(t.Left.Inv(), _)) &&
	(t.Right != nil ==> acc(t.Right, _) && acc(t.Right.Inv(), _)) &&
	// One of value, leaf, or both children must be defined
	(t.Value != nil || t.Leaf != nil || (t.Left != nil && t.Right != nil)) &&
	// If there's one children, there must be two
	(t.Left != nil) == (t.Right != nil) &&
	// Node is either a leaf or has children
	!((t.Leaf != nil) && (t.Left != nil && t.Right != nil)) &&
	// If a node's value is defined, its children's values must be defined
	((t.Value != nil && t.Left != nil && t.Right != nil) ==> (t.Left.Value != nil && t.Right.Value != nil))
}
@*/

// @ requires t != nil
// @ requires acc(t.Inv(), _)
// @ decreases
// @ pure
func (t *PrefixTree) GetValue() *[sha256.Size]byte {
	return /*@ unfolding acc(t.Inv(), _) in unfolding acc(t.InvRec(), _) in @*/ t.Value
}

// @ requires t != nil
// @ requires acc(t.Inv(), _)
// @ requires t.GetValue() != nil
// @ decreases
// @ pure
func (t *PrefixTree) GetValueArray() [sha256.Size]byte {
	return /*@ unfolding acc(t.Inv(), _) in unfolding acc(t.InvRec(), _) in @*/ *t.Value
}

// Recursive prefix tree data structure
type PrefixTree struct {
	// Hash value of this node; must be computed if nil
	Value *[sha256.Size]byte
	// If set, this node is a leaf of the given value. Left and Right must be nil
	// in this case.
	Leaf *PrefixLeaf
	// Left subtree. May be nil even if Right is not nil.
	Left *PrefixTree
	// Right subtree. May be nil even if Left is not nil.
	Right *PrefixTree
}

// Creates a prefix tree recursively from a list of binary ladder steps and
// nodes that give all copaths. The function assumes that steps is sorted
// ascending by steps.Step.Vrf_output and that coPathNodes is sorted ascending
// too. prefix will be initially empty and reflects the current position in the
// prefix tree.
// @ requires forall i int :: { &prefix[i] } 0 <= i && i < len(prefix) ==> acc(&prefix[i], _)
// @ requires forall i int :: { steps[i] } 0 <= i && i < len(steps) ==> acc(&steps[i], _)
// @ requires forall i int :: { coPathNodes[i] } 0 <= i && i < len(coPathNodes) ==> acc(&coPathNodes[i], _)
// @ ensures err == nil ==> tree != nil && tree.Inv()
func ToTreeRecursive(prefix []bool, steps []CompleteBinaryLadderStep, coPathNodes []NodeValue) (tree *PrefixTree, nextSteps []CompleteBinaryLadderStep, nextNodes []NodeValue, err error) {
	tree = nil
	nextSteps = steps
	nextNodes = coPathNodes
	err = nil

	// If there are no more steps to insert into the prefix tree, insert a copath
	// node at the current subtree.
	if len(steps) == 0 {
		if len(coPathNodes) == 0 {
			err = errors.New("not enough co-path nodes")
			return
		} else {
			val /* @@@ */ := coPathNodes[0]
			tree = &PrefixTree{Value: &val}
			//@ fold tree.InvRec()
			//@ fold tree.Inv()
			nextNodes = coPathNodes[1:]
			return
		}
	}

	step := steps[0]

	prefixMatches := false
	if len(prefix) > len(step.Step.Vrf_output)*8 {
		err = errors.New("prefix longer than VRF output")
		return
	} else if len(prefix) > 0 {
		//@ invariant 0 <= i && i <= len(prefix)
		for i := 0; i < len(prefix); i++ {
			//@ assert 0 <= i && i < len(prefix)
			b := step.Step.Vrf_output[i/8]
			bit := ((b >> uint(i%8)) & 1) == 1
			prefixMatches = prefixMatches && bit == prefix[i]
		}
	}

	if prefixMatches {
		// The current prefix is a prefix of step.Step.Vrf_output.
		if int(step.Result.Depth) < len(prefix) { // assume one-based depth; https://github.com/ietf-wg-keytrans/draft-protocol/issues/37
			// The server tells us that this depth does suffice to identify the
			// vrf output. Insert the result in one of its children.
			nextDepth := len(prefix) + 1
			nextBit := step.Step.Vrf_output[nextDepth/8]>>(nextDepth%8) == 0x01
			if nextBit {
				// Go right
				if len(coPathNodes) == 0 {
					err = errors.New("not enough co-path nodes")
					return
				} else {
					// As we must recurse right, the left child must be provided as a co
					// path node.
					left := &PrefixTree{Value: &coPathNodes[0]}
					//@ fold left.InvRec()
					//@ fold left.Inv()
					if right, recSteps, recNodes, e := ToTreeRecursive(append( /*@ perm(1/2), @*/ prefix, true), steps, coPathNodes[1:]); e != nil {
						err = e
						return
					} else {
						tree = &PrefixTree{Left: left, Right: right}
						//@ fold tree.InvRec()
						//@ fold tree.Inv()
						nextSteps = recSteps
						nextNodes = recNodes
						return
					}
				}
			} else {
				// Go left. Continue with the algorithm recursively to the right
				// afterwards. Either, the next step may be inserted there or it is
				// provided as a co path node.
				if left, recSteps, recNodes, e := ToTreeRecursive(append( /*@ perm(1/2), @*/ prefix, false), steps, coPathNodes); e != nil {
					err = e
					return
				} else if right, recSteps2, recNodes2, e := ToTreeRecursive(append( /*@ perm(1/2), @*/ prefix, false), recSteps, recNodes); e != nil {
					err = e
					return
				} else {
					tree = &PrefixTree{Left: left, Right: right}
					//@ fold tree.InvRec()
					//@ fold tree.Inv()
					nextSteps = recSteps2
					nextNodes = recNodes2
					return
				}
			}
		} else if int(step.Result.Depth) == len(prefix) {
			// We are at the right depth to insert the search result. Insert it based
			// on the type of result.
			resultType := step.Result.Result_type
			if resultType == Inclusion {
				leaf /* @@@ */ := step.Step
				tree = &PrefixTree{Leaf: &leaf}
				//@ fold tree.InvRec()
				//@ fold tree.Inv()
				nextSteps = steps[1:]
				return
			} else if resultType == NonInclusionLeaf {
				if step.Result.Leaf == nil {
					err = errors.New("no leaf for inclusion proof given")
					return
				} else {
					leaf /* @@@ */ := step.Result.Leaf
					tree = &PrefixTree{Leaf: leaf}
					//@ fold tree.InvRec()
					//@ fold tree.Inv()
					nextSteps = steps[1:]
					return
				}
			} else if resultType == NonInclusionParent {
				tree = &PrefixTree{Value: &[32]byte{}}
				//@ fold tree.InvRec()
				//@ fold tree.Inv()
				nextSteps = steps[1:]
				return
			} else {
				err = errors.New("invalid result type")
				return
			}
		} else {
			err = errors.New("prefix tree construction invariant violated")
			return
		}
	} else if len(coPathNodes) == 0 {
		err = errors.New("not enough co-path nodes")
		return
	} else {
		tree = &PrefixTree{Value: &coPathNodes[0]}
		//@ fold tree.InvRec()
		//@ fold tree.Inv()
		nextNodes = coPathNodes[1:]
		return
	}
}

// Construct a prefix tree from a prefix proof and the provided binary ladder
// steps. We assume that the binary ladder steps are in the order that the
// binary ladder would request them.
// @ requires prf.Inv()
// @ requires forall i int :: { fullLadder[i] } 0 <= i && i < len(fullLadder) ==> acc(&fullLadder[i], 1/2)
// @ ensures err == nil ==> tree != nil && tree.Inv()
func (prf PrefixProof) ToTree(fullLadder []BinaryLadderStep) (tree *PrefixTree, err error) {
	tree = &PrefixTree{}
	if len(fullLadder) < len(prf.Results) {
		return nil, errors.New("too many results")
	}

	var steps []CompleteBinaryLadderStep
	//@ unfold acc(prf.Inv(), _)
	if steps, err = CombineResults(prf.Results, fullLadder); err != nil {
		//@ fold acc(prf.Inv(), _)
		return nil, err
	}
	//@ fold acc(prf.Inv(), _)

	//@ unfold acc(prf.Inv(), _)
	if tree, _, _, err = ToTreeRecursive([]bool{}, steps, prf.Elements); err != nil {
		//@ fold acc(prf.Inv(), _)
		return
	}
	_, err = tree.ComputeHash()
	//@ fold acc(prf.Inv(), _)
	return
}

// @ preserves acc(tree.Inv(), 1/2)
// @ requires acc(tree.InvRec(), 1/2)
// @ ensures err == nil && tree != nil ==> forall i int :: { &hashContent[i] } 0 <= i && i < len(hashContent) ==> acc(&hashContent[i])
func (tree *PrefixTree) HashContent() (hashContent []byte, err error) {
	hashContent = make([]byte, sha256.Size+1)
	if tree == nil {
		return hashContent, nil
	} else if /*@ unfolding acc(tree.Inv(), _) in unfolding acc(tree.InvRec(), _) in @*/ tree.Left == nil && tree.Right == nil {
		if value /*@ @ @*/, err := tree.ComputeHash(); err != nil {
			return nil, err
		} else {
			return append( /*@ perm(1/2), @*/ []byte{0x01}, value[:]...), nil
		}
	} else {
		//@ unfold acc(tree.Inv(), 1/2)
		//@ unfold acc(tree.InvRec(), 1/2)
		if leftContent, err := tree.Left.HashContent(); err != nil {
			return nil, err
		} else if rightContent, err := tree.Right.HashContent(); err != nil {
			return nil, err
		} else {
			hashContent = append( /*@ perm(1/2), @*/ []byte{0x02}, leftContent...)
			return append( /*@ perm(1/2), @*/ hashContent, rightContent...), nil
		}
	}
}

// Recursively compute all hashes of a prefix tree.
// @ preserves acc(tree.Inv(), 1/2)
// @ requires acc(tree.InvRec(), 1/2)
// @ ensures  tree != nil && err == nil ==> tree.GetValue() != nil && len(tree.GetValueArray()) == len(hash) && (forall i int :: { hash[i] } 0 <= i && i < len(hash) ==> (tree.GetValueArray())[i] == hash[i])
func (tree *PrefixTree) ComputeHash() (hash [sha256.Size]byte, err error) {
	if tree == nil {
		return [sha256.Size]byte{}, errors.New("cannot hash empty node")
	} else if /*@ unfolding acc(tree.Inv(), _) in unfolding acc(tree.InvRec(), _) in @*/ tree.Value != nil {
		return /*@ unfolding acc(tree.Inv(), _) in unfolding acc(tree.InvRec(), _) in @*/ *tree.Value, nil
	} else if /*@ unfolding acc(tree.Inv(), _) in unfolding acc(tree.InvRec(), _) in @*/ tree.Left == nil && tree.Right == nil {
		if /*@ unfolding acc(tree.Inv(), _) in unfolding acc(tree.InvRec(), _) in @*/ tree.Leaf == nil {
			return [sha256.Size]byte{}, errors.New("neither leaf nor value given for empty node")
		} else {
			// TODO: We would have to include length, too, to be compliant with TLS
			// encoding, but not so important right now because inputs are
			// fixed-length and this may get changed in the future
			//@ unfold acc(tree.Inv(), 1/2)
			//@ unfold acc(tree.InvRec(), 1/2)
			value /*@ @ @*/ := sha256.Sum256(
				append( /*@ perm(1/2), @*/ tree.Leaf.Vrf_output[:], tree.Leaf.Commitment[:]...) /*@, perm(1/2) @*/)
			tree.Value = &value
			return value, nil
		}
	} else {
		if leftContent, err := tree.Left.HashContent(); err != nil {
			return [sha256.Size]byte{}, err
		} else if rightContent, err := tree.Right.HashContent(); err != nil {
			return [sha256.Size]byte{}, err
		} else {
			value /*@ @ @*/ := sha256.Sum256(append( /*@ perm(1/2), @*/ leftContent, rightContent...) /*@, perm(1/2) @*/)
			tree.Value = &value
			return value, nil
		}
	}
}
