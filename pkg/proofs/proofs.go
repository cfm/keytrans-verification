package proofs

import (
	"bytes"
	"crypto/sha256"
	"errors"
	"slices"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
)

type NodeValue = [sha256.Size]byte

type UpdateValue struct {
	Value []byte
}

/*@
pred (u UpdateValue) Inv() {
	acc(u.Value)
}
@*/

type CommitmentValue struct {
	Opening []byte
	Label   []byte      // pseudonym; max length 2^8-1 bytes
	Update  UpdateValue // value associated with label, e.g., public key
}

type BinaryLadderStep struct {
	Proof      [sha256.Size]byte
	Commitment [sha256.Size]byte
}

type InclusionProof struct {
}

/*@
pred (i InclusionProof) Inv() {
	true
}
@*/

// Values for PrefixSearchResult.Result_type
const (
	Reserved           = 0
	Inclusion          = 1
	NonInclusionLeaf   = 2
	NonInclusionParent = 3
)

// A leaf in a prefix tree
type PrefixLeaf struct {
	// Vrf_output for the search key and version pair stored at this leaf.
	Vrf_output [sha256.Size]byte
	// Commitment to the public key of the search key and version pair.
	Commitment [sha256.Size]byte
}

/*@
pred (p *PrefixLeaf) Inv() {
	acc(p) &&
	acc(&p.Vrf_output) &&
	acc(&p.Commitment)
}
@*/

type PrefixSearchResult struct {
	Result_type int
	Leaf        *PrefixLeaf // only present when result_type == NonInclusionLeaf
	Depth       uint8
}

/*@
pred (p PrefixSearchResult) Inv() {
	(p.Result_type == Inclusion || p.Result_type == NonInclusionParent || p.Result_type == NonInclusionLeaf) &&
	p.Result_type == NonInclusionLeaf ==> p.Leaf.Inv()
}
@*/

type PrefixProof struct {
	Results  []PrefixSearchResult
	Elements []NodeValue
}

/*@
pred (p PrefixProof) Inv() {
	acc(p.Results) && (forall i int :: { p.Results[i] } 0 <= i && i < len(p.Elements) ==> acc(&p.Elements[i])) &&
	acc(p.Elements) && (forall i int :: { p.Elements[i] } 0 <= i && i < len(p.Elements) ==> acc(&p.Elements[i]))
}
@*/

type CombinedTreeProof struct {
	Timestamps    []uint64
	Prefix_proofs []PrefixProof
	Prefix_roots  []NodeValue
}

/*@
pred (c CombinedTreeProof) Inv() {
	acc(c.Timestamps) &&
	acc(c.Prefix_proofs) &&
	acc(c.Prefix_roots)
}
@*/

type CompleteBinaryLadderStep struct {
	Step   PrefixLeaf
	Result PrefixSearchResult
}

/*@
pred (s *CompleteBinaryLadderStep) Inv() {
    acc(s) &&
	acc(&s.Step) &&
	(&s.Step).Inv() &&
	acc(&s.Result) &&
	s.Result.Inv()
}
@*/

// @ trusted
// @ ensures forall i int :: { completeSteps[i] } 0 <= i && i < len(completeSteps) ==> acc(&completeSteps[i]) && acc(completeSteps[i].Inv())
func CombineResults(results []PrefixSearchResult, steps []BinaryLadderStep) (completeSteps []CompleteBinaryLadderStep, err error) {
	completeSteps = make([]CompleteBinaryLadderStep, 0, len(results))
	if len(steps) < len(results) {
		return completeSteps, errors.New("not enough steps")
	}

	sortedSteps := make([]BinaryLadderStep, 0, len(results))
	copy(sortedSteps, steps[:len(results)])
	sortBinaryLadderSteps(sortedSteps)

	for i, step := range sortedSteps {
		completeSteps = append(completeSteps, CompleteBinaryLadderStep{
			Step: PrefixLeaf{
				Vrf_output: crypto.VRF_proof_to_hash(step.Proof),
				Commitment: step.Commitment,
			},
			Result: results[i],
		})
	}

	return completeSteps, nil
}

// @ trusted
// @ preserves acc(sortedSteps)
func sortBinaryLadderSteps(sortedSteps []BinaryLadderStep) {
	slices.SortFunc(sortedSteps, func(a, b BinaryLadderStep) int {
		hashA := crypto.VRF_proof_to_hash(a.Proof)
		hashB := crypto.VRF_proof_to_hash(b.Proof)
		return bytes.Compare(hashA[:], hashB[:])
	})
}
