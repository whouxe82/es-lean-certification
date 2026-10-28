# Full all-orientation integral bridge matching: formal result

**Kernel-checked:** every vertex of the positive integer ES solution graph, modulo all denominator permutations, has at most one neighbor when edges are integral applications of the specified rational bridge or inverse traversals. There are no self-loops. This is the full graph theorem for this map, not a theorem restricted to supplied normalized certificates.

## Actual build receipt

Module: `round_z5/lean/ES/MatchingGraph.lean`.

```sh
source env.sh
lake env lean -o .lake/build/lib/lean/ES/MatchingGraph.olean ES/MatchingGraph.lean
```

Final process exit code: **0**. Final receipt: `round_z5/logs/matching-graph-build-04.log`. It prints ten axiom closures, all exactly `[propext, Classical.choice, Quot.sound]`, with no diagnostics or `sorryAx`. No `sorry`, `admit`, added axiom, or `native_decide` occurs in the module.

Source SHA-256:
`d48b898178312549c7866994aa314619712a3f92caf41ba5d705a180a88d28f4`.

Object SHA-256:
`c9f3061fb4b12921b89e35c94faeb2ecff8ff5c5ebbcce8cc8e861ba1e33b235`.

The module was frozen after this successful build. The infrastructure lane performs a separate clean aggregate rebuild and audit of imported dependencies.

## Exact graph and public conclusion

Namespace: `ES.MatchingGraph`.

- `triple x y z` is the multiset `{x}+{y}+{z}`. Multiplicities are retained.
- `Step p k` contains arbitrary positive natural source and target ES triples and the three exact denominator-cleared bridge equations. It imposes no ordering, canonical form, Type I/II premise, or selected pivot.
- `Directed p k A B` existentially quantifies such a step whose source and target multisets equal A and B. Consequently every orientation is included; no canonical representative is fixed.
- `Adjacent p k A B` means `Directed A B ∨ Directed B A`.
- `directed_iff_literal` and `adjacent_iff_literal` prove this encoding is exactly the literal rational map `T(x,y,z)=((y+pk)/p,x(y+pk)/y,z(y+pk)/y)` on the positive integer ES endpoints. Denominator clearing has not added spurious edges.
- `Vertex p` is the subtype consisting precisely of positive ES solution multisets. `solutionGraph hp hpk` is the resulting Mathlib `SimpleGraph` on these genuine vertices. An auxiliary ambient graph also exists on all multisets, with non-solutions isolated.

The public theorem `solutionGraph_neighbors_unique` states, for natural p,k with **only** `hp : p.Prime` and `hpk : p=4*k+1`, that for any genuine vertices A,B,C:

```text
solutionGraph.Adj A B → solutionGraph.Adj A C → B=C.
```

`degree_at_most_one` proves the same neighbor uniqueness directly on the ambient multiset relation. `no_self_edge` and `no_directed_self` rule out loops. Thus the ordinary graph-theoretic interpretation is that components are isolated vertices or single edges; the named formal conclusions are neighbor uniqueness and looplessness, rather than a separate theorem about connected-component cardinalities.

## Why no arithmetic hypothesis is hidden

The helper `degree_at_most_one_of_properties` deliberately exposes an `EdgeProperties` premise. **The final theorem does not retain that premise.** It discharges it using the proved `ES.Matching.edge_properties` for every arbitrary integral edge.

The concrete arithmetic chain imports `ES/EdgeClassification.lean`, which invokes the genuine arbitrary-Type-II normalization theorem from `ES/Normalization.lean` and the normalized pivot theorems from `ES/Pivot.lean`. The bridge identities and exact cancellation facts come from `ES/Bridges.lean`; arbitrary Type I obstructions and ordered-map facts are in `ES/Matching.lean`.

The graph proof uses:

1. Every integral edge chooses a least p-divisible source coordinate. Two orientations of the same source multiset therefore have equal pivot values. Removing that occurrence leaves a pair multiset, whose two possibilities are equality and exchange; the cleared equations then give the same target multiset.
2. Every edge has first target denominator below p/2. A positive ES triple cannot have two denominators below p/2, so two incoming edges have the same distinguished first coordinate. Removing it leaves the same two pair possibilities; cancellation in the cleared equations recovers the same source multiset.
3. Every target is Type I, and no Type I vertex has an outgoing integral bridge in any orientation. Hence incoming/outgoing mixed incidences and self-loops are impossible.

All coordinate and pair-multiset cancellation steps are proved in Lean; no finite permutation enumeration or unverified canonical-form assertion substitutes for them.

## Scope and cross-review

The result neither constructs an eligible source for an arbitrary prime nor proves H_D, H_N, or ES universally. It does not prohibit transformations outside this specified map. In particular, paths with rational noninteger intermediate points are outside the integral-vertex graph and are treated separately by the B4 theorems.

The family/arithmetic lane cross-reviewed the multiset representation, explicit discharge of `EdgeProperties`, cancellation cases, mixed-edge obstruction, literal-map equivalence, and final genuine-vertex subtype. The root coordinator reviewed the public statements and required the looplessness and literal-equivalence conclusions. No historical novelty is claimed.
