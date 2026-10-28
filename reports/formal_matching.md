# Matching lane: arithmetic core and global edge classification

This lane pivoted from the already certified regression family to the requested matching theorem. Its core is now kernel checked on arbitrary positive natural ES triples, rather than assuming a canonical-certificate parametrization.

Certified files:

- `lean/ES/Matching.lean`: arbitrary-triple divisibility classification; Type I exclusion for every orientation; exact rational-to-cleared-map translation; unique small coordinate; ordered inverse injectivity.
- `lean/ES/Pivot.lean`: integer-return exclusion for the larger normalized Type II pivot; first-coordinate interval for the smaller pivot; permutation helpers.
- `lean/ES/EdgeClassification.lean`: invokes the separately proved gcd normalization from `ES/Normalization.lean` to derive properties of every arbitrary positive integer edge. It also proves exact equivalence between cleared equations and the literal rational map.

Clean receipts are `logs/matching-build-final.log` and `logs/edgeclassification-build-final.log`. Core tests used actual `lake build` under Lean4.19.0 and Mathlib v4.19.0. Final axiom sets are subsets of `[propext, Classical.choice, Quot.sound]`; no target axiom or proof placeholder is used.

## Exact certified scope

All theorem names below are in `ES.Matching`.

| Theorem | Quantifiers and conclusion |
|---|---|
| `not_all_divisible` | For every positive input p and every positive ES solution, not all three denominators are divisible by p |
| `at_least_one_divisible`, `typeI_or_typeII` | Every positive ES solution at prime p>4 has exactly one or two p-divisible coordinates |
| `pivot_divisible` | Every integral bridge edge's chosen pivot y is divisible by p |
| `typeI_no_forward`, `typeI_no_outgoing`, `typeI_no_literal_outgoing` | No forward integral bridge edge starts at an arbitrary Type I point; IsTypeI is proved permutation-invariant, so no coordinate orientation is omitted |
| `not_two_small` | A positive ES triple cannot have two coordinates strictly below p/2 |
| `inverse_bridge`, `ordered_preimage_unique` | The exact rational inverse, and uniqueness for a fixed ordering; these alone are not a quotient-graph matching theorem |
| `normalized_other_no_outgoing` | The larger p-divisible pivot of every normalized Type II source is ineligible |
| `normalized_first_small` | The smaller pivot's first integral target is strictly below p/2 |
| `typeII_pivot_min_small` | For an arbitrary Type II source with p-free outer coordinate, the returning pivot is the smaller p-divisible coordinate and the first target is below p/2 |
| `target_typeI_right` | The resulting target has exactly one p-divisible coordinate, with no canonical-target parameter premise |
| `edge_properties` | For every prime p=4k+1, arbitrary positive source/target ES triples, and literal cleared bridge equations: the pivot is minimal among p-divisible source coordinates, the first target is below p/2, and the target is Type I |
| `cleared_iff_bridge` | For positive p and pivot y, the cleared natural equations hold iff the literal rational bridge equals the target natural triple |

The global `edge_properties` theorem has **no normalization or canonical-form assumption**: `ESNormalization.normalize_typeII_denominators` is invoked inside its proof. That normalization was independently implemented and kernel checked by the descent lane using gcd(a,b), divisibility, and prime coprimality.

The full matching graph wrapper is now also kernel checked in `ES/MatchingGraph.lean`, owned by the bridge lane. Its final actual compile exited 0 (`logs/matching-graph-build-04.log`), with all ten printed axiom closures standard-only. I independently reviewed the definitions and statement. `Vertex p` is the subtype of multisets that are actual positive ES denominator triples, retaining multiplicities. All source/target coordinate orderings are quantified in the edge witnesses. `directed_iff_literal` and `adjacent_iff_literal` certify that the cleared encoding has exactly the literal rational-map edges. `solutionGraph_neighbors_unique` proves, for every prime p=4k+1 and every actual ES vertex A, that any two adjacent vertices B,C are equal. It has no canonical-form, normalization, or existence hypothesis. `no_self_edge` excludes loops. The requested full integral-edge matching theorem is therefore certified; it is no longer merely a canonical-certificate or arithmetic-core result. Root infrastructure performs an additional clean source-complete build and axiom audit.

No theorem here asserts H_D, H_N, universal ES, connectivity of solution graphs, or eligibility for every prime. The map is the one specific B1 rational bridge. Paths through nonintegral intermediate points are outside the integral-edge matching theorem.
