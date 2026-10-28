# Formal bridges: certified scope and receipts

**Status:** `ES/Bridges.lean` compiles successfully with Lean 4.19.0 and Mathlib v4.19.0. This is a conditional source-to-endpoint theorem package, not an existence theorem for normalized sources at arbitrary primes.

## Actual build

Final checked invocation, from `round_z5/lean`:

```sh
source env.sh
lake env lean -o .lake/build/lib/lean/ES/Bridges.olean ES/Bridges.lean
```

Exit code **0**. Full final diagnostic/axiom receipt: `round_z5/logs/bridges-build-10.log`. Earlier failed intermediate builds are retained under numbered logs, but are not certification receipts. The final log has only linter warnings and successful `#print axioms` output; no `sorryAx` appears.

SHA-256 of final source:
`3d89c241f7a6a4d525e9625f06037b90fb9f145d3ef8d625184a193d5cec03fa`.

SHA-256 of generated object:
`1b623778ef01ff96a5f8200cb683e912455dccfae07c2726068b0f44469e5df4`.

The module contains no `sorry`, `admit`, target axioms, or `native_decide`. Its main theorems depend only on Mathlib/kernel proofs and the standard axioms `propext`, `Classical.choice`, `Quot.sound`; `TypeII.source` uses only `propext`, `Quot.sound`.

## Definitions and exact assumptions

`ESBridge.TypeII p δ r s t` has positive **integer** (`ℤ`) parameters, `IsCoprime δ s`, `δ ≤ s`, and the exact subtraction-free equation `4δrst = pt+δ+s`. It does not assert that a witness exists. Positivity is part of the source, not left as an informal denominator convention.

`IntegerES p x y z` includes positivity of p and all three integer denominators, plus `4xyz=p(xy+xz+yz)`. `RationalES` includes positivity and the literal unit-fraction equation. `Integral q` means that q equals an integer.

The shared natural-number API is connected by `of_normalizedII`, `normalizedII_source`, and `normalizedII_b1_gate`; these take the root module's `ES.NormalizedII`, not a replacement definition.

## Kernel-checked results

| Theorem(s), namespace ESBridge | Certified conclusion |
|---|---|
| `integerES_iff_rationalES` | Full equivalence of positive integer polynomial certificates and their positive rational unit-fraction equations. |
| `TypeII.source`, `normalizedII_source` | Positive source certificate `(δrs,pδrt,prst)`; the latter concludes shared `ES.IsSolution` over ℕ. |
| `TypeII.coprime_delta_t`, `coprime_s_t`, `coprime_delta_p`, `coprime_s_p` | Required pairwise and p-coprimality consequences derived from the source equation and `IsCoprime δ s`; no unit premise added. |
| `b1_gate`, `b1_rational_integral_iff`, `normalizedII_b1_gate` | Exact B1 gate: the two nonautomatic coordinates are integers iff `δ*t ∣ k`. |
| `b1_rational`, `b1_integer_return_iff` | Full positive rational endpoint `(X,Xs/t,pXs/δ)`, `X=k+δrt`; positive integer ES return iff the gate holds, assuming `k≥0` and `p=4k+1`. |
| `b1_single_iterate` | The displayed B1 endpoint is one literal application of the specified ordered rational map. |
| `bridge_preserves` | Each application preserves the **positive rational ES surface**, for `k≥0`, `p=4k+1`; intermediate rational points are permitted explicitly. |
| `bridge_four`, `b4_four_iterates` | Literal fourth iterate, with no intervening permutation, of source orientation `(pδrt,prst,δrs)` equals `(tC/s,tC/δ,pC)`. This is the actual map iteration identity, not just an endpoint polynomial check. |
| `b4_parameters`, `b4_d_mod_four` | From every supplied normalized source with `p=4k+1`, `d=4δrs-p≥3`, `dt=δ+s`, `d≡3 mod4`, and integral `C=pδrs-k(p+1)` satisfies `4C=pd+1`. |
| `b4_gate_algebra`, `b4_rational_integral_iff` | Exact equivalence: endpoint integrality iff `4δs ∣ d²−1`. The intermediate equivalence `δs∣C` is proved, using source-derived coprimality. |
| `b4_rational`, `b4_integer_return_iff` | Positive rational B4 endpoint and full positive integer ES return iff gate. Positivity of C is proved from p,d>0 and `4C=pd+1`. |
| `b4_gate_norm` | Gate plus positive δ,s, `d≥3`, `dt=δ+s` yields an actual integer `m>0` satisfying `(δ+s)²=t²(4mδs+1)`. The norm is constructed, not assumed. |
| `base_endpoints_equal` | At `δ=t=1`, the B4 and B1 endpoints coincide exactly; this supplies the last algebraic link for the descent lane's dyadic no-rescue result. |
| `b1_other_gate`, `b1_other_pivot_impossible` | Exact opposite-pivot gate `st∣k`, and its impossibility for a normalized source with `p=4k+1`. |
| `source_coordinate_bound`, `source_first_not_dvd` | Complete bound `3δrs≤p+1`, hence `δrs<p` and `p∤δrs`. Thus the constructed source really has exactly two p-divisible coordinates. |
| `b1_first_interval` | `p<4X` and `2X<p`, so the distinguished B1 coordinate lies in `(p/4,p/2)`. |

Many bridge conclusions do not require primality; this is a strengthening of those conditional formulas, not an expansion of the claimed existence coverage.

## Explicit exclusions

This module does **not** prove universal ES, H_D, H_N, existence of a B1-eligible source, or existence of a B4-eligible source for arbitrary p. It does not prove the general B1 character/nonresidue theorem, the general B4 character criterion, complete canonical Type I parameterization/inversion, or the all-vertex/all-orientation matching theorem. The opposite-pivot and interval lemmas are inputs to a matching proof, not that entire proof. The family lane separately certifies a uniform nonresidue family.

The norm descent, recurrence classification, and source-level dyadic no-rescue integration belong to `ES/Descent.lean`, not this module. No historical novelty is claimed: the B4 divisibility relation is compatible with the classical Elsholtz–Tao parameter relation `e²≡1 mod4ab`.

## Cross-review and integration

The descent lane reviewed the B1 cancellation hypotheses, B4 algebra signs, and gate-to-positive-m construction. I reviewed its terminal argument, strict companion descent, and mod-4 restriction: its divisibility hypothesis is supplied directly by `dt=δ+s`; it does not claim to preserve the original prime along the auxiliary norm descent.

I reviewed the family lane's reindexing `r=n+1`, positive source/endpoint formulas, primitive progression, exact B1 failure, exact B4 gate, interval statements, and its Jacobi-44 nonresidue argument. I flagged a stale introductory exclusion of its newly proved character theorem; that documentation was corrected. The family-to-four-iterate specialization is not included here as a separately named theorem.
