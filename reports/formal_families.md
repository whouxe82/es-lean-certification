# Families lane: kernel-checked scope

`ES/Families.lean` compiled with Lean 4.19.0 / Mathlib v4.19.0 using `lake build ES.Families`, exit 0. The clean build and axiom receipt is `round_z5/logs/families-build-final.log`. Earlier logs record a corrected cast-normalization error and are not certification receipts.

The file reindexes r=n+1, n:ℕ, to avoid truncated subtraction: p(n)=528n+505=528r−23, H(n)=23n+22=23r−1, k(n)=132n+126. Every statement is uniform in n, not a finite census.

| Certified theorem (`ES.Families.` prefix) | Precise scope |
|---|---|
| `normalizedII` | Shared `ES.NormalizedII (p n) 11 (n+1) 12 1`, including positivity, coprimality, ordering, Type II equation |
| `source_positiveES`, `source_isSolution` | Positive natural source `(132r,11pr,12pr)` and shared ES polynomial identity |
| `endpoint_positiveES`, `endpoint_isSolution` | Positive natural endpoint `(11H,12H,132pH)` and shared ES polynomial identity |
| `PositiveES.unitFractions` | Conversion to the rational unit-fraction identity via `ES.isSolution_unitFraction` |
| `old_gate_fails`, `new_gate_holds` | 11∤k for every n; 528∣23²−1 |
| `endpoint_interval` | p/4<11H<p/2<12H<3p/4, as exact multiplied Nat inequalities |
| `B4_scalar`, `B4_endpoint_formula` | C=(23p+1)/4=132H and exact divisions C/12=11H, C/11=12H |
| `jacobi_44`, `endpoint_nonresidue` | Jacobi(44,p)=−1 and `¬IsSquare (12H : ZMod p)` uniformly, without even requiring p prime |
| `endpoint_HN_witness` | Complete pointwise H_N-style witness with first coordinate 12H; does not assert global H_N |
| `residue_class_infinite`, `family_prime_inputs_infinite` | Infinitely many distinct prime inputs in 505 mod528, exactly parameterized by n |
| `certified_family_infinite`, `nonresidue_family_infinite` | Infinite prime inputs carrying source/endpoint certificates, failed old gate, and (latter theorem) full nonresidue interval witness |
| `refinement_infinite`, `six_classes_infinite` | Infinite family primes in each residue 1,121,169,289,361,529 mod840, using explicit primitive classes mod18480 |
| `example_1033` | Separate finite prime/certificate check: (264,22726,24792) and (495,540,6136020) |

Prime infinitude imports the existing proved theorem `Nat.setOf_prime_and_eq_mod_infinite` from `Mathlib.NumberTheory.LSeries.PrimesInAP`. Coprimality is checked in Lean; infinitude is not inferred from samples. The explicit CRT witnesses are 4201,6841,15289,17929,12121,4729 modulo18480.

The character proof imports `jacobiSym.mod_right` and `ZMod.nonsquare_of_jacobiSym_eq_neg_one` from `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`. Because p mod176=153, Jacobi(44,p)=Jacobi(44,153)=−1 (the latter exact value proved by `norm_num`). The relation 44·12H=23p+1 shows that a square root u of 12H modulo p would make 44=(44u)², a contradiction. Thus this is a fully formal character proof, not an unformalized reciprocity promise. Reciprocity is an audited imported dependency of the Jacobi theory.

Final printed axioms are subsets of `[propext, Classical.choice, Quot.sound]`. No target axiom, `sorry`, `admit`, `native_decide`, or `sorryAx` occurs in the accepted receipt. Finite `decide` proofs are kernel reduction, not native evaluation.

Cross-review: the Bridges lane reviewed the formulas, reindexing, gate and interval quantifiers, primitive progression and character argument. I reviewed its B1 orientation `(δrs,pδrt,prst)`, B4 orientation `(pδrt,prst,δrs)`, positive rational identities and exact divisibility gates against the source notes. Family endpoint formulas match its generic `b4_four_iterates`. The family file itself does not contain the literal fourth-iterate specialization; it proves the endpoint algebra, and Bridges proves the generic iteration. A separate type-cast adapter was deferred when the coordinator redirected work to matching.

Scope limits: this is the existing a=11 example family, a regression/prior-art example, not universal progress. All prime inputs lie in the previously covered q=11 class. The general fixed-shape F1/F2/F3 classifications, all odd-a adjacent families, source-character refinements, and publication priority are not formalized here. Neither H_D nor H_N nor the Erdős–Straus conjecture is asserted globally. At the coordinator's request, new family generation stopped after this clean build and effort moved to the matching theorem.

Matching pivot outcome: the subsequent full graph task was completed. See `formal_matching.md` and the bridge lane's `formal_matching_graph.md`; the new arbitrary-source normalization and `solutionGraph_neighbors_unique` close the earlier formalization gap. This does not change the regression/prior-art scope of the family above.
