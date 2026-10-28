# Formal forcing lane

**Status: kernel-checked, with explicit partial scope.** `ES/Forcing.lean` has 27 theorems and compiles with Lean 4.19.0 / Mathlib v4.19.0. It proves the maximal complement-preserving group quotient, a finite orbit-energy forcing theorem, and the complete p=577, x=154 local histogram/energy/target certificate. It does not prove H_N, H_D, a uniform selector, or the general arithmetic realization of all abstract assumptions.

## Actual build and axiom receipt

The final command was run from `round_z5/lean`:

```sh
source env.sh
lake env lean -o .lake/build/lib/lean/ES/Forcing.olean ES/Forcing.lean > ../logs/forcing-build.log 2>&1
```

Observed exit code: **0**. The output `.lake/build/lib/lean/ES/Forcing.olean` exists. The build log contains the `#print axioms` outputs for the principal statements. All printed dependencies are subsets of `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, custom axiom, or unproved target hypothesis occurs. `cell577_avoidance_attained` depends only on `propext`. Finite certificates use `decide`, `norm_num`, and arithmetic tactics, never `native_decide`.

Final reviewed source SHA-256: `822dd2db9acddecf1d4a6f3c13272c283c8aeb5411680c691dbd0fe25b3ddde9`.

## Exact checked coverage

All names below are in namespace `ES.Forcing`.

| Checked theorem(s) | Exact mathematical content |
|---|---|
| `complement_involutive`, `complement_ratio` | For any commutative group and any x, i(g)=x²/g is an involution and i(g)/g=(x/g)². |
| `preservesCosets_iff_squares_le`, `square_cosets_preserved`, `quotient_preserved_iff` | A subgroup quotient G/L preserves every complement cell iff the square subgroup is contained in L. The last theorem uses actual quotient-group equality. This establishes maximality among group-quotient partitions, not among arbitrary partitions. No finiteness assumption is needed. |
| `squares_le_kernel` | Any group character satisfying χ(g)²=1 kills the square subgroup. No specific Jacobi character has been instantiated. |
| `fiberCount_complement` | Equal fiber counts follow from an involution on a finite source set whose labels intertwine with complementation. The arithmetic divisor involution is not instantiated in general. |
| `energy_lt_avoidanceMinimum_forces` | Natural occupancies bounded by T are explicitly enumerated as functions `Fin n → Fin (T+1)`. `avoidanceProfiles` imposes total mass T, equality on involution pairs, odd central/even other fixed bins, and zero target bins. `avoidanceMinimum` is the minimum energy over this finite set, with top for an empty set. A compatible actual profile of energy strictly below this minimum has a positive target bin. The conclusion is not assumed as a premise. Both finite-search definitions are computable Lean definitions. |
| `minimum_mono` | Shrinking any finite feasible set cannot lower its minimum, including the empty-set/top cases. |
| `sum_strict_forces_component` | If the sum of actual energies is below the sum of thresholds, some component has a strict inequality. This alone is not the full square-class/Jacobi dominance theorem. |
| `squares39_exact`, `cell577_square_class` | The squares of all coprime residues modulo 39 are exactly {1,4,10,16,22,25}, and the specified six-residue cell is twice that square set. |
| `involution577_involutive`, `cell577_complements` | The six-bin permutation is an involution and each paired product is 4 mod 39. |
| `counts577_symmetric`, `counts577_fixed_even`, `counts577_mass`, `counts577_energy` | The six counts (2,1,1,2,1,1) obey the pair/fixed-bin restrictions and have T=8, E=12. |
| `cell577_avoidance_lower_bound`, `cell577_avoidance_attained` | For nonnegative j,b,c with j+b+c=4, 4j²+2b²+2c²≥14; equality is attained at (1,1,2). This proves an exact arithmetic avoidance minimum. |
| `cell577_energy_forces` | Any four orbit occupancies with the required mass, even remaining fixed count, and energy<14 must have a positive target count. |
| `avoidanceProfile577_lower_bound`, `avoidanceMinimum577_eq` | The exact general finite optimizer above, instantiated with the six-bin involution, no central bin, and target {0}, has minimum exactly 14. This links the arithmetic calculation to the abstract optimizer. |
| `divisors577_factorization`, `counts577_is_divisorHistogram` | The complete divisor set of 154² is the pointwise product {1,2,4}{1,7,49}{1,11,121}. Filtering that complete set by the six residues gives exactly the stated histogram. These are actual divisor counts, not a hand-supplied compatible vector. |
| `counts577_target_forced`, `divisor577_target_exists` | The generic forcing theorem, using E=12 and the exact minimum14, proves positivity in the target bin. The full histogram identity then proves an actual a dividing 154² with a≡2 mod39. |

The actual proof chain for the local certificate is:

`avoidanceProfile577_lower_bound` + explicit attaining profile → `avoidanceMinimum577_eq` → generic `energy_lt_avoidanceMinimum_forces` on actual six counts → `counts577_target_forced` → complete divisor-histogram identity → `divisor577_target_exists`.

## Important boundaries

1. There is **no uniform x-selection theorem**. Local soundness and a successful finite example do not imply the all-prime energy premise.
2. The general divisor histogram's complement symmetry/parity has not been fully instantiated. The abstract fiber-symmetry theorem is proved; general fixed-residue evenness and the positive odd central residue remain a gap. The actual p577 parity is checked directly.
3. The complete marginal-cost formula for arbitrary numbers of fixed/pair/central orbits is not proved. The finite optimizer is rigorously defined and its soundness is proved; its p577 value14 is proved exactly.
4. The quotient result is fully abstract. In the p577 example, the ambient modular square set is checked, but the claim that residues of prime factors 2,7,11 generate the entire unit group is not proved here.
5. Full Jacobi-cell versus square-class dominance, including the gluing of feasible profiles and zero-target subcells, is not proved. The general minimum monotonicity and numerical strict-component lemma are proved. The two old Jacobi-cell failure values are not certified in this module, so **strict improvement over the old criterion is not itself certified by this lane**.
6. The local divisor target is proved. This module does not prove prime577, the quadratic-nonresidue claim for154, the general target-to-ES construction, or an H_N theorem. Separate concrete ES identity/positivity checks may be supplied by the shared Basic lane and must retain their separate status.
7. No character-product mass/energy identities, support-graph bounds, or p3361 complete rejection theorem are formalized here.

## Cross-review

Reviewed `ES/Descent.lean`'s norm-shape descent and statements. The proof has an actual decreasing smaller-coordinate induction and does not assume t=1. Its explicit `t ∣ a+b` premise is used in terminal coprimality and must be discharged by the bridge connection. The difference-mod4 descent and dyadic restriction were mathematically consistent on review. The descent owner reports a successful standalone build with only standard axioms and is completing its integrated bridge wrappers. This review does not substitute for that lane's final build receipt.

## Precise next analytic target: Q(p)

This is a proposed **open obligation**, not a theorem proved by this module.

Fix a prime p with p≡1 (mod24). Let I_p be the integers x satisfying p/4<x<3p/4, equivalently `(p+3)/4 ≤ x ≤ 3(p−1)/4`. For an x in I_p with Legendre symbol χ_p(x)=−1, put d=4x−p and let H be the subgroup of `(ℤ/dℤ)×` generated by the prime factors of x. Let C range over cosets of H² in H. Define

- `w_x(g) = #{a>0 : a ∣ x² and a≡g mod d}`;
- `i_x(g)=x²/g`;
- `A_C = C ∩ {−px, −x}`, retaining only residues in H;
- `T_C = Σ_{g∈C} w_x(g)` and `E_C = Σ_{g∈C} w_x(g)²`;
- `M_C(T_C)` as the minimum of `Σ_{g∈C} v(g)²` over all nonnegative integer vectors v on C with mass T_C, equal values on each i_x-pair, even values at noncentral fixed residues, an odd positive value at x if x∈C, and v(g)=0 for every g∈A_C. An empty feasible set has minimum +∞.

The candidate assertion is

> **Q(p):** There exist an x∈I_p with χ_p(x)=−1 and a square-class cell C such that A_C is nonempty and E_C<M_C(T_C).

The proposed uniform theorem is `∀ p, Prime(p) ∧ p≡1 (mod24) → Q(p)`. The source note's exact character-product expressions are possible tools for estimating T_C and E_C; this module does not prove those formulas or any estimate that establishes Q(p).

The eligibility clause A_C≠∅ means that C contains a **designated target residue**. It does **not** assume a divisor occupies that residue, and it must never be replaced by `∃g∈A_C, w_x(g)>0`, since that replacement would already assume the sought local hit. With the general divisor orbit compatibility proved, an actual target-avoiding histogram belongs to the defining feasible set and forces E_C≥M_C. Thus the strict inequality is a genuine sufficient condition. Proving the uniform existence of such an inequality remains the substantive analytic problem.

For p3361, the prior human/executable audit reports eight NR coordinates with actual target hits, only one of which satisfies the refined square-class energy test. That observation demonstrates that actual solvability is stronger information than this particular sufficient certificate at a fixed x; it is not a proof of Q(p) uniformly. The separate divisor(x)-support graph energy premise has a different threshold and was reported to fail at every candidate at p3361. That rejects that exact alternative uniform premise, not Q(p). Neither complete p3361 statement is kernel-certified by this lane.

## Final audit clarification

The whole-project inventory found eighteen unsafe computational specialization entries generated while compiling executable forcing definitions. These are not logical dependencies of the proofs. Independent audits checked all 310 project theorem constants and 75 other safe declarations against the unchanged standard-axiom whitelist, and separately verified all 18 entries have compiler IR. See `reports/forcing_compiler_stub_review.md` and the two `forcing-stub-*.log` receipts. No forcing proof source was changed.

The Descent owner subsequently completed the integrated wrappers and reported a frozen successful build in `logs/descent-final-build.log`. Its `b4_source_restriction`, `b4_dyadic_no_rescue`, and `normalizedII_b4_dyadic_no_rescue` discharge the auxiliary norm premises from TypeII, p=4k+1, and the exact B4 gate; `b4_dyadic_endpoints_equal` proves full endpoint equality. This addresses the explicit bridge-discharge obligation noted in the earlier statement review.
