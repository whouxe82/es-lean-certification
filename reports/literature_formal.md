# Prior formalizations: source audit and local replay

Audit date: 28 October 2026. This is a bounded literature/source audit, not a priority determination. The main conclusion is that substantial parts of the mathematical infrastructure already have formal proofs. The exact conditional B1/B4 transports and the full ES-specific descent/forcing package were not located as formal declarations in the inspected sources. That does not establish novelty or absence elsewhere.

## Evidence levels

- **Locally checked:** the explicitly listed declarations in `ES/PriorOffsetCore.lean` and `ES/Literature.lean`, compiled here against Lean 4.19.0 / mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Local logs and `#print axioms` distinguish these from upstream claims.
- **Upstream CI observed:** exact repository commit and GitHub Actions status/steps inspected. This is independently retrieved evidence of upstream execution, not our own replay of its original toolchain.
- **Source inspected / author receipt:** theorem statements, proofs, pins, and archived receipts read, but the full original environment was not rerun.
- **Statement or open axiom:** a Lean declaration can state an open problem or depend on an unproved axiom. Such a declaration does not certify the target theorem.

## Exact comparison

| This project | Located formal precedent | Exact relationship and limit |
|---|---|---|
| Normalized Type II source equation and rational triple | `ErdosStraus.typeII_identity`, creelie/ErdosProblem1 | Its variables `(n,u,v,a,α)=(p,δ,s,t,r)` give exactly `4δrst=pt+δ+s` and `(δrs,pδrt,prst)`. The source theorem is over nonzero rationals; positivity, integrality, gcd normalization, and universal existence are not in that theorem. |
| Fixed-first-denominator divisor criterion | carlok `engine_lemma`, `constructive_offset`; Foundation `divisorShellFactorization`, `divisorShellReconstruction` | The classical identity `(dy−px)(dz−px)=(px)²`, with `d=4x−p`, is precisely the common algebra. The carlok constructor proves positive natural denominators under explicit divisor/congruence hypotheses. This is related to our divisor channels, not a universal witness selector. |
| B1 transport at fixed prime, gate `δt ∣ k` | No matching declaration located in inspected ES Lean files | carlok's named “transport” changes the input `n` by `4qdk`; B1 changes a denominator triple while holding prime `p` fixed. The names alone do not identify the maps. The previous round's Elsholtz–Tao coordinate dictionary remains the relevant mathematical comparison. |
| B4 iterate, gate `4δs ∣ d²−1`, and B1/B4 endpoint relation | No matching Lean declaration located; exact endpoint occurs in Elsholtz–Tao's classical Type I family | With `a=δ,b=s,c=t,e=d`, their Type II/Type I classes are `p≡−e` / `p≡−e⁻¹ (mod4ab)`. Their coincidence is exactly `e²≡1 (mod4ab)`, and their printed Type I coordinate is `R′=(pe+1)/(4ab)`. The four-iterate interpretation is additional framing; no novelty is established. |
| Vieta descent and terminal recurrence | Mathlib `Pell.eq_pell`, `Pell.yn_succ_succ`; general `Pell` library | For terminal `t=1`, put `A=2m−1`, `X=s−Aδ`, `Y=δ`. Then `X²−(A²−1)Y² = δ²+s²−(4m−2)δs`. The recurrence coefficient `2A` is exactly `4m−2`. Mathlib classifies the classical Pell family; it does not directly supply the preceding `t>1` ES descent or force `δ=t=1`. Standard positive nonsquare Pell classification needs `A>1` (here `m≥2`); `m=1` is degenerate. The algebraic dictionary itself is locally checked without extra hypotheses. |
| Square-class quotient preserved by divisor complementation | Foundation `divisorComplementInvolution` | Exact precedent for `A²/(A²/d)=d` over rationals. This does not state the strongest quotient condition `H²⊆L`, weighted orbit energy minimum, or the `E<M` target-forcing theorem. Foundation has additional finite carrier/character certificates, but the inspected archive's many `native_decide` examples do not meet this round's evidence policy. |
| Infinitely many primes in the explicit primitive AP | Mathlib Dirichlet; earlier HOL Light and Isabelle/HOL proofs | This is an imported existing theorem. It establishes prime infinitude after our arithmetic progression is shown primitive; it neither creates the ES witnesses nor proves H_D/H_N. |

## ES repositories and their actual scope

### carlok/erdos-straus-offset-lean

Inspected commit: `aa79d27ff20f61573cb4b0c0f142c42566769e3f`.

- [Pinned source](https://github.com/carlok/erdos-straus-offset-lean/blob/aa79d27ff20f61573cb4b0c0f142c42566769e3f/lean/ESTheorem.lean), [README](https://github.com/carlok/erdos-straus-offset-lean/blob/main/README.md).
- Pins: Lean `4.34.0`; mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
- The actual positive predicate `IsES n x y z` includes `0<n`, `0<x,y,z`, and the rational unit-fraction equality. By contrast, the earlier `mordell_3mod4` and `family_I` declarations only prove integer polynomial identities without positivity. These levels must not be conflated.
- `constructive_offset` requires `n≥2`, an auxiliary prime `q≡3 (mod 4)`, `n≡1 (mod 4)`, `q∤n`, a positive factor `d∣n((n+q)/4)`, and `q∣n((n+q)/4)+d`. It then constructs exact positive natural denominators. Here `q` is the repository's variable named `p`, not necessarily our ES input prime.
- Source scan found no `sorry`, custom `axiom`, or `native_decide`; one textual “admit” was ordinary prose. The inspected CI script audits named theorem dependency cones against `{propext, Classical.choice, Quot.sound}`.
- [Exact-head CI run](https://github.com/carlok/erdos-straus-offset-lean/actions/runs/35660492571) reports success; its build and axiom-audit steps both report success. Saved raw API responses: `prior_art/offset_ci.json`, `offset_ci_jobs.json`. This is upstream CI evidence.

**Our replay:** copied the source through `constructive_offset` and its first concrete example into `ES/PriorOffsetCore.lean`. Statements are unchanged. Compatibility edits are narrowed imports; anonymous instance `let : Fact p.Prime` spelled `letI : Fact (p.Prime)`; new `ZMod.natCast_eq_zero_iff` replaced by the old name `ZMod.natCast_zmod_eq_zero_iff_dvd`. Thus this is a transparent partial port to 4.19.0, not a claim to have rerun the complete upstream 4.34.0 project. The copied source is Apache-2.0 licensed; upstream license is retained in `prior_art/offset/LICENSE`.

### creelie/ErdosProblem1

Inspected commit: `8036770ea8fbff32f07676aa58a6a42320652f40`.

- [Pinned arithmetic source](https://github.com/creelie/ErdosProblem1/blob/8036770ea8fbff32f07676aa58a6a42320652f40/lean/ErdosStraus/Arithmetic.lean), [primary release description](https://zenodo.org/records/23486200).
- Pins: Lean `4.34.1`; mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Source inspected in `Arithmetic.lean`, `Exceptional.lean`, `Centre.lean`, and `Axioms.lean`. The selected declarations concern algebra, totients, constants, rational Type II identities, and bounded inequalities. The Lean development must not be described as a complete formal proof of the release's analytic exceptional-set theorem or of ES.
- No textual `sorry`, `admit`, custom `axiom`, or `native_decide` found in the five Lean files. [Exact-head verify run](https://github.com/creelie/ErdosProblem1/actions/runs/39348247928) and its Lean build/axiom step report success; raw API records are saved.
- Our local `ES.Literature.sieve_typeII_identity` has the same statement, independently rederived using 4.19's `field_simp` normalization and an explicit polynomial multiple of the premise. This is a statement-aligned local proof, not the original pinned build or a replay of the analytic paper.

### KokunoYumeto/erdos-straus-foundation

Inspected commit: `d20b32e1547aee2f08b440d56cceb47ab16dc4b7`.

- [Repository](https://github.com/KokunoYumeto/erdos-straus-foundation), [verification archive](https://github.com/KokunoYumeto/erdos-straus-foundation/blob/d20b32e1547aee2f08b440d56cceb47ab16dc4b7/02_ERDOS_STRAUSS_Verification_and_Lean.zip), [earlier primary release](https://zenodo.org/records/21805460).
- The archive contains a pinned three-file project (`lean/`) plus 32 separate `current_reader/verification/*.lean` files. The three-file project pins Lean `4.32.0`, mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Its `FORMAL_VERIFICATION_RECEIPT.md` reports 39 declarations and an extracted-copy build with standard/empty axiom reports. We checked the three source SHA-256 values against that receipt; they match. This remains an inspected author receipt rather than our original-toolchain replay.
- The pinned three-file project contains no `native_decide`. Thirteen of the 32 additional certificate files do contain it. Those additional files are outside the three-file receipt's scope; neither a passing core receipt nor an all-archive textual “no sorry” result certifies them under our stricter policy.
- The locally checked shell factorization, rational reconstruction, and complement involution are source-aligned elementary rederivations. They do not formalize the entire archive's geometric, spectral, or universal-occupancy program.
- A later informal “divisor descent” audit and “square-zero/Pell” README were inspected. Their maps concern deletion factors and rational trace sources (`R∣G²` versus `R∣G`), not our norm-equation Vieta step. The latter README expressly does not claim a full Lean build. Similar terminology is not evidence of an identical formal theorem.

### Open targets and false positives

- [Suro-One source](https://github.com/Suro-One/auro-zera_Erdos-Straus_proof/blob/2ee8a7ea72f92a599ef19a90b98e74a1dfef8360/auro-zera-proof.lean), commit `2ee8a7ea72f92a599ef19a90b98e74a1dfef8360`, explicitly declares `axiom good_divisor_exists` at source line 754. `ES_hard_residues` calls it; later universal `ErdosStraus_conjecture` is consequently conditional on that open witness assertion. No full replay was attempted. This is not an unconditional ES proof, even if the file compiles with no literal `sorry` tactics. The source itself discusses the remaining axiom.
- [Formal Conjectures problem 242](https://github.com/google-deepmind/formal-conjectures/blob/1efd73f117f6216638894027d87804d175e6b187/FormalConjectures/ErdosProblems/242.lean) is tagged `research open` and ends its target with `sorry`. It also asks for distinct denominators and `n>2`, which is a different statement from our repeated-denominator-allowed `n≥2` predicate. It is a formal statement, not a proof.
- The author [forum report about leochlon/erdstrau](https://www.erdosproblems.com/forum/thread/242) describes partial congruence coverage and conditional certificates. Direct clone failed with an unavailable/private-repository authentication response; no theorem source or dependency receipt was obtained here. Counts and “sorry-free” claims are therefore unverified author reports, not our conclusions.
- [lyfar/egrs75-lean](https://github.com/lyfar/egrs75-lean) concerns infinitely many central binomial coefficients avoiding two fixed odd primes. It is the Erdős–Graham–Ruzsa–Straus theorem, not the Erdős–Straus unit-fraction conjecture. It is excluded from substantive ES comparison.

## Existing Dirichlet and Pell formalizations

The installed `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` is attributed to Michael Stoll (2024) and proves, for `[NeZero q]` and `IsUnit a`, infinitude of `{p : ℕ | p.Prime ∧ (p : ZMod q)=a}`. Its exact 4.19 names are `Nat.setOf_prime_and_eq_mod_infinite` and `Nat.forall_exists_prime_gt_and_eq_mod`. Current online Mathlib has renamed the first theorem; we verified the installed source rather than guessing the current API. The local wrapper simply applies this existing theorem.

Primary history: [Loeffler–Stoll, *Formalizing zeta and L-functions in Lean*, AFM 2025](https://afm.episciences.org/15954); [Harrison, JFR 2(1), 63–83 (2009)](https://jfr.unibo.it/article/view/1558), whose journal landing page has an online date of 7 January 2010; [Eberl, AFP *Dirichlet L-Functions and Dirichlet's Theorem*, 21 December 2017](https://isa-afp.org/entries/Dirichlet_L.html). The [Isabelle source](https://isa-afp.org/browser_info/current/AFP/Dirichlet_L/Dirichlet_Theorem.html) contains `Dirichlet` with coprimality and infinitude of the prime congruence class. Neither HOL Light nor Isabelle was rerun in this session.

For the terminal norm comparison, we inspected installed [PellMatiyasevic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/PellMatiyasevic.html), attributed to Mario Carneiro, and the general [Pell theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Pell.html), attributed to Michael Geißer and Michael Stoll. The printed local axiom receipts cover `Pell.eq_pell` and `Pell.yn_succ_succ`; our new dictionary is only the algebraic change of variables.

## Supplement: direct mathematical-primary-source check

This section was added after the formal replay completed. It distinguishes a classical mathematical correspondence from an already-located Lean proof of the exact transport.

**Elsholtz–Tao.** The actual [arXiv v6 PDF](https://arxiv.org/pdf/1107.1010) was inspected, not just its abstract. Proposition 1.9, PDF page 8 (printed page 7), lists the Type II class `−e mod4ab` and Type I class `−e⁻¹ mod4ab`, both with `e∣a+b` and `gcd(e,4ab)=1`. Section 10, PDF page 38 (printed page 37), explicitly constructs Type II `d=(p+e)/(4ab)` and Type I `d=(pe+1)/(4ab)`, retaining `c=(a+b)/e`.

For our shape `(a,b,c,d,e)=(δ,s,t,r,4δrs−p)`, the intersection condition is exactly `e²≡1 (mod4ab)`. The resulting Type I scale is

`R′=(pe+1)/(4ab)=re−(e²−1)/(4ab)`.

Hence the B4 endpoint `(R′ac,R′bc,pR′ab)` belongs to the explicitly printed classical family. This observation does not identify a previously published proof of the exact ordered rational identity `T⁴`, or of every normalization/integrality/nonresidue refinement. It does show that the endpoint family and its scale must not be presented as newly discovered. No novelty claim is supported. Source handles: `turn89view0`, `turn89view1`, `turn89view2`.

**Chamberland.** The primary [Integers 26 (2026), A42 PDF](https://math.colgate.edu/~integers/aa42/aa42.pdf) was directly read. Theorem 1 (page 2) characterizes Type II by `p=qr−4s₁s₂`, with `q≡3 mod4` and `s₁,s₂∣(q+1)/4`. In our normalized notation, the exact dictionary is `q=4δrt−1`, `r_Ch=4δrs−p`, `s₁=δ`, `s₂=δr`. Its equation is our existing shifted-factor identity. The universal availability of this representation is explicitly **Conjecture 2**, page 4, not a supplied seed theorem. No Lean formalization of Chamberland's complete equivalence was located in this audit. Source handles: `turn88view0`, `turn89view3`.

**Jiang.** The primary [arXiv abstract/version page](https://arxiv.org/abs/2609.09204) was checked directly: it marks the paper withdrawn by Xinyang Jiang; version 2 is dated 13 September 2026 and its comment is “some errors.” It is excluded as support for a proved result. This is a verified primary-source status, not an inference from an unavailable PDF. Source handle: `turn88view1`.

**Quadratic reciprocity.** The installed Mathlib source `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean` was inspected. The standard declarations include `legendreSym.quadratic_reciprocity`, `legendreSym.quadratic_reciprocity_one_mod_four`, and `legendreSym.quadratic_reciprocity_three_mod_four`, under prime `Fact` instances and their stated parity hypotheses. These are existing foundational number-theoretic results; any family proof using them must label reciprocity as imported and separately prove the actual character evaluation for the ES family. The local `ES/Literature.lean` additionally checks the installed statements and prints axiom dependencies for `legendreSym.quadratic_reciprocity`, `legendreSym.quadratic_reciprocity'`, `jacobiSym.quadratic_reciprocity`, `jacobiSym.quadratic_reciprocity'`, `jacobiSym.mod_right`, and `ZMod.nonsquare_of_jacobiSym_eq_neg_one`.

The actual family lane uses `jacobiSym.mod_right` and `ZMod.nonsquare_of_jacobiSym_eq_neg_one`, together with the specific checked value `jacobiSym 44 153 = −1`. Source inspection verifies the dependency route `mod_right → mod_right' → jacobiSym.quadratic_reciprocity' → legendreSym.quadratic_reciprocity'`. Its actual ES-family applications are `jacobi_44` and `endpoint_nonresidue` in the family module, with its own `logs/families-build-final.log` receipt. A general B1 character theorem from the earlier mathematical notes remains an ordinary mathematical argument using the audited reciprocity dependency; checking the library dependency alone does **not** turn that application into a Lean theorem.

## Local theorem/axiom receipt

Commands, from `round_z5/lean` after sourcing `env.sh`:

```text
lake build ES.PriorOffsetCore
lake build ES.Literature
```

Both builds exited 0. Logs: `logs/literature_offset_build.log`, `logs/literature_build.log`. The machine-readable `logs/literature_receipt.json` records 24 distinct named axiom reports and the successful source-hash comparisons.

`ES.PriorOffsetCore` prints dependency receipts for `ESTheorem.engine_lemma`, `unified_offset_theorem`, `mordell_3mod4`, `family_I`, `isES_of_polynomial`, `isES_of_offset_certificate`, `second_divisibility`, and `constructive_offset`.

`ES.Literature` prints receipts for `divisorShellFactorization`, `divisorShellReconstruction`, `divisorComplementInvolution`, `sieve_typeII_identity`, `terminal_pell_dictionary`, `existing_dirichlet`, plus the two existing Dirichlet theorems, two Pell theorems, and six reciprocity/Jacobi dependencies listed above. Standard dependencies are recorded exactly in the logs; none of these final checked targets uses `sorryAx`, a custom axiom, or `Lean.ofReduceBool`.

The copied `es_polynomial` declaration merely repeats its polynomial premise and is not counted as a substantive result. The integer-only family declarations are not silently upgraded to positive solutions. No H_D, H_N, uniform selector, universal Type II existence, or universal ES assertion is proved by this literature replay.

## Search limits and provenance files

Searches used both web engines for ES/Lean/formalization, Type II, bridge, Vieta, and square-class combinations; inspected primary GitHub sources and archived Lean files; and checked Dirichlet/Pell source in the actually installed Mathlib version. The search was not an exhaustive audit of every historical release, private repository, proof assistant, or nested archive. Source keyword absence is not a proof of mathematical novelty.

`prior_art/source_sha256.json` identifies selected retrieved files. Per-repository `*_static_audit.json` files distinguish textual scans from dependency-cone checks. The full Foundation clone is roughly 500 MB and should not be included unnecessarily in the deliverable; a curated source/receipt subset plus pinned URLs is enough for this audit.

Web citation handles available to the coordinator: carlok README `turn77search0` / `turn86search3`; Foundation repository `turn77search3` / `turn86search0`; Sieve primary release `turn80search0`; Suro-One source `turn85view2`; Dirichlet Mathlib `turn77search5`, publication `turn81view2`, Harrison `turn77search7`, AFP `turn79view0`, Isabelle final statement `turn85view3`; Pell `turn87view0` and `turn87view1`; leochlon author report `turn86search5`; EGRS false positive `turn81view0`. Pinned source URLs and exact local files support statements whose web renderer was unavailable.
