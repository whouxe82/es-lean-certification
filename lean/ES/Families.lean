import ES.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# An infinite family with a failed B1 gate and an integral B4 endpoint

This file uses `n = r - 1` so every displayed denominator is a positive natural
number without relying on truncated subtraction. The formulas are precisely
`p = 528*r - 23` and `H = 23*r - 1`, with `r = n + 1`.

Infinitude is imported from Mathlib's proved Dirichlet theorem. The larger
endpoint coordinate is proved a quadratic nonresidue using Mathlib's Jacobi
periodicity theorem. No uniform existence claim for arbitrary primes is made.
-/

namespace ES.Families

/-- Positive-integer, denominator-cleared Erdős–Straus certificate. -/
def PositiveES (p x y z : ℕ) : Prop :=
  0 < p ∧ ES.IsSolution p x y z

/-- Prime input, when this natural number happens to be prime. -/
def p (n : ℕ) : ℕ := 528*n+505
/-- The B4 endpoint's canonical coefficient. -/
def H (n : ℕ) : ℕ := 23*n+22
/-- `p = 4*k + 1`. -/
def k (n : ℕ) : ℕ := 132*n+126

theorem original_parameterization (n : ℕ) :
    p n = 528*(n+1)-23 ∧ H n = 23*(n+1)-1 := by
  dsimp [p, H]
  omega

theorem p_eq_four_k_add_one (n : ℕ) : p n = 4*k n+1 := by
  dsimp [p, k]
  ring

theorem p_mod_twentyfour (n : ℕ) : p n % 24 = 1 := by
  dsimp [p]
  omega

/-- The uniform normalized Type II state is `(δ,r,s,t)=(11,n+1,12,1)`.
The last equality is the subtraction-free defining Type II equation. -/
theorem normalized_source_state (n : ℕ) :
    0 < (11:ℕ) ∧ 0 < n+1 ∧ 0 < (12:ℕ) ∧ 0 < (1:ℕ) ∧
    Nat.Coprime 11 12 ∧ 11 ≤ (12:ℕ) ∧
    4*11*(n+1)*12*1 = p n*1+11+12 := by
  dsimp [p]
  norm_num
  omega

theorem normalizedII (n : ℕ) : ES.NormalizedII (p n) 11 (n+1) 12 1 := by
  have h := normalized_source_state n
  exact ⟨by dsimp [p]; omega, h⟩

/-- The source triple is a positive natural-number ES certificate for every n. -/
theorem source_positiveES (n : ℕ) :
    PositiveES (p n) (132*(n+1)) (11*p n*(n+1)) (12*p n*(n+1)) := by
  unfold PositiveES ES.IsSolution p
  refine ⟨by positivity, by positivity, by positivity, by positivity, ?_⟩
  ring

/-- The displayed four-step endpoint is a positive natural-number ES certificate. -/
theorem endpoint_positiveES (n : ℕ) :
    PositiveES (p n) (11*H n) (12*H n) (132*p n*H n) := by
  unfold PositiveES ES.IsSolution p H
  refine ⟨by positivity, by positivity, by positivity, by positivity, ?_⟩
  ring

/-- Connection to the shared ES definition. -/
theorem source_isSolution (n : ℕ) :
    ES.IsSolution (p n) (132*(n+1)) (11*p n*(n+1)) (12*p n*(n+1)) :=
  (source_positiveES n).2

theorem endpoint_isSolution (n : ℕ) :
    ES.IsSolution (p n) (11*H n) (12*H n) (132*p n*H n) :=
  (endpoint_positiveES n).2

/-- The old one-step gate `δ*t ∣ k` fails for every member. -/
theorem old_gate_fails (n : ℕ) : ¬ (11:ℕ) ∣ k n := by
  rw [Nat.dvd_iff_mod_eq_zero]
  dsimp [k]
  omega

/-- The four-step divisibility gate `4*δ*s ∣ d²-1` holds. -/
theorem new_gate_holds : (4*11*12:ℕ) ∣ 23^2-1 := by decide

/-- Strict endpoint bounds, stated without rational division:
`p/4 < 11*H < p/2 < 12*H < 3*p/4`. -/
theorem endpoint_interval (n : ℕ) :
    p n < 4*(11*H n) ∧ 2*(11*H n) < p n ∧
    p n < 2*(12*H n) ∧ 4*(12*H n) < 3*p n := by
  dsimp [p, H]
  omega

/-- The intermediate scalar from the B4 formula is exactly `132*H`. -/
theorem B4_scalar (n : ℕ) : (p n*23+1) = 4*(132*H n) := by
  dsimp [p, H]
  ring

/-- The actual divisions in the B4 endpoint formula give the displayed integers. -/
theorem B4_endpoint_formula (n : ℕ) :
    let C := (p n*23+1)/4
    C/12 = 11*H n ∧ C/11 = 12*H n ∧ p n*C = 132*p n*H n := by
  have hC : (p n*23+1)/4 = 132*H n := by
    dsimp [p, H]
    omega
  dsimp only
  rw [hC]
  constructor
  · omega
  constructor
  · omega
  · ring

/-- Positive natural certificates imply the original rational unit-fraction equation. -/
theorem PositiveES.unitFractions {p x y z : ℕ} (h : PositiveES p x y z) :
    (4:ℚ)/p = 1/(x:ℚ)+1/(y:ℚ)+1/(z:ℚ) := by
  exact ES.isSolution_unitFraction h.2 h.1

/-- Dirichlet is applied to the primitive progression `505 mod 528`. -/
theorem residue_class_infinite :
    {q : ℕ | q.Prime ∧ (q:ZMod 528) = (505:ZMod 528)}.Infinite := by
  apply Nat.setOf_prime_and_eq_mod_infinite
  exact (ZMod.isUnit_iff_coprime 505 528).mpr (by decide)

/-- Exact conversion from a residue-class member to our nonnegative parameter. -/
theorem parameter_of_residue {q : ℕ}
    (hq : (q:ZMod 528) = (505:ZMod 528)) : ∃ n, q = p n := by
  have hm : q % 528 = 505 := by
    have := (ZMod.natCast_eq_natCast_iff' q 505 528).mp hq
    norm_num at this
    exact this
  refine ⟨q/528, ?_⟩
  have := Nat.mod_add_div q 528
  dsimp [p]
  omega

/-- Infinitely many distinct PRIME INPUTS admit the displayed uniform formulas.
This does not say that every prime lies in this progression. -/
theorem family_prime_inputs_infinite : {q : ℕ | q.Prime ∧ ∃ n, q = p n}.Infinite := by
  apply residue_class_infinite.mono
  intro q hq
  exact ⟨hq.1, parameter_of_residue hq.2⟩

/-- Infinitely many prime inputs carry both positive-integer certificates and
old-gate failure. This theorem packages the algebra and the imported infinitude. -/
theorem certified_family_infinite :
    {q : ℕ | q.Prime ∧ ∃ n, q = p n ∧
      PositiveES q (132*(n+1)) (11*q*(n+1)) (12*q*(n+1)) ∧
      PositiveES q (11*H n) (12*H n) (132*q*H n) ∧
      ¬ (11:ℕ) ∣ k n}.Infinite := by
  apply family_prime_inputs_infinite.mono
  rintro q ⟨hq, n, rfl⟩
  exact ⟨hq, n, rfl, source_positiveES n, endpoint_positiveES n, old_gate_fails n⟩

/-- The Jacobi symbol of 44 is constantly -1 in this progression.
This invokes the proved Jacobi periodicity theorem, rather than a character
assumption attached to the family. -/
theorem jacobi_44 (n : ℕ) : jacobiSym 44 (p n) = -1 := by
  have hpodd : Odd (p n) := by
    rw [Nat.odd_iff]
    dsimp [p]
    omega
  have hm : p n % 176 = 153 := by
    dsimp [p]
    omega
  rw [jacobiSym.mod_right 44 hpodd]
  norm_num at hm ⊢
  rw [hm]
  norm_num

/-- The larger endpoint coordinate is a quadratic nonresidue, uniformly.
In fact primality is unnecessary for this sufficient Jacobi obstruction. -/
theorem endpoint_nonresidue (n : ℕ) : ES.Nonresidue (p n) (12*H n) := by
  have h44 : ¬IsSquare (44 : ZMod (p n)) := by
    have := ZMod.nonsquare_of_jacobiSym_eq_neg_one (jacobi_44 n)
    norm_num at this
    exact this
  have heq : (44*(12*H n):ℕ) = 23*p n+1 := by
    dsimp [p, H]
    ring
  have hm : (44 : ZMod (p n))*((12*H n:ℕ):ZMod (p n)) = 1 := by
    have hh := congrArg (fun a : ℕ => (a : ZMod (p n))) heq
    norm_num at hh
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
  rintro ⟨u, hu⟩
  apply h44
  refine ⟨44*u, ?_⟩
  rw [hu] at hm
  calc
    (44 : ZMod (p n)) = 44*(44*(u*u)) := by rw [hm]; ring
    _ = (44*u)*(44*u) := by ring

/-- Every family input has the complete certificate requested in the H_N
predicate, with the larger endpoint moved into the first position. -/
theorem endpoint_HN_witness (n : ℕ) :
    ∃ x y z, ES.IsSolution (p n) x y z ∧ p n < 4*x ∧
      4*x < 3*p n ∧ ES.Nonresidue (p n) x := by
  refine ⟨12*H n, 11*H n, 132*p n*H n, ?_, ?_,
    (endpoint_interval n).2.2.2, endpoint_nonresidue n⟩
  · unfold ES.IsSolution p H
    refine ⟨by positivity, by positivity, by positivity, ?_⟩
    ring
  · have := (endpoint_interval n).2.2.1
    omega

/-- Infinitely many prime inputs carry the full H_N witness, while the
specified source fails B1. This is a progression theorem, not universal H_N. -/
theorem nonresidue_family_infinite :
    {q : ℕ | q.Prime ∧ ∃ n, q = p n ∧ ¬ (11:ℕ) ∣ k n ∧
      ∃ x y z, ES.IsSolution q x y z ∧ q < 4*x ∧
        4*x < 3*q ∧ ES.Nonresidue q x}.Infinite := by
  apply family_prime_inputs_infinite.mono
  rintro q ⟨hq, n, rfl⟩
  exact ⟨hq, n, rfl, old_gate_fails n, endpoint_HN_witness n⟩

/-- A verified primitive refinement suffices for prime infinitude in an
additional residue class. The six rows below instantiate this one lemma. -/
theorem refinement_infinite (a b : ℕ) (hb : b < 18480)
    (hc : b.Coprime 18480) (h528 : b % 528 = 505) (h840 : b % 840 = a) :
    {q : ℕ | q.Prime ∧ q % 840 = a ∧ ∃ n, q = p n}.Infinite := by
  have hi : {q : ℕ | q.Prime ∧ (q:ZMod 18480) = (b:ZMod 18480)}.Infinite :=
    Nat.setOf_prime_and_eq_mod_infinite ((ZMod.isUnit_iff_coprime b 18480).mpr hc)
  apply hi.mono
  intro q hq
  have hmod : q % 18480 = b := by
    have := (ZMod.natCast_eq_natCast_iff' q b 18480).mp hq.2
    rwa [Nat.mod_eq_of_lt hb] at this
  have hq528 : q % 528 = 505 := by
    rw [← Nat.mod_mod_of_dvd q (by decide : 528 ∣ 18480), hmod, h528]
  have hq840 : q % 840 = a := by
    rw [← Nat.mod_mod_of_dvd q (by decide : 840 ∣ 18480), hmod, h840]
  refine ⟨hq.1, hq840, parameter_of_residue ?_⟩
  apply (ZMod.natCast_eq_natCast_iff' q 505 528).mpr
  norm_num [hq528]

/-- Each of the six residual classes receives infinitely many members of this
same family. Explicit CRT witnesses avoid an unproved compatibility assertion. -/
theorem six_classes_infinite :
    ∀ a ∈ ([1,121,169,289,361,529] : List ℕ),
      {q : ℕ | q.Prime ∧ q % 840 = a ∧ ∃ n, q = p n}.Infinite := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact refinement_infinite 1 4201 (by decide) (by decide) (by decide) (by decide)
  · exact refinement_infinite 121 6841 (by decide) (by decide) (by decide) (by decide)
  · exact refinement_infinite 169 15289 (by decide) (by decide) (by decide) (by decide)
  · exact refinement_infinite 289 17929 (by decide) (by decide) (by decide) (by decide)
  · exact refinement_infinite 361 12121 (by decide) (by decide) (by decide) (by decide)
  · exact refinement_infinite 529 4729 (by decide) (by decide) (by decide) (by decide)

/-- A finite example, separately labelled: n=1 corresponds to r=2 and p=1033. -/
theorem example_1033 :
    Nat.Prime 1033 ∧ PositiveES 1033 264 22726 24792 ∧
    PositiveES 1033 495 540 6136020 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · exact source_positiveES 1
  · exact endpoint_positiveES 1

#print axioms source_positiveES
#print axioms endpoint_positiveES
#print axioms old_gate_fails
#print axioms new_gate_holds
#print axioms endpoint_interval
#print axioms PositiveES.unitFractions
#print axioms residue_class_infinite
#print axioms family_prime_inputs_infinite
#print axioms certified_family_infinite
#print axioms normalizedII
#print axioms B4_endpoint_formula
#print axioms refinement_infinite
#print axioms six_classes_infinite
#print axioms jacobi_44
#print axioms endpoint_nonresidue
#print axioms endpoint_HN_witness
#print axioms nonresidue_family_infinite
#print axioms example_1033

end ES.Families
