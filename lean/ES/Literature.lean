import ES.PriorOffsetCore
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PellMatiyasevic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! Source-aligned prior-art checks. The short proofs below are transparent
re-derivations of displayed formulas, not an upstream pinned-version replay.
Foundation commit d20b32e1547aee2f08b440d56cceb47ab16dc4b7:
02_ERDOS_STRAUSS_Verification_and_Lean.zip/lean/ErdosStraussChecks.lean.
Sieve commit 8036770ea8fbff32f07676aa58a6a42320652f40:
lean/ErdosStraus/Arithmetic.lean, typeII_identity.
-/
namespace ES.Literature

theorem divisorShellFactorization (R N b c : ℤ) :
    (R * b - N) * (R * c - N) - N ^ 2 =
      R * (R * b * c - N * (b + c)) := by ring

theorem divisorShellReconstruction (R N d e : ℚ) (hR : R ≠ 0) :
    R * ((N + d) / R * ((N + e) / R)) -
        N * ((N + d) / R + (N + e) / R) =
      (d * e - N ^ 2) / R := by
  field_simp
  <;> ring

theorem divisorComplementInvolution (A d : ℚ) (hA : A ≠ 0) (hd : d ≠ 0) :
    A ^ 2 / (A ^ 2 / d) = d := by field_simp

theorem sieve_typeII_identity (n u a v α : ℚ)
    (hn : n ≠ 0) (hu : u ≠ 0) (ha : a ≠ 0) (hv : v ≠ 0) (hα : α ≠ 0)
    (h : a * n + u = v * (4 * a * α * u - 1)) :
    4 / n = 1 / (α * u * v) + 1 / (a * α * n * u) + 1 / (a * α * n * v) := by
  field_simp
  linear_combination -(α ^ 2 * u * v * a * n ^ 2) * h

/-- Exact algebraic dictionary from the terminal norm to the classical Pell family.
This identity does not prove positivity or the ES-specific descent. -/
theorem terminal_pell_dictionary (m δ s : ℤ) :
    (s - (2 * m - 1) * δ)^2 - ((2 * m - 1)^2 - 1) * δ^2 =
      δ^2 + s^2 - (4 * m - 2) * δ * s := by ring

/-- An application of existing mathlib Dirichlet; no new analytic proof. -/
theorem existing_dirichlet {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    {p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite :=
  Nat.setOf_prime_and_eq_mod_infinite ha

#print axioms divisorShellFactorization
#print axioms divisorShellReconstruction
#print axioms divisorComplementInvolution
#print axioms sieve_typeII_identity
#print axioms terminal_pell_dictionary
#print axioms Pell.eq_pell
#print axioms Pell.yn_succ_succ
#print axioms existing_dirichlet
#print axioms Nat.setOf_prime_and_eq_mod_infinite
#print axioms Nat.forall_exists_prime_gt_and_eq_mod
end ES.Literature

/-! Audited existing reciprocity dependencies. These commands expose the actual
installed statements and dependency axioms; they do not formalize the general
B1 character application. The Families lane proves its own specific application. -/
#check legendreSym.quadratic_reciprocity
#check legendreSym.quadratic_reciprocity'
#check jacobiSym.quadratic_reciprocity
#check jacobiSym.quadratic_reciprocity'
#check jacobiSym.mod_right
#check ZMod.nonsquare_of_jacobiSym_eq_neg_one
#print axioms legendreSym.quadratic_reciprocity
#print axioms legendreSym.quadratic_reciprocity'
#print axioms jacobiSym.quadratic_reciprocity
#print axioms jacobiSym.quadratic_reciprocity'
#print axioms jacobiSym.mod_right
#print axioms ZMod.nonsquare_of_jacobiSym_eq_neg_one
