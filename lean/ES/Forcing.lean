import Mathlib

/-!
# Complement-preserving quotients and finite orbit-energy forcing

These are abstract group/combinatorial theorems, followed by a finite six-bin
certificate from the p=577 example. No uniform selector or number-theoretic
realization of the abstract assumptions is asserted here.
-/

namespace ES.Forcing
open scoped Pointwise

section Group
variable {G : Type*} [CommGroup G]

/-- The square subgroup of a commutative group. -/
def squares : Subgroup G where
  carrier := {g | ∃ h : G, h ^ 2 = g}
  one_mem' := ⟨1, one_pow 2⟩
  mul_mem' := by
    rintro a b ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u * v, mul_pow u v 2⟩
  inv_mem' := by
    rintro a ⟨u, rfl⟩
    exact ⟨u⁻¹, inv_pow u 2⟩

/-- Complementation in the residue group. -/
def complement (x g : G) : G := x ^ 2 / g

theorem complement_involutive (x : G) : Function.Involutive (complement x) := by
  intro g
  simp [complement]

theorem complement_ratio (x g : G) : complement x g / g = (x / g) ^ 2 := by
  unfold complement
  rw [div_pow, div_div, pow_two g]

/-- Expressing equality of quotient cells by subgroup membership. -/
def PreservesCosets (x : G) (L : Subgroup G) : Prop :=
  ∀ g : G, complement x g / g ∈ L

/-- H/H² is the finest group-quotient partition preserved by complementation.
This says nothing about arbitrary set partitions, which can be finer. -/
theorem preservesCosets_iff_squares_le (x : G) (L : Subgroup G) :
    PreservesCosets x L ↔ squares ≤ L := by
  constructor
  · intro h a ha
    obtain ⟨u, rfl⟩ := ha
    have hu : x / (x / u) = u := div_div_cancel x u
    simpa [complement_ratio, hu] using h (x / u)
  · intro h g
    rw [complement_ratio]
    exact h ⟨x / g, rfl⟩

theorem square_cosets_preserved (x : G) : PreservesCosets x (squares : Subgroup G) :=
  (preservesCosets_iff_squares_le x squares).2 le_rfl

/-- The same statement with actual quotient-group equality. -/
theorem quotient_preserved_iff (x : G) (L : Subgroup G) :
    (∀ g : G, ((complement x g : G) : G ⧸ L) = (g : G ⧸ L)) ↔ squares ≤ L := by
  haveI : L.Normal := L.normal_of_comm
  simpa only [PreservesCosets, QuotientGroup.eq_iff_div_mem] using
    preservesCosets_iff_squares_le x L

/-- Any character/kernel quotient that kills squares is a coarsening. -/
theorem squares_le_kernel {K : Type*} [CommGroup K] (χ : G →* K)
    (hχ : ∀ g : G, χ g ^ 2 = 1) : squares ≤ χ.ker := by
  rintro a ⟨u, rfl⟩
  simpa only [MonoidHom.mem_ker, map_pow] using hχ u

/-- Histogram of labels on an arbitrary finite source set. -/
def fiberCount {D : Type*} [Fintype D] [DecidableEq G]
    (label : D → G) (g : G) : ℕ :=
  (Finset.univ.filter fun a => label a = g).card

/-- A complement-compatible involution on the source objects proves equality
of the two residue occupancies. For divisors, the source involution would be
`a ↦ x²/a`; that arithmetic instantiation is a separate obligation. -/
theorem fiberCount_complement {D : Type*} [Fintype D] [DecidableEq G]
    (x : G) (label : D → G) (σ : D → D) (hσ : Function.Involutive σ)
    (hlabel : ∀ a, label (σ a) = complement x (label a)) (g : G) :
    fiberCount label g = fiberCount label (complement x g) := by
  classical
  unfold fiberCount
  refine Finset.card_bij (fun a _ => σ a) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [hlabel, ha]
  · intro a ha b hb hab
    exact hσ.injective hab
  · intro b hb
    refine ⟨σ b, ?_, hσ b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [hlabel, hb, complement_involutive x g]

end Group

section FiniteEnergy
open Finset

/-- A bounded occupancy vector. Its bound makes the search genuinely finite. -/
abbrev Profile (n T : ℕ) := Fin n → Fin (T + 1)

def mass {n T : ℕ} (w : Profile n T) : ℕ := ∑ i, (w i : ℕ)
def energy {n T : ℕ} (w : Profile n T) : ℕ := ∑ i, (w i : ℕ) ^ 2

/-- The abstract divisor-orbit restrictions. A supplied central bin is odd;
all other fixed bins are even, and paired bins have equal occupancy. -/
def OrbitCompatible {n T : ℕ} (ι : Fin n → Fin n) (central : Option (Fin n))
    (w : Profile n T) : Prop :=
  (∀ i, w (ι i) = w i) ∧
  (∀ i, ι i = i → if central = some i then Odd (w i : ℕ) else Even (w i : ℕ))

/-- Explicitly enumerable profiles with the required mass, orbit constraints,
and zero occupancy at every target. -/
def avoidanceProfiles {n : ℕ} (T : ℕ) (ι : Fin n → Fin n)
    (central : Option (Fin n)) (targets : Finset (Fin n)) : Finset (Profile n T) := by
  letI : DecidablePred (OrbitCompatible ι central (T := T)) := fun w => by
    unfold OrbitCompatible
    infer_instance
  exact univ.filter fun w => mass w = T ∧ OrbitCompatible ι central w ∧
    ∀ i ∈ targets, (w i : ℕ) = 0

/-- Exact finite avoidance minimum, with ⊤ for an empty feasible set. -/
def avoidanceMinimum {n : ℕ} (T : ℕ) (ι : Fin n → Fin n)
    (central : Option (Fin n)) (targets : Finset (Fin n)) : WithTop ℕ :=
  ((avoidanceProfiles T ι central targets).image energy).min

/-- Strict energy below an actual finite constrained minimum forces a hit.
The premise is an inequality against an explicit finite search, not a premise
that assumes the existence of the desired target divisor. -/
theorem energy_lt_avoidanceMinimum_forces {n T : ℕ} (ι : Fin n → Fin n)
    (central : Option (Fin n)) (targets : Finset (Fin n)) (w : Profile n T)
    (hmass : mass w = T) (horbit : OrbitCompatible ι central w)
    (hlt : (energy w : WithTop ℕ) < avoidanceMinimum T ι central targets) :
    ∃ i ∈ targets, 0 < (w i : ℕ) := by
  classical
  by_contra h
  have hzero : ∀ i ∈ targets, (w i : ℕ) = 0 := by
    intro i hi
    have hn : ¬ 0 < (w i : ℕ) := by
      intro hp
      exact h ⟨i, hi, hp⟩
    omega
  have hw : w ∈ avoidanceProfiles T ι central targets := by
    simp only [avoidanceProfiles, mem_filter, mem_univ, true_and]
    exact ⟨hmass, horbit, hzero⟩
  have he : energy w ∈ (avoidanceProfiles T ι central targets).image energy :=
    mem_image.mpr ⟨w, hw, rfl⟩
  have hle : avoidanceMinimum T ι central targets ≤ (energy w : WithTop ℕ) :=
    Finset.min_le he
  exact (not_lt_of_ge hle) hlt

/-- An independently useful monotonicity fact: imposing more constraints
cannot lower a finite avoidance minimum; it also handles empty feasible sets. -/
theorem minimum_mono {α : Type*} [DecidableEq α] (coarse fine : Finset α)
    (cost : α → ℕ) (h : fine ⊆ coarse) :
    (coarse.image cost).min ≤ (fine.image cost).min := by
  exact Finset.min_mono (Finset.image_subset_image h)

/-- The numerical last step of refinement dominance. To apply it, the coarse
and fine feasible-profile constructions still have to be linked. -/
theorem sum_strict_forces_component {α : Type*} [Fintype α]
    (actual threshold : α → ℕ) (h : (∑ i, actual i) < ∑ i, threshold i) :
    ∃ i, actual i < threshold i := by
  by_contra hn
  have hle : ∀ i, threshold i ≤ actual i := by
    intro i
    by_contra hi
    exact hn ⟨i, by omega⟩
  exact (not_lt_of_ge (Finset.sum_le_sum fun i _ => hle i)) h

end FiniteEnergy

section Cell577

/-- The six residues in the Type-II square-class cell, in the order used below.
This definition alone does not identify it with a quotient square class. -/
def cell577 : Fin 6 → ℕ := ![2, 5, 8, 11, 20, 32]

/-- Canonical representatives of the units modulo 39. -/
def units39 : Finset ℕ := (Finset.range 39).filter fun g => Nat.gcd g 39 = 1

def squares39 : Finset ℕ := units39.image fun g => g ^ 2 % 39

theorem squares39_exact : squares39 = {1, 4, 10, 16, 22, 25} := by decide

/-- This concrete cell is precisely twice the square residues among units. -/
theorem cell577_square_class :
    (Finset.univ.image cell577) = squares39.image (fun g => (2 * g) % 39) := by
  decide

def counts577 : Fin 6 → ℕ := ![2, 1, 1, 2, 1, 1]

def involution577 : Fin 6 → Fin 6 := ![0, 5, 4, 3, 2, 1]

theorem involution577_involutive : Function.Involutive involution577 := by
  change ∀ i : Fin 6, involution577 (involution577 i) = i
  decide

theorem cell577_complements : ∀ i : Fin 6,
    (cell577 i * cell577 (involution577 i)) % 39 = 4 := by
  decide

theorem counts577_symmetric : ∀ i : Fin 6,
    counts577 (involution577 i) = counts577 i := by
  decide

theorem counts577_fixed_even : ∀ i : Fin 6,
    involution577 i = i → Even (counts577 i) := by
  decide

theorem counts577_mass : (∑ i : Fin 6, counts577 i) = 8 := by decide

theorem counts577_energy : (∑ i : Fin 6, counts577 i ^ 2) = 12 := by decide

/-- After removing the target fixed bin, the remaining orbit occupancies are
2j at the other fixed bin, b at each member of one pair, and c at each member
of the other pair. This is the exact lower bound at total mass eight. -/
theorem cell577_avoidance_lower_bound (j b c : ℕ) (hmass : j + b + c = 4) :
    14 ≤ 4 * j ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 := by
  have hj : j ≤ 4 := by omega
  have hb : b ≤ 4 := by omega
  have hc : c ≤ 4 := by omega
  interval_cases j <;> interval_cases b <;> interval_cases c <;> norm_num at *

/-- The bound is attained; thus fourteen is an exact minimum, not merely a
convenient lower bound. -/
theorem cell577_avoidance_attained :
    ∃ j b c : ℕ, j + b + c = 4 ∧ 4 * j ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 = 14 := by
  exact ⟨1, 1, 2, by norm_num, by norm_num⟩

/-- Sound local orbit forcing, with no target-hit premise. -/
theorem cell577_energy_forces (a f b c : ℕ) (hf : Even f)
    (hmass : a + f + 2 * b + 2 * c = 8)
    (henergy : a ^ 2 + f ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 < 14) : 0 < a := by
  by_contra ha
  have ha0 : a = 0 := by omega
  obtain ⟨j, hj⟩ := hf
  have hsum : j + b + c = 4 := by omega
  have hbound := cell577_avoidance_lower_bound j b c hsum
  subst a
  rw [hj] at henergy
  nlinarith

/-- An arbitrary feasible avoiding six-bin profile obeys the proved bound. -/
theorem avoidanceProfile577_lower_bound (w : Profile 6 8)
    (hw : w ∈ avoidanceProfiles 8 involution577 none {0}) : 14 ≤ energy w := by
  simp only [avoidanceProfiles, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  have hzero : (w 0 : ℕ) = 0 := hw.2.2 0 (by simp)
  have h51 : w 5 = w 1 := by simpa [involution577] using hw.2.1.1 1
  have h42 : w 4 = w 2 := by simpa [involution577] using hw.2.1.1 2
  have hfixed : Even (w 3 : ℕ) := by
    simpa using hw.2.1.2 3 (by decide)
  obtain ⟨j, hj⟩ := hfixed
  have hm := hw.1
  simp [mass, Fin.sum_univ_succ] at hm
  have hsum : j + (w 1 : ℕ) + (w 2 : ℕ) = 4 := by
    simp only [h51, h42] at hm
    omega
  have hbound := cell577_avoidance_lower_bound j (w 1) (w 2) hsum
  simp [energy, Fin.sum_univ_succ, h51, h42, hzero]
  nlinarith

/-- Fourteen is also the exact value of the general finite optimizer on this
cell, not just of a separately stated arithmetic relaxation. -/
theorem avoidanceMinimum577_eq :
    avoidanceMinimum 8 involution577 none {0} = (14 : WithTop ℕ) := by
  unfold avoidanceMinimum
  apply le_antisymm
  · let v : Profile 6 8 := ![0, 1, 2, 2, 2, 1]
    have hv : v ∈ avoidanceProfiles 8 involution577 none {0} := by
      simp only [avoidanceProfiles, Finset.mem_filter, Finset.mem_univ, true_and]
      unfold OrbitCompatible
      decide
    have he : energy v = 14 := by decide
    simpa only [he] using (Finset.min_le (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
  · apply Finset.le_min
    intro e he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
    exact WithTop.coe_le_coe.mpr (avoidanceProfile577_lower_bound w hw)

/-- Complete factorization of the actual divisor set, reduced to three small
finite sets. This uses Mathlib's general divisors-of-a-product theorem. -/
theorem divisors577_factorization :
    Nat.divisors (154 ^ 2) =
      ({1, 2, 4} : Finset ℕ) * {1, 7, 49} * {1, 11, 121} := by
  have hnum : (154 : ℕ) ^ 2 = 4 * 49 * 121 := by norm_num
  rw [hnum, Nat.divisors_mul, Nat.divisors_mul]
  have h4 : Nat.divisors 4 = {1, 2, 4} := by decide
  have h49 : Nat.divisors 49 = {1, 7, 49} := by decide
  have h121 : Nat.divisors 121 = {1, 11, 121} := by decide
  rw [h4, h49, h121]

/-- These six counts are the complete actual divisor histogram in the stated
cell, not an invented compatible profile. -/
theorem counts577_is_divisorHistogram : ∀ i : Fin 6,
    ((Nat.divisors (154 ^ 2)).filter fun a => a % 39 = cell577 i).card = counts577 i := by
  rw [divisors577_factorization]
  decide

/-- Applying the sound criterion to the concrete six-bin occupancies. -/
theorem counts577_target_forced : 0 < counts577 0 := by
  let w : Profile 6 8 := ![2, 1, 1, 2, 1, 1]
  have hm : mass w = 8 := by decide
  have ho : OrbitCompatible involution577 none w := by
    unfold OrbitCompatible
    decide
  have he : (energy w : WithTop ℕ) < avoidanceMinimum 8 involution577 none {0} := by
    rw [avoidanceMinimum577_eq]
    decide
  obtain ⟨i, hi, hp⟩ :=
    energy_lt_avoidanceMinimum_forces involution577 none {0} w hm ho he
  have hi0 : i = 0 := by simpa using hi
  subst i
  exact hp

/-- The energy certificate yields an actual divisor at the Type-II target
residue. The conversion of this local target to a general ES/NR theorem is
outside this module. -/
theorem divisor577_target_exists :
    ∃ a : ℕ, a ∣ 154 ^ 2 ∧ a % 39 = 2 := by
  have hpos : 0 < ((Nat.divisors (154 ^ 2)).filter
      fun a => a % 39 = cell577 0).card := by
    rw [counts577_is_divisorHistogram]
    exact counts577_target_forced
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  have hamem := Finset.mem_filter.mp ha
  exact ⟨a, Nat.dvd_of_mem_divisors hamem.1, hamem.2⟩

end Cell577

end ES.Forcing

#print axioms ES.Forcing.quotient_preserved_iff
#print axioms ES.Forcing.squares_le_kernel
#print axioms ES.Forcing.energy_lt_avoidanceMinimum_forces
#print axioms ES.Forcing.minimum_mono
#print axioms ES.Forcing.sum_strict_forces_component
#print axioms ES.Forcing.cell577_avoidance_lower_bound
#print axioms ES.Forcing.cell577_avoidance_attained
#print axioms ES.Forcing.cell577_energy_forces
#print axioms ES.Forcing.counts577_target_forced

#print axioms ES.Forcing.divisors577_factorization
#print axioms ES.Forcing.counts577_is_divisorHistogram
#print axioms ES.Forcing.divisor577_target_exists

#print axioms ES.Forcing.fiberCount_complement

#print axioms ES.Forcing.avoidanceMinimum577_eq

#print axioms ES.Forcing.squares39_exact
#print axioms ES.Forcing.cell577_square_class
