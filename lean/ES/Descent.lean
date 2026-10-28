import ES.Bridges

/-!
# Auxiliary shape descent for the four-step bridge

This module concerns solutions of a norm equation. It does not assert that a
source exists at an arbitrary prime, and the descent is not at a fixed prime.
-/

namespace ESDescent

/-- The integral Vieta companion; no division or truncated subtraction. -/
def companion (m t a b : ℤ) : ℤ := (4 * m * t ^ 2 - 2) * a - b

lemma companion_product {m t a b : ℤ}
    (hnorm : (a + b) ^ 2 = t ^ 2 * (4 * m * a * b + 1)) :
    b * companion m t a b = a ^ 2 - t ^ 2 := by
  dsimp [companion]
  nlinarith [hnorm]

lemma companion_norm {m t a b : ℤ}
    (hnorm : (a + b) ^ 2 = t ^ 2 * (4 * m * a * b + 1)) :
    (companion m t a b + a) ^ 2 =
      t ^ 2 * (4 * m * companion m t a b * a + 1) := by
  have hidentity :
      (companion m t a b + a) ^ 2 -
        t ^ 2 * (4 * m * companion m t a b * a + 1) =
      (a + b) ^ 2 - t ^ 2 * (4 * m * a * b + 1) := by
    dsimp [companion]
    ring
  nlinarith

lemma companion_coprime {m t a b : ℤ} (hc : IsCoprime a b) :
    IsCoprime (companion m t a b) a := by
  rcases hc with ⟨u, v, huv⟩
  refine ⟨-v, u + v * (4 * m * t ^ 2 - 2), ?_⟩
  dsimp [companion]
  linear_combination huv

lemma companion_sum_dvd {m t a b : ℤ} (hdiv : t ∣ a + b) :
    t ∣ companion m t a b + a := by
  rcases hdiv with ⟨q, hq⟩
  refine ⟨4 * m * t * a - q, ?_⟩
  dsimp [companion]
  nlinarith [hq]

/-- The strict bound valid at every positive ordered auxiliary shape. -/
lemma norm_large_coordinate {m t a b : ℤ}
    (hm : 0 < m) (ha : 0 < a) (hab : a ≤ b)
    (hnorm : (a + b) ^ 2 = t ^ 2 * (4 * m * a * b + 1)) :
    a * t ^ 2 < b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hm1 : 0 ≤ m - 1 := by omega
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hnonneg : 0 ≤ a * (b - a) * (3 * b + a) +
      4 * (m - 1) * a * b ^ 2 := by positivity
  have hgap : 0 < b * (4 * m * a * b + 1) - a * (a + b) ^ 2 := by
    nlinarith [hnonneg]
  have hmul := congrArg (fun z : ℤ => a * z) hnorm
  have hfactor : 0 < 4 * m * a * b + 1 := by positivity
  have hprod : 0 < (b - a * t ^ 2) * (4 * m * a * b + 1) := by
    nlinarith [hmul]
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hfactor).mp hprod)

/-- The Vieta step is positive and strictly reduces the smaller coordinate. -/
lemma companion_bounds {m t a b : ℤ}
    (ht : 0 < t) (hat : t < a) (hab : a ≤ b)
    (hnorm : (a + b) ^ 2 = t ^ 2 * (4 * m * a * b + 1)) :
    0 < companion m t a b ∧ companion m t a b < a := by
  have ha : 0 < a := lt_trans ht hat
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hp := companion_product hnorm
  have hnum : 0 < a ^ 2 - t ^ 2 := by nlinarith
  have hpos : 0 < companion m t a b :=
    (mul_pos_iff_of_pos_left hb).mp (hp.symm ▸ hnum)
  constructor
  · exact hpos
  · by_contra h
    have hca : a ≤ companion m t a b := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (le_of_lt hpos),
      mul_nonneg (le_of_lt ha) (sub_nonneg.mpr hca)]

/-- At a terminal pair, positivity and coprimality force `t = 1`. -/
lemma terminal_t_one {m t a b : ℤ}
    (hm : 0 < m) (ht : 0 < t) (ha : 0 < a) (hab : a ≤ b)
    (hat : a ≤ t) (hc : IsCoprime a b) (hdiv : t ∣ a + b)
    (hnorm : (a + b) ^ 2 = t ^ 2 * (4 * m * a * b + 1)) :
    t = 1 := by
  have hlarge := norm_large_coordinate hm ha hab hnorm
  have hsq : 0 ≤ t ^ 2 - a ^ 2 := by nlinarith
  have hsmall : t ^ 2 - a ^ 2 < b := by
    have ha1 : 1 ≤ a := by omega
    nlinarith [sq_nonneg t, mul_nonneg (sub_nonneg.mpr ha1) (sq_nonneg t)]
  have hzero : t ^ 2 - a ^ 2 = 0 :=
    Int.eq_zero_of_dvd_of_nonneg_of_lt hsq hsmall
      ⟨-companion m t a b, by nlinarith [companion_product hnorm]⟩
  have hat' : a = t := by nlinarith
  rcases hc with ⟨u, v, huv⟩
  rcases hdiv with ⟨q, hq⟩
  have hdvd : t ∣ 1 := by
    refine ⟨u + v * (q - 1), ?_⟩
    rw [hat'] at huv hq
    linear_combination -huv + v * hq
  have := Int.le_of_dvd (by norm_num : (0 : ℤ) < 1) hdvd
  omega

/-- Strong induction on the smaller positive coordinate completes the descent. -/
theorem norm_t_one_aux (m t : ℤ) (hm : 0 < m) (ht : 0 < t) :
    ∀ n : ℕ, ∀ a b : ℤ, a.toNat = n → 0 < a → a ≤ b →
      IsCoprime a b → t ∣ a + b →
      (a + b) ^ 2 = t ^ 2 * (4 * m * a * b + 1) → t = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b han ha hab hc hdiv hnorm
    by_cases hat : a ≤ t
    · exact terminal_t_one hm ht ha hab hat hc hdiv hnorm
    · have hbounds := companion_bounds ht (lt_of_not_ge hat) hab hnorm
      exact ih (companion m t a b).toNat (by omega)
        (companion m t a b) a rfl hbounds.1 (le_of_lt hbounds.2)
        (companion_coprime hc) (companion_sum_dvd hdiv) (companion_norm hnorm)

/-- The positive coprime norm shapes arising from the gate all have `t = 1`. -/
theorem norm_t_one {m t a b : ℤ}
    (hm : 0 < m) (ht : 0 < t) (ha : 0 < a) (hab : a ≤ b)
    (hc : IsCoprime a b) (hdiv : t ∣ a + b)
    (hnorm : (a + b) ^ 2 = t ^ 2 * (4 * m * a * b + 1)) : t = 1 :=
  norm_t_one_aux m t hm ht a.toNat a b rfl ha hab hc hdiv hnorm

/-- Bridge-facing form using the integer gcd. -/
theorem norm_t_one_gcd {m t a b : ℤ}
    (hm : 0 < m) (ht : 0 < t) (ha : 0 < a) (hab : a ≤ b)
    (hc : Int.gcd a b = 1) (hdiv : t ∣ a + b)
    (hnorm : (a + b) ^ 2 = t ^ 2 * (4 * m * a * b + 1)) : t = 1 :=
  norm_t_one hm ht ha hab (Int.isCoprime_iff_gcd_eq_one.mpr hc) hdiv hnorm

/-- The difference of the coordinates is `1 mod 4`; proved by a second descent. -/
theorem norm_difference_mod_four_aux (m : ℤ) (_hm : 0 < m) :
    ∀ n : ℕ, ∀ a b : ℤ, a.toNat = n → 0 < a → a ≤ b →
      (a + b) ^ 2 = 4 * m * a * b + 1 → (b - a) % 4 = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b han ha hab hnorm
    by_cases ha1 : a ≤ 1
    · have haeq : a = 1 := by omega
      subst a
      have hb : 0 < b := by omega
      have hp : b * (b - (4 * m - 2)) = 0 := by nlinarith [hnorm]
      have hbform : b = 4 * m - 2 := by
        rcases mul_eq_zero.mp hp with h | h
        · omega
        · omega
      rw [hbform]
      omega
    · have hnorm' : (a + b) ^ 2 = (1 : ℤ) ^ 2 * (4 * m * a * b + 1) := by
        simpa using hnorm
      have hbounds := companion_bounds (by norm_num : (0 : ℤ) < 1)
        (lt_of_not_ge ha1) hab hnorm'
      have hprev : (a - companion m 1 a b) % 4 = 1 :=
        ih (companion m 1 a b).toNat (by omega)
          (companion m 1 a b) a rfl hbounds.1 (le_of_lt hbounds.2)
          (by simpa using companion_norm hnorm')
      have hid : b - a = (a - companion m 1 a b) + 4 * ((m - 1) * a) := by
        dsimp [companion]
        ring
      rw [hid, Int.add_emod]
      simp [hprev]

theorem norm_difference_mod_four {m a b : ℤ}
    (hm : 0 < m) (ha : 0 < a) (hab : a ≤ b)
    (hnorm : (a + b) ^ 2 = 4 * m * a * b + 1) : (b - a) % 4 = 1 :=
  norm_difference_mod_four_aux m hm a.toNat a b rfl ha hab hnorm

/-- The original `d = 3 mod 4` condition selects an odd smaller coordinate. -/
theorem norm_delta_odd {m t a b : ℤ}
    (hm : 0 < m) (ht : 0 < t) (ha : 0 < a) (hab : a ≤ b)
    (hc : Int.gcd a b = 1) (hdiv : t ∣ a + b)
    (hnorm : (a + b) ^ 2 = t ^ 2 * (4 * m * a * b + 1))
    (hsum : (a + b) % 4 = 3) : a % 2 = 1 := by
  have ht1 := norm_t_one_gcd hm ht ha hab hc hdiv hnorm
  have hnorm1 : (a + b) ^ 2 = 4 * m * a * b + 1 := by simpa [ht1] using hnorm
  have hdiff := norm_difference_mod_four hm ha hab hnorm1
  omega

/-- A dyadic odd integer is `1`. -/
lemma dyadic_odd_eq_one {a : ℤ} (hodd : a % 2 = 1)
    (hdyadic : ∃ j : ℕ, a = 2 ^ j) : a = 1 := by
  obtain ⟨j, rfl⟩ := hdyadic
  cases j with
  | zero => simp
  | succ j =>
    rw [pow_succ] at hodd
    omega

/-- The norm gate cannot give a new old-ineligible dyadic source. -/
theorem dyadic_no_rescue {m t a b k : ℤ}
    (hm : 0 < m) (ht : 0 < t) (ha : 0 < a) (hab : a ≤ b)
    (hc : Int.gcd a b = 1) (hdiv : t ∣ a + b)
    (hnorm : (a + b) ^ 2 = t ^ 2 * (4 * m * a * b + 1))
    (hsum : (a + b) % 4 = 3) (hdyadic : ∃ j : ℕ, a = 2 ^ j) :
    a = 1 ∧ t = 1 ∧ a * t ∣ k := by
  have ht1 := norm_t_one_gcd hm ht ha hab hc hdiv hnorm
  have ha1 := dyadic_odd_eq_one
    (norm_delta_odd hm ht ha hab hc hdiv hnorm hsum) hdyadic
  exact ⟨ha1, ht1, by simp [ha1, ht1]⟩

/-- The bridge-facing restriction, with the residue condition on the original `d`. -/
theorem norm_shape_restriction {m t a b d : ℤ}
    (hm : 0 < m) (ht : 0 < t) (ha : 0 < a) (hab : a ≤ b)
    (hc : IsCoprime a b) (he : d * t = a + b)
    (hnorm : (a + b) ^ 2 = t ^ 2 * (4 * m * a * b + 1))
    (hd : d % 4 = 3) : t = 1 ∧ a % 2 = 1 := by
  have hdiv : t ∣ a + b := ⟨d, by nlinarith [he]⟩
  have ht1 := norm_t_one hm ht ha hab hc hdiv hnorm
  have hsum : (a + b) % 4 = 3 := by
    rw [← he, ht1, mul_one]
    exact hd
  exact ⟨ht1, norm_delta_odd hm ht ha hab
    (Int.isCoprime_iff_gcd_eq_one.mp hc) hdiv hnorm hsum⟩

/-- Original-shape version: no B4-eligible dyadic source fails the B1 gate. -/
theorem dyadic_no_rescue_from_d {m t a b d k : ℤ}
    (hm : 0 < m) (ht : 0 < t) (ha : 0 < a) (hab : a ≤ b)
    (hc : IsCoprime a b) (he : d * t = a + b)
    (hnorm : (a + b) ^ 2 = t ^ 2 * (4 * m * a * b + 1))
    (hd : d % 4 = 3) (hdyadic : ∃ j : ℕ, a = 2 ^ j) :
    a = 1 ∧ t = 1 ∧ a * t ∣ k := by
  have hr := norm_shape_restriction hm ht ha hab hc he hnorm hd
  have ha1 := dyadic_odd_eq_one hr.2 hdyadic
  exact ⟨ha1, hr.1, by simp [ha1, hr.1]⟩

/-- The ordered-pair recurrence, starting at `(1, 4m−2)`. -/
def shapePair (m : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 4 * m - 2)
  | n + 1 => let q := shapePair m n; (q.2, (4 * m - 2) * q.2 - q.1)

lemma recurrence_step_norm {m a b : ℤ}
    (hnorm : (a + b) ^ 2 = 4 * m * a * b + 1) :
    (b + ((4 * m - 2) * b - a)) ^ 2 =
      4 * m * b * ((4 * m - 2) * b - a) + 1 := by
  have hid :
      (b + ((4 * m - 2) * b - a)) ^ 2 -
        (4 * m * b * ((4 * m - 2) * b - a) + 1) =
      (a + b) ^ 2 - (4 * m * a * b + 1) := by ring
  nlinarith

/-- Every recurrence pair is positive, strictly ordered, and solves the norm. -/
theorem shapePair_valid {m : ℤ} (hm : 0 < m) (n : ℕ) :
    0 < (shapePair m n).1 ∧
    (shapePair m n).1 < (shapePair m n).2 ∧
    ((shapePair m n).1 + (shapePair m n).2) ^ 2 =
      4 * m * (shapePair m n).1 * (shapePair m n).2 + 1 := by
  induction n with
  | zero =>
    simp only [shapePair]
    constructor
    · norm_num
    constructor
    · omega
    · ring
  | succ n ih =>
    simp only [shapePair]
    obtain ⟨ha, hab, hnorm⟩ := ih
    constructor
    · linarith
    constructor
    · have hm1 : 0 ≤ m - 1 := by omega
      have hb : 0 ≤ (shapePair m n).2 := by linarith
      nlinarith [mul_nonneg hm1 hb]
    · exact recurrence_step_norm hnorm

/-- Completeness of the recurrence, by Vieta descent. -/
theorem norm_recurrence_complete_aux (m : ℤ) (_hm : 0 < m) :
    ∀ n : ℕ, ∀ a b : ℤ, a.toNat = n → 0 < a → a ≤ b →
      (a + b) ^ 2 = 4 * m * a * b + 1 →
      ∃ j : ℕ, shapePair m j = (a, b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b han ha hab hnorm
    by_cases ha1 : a ≤ 1
    · have haeq : a = 1 := by omega
      subst a
      have hb : 0 < b := by omega
      have hp : b * (b - (4 * m - 2)) = 0 := by nlinarith [hnorm]
      have hbform : b = 4 * m - 2 := by
        rcases mul_eq_zero.mp hp with h | h
        · omega
        · omega
      exact ⟨0, by simp [shapePair, hbform]⟩
    · have hnorm' : (a + b) ^ 2 = (1 : ℤ) ^ 2 * (4 * m * a * b + 1) := by
        simpa using hnorm
      have hbounds := companion_bounds (by norm_num : (0 : ℤ) < 1)
        (lt_of_not_ge ha1) hab hnorm'
      obtain ⟨j, hj⟩ := ih (companion m 1 a b).toNat (by omega)
        (companion m 1 a b) a rfl hbounds.1 (le_of_lt hbounds.2)
        (by simpa using companion_norm hnorm')
      refine ⟨j + 1, ?_⟩
      simp only [shapePair, hj]
      apply Prod.ext
      · rfl
      · dsimp [companion]
        ring

theorem norm_recurrence_complete {m a b : ℤ}
    (hm : 0 < m) (ha : 0 < a) (hab : a ≤ b)
    (hnorm : (a + b) ^ 2 = 4 * m * a * b + 1) :
    ∃ n : ℕ, shapePair m n = (a, b) :=
  norm_recurrence_complete_aux m hm a.toNat a b rfl ha hab hnorm

/-- Exact modular cycle `(1,2),(2,3),(3,0),(0,1)`. -/
theorem shapePair_mod_four (m : ℤ) (n : ℕ) :
    (shapePair m n).1 % 4 = ((n : ℤ) + 1) % 4 ∧
    (shapePair m n).2 % 4 = ((n : ℤ) + 2) % 4 := by
  induction n with
  | zero => simp [shapePair]; omega
  | succ n ih =>
    simp only [shapePair, Nat.cast_add, Nat.cast_one]
    constructor
    · simpa [add_assoc] using ih.2
    · have hid : (4 * m - 2) * (shapePair m n).2 - (shapePair m n).1 =
          4 * (m * (shapePair m n).2) -
          2 * (shapePair m n).2 - (shapePair m n).1 := by ring
      rw [hid]
      omega

/-- The original `d = 3 mod 4` constraint selects exactly even recurrence indices. -/
theorem shapePair_allowed_iff_even (m : ℤ) (n : ℕ) :
    ((shapePair m n).1 + (shapePair m n).2) % 4 = 3 ↔ n % 2 = 0 := by
  have h := shapePair_mod_four m n
  omega

/-- Source-level B4 restriction: the norm parameter is derived from the gate. -/
theorem b4_source_restriction {p k a r b t : ℤ}
    (h : ESBridge.TypeII p a r b t) (hp : p = 4 * k + 1)
    (hgate : 4 * a * b ∣ (4 * a * r * b - p) ^ 2 - 1) :
    t = 1 ∧ a % 2 = 1 := by
  obtain ⟨hd, he, _, _⟩ := ESBridge.b4_parameters h hp
  obtain ⟨m, hm, hnorm⟩ :=
    ESBridge.b4_gate_norm h.delta_pos h.s_pos hd he hgate
  exact norm_shape_restriction hm h.t_pos h.delta_pos h.ordered h.coprime he hnorm
    (ESBridge.b4_d_mod_four h hp)

/-- An actual normalized dyadic source passing B4 already passes B1. -/
theorem b4_dyadic_no_rescue {p k a r b t : ℤ}
    (h : ESBridge.TypeII p a r b t) (hp : p = 4 * k + 1)
    (hgate : 4 * a * b ∣ (4 * a * r * b - p) ^ 2 - 1)
    (hdyadic : ∃ j : ℕ, a = 2 ^ j) :
    a = 1 ∧ t = 1 ∧ a * t ∣ k := by
  have hr := b4_source_restriction h hp hgate
  have ha1 := dyadic_odd_eq_one hr.2 hdyadic
  exact ⟨ha1, hr.1, by simp [ha1, hr.1]⟩

/-- Shared natural-number API; the gate is stated in integers to avoid subtraction truncation. -/
theorem normalizedII_b4_dyadic_no_rescue {p k a r b t : ℕ}
    (h : ES.NormalizedII p a r b t) (hp : p = 4 * k + 1)
    (hgate : 4 * (a : ℤ) * b ∣ (4 * (a : ℤ) * r * b - p) ^ 2 - 1)
    (hdyadic : ES.Dyadic a) : a = 1 ∧ t = 1 ∧ a * t ∣ k := by
  have hp' : (p : ℤ) = 4 * k + 1 := by exact_mod_cast hp
  have hdyadic' : ∃ j : ℕ, (a : ℤ) = 2 ^ j := by
    obtain ⟨j, hj⟩ := hdyadic
    exact ⟨j, by exact_mod_cast hj⟩
  exact_mod_cast b4_dyadic_no_rescue (ESBridge.of_normalizedII h) hp' hgate hdyadic'

/-- Every B4-eligible dyadic source returns to exactly its B1 endpoint. -/
theorem b4_dyadic_endpoints_equal {p k a r b t d C : ℤ}
    (h : ESBridge.TypeII p a r b t) (hp : p = 4 * k + 1)
    (hgate : 4 * a * b ∣ (4 * a * r * b - p) ^ 2 - 1)
    (hdyadic : ∃ j : ℕ, a = 2 ^ j)
    (hpd : p + d = 4 * a * r * b) (hC : 4 * C = p * d + 1) :
    ((t : ℚ) * C / b, (t : ℚ) * C / a, (p : ℚ) * C) =
      (((k + a * r * t : ℤ) : ℚ),
        ((k + a * r * t : ℤ) : ℚ) * b / t,
        (p : ℚ) * (k + a * r * t : ℤ) * b / a) := by
  obtain ⟨ha1, ht1, _⟩ := b4_dyadic_no_rescue h hp hgate hdyadic
  subst a
  subst t
  have he : d = 1 + b := by nlinarith [h.equation]
  have hs : (b : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt h.s_pos)
  have hp' : (p : ℚ) = 4 * k + 1 := by exact_mod_cast hp
  have he' : (d : ℚ) = 1 + b := by exact_mod_cast he
  have hd' : (p : ℚ) + d = 4 * r * b := by simpa using (show
      (p : ℚ) + d = 4 * 1 * r * b by exact_mod_cast hpd)
  have hC' : 4 * (C : ℚ) = p * d + 1 := by exact_mod_cast hC
  have hh := ESBridge.base_endpoints_equal hs hp' he' hd' hC'
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_one, one_mul, mul_one, div_one] using hh

end ESDescent

#print axioms ESDescent.norm_large_coordinate
#print axioms ESDescent.companion_bounds
#print axioms ESDescent.norm_t_one
#print axioms ESDescent.norm_t_one_gcd
#print axioms ESDescent.norm_difference_mod_four
#print axioms ESDescent.norm_delta_odd
#print axioms ESDescent.dyadic_no_rescue
#print axioms ESDescent.norm_shape_restriction
#print axioms ESDescent.dyadic_no_rescue_from_d
#print axioms ESDescent.shapePair_valid
#print axioms ESDescent.norm_recurrence_complete
#print axioms ESDescent.shapePair_mod_four
#print axioms ESDescent.shapePair_allowed_iff_even

#print axioms ESDescent.b4_source_restriction
#print axioms ESDescent.b4_dyadic_no_rescue
#print axioms ESDescent.normalizedII_b4_dyadic_no_rescue

#print axioms ESDescent.b4_dyadic_endpoints_equal
