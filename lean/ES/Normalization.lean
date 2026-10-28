import ES.Bridges

/-!
# Normalization of arbitrary Type II prime-input solutions

This module derives the normalized source parameters from arbitrary positive
integer coordinates. No normal form is assumed in its hypotheses.
-/
namespace ESNormalization

/-- Cancel the prime factors from a Type II solution without subtraction. -/
lemma typeII_reduced_equation {p x a b : ℕ} (hp : 0 < p)
    (h : ES.IsSolution p x (p * a) (p * b)) :
    4 * x * a * b = p * a * b + x * (a + b) := by
  apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < p ^ 2)
  calc
    p ^ 2 * (4 * x * a * b) = 4 * x * (p * a) * (p * b) := by ring
    _ = p * (x * (p * a) + x * (p * b) + (p * a) * (p * b)) := h.2.2.2
    _ = p ^ 2 * (p * a * b + x * (a + b)) := by ring

/-- Arbitrary Type II solutions yield normalized positive source parameters. -/
theorem normalize_typeII {p x a b : ℕ} (hp : p.Prime) (hx : ¬p ∣ x)
    (ha : 0 < a) (hab : a ≤ b) (h : ES.IsSolution p x (p * a) (p * b)) :
    ∃ δ r s t : ℕ, ES.NormalizedII p δ r s t ∧
      x = δ * r * s ∧ a = δ * r * t ∧ b = r * s * t := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have he := typeII_reduced_equation hp.pos h
  obtain ⟨g, δ, s, hg, hcop, haeq, hbeq⟩ :=
    Nat.exists_coprime' (Nat.gcd_pos_of_pos_left b ha)
  have hδ : 0 < δ := Nat.pos_of_mul_pos_right (haeq ▸ ha)
  have hs : 0 < s := Nat.pos_of_mul_pos_right (hbeq ▸ hb)
  have hδs : 0 < δ * s := Nat.mul_pos hδ hs
  have hord : δ ≤ s := by
    apply Nat.le_of_mul_le_mul_left (c := g) _ hg
    simpa [haeq, hbeq, Nat.mul_comm] using hab
  have he1 : 4 * x * g * δ * s = p * g * δ * s + x * (δ + s) := by
    apply Nat.eq_of_mul_eq_mul_left hg
    calc
      g * (4 * x * g * δ * s) = 4 * x * a * b := by rw [haeq, hbeq]; ring
      _ = p * a * b + x * (a + b) := he
      _ = g * (p * g * δ * s + x * (δ + s)) := by rw [haeq, hbeq]; ring
  have hcop1 : (δ + s).Coprime δ := by simpa using hcop.symm
  have hcop2 : (δ + s).Coprime s := by simpa using hcop
  have hcSum : (δ * s).Coprime (δ + s) := (hcop1.mul_right hcop2).symm
  have hdleft : δ * s ∣ 4 * x * g * δ * s := ⟨4 * x * g, by ring⟩
  have hdterm : δ * s ∣ p * g * δ * s := ⟨p * g, by ring⟩
  rw [he1] at hdleft
  have hdsx : δ * s ∣ x :=
    hcSum.dvd_of_dvd_mul_right ((Nat.dvd_add_iff_right hdterm).mpr hdleft)
  obtain ⟨r, hrx⟩ := hdsx
  have hr : 0 < r := Nat.pos_of_mul_pos_left (hrx ▸ h.1)
  have hrdivx : r ∣ x := ⟨δ * s, by rw [hrx]; ring⟩
  have hrcop : r.Coprime p :=
    (hp.coprime_iff_not_dvd.mpr (fun hpr => hx (dvd_trans hpr hrdivx))).symm
  have he2 : 4 * r * g * δ * s = p * g + r * (δ + s) := by
    apply Nat.eq_of_mul_eq_mul_left hδs
    calc
      (δ * s) * (4 * r * g * δ * s) = 4 * x * g * δ * s := by rw [hrx]; ring
      _ = p * g * δ * s + x * (δ + s) := he1
      _ = (δ * s) * (p * g + r * (δ + s)) := by rw [hrx]; ring
  have hrleft : r ∣ 4 * r * g * δ * s := ⟨4 * g * δ * s, by ring⟩
  rw [he2] at hrleft
  have hrpg : r ∣ p * g :=
    (Nat.dvd_add_iff_left (dvd_mul_right r (δ + s))).mpr hrleft
  obtain ⟨t, hgt⟩ := hrcop.dvd_of_dvd_mul_left hrpg
  have ht : 0 < t := Nat.pos_of_mul_pos_left (hgt ▸ hg)
  have hnorm : 4 * δ * r * s * t = p * t + δ + s := by
    apply Nat.eq_of_mul_eq_mul_left hr
    calc
      r * (4 * δ * r * s * t) = 4 * r * g * δ * s := by rw [hgt]; ring
      _ = p * g + r * (δ + s) := he2
      _ = r * (p * t + δ + s) := by rw [hgt]; ring
  refine ⟨δ, r, s, t, ⟨hp.pos, hδ, hr, hs, ht, hcop, hord, hnorm⟩, ?_, ?_, ?_⟩
  · rw [hrx]
    ring
  · rw [haeq, hgt]
    ring
  · rw [hbeq, hgt]
    ring

/-- Normalize an arbitrary solution with its two p-divisible denominators ordered. -/
theorem normalize_typeII_denominators {p x y z : ℕ} (hp : p.Prime)
    (hx : ¬p ∣ x) (hy : p ∣ y) (hz : p ∣ z) (hyz : y ≤ z)
    (h : ES.IsSolution p x y z) :
    ∃ δ r s t : ℕ, ES.NormalizedII p δ r s t ∧
      x = δ * r * s ∧ y = p * δ * r * t ∧ z = p * r * s * t := by
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hz
  have ha : 0 < a := Nat.pos_of_mul_pos_left h.2.1
  have hab : a ≤ b := Nat.le_of_mul_le_mul_left hyz hp.pos
  obtain ⟨δ, r, s, t, hn, hx', ha', hb'⟩ := normalize_typeII hp hx ha hab h
  refine ⟨δ, r, s, t, hn, hx', ?_, ?_⟩
  · rw [ha']
    ring
  · rw [hb']
    ring

/-- The same genuine normalization gives the integer bridge structure directly. -/
theorem normalize_typeII_bridge {p x y z : ℕ} (hp : p.Prime)
    (hx : ¬p ∣ x) (hy : p ∣ y) (hz : p ∣ z) (hyz : y ≤ z)
    (h : ES.IsSolution p x y z) :
    ∃ δ r s t : ℕ, ESBridge.TypeII p δ r s t ∧
      x = δ * r * s ∧ y = p * δ * r * t ∧ z = p * r * s * t := by
  obtain ⟨δ, r, s, t, hn, hcoords⟩ := normalize_typeII_denominators hp hx hy hz hyz h
  exact ⟨δ, r, s, t, ESBridge.of_normalizedII hn, hcoords⟩

#print axioms typeII_reduced_equation
#print axioms normalize_typeII
#print axioms normalize_typeII_denominators
#print axioms normalize_typeII_bridge
end ESNormalization
