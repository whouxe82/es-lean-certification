import ES.Basic
import ES.Bridges

/-!
# Unrestricted orientation obstructions for the integer bridge

This module does NOT assert the full graph matching theorem. It works with
arbitrary positive natural ES triples, and isolates global facts needed for
that theorem. Arbitrary-source normalization, global edge classification, and the
complete permutation-quotient graph statement are handled in separate modules.
-/
namespace ES.Matching

/-- Denominator-cleared equations for the literal ordered rational bridge.
For positive source coordinates these equations have no extraneous solutions. -/
def ClearedBridge (p k x y z X Y Z : ℕ) : Prop :=
  p*X = y+p*k ∧ y*Y = x*(y+p*k) ∧ y*Z = z*(y+p*k)

/-- No positive integer ES triple has every denominator divisible by its input. -/
theorem not_all_divisible {p x y z : ℕ} (hp : 0 < p)
    (h : ES.IsSolution p x y z) : ¬(p ∣ x ∧ p ∣ y ∧ p ∣ z) := by
  rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩
  rcases h with ⟨hx, hy, hz, he⟩
  have ha : 0 < a := Nat.pos_of_mul_pos_left hx
  have hb : 0 < b := Nat.pos_of_mul_pos_left hy
  have hc : 0 < c := Nat.pos_of_mul_pos_left hz
  have he' : 4*a*b*c = a*b+a*c+b*c := by
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < p^3)
    calc
      p^3*(4*a*b*c) = 4*(p*a)*(p*b)*(p*c) := by ring
      _ = p*((p*a)*(p*b)+(p*a)*(p*c)+(p*b)*(p*c)) := he
      _ = p^3*(a*b+a*c+b*c) := by ring
  have hpos : 0 < a*b*c := by positivity
  have hab : a*b ≤ a*b*c := Nat.le_mul_of_pos_right _ hc
  have hac : a*c ≤ a*b*c := by nlinarith [Nat.le_mul_of_pos_left (a*c) hb]
  have hbc : b*c ≤ a*b*c := by nlinarith [Nat.le_mul_of_pos_left (b*c) ha]
  nlinarith [he']

/-- Every positive ES triple at a prime p>4 has a p-divisible denominator. -/
theorem at_least_one_divisible {p x y z : ℕ} (hp : p.Prime) (hp4 : 4 < p)
    (h : ES.IsSolution p x y z) : p ∣ x ∨ p ∣ y ∨ p ∣ z := by
  have hdiv : p ∣ 4*x*y*z := by rw [h.2.2.2]; exact dvd_mul_right p _
  have h4 : ¬p ∣ 4 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 4) hd
    omega
  rcases hp.dvd_mul.mp hdiv with hab | hz
  · rcases hp.dvd_mul.mp hab with ha | hy
    · exact Or.inl ((hp.dvd_mul.mp ha).resolve_left h4)
    · exact Or.inr (Or.inl hy)
  · exact Or.inr (Or.inr hz)

/-- Arbitrary prime-input solutions have exactly one or exactly two
p-divisible coordinates; this is not a canonical-parameter premise. -/
theorem typeI_or_typeII {p x y z : ℕ} (hp : p.Prime) (hp4 : 4 < p)
    (h : ES.IsSolution p x y z) :
    ((p ∣ x ∧ ¬p ∣ y ∧ ¬p ∣ z) ∨
      (¬p ∣ x ∧ p ∣ y ∧ ¬p ∣ z) ∨
      (¬p ∣ x ∧ ¬p ∣ y ∧ p ∣ z)) ∨
    ((p ∣ x ∧ p ∣ y ∧ ¬p ∣ z) ∨
      (p ∣ x ∧ ¬p ∣ y ∧ p ∣ z) ∨
      (¬p ∣ x ∧ p ∣ y ∧ p ∣ z)) := by
  have hsome := at_least_one_divisible hp hp4 h
  have hnot := not_all_divisible hp.pos h
  tauto

/-- Every integral bridge step must choose a p-divisible pivot y. -/
theorem pivot_divisible {p k x y z X Y Z : ℕ}
    (h : ClearedBridge p k x y z X Y Z) : p ∣ y := by
  have hh := congrArg (fun a : ℕ => a % p) h.1
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod,
    add_zero, Nat.mod_mod] at hh
  exact Nat.dvd_of_mod_eq_zero hh.symm

/-- Literal rational-map equality implies the cleared equations, with no
canonical-source assumptions. -/
theorem cleared_of_bridge_eq {p k x y z X Y Z : ℕ} (hp : 0 < p) (hy : 0 < y)
    (h : ESBridge.bridge (p:ℚ) k ((x:ℚ),(y:ℚ),(z:ℚ)) = ((X:ℚ),(Y:ℚ),(Z:ℚ))) :
    ClearedBridge p k x y z X Y Z := by
  have hpq : (p:ℚ) ≠ 0 := by positivity
  have hyq : (y:ℚ) ≠ 0 := by positivity
  have hX := congrArg Prod.fst h
  have hY := congrArg (fun v : ℚ × ℚ × ℚ => v.2.1) h
  have hZ := congrArg (fun v : ℚ × ℚ × ℚ => v.2.2) h
  dsimp [ESBridge.bridge] at hX hY hZ
  have eX := (div_eq_iff hpq).mp hX
  have eY := (div_eq_iff hyq).mp hY
  have eZ := (div_eq_iff hyq).mp hZ
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast (by linarith [eX] : (p:ℚ)*X=y+p*k)
  · exact_mod_cast (by linarith [eY] : (y:ℚ)*Y=x*(y+p*k))
  · exact_mod_cast (by linarith [eZ] : (y:ℚ)*Z=z*(y+p*k))

/-- At an arbitrary Type I source, choosing its unique p-divisible
coordinate cannot yield another positive integer ES vertex. No normal-form
parameterization is assumed. -/
theorem typeI_no_forward {p k x y z X Y Z : ℕ} (hp : p.Prime) (hp4 : 4 < p)
    (hpk : p = 4*k+1) (hs : ES.IsSolution p x y z)
    (hx : ¬p ∣ x) (hz : ¬p ∣ z) (ht : ES.IsSolution p X Y Z)
    (hb : ClearedBridge p k x y z X Y Z) : False := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases pivot_divisible hb with ⟨c, rfl⟩
  have he : 4*x*c*z = x*p*c+x*z+p*c*z := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc
      p*(4*x*c*z) = 4*x*(p*c)*z := by ring
      _ = p*(x*(p*c)+x*z+(p*c)*z) := hs.2.2.2
      _ = p*(x*p*c+x*z+p*c*z) := by ring
  have hx0 : (x:ZMod p) ≠ 0 := by
    intro hh
    exact hx ((ZMod.natCast_zmod_eq_zero_iff_dvd x p).mp hh)
  have hz0 : (z:ZMod p) ≠ 0 := by
    intro hh
    exact hz ((ZMod.natCast_zmod_eq_zero_iff_dvd z p).mp hh)
  have hr : (4:ZMod p)*x*c*z = x*z := by
    have hh := congrArg (fun a : ℕ => (a:ZMod p)) he
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_self,
      zero_mul, mul_zero, zero_add, add_zero] using hh
  have hc4 : (4:ZMod p)*c = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero hx0 hz0)
    calc
      ((x:ZMod p)*z)*(4*c) = 4*x*c*z := by ring
      _ = x*z := hr
      _ = ((x:ZMod p)*z)*1 := by ring
  have hc0 : (c:ZMod p) ≠ 0 := by
    intro hh
    simp only [hh, mul_zero, zero_ne_one] at hc4
  have hpk0 : (0:ZMod p) = 4*k+1 := by
    have hh := congrArg (fun a : ℕ => (a:ZMod p)) hpk
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_self,
      Nat.cast_one] using hh
  have hXeq : X = c+k := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc
      p*X = p*c+p*k := hb.1
      _ = p*(c+k) := by ring
  have h4 : (4:ZMod p) ≠ 0 := by
    intro hh
    have hd : p ∣ 4 := (ZMod.natCast_zmod_eq_zero_iff_dvd 4 p).mp hh
    have := Nat.le_of_dvd (by norm_num : 0 < 4) hd
    omega
  have hX4 : (4:ZMod p)*X = 0 := by
    rw [hXeq]
    push_cast
    linear_combination hc4 - hpk0
  have hX0 : (X:ZMod p) = 0 := (mul_eq_zero.mp hX4).resolve_left h4
  have hYeq : c*Y = x*X := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc
      p*(c*Y) = (p*c)*Y := by ring
      _ = x*(p*c+p*k) := hb.2.1
      _ = x*(p*X) := by rw [hb.1]
      _ = p*(x*X) := by ring
  have hZeq : c*Z = z*X := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc
      p*(c*Z) = (p*c)*Z := by ring
      _ = z*(p*c+p*k) := hb.2.2
      _ = z*(p*X) := by rw [hb.1]
      _ = p*(z*X) := by ring
  have hY0 : (Y:ZMod p) = 0 := by
    have hh := congrArg (fun a : ℕ => (a:ZMod p)) hYeq
    push_cast at hh
    rw [hX0, mul_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left hc0
  have hZ0 : (Z:ZMod p) = 0 := by
    have hh := congrArg (fun a : ℕ => (a:ZMod p)) hZeq
    push_cast at hh
    rw [hX0, mul_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left hc0
  exact not_all_divisible hp.pos ht
    ⟨(ZMod.natCast_zmod_eq_zero_iff_dvd X p).mp hX0,
     (ZMod.natCast_zmod_eq_zero_iff_dvd Y p).mp hY0,
     (ZMod.natCast_zmod_eq_zero_iff_dvd Z p).mp hZ0⟩

/-- The property of having exactly one p-divisible denominator is invariant
under permuting the displayed coordinates. -/
def IsTypeI (p x y z : ℕ) : Prop :=
  (p ∣ x ∧ ¬p ∣ y ∧ ¬p ∣ z) ∨
  (¬p ∣ x ∧ p ∣ y ∧ ¬p ∣ z) ∨
  (¬p ∣ x ∧ ¬p ∣ y ∧ p ∣ z)

theorem isTypeI_swap (p x y z : ℕ) : IsTypeI p x y z ↔ IsTypeI p y x z := by
  unfold IsTypeI
  tauto

theorem isTypeI_rotate (p x y z : ℕ) : IsTypeI p x y z ↔ IsTypeI p y z x := by
  unfold IsTypeI
  tauto

/-- No forward edge can start at any Type I vertex, in any orientation.
The input x,y,z is arbitrary and IsTypeI is permutation-invariant. -/
theorem typeI_no_outgoing {p k x y z X Y Z : ℕ} (hp : p.Prime)
    (hpk : p = 4*k+1) (hs : ES.IsSolution p x y z)
    (hI : IsTypeI p x y z) (ht : ES.IsSolution p X Y Z)
    (hb : ClearedBridge p k x y z X Y Z) : False := by
  have hp4 : 4 < p := by have := hp.two_le; omega
  have hy := pivot_divisible hb
  rcases hI with hI | hI | hI
  · exact hI.2.1 hy
  · exact typeI_no_forward hp hp4 hpk hs hI.1 hI.2.2 ht hb
  · exact hI.2.1 hy

/-- The same obstruction refers to literal rational-map equality, rather than
only a cleared equation encoding. -/
theorem typeI_no_literal_outgoing {p k x y z X Y Z : ℕ} (hp : p.Prime)
    (hpk : p = 4*k+1) (hs : ES.IsSolution p x y z)
    (hI : IsTypeI p x y z) (ht : ES.IsSolution p X Y Z) :
    ESBridge.bridge (p:ℚ) k ((x:ℚ),(y:ℚ),(z:ℚ)) ≠
      ((X:ℚ),(Y:ℚ),(Z:ℚ)) := by
  intro hb
  exact typeI_no_outgoing hp hpk hs hI ht (cleared_of_bridge_eq hp.pos hs.2.1 hb)

/-- Two denominators of one positive ES solution cannot both be below p/2.
This supplies the coordinate-uniqueness bound needed for incoming-edge arguments. -/
theorem not_two_small {p x y z : ℕ} (h : ES.IsSolution p x y z)
    (hx : 2*x < p) (hy : 2*y < p) : False := by
  have h1 := Nat.mul_lt_mul_of_pos_right hx (Nat.mul_pos h.2.1 h.2.2.1)
  have h2 := Nat.mul_lt_mul_of_pos_right hy (Nat.mul_pos h.1 h.2.2.1)
  nlinarith [h.2.2.2, Nat.zero_le (p*x*y)]

/-- The ordered rational inverse. No claim about preservation of integrality. -/
def inverseBridge (p k : ℚ) (v : ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ :=
  (v.2.1*(v.1-k)/v.1, p*(v.1-k), v.2.2*(v.1-k)/v.1)

theorem inverse_bridge {p k x y z : ℚ} (hp : 0 < p) (hk : 0 ≤ k) (hy : 0 < y) :
    inverseBridge p k (ESBridge.bridge p k (x,y,z)) = (x,y,z) := by
  have hsum : 0 < y+p*k := by positivity
  ext <;> dsimp [inverseBridge, ESBridge.bridge] <;>
    field_simp [ne_of_gt hp, ne_of_gt hy, ne_of_gt hsum] <;> ring

/-- The bridge has at most one ordered rational preimage among positive pivots.
This is ordered injectivity; the permutation-quotient statement is handled separately. -/
theorem ordered_preimage_unique {p k x y z a b c : ℚ}
    (hp : 0 < p) (hk : 0 ≤ k) (hy : 0 < y) (hb : 0 < b)
    (he : ESBridge.bridge p k (x,y,z) = ESBridge.bridge p k (a,b,c)) :
    (x,y,z) = (a,b,c) := by
  have hh := congrArg (inverseBridge p k) he
  rwa [inverse_bridge hp hk hy, inverse_bridge hp hk hb] at hh

#print axioms not_all_divisible
#print axioms at_least_one_divisible
#print axioms typeI_or_typeII
#print axioms pivot_divisible
#print axioms cleared_of_bridge_eq
#print axioms typeI_no_forward
#print axioms typeI_no_outgoing
#print axioms typeI_no_literal_outgoing
#print axioms not_two_small
#print axioms inverse_bridge
#print axioms ordered_preimage_unique

end ES.Matching
