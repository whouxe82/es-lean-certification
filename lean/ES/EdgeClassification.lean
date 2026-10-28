import ES.Pivot
import ES.Normalization

namespace ES.Matching

/-- The integrally returning pivot is the smaller p-divisible source denominator,
proved for arbitrary Type II solutions using actual gcd normalization. -/
theorem typeII_pivot_min_small {p k x y z X Y Z : ℕ} (hp : p.Prime)
    (hpk : p=4*k+1) (hs : ES.IsSolution p x y z)
    (hx : ¬p ∣ x) (hz : p ∣ z) (hb : ClearedBridge p k x y z X Y Z) :
    y ≤ z ∧ 2*X < p := by
  have hy := pivot_divisible hb
  by_cases hyz : y ≤ z
  · obtain ⟨δ,r,s,t,hn,hx',hy',hz'⟩ :=
      ESNormalization.normalize_typeII_denominators hp hx hy hz hyz hs
    refine ⟨hyz, ?_⟩
    apply normalized_first_small hn hpk
    simpa only [hx',hy',hz'] using hb
  · have hzy : z ≤ y := Nat.le_of_lt (lt_of_not_ge hyz)
    obtain ⟨δ,r,s,t,hn,hx',hz',hy'⟩ :=
      ESNormalization.normalize_typeII_denominators hp hx hz hy hzy (solution_last_swap hs)
    exact (normalized_other_no_outgoing hn hpk (by simpa only [hx',hy',hz'] using hb)).elim

lemma cleared_cancel_pivot {p k x c z X Y Z : ℕ} (hp : 0 < p)
    (hb : ClearedBridge p k x (p*c) z X Y Z) :
    X = c+k ∧ c*Y = x*X ∧ c*Z = z*X := by
  refine ⟨?_, ?_, ?_⟩
  · apply Nat.eq_of_mul_eq_mul_left hp
    calc
      p*X = p*c+p*k := hb.1
      _ = p*(c+k) := by ring
  · apply Nat.eq_of_mul_eq_mul_left hp
    calc
      p*(c*Y) = (p*c)*Y := by ring
      _ = x*(p*c+p*k) := hb.2.1
      _ = x*(p*X) := by rw [hb.1]
      _ = p*(x*X) := by ring
  · apply Nat.eq_of_mul_eq_mul_left hp
    calc
      p*(c*Z) = (p*c)*Z := by ring
      _ = z*(p*c+p*k) := hb.2.2
      _ = z*(p*X) := by rw [hb.1]
      _ = p*(z*X) := by ring

/-- Once the first target is below p/2, primality forces exactly the displayed
Type I target pattern. This is proved without canonical target parameters. -/
theorem target_typeI_right {p k x y z X Y Z : ℕ} (hp : p.Prime)
    (hs : ES.IsSolution p x y z) (ht : ES.IsSolution p X Y Z)
    (hx : ¬p ∣ x) (hz : p ∣ z) (hsmall : 2*X < p)
    (hb : ClearedBridge p k x y z X Y Z) : IsTypeI p X Y Z := by
  rcases pivot_divisible hb with ⟨c,rfl⟩
  obtain ⟨hX,hY,hZ⟩ := cleared_cancel_pivot hp.pos hb
  have hc : 0 < c := Nat.pos_of_mul_pos_left hs.2.1
  have hXp : ¬p ∣ X := by
    intro hd
    have := Nat.le_of_dvd ht.1 hd
    omega
  have hcp : ¬p ∣ c := by
    intro hd
    have := Nat.le_of_dvd hc hd
    omega
  have hYp : ¬p ∣ Y := by
    intro hd
    have he : p ∣ x*X := by
      rw [← hY]
      exact dvd_mul_of_dvd_right hd c
    exact (hp.dvd_mul.mp he).elim hx hXp
  have hZp : p ∣ Z := by
    have he : p ∣ c*Z := by
      rw [hZ]
      exact dvd_mul_of_dvd_left hz X
    exact (hp.dvd_mul.mp he).resolve_left hcp
  exact Or.inr (Or.inr ⟨hXp,hYp,hZp⟩)

/-- Global edge classification on arbitrary positive natural ES triples.
There is no unproved canonical-form premise: normalization is invoked inside
the proof. The theorem supplies the facts used by the permutation-quotient
matching argument. -/
theorem edge_properties {p k x y z X Y Z : ℕ} (hp : p.Prime)
    (hpk : p=4*k+1) (hs : ES.IsSolution p x y z) (ht : ES.IsSolution p X Y Z)
    (hb : ClearedBridge p k x y z X Y Z) :
    (p ∣ x → y ≤ x) ∧ (p ∣ z → y ≤ z) ∧ 2*X < p ∧ IsTypeI p X Y Z := by
  have hp4 : 4 < p := by have := hp.two_le; omega
  rcases typeI_or_typeII hp hp4 hs with hI | hII
  · exact (typeI_no_outgoing hp hpk hs hI ht hb).elim
  rcases hII with hII | hII | hII
  · obtain ⟨hmin,hsmall⟩ := typeII_pivot_min_small hp hpk (solution_outer_swap hs)
      hII.2.2 hII.1 hb.outer_swap
    have hIt := target_typeI_right hp (solution_outer_swap hs) (solution_last_swap ht)
      hII.2.2 hII.1 hsmall hb.outer_swap
    refine ⟨fun _ => hmin, fun hz => (hII.2.2 hz).elim, hsmall, ?_⟩
    unfold IsTypeI at hIt ⊢
    tauto
  · exact (hII.2.1 (pivot_divisible hb)).elim
  · obtain ⟨hmin,hsmall⟩ := typeII_pivot_min_small hp hpk hs hII.1 hII.2.2 hb
    exact ⟨fun hx => (hII.1 hx).elim, fun _ => hmin, hsmall,
      target_typeI_right hp hs ht hII.1 hII.2.2 hsmall hb⟩

/-- Clearing denominators is exact for positive p and pivot; the graph's
arithmetic edge encoding is precisely the literal rational bridge. -/
theorem bridge_eq_of_cleared {p k x y z X Y Z : ℕ} (hp : 0 < p) (hy : 0 < y)
    (hb : ClearedBridge p k x y z X Y Z) :
    ESBridge.bridge (p:ℚ) k ((x:ℚ),(y:ℚ),(z:ℚ)) =
      ((X:ℚ),(Y:ℚ),(Z:ℚ)) := by
  have hpq : (p:ℚ) ≠ 0 := by positivity
  have hyq : (y:ℚ) ≠ 0 := by positivity
  ext <;> dsimp [ESBridge.bridge]
  · apply (div_eq_iff hpq).mpr
    exact_mod_cast (by nlinarith [hb.1] : y+p*k=X*p)
  · apply (div_eq_iff hyq).mpr
    exact_mod_cast (by nlinarith [hb.2.1] : x*(y+p*k)=Y*y)
  · apply (div_eq_iff hyq).mpr
    exact_mod_cast (by nlinarith [hb.2.2] : z*(y+p*k)=Z*y)

theorem cleared_iff_bridge {p k x y z X Y Z : ℕ} (hp : 0 < p) (hy : 0 < y) :
    ClearedBridge p k x y z X Y Z ↔
      ESBridge.bridge (p:ℚ) k ((x:ℚ),(y:ℚ),(z:ℚ)) =
        ((X:ℚ),(Y:ℚ),(Z:ℚ)) :=
  ⟨bridge_eq_of_cleared hp hy, cleared_of_bridge_eq hp hy⟩

#print axioms typeII_pivot_min_small
#print axioms target_typeI_right
#print axioms edge_properties
#print axioms cleared_iff_bridge
end ES.Matching
