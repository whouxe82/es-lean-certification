import ES.Matching

namespace ES.Matching

lemma ClearedBridge.outer_swap {p k x y z X Y Z : ℕ}
    (h : ClearedBridge p k x y z X Y Z) : ClearedBridge p k z y x X Z Y :=
  ⟨h.1, h.2.2, h.2.1⟩

lemma solution_outer_swap {p x y z : ℕ} (h : ES.IsSolution p x y z) :
    ES.IsSolution p z y x := by
  refine ⟨h.2.2.1, h.2.1, h.1, ?_⟩
  nlinarith [h.2.2.2]

lemma solution_last_swap {p x y z : ℕ} (h : ES.IsSolution p x y z) :
    ES.IsSolution p x z y := by
  refine ⟨h.1, h.2.2.1, h.2.1, ?_⟩
  nlinarith [h.2.2.2]

lemma normalized_other_no_outgoing {p k δ r s t X Y Z : ℕ}
    (h : ES.NormalizedII p δ r s t) (hp : p=4*k+1)
    (hb : ClearedBridge p k (δ*r*s) (p*r*s*t) (p*δ*r*t) X Y Z) : False := by
  have hi := ESBridge.of_normalizedII h
  have hX : X = k+r*s*t := by
    apply Nat.eq_of_mul_eq_mul_left h.1
    calc
      p*X = p*r*s*t+p*k := hb.1
      _ = p*(k+r*s*t) := by ring
  have hY : t*Y = δ*X := by
    apply Nat.eq_of_mul_eq_mul_left (by rcases h with ⟨hp,hδ,hr,hs,ht,_⟩; positivity : 0 < p*r*s)
    calc
      (p*r*s)*(t*Y) = (p*r*s*t)*Y := by ring
      _ = (δ*r*s)*(p*r*s*t+p*k) := hb.2.1
      _ = (δ*r*s)*(p*X) := by rw [hb.1]
      _ = (p*r*s)*(δ*X) := by ring
  have hZ : s*Z = p*δ*X := by
    apply Nat.eq_of_mul_eq_mul_left (by rcases h with ⟨hp,hδ,hr,hs,ht,_⟩; positivity : 0 < p*r*t)
    calc
      (p*r*t)*(s*Z) = (p*r*s*t)*Z := by ring
      _ = (p*δ*r*t)*(p*r*s*t+p*k) := hb.2.2
      _ = (p*δ*r*t)*(p*X) := by rw [hb.1]
      _ = (p*r*t)*(p*δ*X) := by ring
  have hg : t ∣ (k+r*s*t)*δ ∧ s ∣ p*(k+r*s*t)*δ := by
    constructor
    · refine ⟨Y, ?_⟩
      rw [hY, hX]
      ring
    · refine ⟨Z, ?_⟩
      rw [hZ, hX]
      ring
  apply ESBridge.b1_other_pivot_impossible (k := (k:ℤ)) hi (by exact_mod_cast hp)
  apply (ESBridge.b1_other_gate (k := (k:ℤ)) hi).mp
  exact_mod_cast hg

lemma normalized_first_small {p k δ r s t X Y Z : ℕ}
    (h : ES.NormalizedII p δ r s t) (hp : p=4*k+1)
    (hb : ClearedBridge p k (δ*r*s) (p*δ*r*t) (p*r*s*t) X Y Z) : 2*X < p := by
  have hX : X = k+δ*r*t := by
    apply Nat.eq_of_mul_eq_mul_left h.1
    calc
      p*X = p*δ*r*t+p*k := hb.1
      _ = p*(k+δ*r*t) := by ring
  rw [hX]
  exact_mod_cast (ESBridge.b1_first_interval (k := (k:ℤ)) (ESBridge.of_normalizedII h)
    (by exact_mod_cast hp)).2

#print axioms normalized_other_no_outgoing
#print axioms normalized_first_small
end ES.Matching
