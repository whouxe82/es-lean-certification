import ES.Basic

/-!
# Exact Type II bridges

The source assumptions are positive integral parameters, coprimality, and the
Type II equation. No existence of such parameters is asserted. B1 and B4
integrality are proved as equivalences, separately from the rational identities.
All integer variables below have type `ℤ`; positivity is always explicit.
-/
namespace ESBridge

/-- Positive rational Erdős–Straus equation. -/
def RationalES (p x y z : ℚ) : Prop :=
  0 < p ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧ 4 / p = 1 / x + 1 / y + 1 / z

/-- Positive integer Erdős–Straus equation in polynomial form. -/
def IntegerES (p x y z : ℤ) : Prop :=
  0 < p ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧ 4*x*y*z = p*(x*y+x*z+y*z)

/-- Being an integer is distinct from merely satisfying the rational equation. -/
def Integral (q : ℚ) : Prop := ∃ n : ℤ, q = n

/-- Normalized source; its existence is not claimed. -/
structure TypeII (p δ r s t : ℤ) : Prop where
  p_pos : 0 < p
  delta_pos : 0 < δ
  r_pos : 0 < r
  s_pos : 0 < s
  t_pos : 0 < t
  coprime : IsCoprime δ s
  ordered : δ ≤ s
  equation : 4*δ*r*s*t = p*t+δ+s

lemma rational_iff_polynomial {p x y z : ℚ}
    (hp : p ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    4 / p = 1 / x + 1 / y + 1 / z ↔
      4*x*y*z = p*(x*y+x*z+y*z) := by
  field_simp
  ring_nf

lemma integerES_iff_rationalES {p x y z : ℤ} :
    IntegerES p x y z ↔ RationalES p x y z := by
  unfold IntegerES RationalES
  constructor
  · rintro ⟨hp,hx,hy,hz,he⟩
    have hpq : (0:ℚ) < p := by exact_mod_cast hp
    have hxq : (0:ℚ) < x := by exact_mod_cast hx
    have hyq : (0:ℚ) < y := by exact_mod_cast hy
    have hzq : (0:ℚ) < z := by exact_mod_cast hz
    refine ⟨hpq,hxq,hyq,hzq,?_⟩
    apply (rational_iff_polynomial (ne_of_gt hpq) (ne_of_gt hxq)
      (ne_of_gt hyq) (ne_of_gt hzq)).mpr
    exact_mod_cast he
  · rintro ⟨hp,hx,hy,hz,he⟩
    refine ⟨by exact_mod_cast hp, by exact_mod_cast hx,
      by exact_mod_cast hy, by exact_mod_cast hz, ?_⟩
    have h := (rational_iff_polynomial (ne_of_gt hp) (ne_of_gt hx)
      (ne_of_gt hy) (ne_of_gt hz)).mp he
    exact_mod_cast h

lemma integral_div_iff {a b : ℤ} (hb : b ≠ 0) :
    Integral ((a:ℚ) / b) ↔ b ∣ a := by
  have hbq : (b:ℚ) ≠ 0 := by exact_mod_cast hb
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n, ?_⟩
    have h := (div_eq_iff hbq).mp hn
    exact_mod_cast (by nlinarith [h] : (a:ℚ) = b*n)
  · rintro ⟨n,hn⟩
    refine ⟨n, ?_⟩
    apply (div_eq_iff hbq).mpr
    exact_mod_cast (by nlinarith [hn] : a = n*b)

lemma TypeII.source {p δ r s t : ℤ} (h : TypeII p δ r s t) :
    IntegerES p (δ*r*s) (p*δ*r*t) (p*r*s*t) := by
  rcases h with ⟨hp,hδ,hr,hs,ht,hcop,hord,he⟩
  refine ⟨hp, by positivity, by positivity, by positivity, ?_⟩
  linear_combination p^2*δ*r^2*s*t * he

lemma TypeII.coprime_delta_t {p δ r s t : ℤ} (h : TypeII p δ r s t) :
    IsCoprime δ t := by
  rcases h.coprime with ⟨a,b,hb⟩
  refine ⟨a-b, b*(4*δ*r*s-p), ?_⟩
  linear_combination hb + b*h.equation

lemma TypeII.coprime_s_t {p δ r s t : ℤ} (h : TypeII p δ r s t) :
    IsCoprime s t := by
  rcases h.coprime with ⟨a,b,hb⟩
  refine ⟨b-a, a*(4*δ*r*s-p), ?_⟩
  linear_combination hb + a*h.equation

lemma TypeII.coprime_delta_p {p δ r s t : ℤ} (h : TypeII p δ r s t) :
    IsCoprime δ p := by
  rcases h.coprime with ⟨a,b,hb⟩
  refine ⟨a+b*(4*r*s*t-1), -b*t, ?_⟩
  linear_combination hb + b*h.equation

/-- Exact B1 integrality gate; no additional unproved unit assumptions. -/
theorem b1_gate {p k δ r s t : ℤ} (h : TypeII p δ r s t) :
    (t ∣ (k+δ*r*t)*s ∧ δ ∣ p*(k+δ*r*t)*s) ↔ δ*t ∣ k := by
  let X := k+δ*r*t
  have hdt : IsCoprime δ t := h.coprime_delta_t
  have hts : IsCoprime t s := h.coprime_s_t.symm
  have hdps : IsCoprime δ (p*s) := h.coprime_delta_p.mul_right h.coprime
  have hmul : δ*t ∣ δ*r*t := ⟨r, by ring⟩
  constructor
  · rintro ⟨ht,hd⟩
    have htX : t ∣ X := hts.dvd_of_dvd_mul_right ht
    have hdX : δ ∣ X := hdps.dvd_of_dvd_mul_right (by convert hd using 1 <;> ring)
    have hX := hdt.mul_dvd hdX htX
    have hh := dvd_sub hX hmul
    simpa [X] using hh
  · intro hk
    have hX : δ*t ∣ X := dvd_add hk hmul
    have htX : t ∣ X := dvd_trans (dvd_mul_left t δ) hX
    have hdX : δ ∣ X := dvd_trans (dvd_mul_right δ t) hX
    exact ⟨dvd_mul_of_dvd_left htX s,
      by convert dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hdX s) p using 1 <;> ring⟩

/-- B1's rational endpoint is integral exactly on its gate. -/
theorem b1_rational_integral_iff {p k δ r s t : ℤ} (h : TypeII p δ r s t) :
    (Integral (((k+δ*r*t:ℤ):ℚ)*s/t) ∧
     Integral ((p:ℚ)*(k+δ*r*t:ℤ)*s/δ)) ↔ δ*t ∣ k := by
  have ht : t ≠ 0 := ne_of_gt h.t_pos
  have hd : δ ≠ 0 := ne_of_gt h.delta_pos
  have h1 := integral_div_iff (a := (k+δ*r*t)*s) ht
  have h2 := integral_div_iff (a := p*(k+δ*r*t)*s) hd
  push_cast at h1 h2 ⊢
  rw [h1,h2]
  exact b1_gate h

/-- Polynomial B1 identity with the source relation retained as a premise. -/
lemma b1_polynomial {p k δ r s t : ℚ}
    (hp : p = 4*k+1) (h : 4*δ*r*s*t = p*t+δ+s) :
    4*(k+δ*r*t)*s = δ+p*t+p*s := by
  linear_combination h - s*hp

/-- Full positive rational B1 endpoint. -/
theorem b1_rational {p k δ r s t : ℤ} (h : TypeII p δ r s t)
    (hk : 0 ≤ k) (hp : p = 4*k+1) :
    RationalES p (k+δ*r*t:ℤ)
      (((k+δ*r*t:ℤ):ℚ)*s/t) ((p:ℚ)*(k+δ*r*t:ℤ)*s/δ) := by
  have hpq : (0:ℚ) < p := by exact_mod_cast h.p_pos
  have hdq : (0:ℚ) < δ := by exact_mod_cast h.delta_pos
  have hrq : (0:ℚ) < r := by exact_mod_cast h.r_pos
  have hsq : (0:ℚ) < s := by exact_mod_cast h.s_pos
  have htq : (0:ℚ) < t := by exact_mod_cast h.t_pos
  have hkq : (0:ℚ) ≤ k := by exact_mod_cast hk
  have hX : (0:ℚ) < (k+δ*r*t:ℤ) := by push_cast; positivity
  refine ⟨hpq,hX, by positivity, by positivity, ?_⟩
  have he : 4*(δ:ℚ)*r*s*t = (p:ℚ)*t+δ+s := by exact_mod_cast h.equation
  have hpp : (p:ℚ) = 4*k+1 := by exact_mod_cast hp
  have hb := b1_polynomial hpp he
  push_cast
  field_simp
  linear_combination (p:ℚ)*((k:ℚ)+δ*r*t)*s*hb

/-- Positive integer B1 endpoints exist exactly when the gate holds. -/
theorem b1_integer_return_iff {p k δ r s t : ℤ} (h : TypeII p δ r s t)
    (hk : 0 ≤ k) (hp : p=4*k+1) :
    (∃ y z : ℤ,
      ((k+δ*r*t:ℤ):ℚ)*s/t = y ∧
      (p:ℚ)*(k+δ*r*t:ℤ)*s/δ = z ∧
      IntegerES p (k+δ*r*t) y z) ↔ δ*t ∣ k := by
  constructor
  · rintro ⟨y,z,hy,hz,_⟩
    exact (b1_rational_integral_iff h).mp ⟨⟨y,hy⟩,⟨z,hz⟩⟩
  · intro hg
    obtain ⟨⟨y,hy⟩,⟨z,hz⟩⟩ := (b1_rational_integral_iff h).mpr hg
    refine ⟨y,z,hy,hz,?_⟩
    apply integerES_iff_rationalES.mpr
    have he := b1_rational h hk hp
    rwa [hy,hz] at he

/-- Exact B4 divisibility gate, before using coprimality. -/
theorem b4_gate_algebra {p δ r s d C : ℤ}
    (hp : p+d=4*δ*r*s) (hC : 4*C=p*d+1) :
    δ*s ∣ C ↔ 4*δ*s ∣ d^2-1 := by
  constructor
  · rintro ⟨q,hq⟩
    refine ⟨r*d-q, ?_⟩
    linear_combination d*hp + hC - 4*hq
  · rintro ⟨q,hq⟩
    refine ⟨r*d-q, ?_⟩
    have he : 4*(C-δ*s*(r*d-q))=0 := by
      linear_combination hC + d*hp - hq
    linarith

/-- The rational B4 endpoint has integer coordinates iff the stated gate holds. -/
theorem b4_rational_integral_iff {p δ r s t d C : ℤ}
    (h : TypeII p δ r s t) (hp : p+d=4*δ*r*s) (hC : 4*C=p*d+1) :
    (Integral ((t:ℚ)*C/s) ∧ Integral ((t:ℚ)*C/δ)) ↔
      4*δ*s ∣ d^2-1 := by
  have h1 := integral_div_iff (a := t*C) (ne_of_gt h.s_pos)
  have h2 := integral_div_iff (a := t*C) (ne_of_gt h.delta_pos)
  push_cast at h1 h2
  rw [h1,h2,← b4_gate_algebra hp hC]
  constructor
  · rintro ⟨hs,hd⟩
    exact h.coprime.mul_dvd
      (h.coprime_delta_t.dvd_of_dvd_mul_left hd)
      (h.coprime_s_t.dvd_of_dvd_mul_left hs)
  · intro hcs
    have hsC : s ∣ C := dvd_trans (dvd_mul_left s δ) hcs
    have hdC : δ ∣ C := dvd_trans (dvd_mul_right δ s) hcs
    exact ⟨dvd_mul_of_dvd_right hsC t, dvd_mul_of_dvd_right hdC t⟩

/-- Full B4 positive rational endpoint, independently of integral return. -/
theorem b4_rational {p δ r s t d C : ℤ}
    (h : TypeII p δ r s t) (hd : 0 < d)
    (he : d*t=δ+s) (hC : 4*C=p*d+1) :
    RationalES p ((t:ℚ)*C/s) ((t:ℚ)*C/δ) ((p:ℚ)*C) := by
  have hpq : (0:ℚ) < p := by exact_mod_cast h.p_pos
  have hdq : (0:ℚ) < δ := by exact_mod_cast h.delta_pos
  have hsq : (0:ℚ) < s := by exact_mod_cast h.s_pos
  have htq : (0:ℚ) < t := by exact_mod_cast h.t_pos
  have hCp : 0 < C := by nlinarith [h.p_pos]
  have hCq : (0:ℚ) < C := by exact_mod_cast hCp
  refine ⟨hpq,by positivity,by positivity,by positivity,?_⟩
  have heq : (d:ℚ)*t=δ+s := by exact_mod_cast he
  have hCeq : 4*(C:ℚ)=(p:ℚ)*d+1 := by exact_mod_cast hC
  field_simp
  linear_combination (p:ℚ)*C*t*hCeq + (p:ℚ)^2*C*heq

/-- The B4 integer-return theorem includes positivity and the ES equation. -/
theorem b4_integer_return_iff {p δ r s t d C : ℤ}
    (h : TypeII p δ r s t) (hd : 0 < d)
    (he : d*t=δ+s) (hp : p+d=4*δ*r*s) (hC : 4*C=p*d+1) :
    (∃ x y : ℤ, (t:ℚ)*C/s=x ∧ (t:ℚ)*C/δ=y ∧
      IntegerES p x y (p*C)) ↔ 4*δ*s ∣ d^2-1 := by
  constructor
  · rintro ⟨x,y,hx,hy,_⟩
    exact (b4_rational_integral_iff h hp hC).mp ⟨⟨x,hx⟩,⟨y,hy⟩⟩
  · intro hg
    obtain ⟨⟨x,hx⟩,⟨y,hy⟩⟩ := (b4_rational_integral_iff h hp hC).mpr hg
    refine ⟨x,y,hx,hy,?_⟩
    apply integerES_iff_rationalES.mpr
    have hh := b4_rational h hd he hC
    rw [hx,hy] at hh
    simpa using hh

/-- Integral formulas for the B4 auxiliary data, from every p=4k+1 source. -/
theorem b4_parameters {p k δ r s t : ℤ} (h : TypeII p δ r s t)
    (hp : p=4*k+1) :
    let d := 4*δ*r*s-p
    let C := p*δ*r*s-k*(p+1)
    3 ≤ d ∧ d*t=δ+s ∧ p+d=4*δ*r*s ∧ 4*C=p*d+1 := by
  dsimp
  have he : (4*δ*r*s-p)*t=δ+s := by linear_combination h.equation
  have hdpos : 0 < 4*δ*r*s-p := by
    by_contra hneg
    have hnon : 4*δ*r*s-p ≤ 0 := le_of_not_gt hneg
    have hh := mul_nonpos_of_nonpos_of_nonneg hnon (le_of_lt h.t_pos)
    linarith [h.delta_pos,h.s_pos]
  have hex : 4*δ*r*s-p = 4*(δ*r*s-k-1)+3 := by
    linear_combination -hp
  have hd3 : 3 ≤ 4*δ*r*s-p := by omega
  refine ⟨hd3,he,by ring,?_⟩
  linear_combination (p+1)*hp

/-- The gate supplies a positive norm parameter; no existence hypothesis is hidden. -/
theorem b4_gate_norm {δ s t d : ℤ}
    (hδ : 0 < δ) (hs : 0 < s) (hd : 3 ≤ d)
    (he : d*t=δ+s) (hg : 4*δ*s ∣ d^2-1) :
    ∃ m : ℤ, 0 < m ∧ (δ+s)^2=t^2*(4*m*δ*s+1) := by
  rcases hg with ⟨m,hm⟩
  have hds : 0 < 4*δ*s := by positivity
  have hmpos : 0 < m := by
    by_contra hnot
    have hmn : m ≤ 0 := le_of_not_gt hnot
    have : 4*δ*s*m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hds) hmn
    nlinarith
  refine ⟨m,hmpos,?_⟩
  calc
    (δ+s)^2 = (d*t)^2 := by rw [he]
    _ = t^2*(4*m*δ*s+1) := by nlinarith [congrArg (fun z : ℤ => t^2*z) hm]

/-- The ordered rational bridge, with no intervening coordinate permutation. -/
def bridge (p k : ℚ) (v : ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ :=
  ((v.2.1+p*k)/p, v.1*(v.2.1+p*k)/v.2.1,
    v.2.2*(v.2.1+p*k)/v.2.1)

/-- Every intermediate bridge point remains on the positive rational ES surface. -/
theorem bridge_preserves {p k x y z : ℚ} (h : RationalES p x y z)
    (hk : 0 ≤ k) (hpk : p=4*k+1) :
    let v := bridge p k (x,y,z)
    RationalES p v.1 v.2.1 v.2.2 := by
  rcases h with ⟨hp,hx,hy,hz,he⟩
  have hS : 0 < y+p*k := by positivity
  have hpoly := (rational_iff_polynomial (ne_of_gt hp) (ne_of_gt hx)
    (ne_of_gt hy) (ne_of_gt hz)).mp he
  dsimp [bridge, RationalES]
  refine ⟨hp,by positivity,by positivity,by positivity,?_⟩
  have hlin : 4*(y+p*k)*x*z = p*(p*x*z+y*z+y*x) := by
    linear_combination hpoly - p*x*z*hpk
  have hrec : 1/((y+p*k)/p)+1/(x*(y+p*k)/y)+1/(z*(y+p*k)/y)
      = (p*x*z+y*z+y*x)/((y+p*k)*x*z) := by
    field_simp [ne_of_gt hp,ne_of_gt hx,ne_of_gt hy,ne_of_gt hz,ne_of_gt hS]
    ring
  rw [hrec]
  apply (div_eq_div_iff (ne_of_gt hp) (by positivity)).mpr
  nlinarith only [hlin]

/-- B1 is one literal bridge step on the indicated source orientation. -/
theorem b1_single_iterate {p k δ r s t : ℚ}
    (hp : 0 < p) (hδ : 0 < δ) (hr : 0 < r) (ht : 0 < t) :
    bridge p k (δ*r*s,p*δ*r*t,p*r*s*t) =
      (k+δ*r*t,(k+δ*r*t)*s/t,p*(k+δ*r*t)*s/δ) := by
  ext <;> dsimp [bridge] <;>
    field_simp [ne_of_gt hp,ne_of_gt hδ,ne_of_gt hr,ne_of_gt ht] <;> ring

lemma bridge_two {p k x y z : ℚ} (hp : 0 < p) (hk : 0 ≤ k)
    (hx : 0 < x) (hy : 0 < y) :
    bridge p k (bridge p k (x,y,z)) =
      ((x*y+p*k*(x+y))/(p*y), (x*y+p*k*(x+y))/(p*x),
        z*(x*y+p*k*(x+y))/(x*y)) := by
  have hpk : 0 < y+p*k := by positivity
  ext <;> dsimp [bridge] <;>
    field_simp [ne_of_gt hp, ne_of_gt hx, ne_of_gt hy, ne_of_gt hpk] <;> ring

/-- Literal fourth iterate on arbitrary positive first two coordinates. -/
lemma bridge_four {p k x y z : ℚ} (hp : 0 < p) (hk : 0 ≤ k)
    (hx : 0 < x) (hy : 0 < y) :
    bridge p k (bridge p k (bridge p k (bridge p k (x,y,z)))) =
      ((x*y+p*k*(p+1)*(x+y))/(p^2*y),
       (x*y+p*k*(p+1)*(x+y))/(p^2*x),
        z*(x*y+p*k*(p+1)*(x+y))/(x*y)) := by
  have hF : 0 < x*y+p*k*(x+y) := by positivity
  rw [bridge_two hp hk hx hy]
  rw [bridge_two hp hk (div_pos hF (mul_pos hp hy))
    (div_pos hF (mul_pos hp hx))]
  ext <;> dsimp <;>
    field_simp [ne_of_gt hp, ne_of_gt hx, ne_of_gt hy, ne_of_gt hF] <;> ring

/-- The displayed B4 endpoint is the literal fourth iterate of the same map. -/
theorem b4_four_iterates {p k δ r s t d C : ℚ}
    (hp : 0 < p) (hk : 0 ≤ k) (hδ : 0 < δ) (hr : 0 < r)
    (hs : 0 < s) (ht : 0 < t) (hpk : p=4*k+1)
    (he : d*t=δ+s) (hd : p+d=4*δ*r*s) (hC : 4*C=p*d+1) :
    bridge p k (bridge p k (bridge p k
      (bridge p k (p*δ*r*t,p*r*s*t,δ*r*s)))) =
      (t*C/s,t*C/δ,p*C) := by
  rw [bridge_four hp hk (by positivity) (by positivity)]
  have hcoef : δ*r*s+k*(p+1)*d=p*C := by
    linear_combination -(1/4:ℚ)*hd - ((p+1)*d/4)*hpk - (p/4)*hC
  have hmain :
      (p*δ*r*t)*(p*r*s*t)+p*k*(p+1)*(p*δ*r*t+p*r*s*t)
      = p^3*r*t^2*C := by
    linear_combination p^2*r*t^2*hcoef - p^2*k*(p+1)*r*t*he
  ext <;> dsimp
  · rw [hmain]
    field_simp [ne_of_gt hp, ne_of_gt hr, ne_of_gt hs, ne_of_gt ht]
    ring
  · rw [hmain]
    field_simp [ne_of_gt hp, ne_of_gt hδ, ne_of_gt hr, ne_of_gt ht]
    ring
  · rw [hmain]
    field_simp [ne_of_gt hp, ne_of_gt hδ, ne_of_gt hr, ne_of_gt hs, ne_of_gt ht]
    ring

/-- Shared natural-number normalization gives the positive integer source data. -/
lemma of_normalizedII {p δ r s t : ℕ} (h : ES.NormalizedII p δ r s t) :
    TypeII p δ r s t := by
  rcases h with ⟨hp,hδ,hr,hs,ht,hcop,hord,he⟩
  refine ⟨by exact_mod_cast hp, by exact_mod_cast hδ, by exact_mod_cast hr,
    by exact_mod_cast hs, by exact_mod_cast ht, hcop.isCoprime,
    by exact_mod_cast hord, by exact_mod_cast he⟩

/-- The central source construction in the shared natural-number API. -/
theorem normalizedII_source {p δ r s t : ℕ} (h : ES.NormalizedII p δ r s t) :
    ES.IsSolution p (δ*r*s) (p*δ*r*t) (p*r*s*t) := by
  rcases (of_normalizedII h).source with ⟨_,hx,hy,hz,he⟩
  exact ⟨by exact_mod_cast hx, by exact_mod_cast hy, by exact_mod_cast hz,
    by exact_mod_cast he⟩

/-- Exact B1 gate in natural arithmetic, with all cancellation facts derived. -/
theorem normalizedII_b1_gate {p k δ r s t : ℕ} (h : ES.NormalizedII p δ r s t) :
    (t ∣ (k+δ*r*t)*s ∧ δ ∣ p*(k+δ*r*t)*s) ↔ δ*t ∣ k := by
  exact_mod_cast (b1_gate (k := (k:ℤ)) (of_normalizedII h))

lemma b4_d_mod_four {p k δ r s t : ℤ} (h : TypeII p δ r s t)
    (hp : p=4*k+1) : (4*δ*r*s-p) % 4 = 3 := by
  have hex : 4*δ*r*s-p = 4*(δ*r*s-k-1)+3 := by
    linear_combination -hp
  rw [hex]
  omega

/-- When δ=t=1, the two displayed rational endpoints coincide exactly. -/
theorem base_endpoints_equal {p k r s d C : ℚ} (hs : s ≠ 0)
    (hp : p=4*k+1) (he : d=1+s) (hd : p+d=4*r*s)
    (hC : 4*C=p*d+1) :
    (C/s,C,p*C) = (k+r,(k+r)*s,p*(k+r)*s) := by
  have hc : C=(k+r)*s := by
    linear_combination (1/4:ℚ)*hC + (1/4:ℚ)*hd +
      ((p-1)/4)*he + (s/4)*hp
  rw [hc]
  ext <;> field_simp <;> ring

/-- The opposite p-divisible source pivot can never meet its B1 gate. -/
theorem b1_other_pivot_impossible {p k δ r s t : ℤ}
    (h : TypeII p δ r s t) (hp : p=4*k+1) : ¬ s*t ∣ k := by
  rintro ⟨q,hq⟩
  have hs : 0 < s := h.s_pos
  obtain ⟨hd,he,_,_⟩ := b4_parameters h hp
  let a := δ*r-t*q
  have hda : 4*δ*r*s-p=4*s*a-1 := by
    dsimp [a]
    linear_combination -hp - 4*hq
  have ha : 1 ≤ a := by
    by_contra hh
    have han : a ≤ 0 := by omega
    have hh := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 4*s) han
    linarith
  have hs1 : 1 ≤ s := by linarith [h.s_pos]
  have ht1 : 1 ≤ t := by linarith [h.t_pos]
  have hda' : 4*s-1 ≤ 4*δ*r*s-p := by
    have hh := mul_nonneg (by positivity : 0 ≤ 4*s) (by linarith : 0 ≤ a-1)
    nlinarith
  have hdt : 4*δ*r*s-p ≤ (4*δ*r*s-p)*t := by
    have hh := mul_nonneg (by linarith : 0 ≤ 4*δ*r*s-p) (by linarith : 0 ≤ t-1)
    nlinarith
  linarith [h.ordered]

lemma TypeII.coprime_s_p {p δ r s t : ℤ} (h : TypeII p δ r s t) :
    IsCoprime s p := by
  rcases h.coprime with ⟨a,b,hb⟩
  refine ⟨b+a*(4*δ*r*t-1), -a*t, ?_⟩
  linear_combination hb + a*h.equation

/-- Exact arithmetic gate for choosing the other p-divisible source coordinate. -/
theorem b1_other_gate {p k δ r s t : ℤ} (h : TypeII p δ r s t) :
    (t ∣ (k+r*s*t)*δ ∧ s ∣ p*(k+r*s*t)*δ) ↔ s*t ∣ k := by
  let X := k+r*s*t
  have hst : IsCoprime s t := h.coprime_s_t
  have htd : IsCoprime t δ := h.coprime_delta_t.symm
  have hspd : IsCoprime s (p*δ) := h.coprime_s_p.mul_right h.coprime.symm
  have hmul : s*t ∣ r*s*t := ⟨r, by ring⟩
  constructor
  · rintro ⟨ht,hs⟩
    have htX : t ∣ X := htd.dvd_of_dvd_mul_right ht
    have hsX : s ∣ X := hspd.dvd_of_dvd_mul_right (by convert hs using 1 <;> ring)
    have hX := hst.mul_dvd hsX htX
    have hh := dvd_sub hX hmul
    simpa [X] using hh
  · intro hk
    have hX : s*t ∣ X := dvd_add hk hmul
    have htX : t ∣ X := dvd_trans (dvd_mul_left t s) hX
    have hsX : s ∣ X := dvd_trans (dvd_mul_right s t) hX
    exact ⟨dvd_mul_of_dvd_left htX δ,
      by convert dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hsX δ) p using 1 <;> ring⟩

/-- The complete source-coordinate bound, without a primality assumption. -/
theorem source_coordinate_bound {p k δ r s t : ℤ}
    (h : TypeII p δ r s t) (hp : p=4*k+1) :
    3*(δ*r*s) ≤ p+1 ∧ δ*r*s < p := by
  have hδ1 : 1 ≤ δ := by linarith [h.delta_pos]
  have hs1 : 1 ≤ s := by linarith [h.s_pos]
  have hr1 : 1 ≤ r := by linarith [h.r_pos]
  have ht1 : 1 ≤ t := by linarith [h.t_pos]
  have hds : δ+s ≤ δ*s+1 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ δ-1) (by linarith : 0 ≤ s-1)]
  have hprod : δ*s ≤ δ*r*s := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ δ*s) (by linarith : 0 ≤ r-1)]
  have hx : 1 ≤ δ*r*s := by
    have hh : 0 < δ*r*s := mul_pos (mul_pos h.delta_pos h.r_pos) h.s_pos
    omega
  obtain ⟨hd,he,_,_⟩ := b4_parameters h hp
  have hdt : 4*δ*r*s-p ≤ (4*δ*r*s-p)*t := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 4*δ*r*s-p)
      (by linarith : 0 ≤ t-1)]
  constructor <;> nlinarith

/-- Thus the displayed source has exactly two p-divisible coordinates. -/
theorem source_first_not_dvd {p k δ r s t : ℤ}
    (h : TypeII p δ r s t) (hp : p=4*k+1) : ¬ p ∣ δ*r*s := by
  intro hdvd
  have hx : 0 < δ*r*s := mul_pos (mul_pos h.delta_pos h.r_pos) h.s_pos
  have hle := Int.le_of_dvd hx hdvd
  linarith [(source_coordinate_bound h hp).2]

/-- B1's distinguished first coordinate lies strictly between p/4 and p/2. -/
theorem b1_first_interval {p k δ r s t : ℤ}
    (h : TypeII p δ r s t) (hp : p=4*k+1) :
    p < 4*(k+δ*r*t) ∧ 2*(k+δ*r*t) < p := by
  have hp0 := h.p_pos
  have hs0 := h.s_pos
  have hprod : 1 ≤ δ*r*t := by
    have hh : 0 < δ*r*t := mul_pos (mul_pos h.delta_pos h.r_pos) h.t_pos
    omega
  have hδr : 1 ≤ δ*r := by
    have hh := mul_pos h.delta_pos h.r_pos
    omega
  have hsp : s < p := by
    have hh := mul_nonneg (by linarith : 0 ≤ δ*r-1) (le_of_lt hs0)
    nlinarith [(source_coordinate_bound h hp).2]
  obtain ⟨hd,he,_,_⟩ := b4_parameters h hp
  have hdt : 3*t ≤ (4*δ*r*s-p)*t :=
    mul_le_mul_of_nonneg_right hd (le_of_lt h.t_pos)
  have hts : t ≤ s-1 := by linarith [h.ordered]
  have hpt : p*t ≤ p*(s-1) := mul_le_mul_of_nonneg_left hts (le_of_lt hp0)
  have hb : 4*(k+δ*r*t)*s=δ+p*t+p*s := by
    linear_combination h.equation - s*hp
  constructor
  · nlinarith
  · by_contra hh
    have hx : p ≤ 2*(k+δ*r*t) := le_of_not_gt hh
    have hm := mul_le_mul_of_nonneg_right hx (le_of_lt hs0)
    nlinarith [h.ordered]

#print axioms integerES_iff_rationalES
#print axioms TypeII.source
#print axioms b1_gate
#print axioms b1_rational_integral_iff
#print axioms b1_rational
#print axioms b1_integer_return_iff
#print axioms b4_gate_algebra
#print axioms b4_rational_integral_iff
#print axioms b4_rational
#print axioms b4_integer_return_iff
#print axioms b4_parameters
#print axioms b4_gate_norm
#print axioms bridge_preserves
#print axioms b1_single_iterate
#print axioms b4_four_iterates
#print axioms normalizedII_source
#print axioms normalizedII_b1_gate
#print axioms base_endpoints_equal
#print axioms b1_other_pivot_impossible
#print axioms b1_other_gate
#print axioms source_coordinate_bound
#print axioms source_first_not_dvd
#print axioms b1_first_interval
end ESBridge
