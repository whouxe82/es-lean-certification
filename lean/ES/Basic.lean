import Mathlib

namespace ES

/-- Positive natural denominators with the polynomial ES identity. -/
def IsSolution (n x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧
    4 * x * y * z = n * (x * y + x * z + y * z)

def Solvable (n : ℕ) : Prop := ∃ x y z, IsSolution n x y z

/-- This is a definition of the open conjecture, not a theorem asserting it. -/
def ErdosStraus : Prop := ∀ n : ℕ, 2 ≤ n → Solvable n

def NormalizedII (p δ r s t : ℕ) : Prop :=
  0 < p ∧ 0 < δ ∧ 0 < r ∧ 0 < s ∧ 0 < t ∧
  δ.Coprime s ∧ δ ≤ s ∧
  4 * δ * r * s * t = p * t + δ + s

def Dyadic (δ : ℕ) : Prop := ∃ j : ℕ, δ = 2 ^ j

/-- Open dyadic existence hypothesis. -/
def HD : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 →
    ∃ δ r s t, NormalizedII p δ r s t ∧ Dyadic δ

/-- Quadratic nonresidue: the residue class has no square root. -/
def Nonresidue (p x : ℕ) : Prop := ¬ IsSquare (x : ZMod p)

/-- Open negative-character existence hypothesis. -/
def HN : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 →
    ∃ x y z, IsSolution p x y z ∧ p < 4 * x ∧
      4 * x < 3 * p ∧ Nonresidue p x

theorem isSolution_scale {n x y z k : ℕ}
    (h : IsSolution n x y z) (hk : 0 < k) :
    IsSolution (k*n) (k*x) (k*y) (k*z) := by
  rcases h with ⟨hx, hy, hz, he⟩
  refine ⟨Nat.mul_pos hk hx, Nat.mul_pos hk hy, Nat.mul_pos hk hz, ?_⟩
  calc
    4 * (k*x) * (k*y) * (k*z) = k^3 * (4*x*y*z) := by ring
    _ = k^3 * (n*(x*y+x*z+y*z)) := by rw [he]
    _ = (k*n) * ((k*x)*(k*y)+(k*x)*(k*z)+(k*y)*(k*z)) := by ring

theorem isSolution_unitFraction {n x y z : ℕ}
    (h : IsSolution n x y z) (hn : 0 < n) :
    (4 : ℚ) / n = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  rcases h with ⟨hx, hy, hz, he⟩
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hx' : (x : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hx)
  have hy' : (y : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hy)
  have hz' : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz)
  have he' : (4 : ℚ)*x*y*z = (n : ℚ)*(x*y+x*z+y*z) := by exact_mod_cast he
  field_simp
  nlinarith [he']

#print axioms isSolution_scale
#print axioms isSolution_unitFraction

theorem NormalizedII.isSolution {p δ r s t : ℕ}
    (h : NormalizedII p δ r s t) :
    IsSolution p (δ*r*s) (p*δ*r*t) (p*r*s*t) := by
  rcases h with ⟨hp,hδ,hr,hs,ht,_,_,he⟩
  refine ⟨by positivity, by positivity, by positivity, ?_⟩
  calc
    4*(δ*r*s)*(p*δ*r*t)*(p*r*s*t) =
      (p*p*δ*r*r*s*t)*(4*δ*r*s*t) := by ring
    _ = (p*p*δ*r*r*s*t)*(p*t+δ+s) := by rw [he]
    _ = p*((δ*r*s)*(p*δ*r*t)+(δ*r*s)*(p*r*s*t)+
      (p*δ*r*t)*(p*r*s*t)) := by ring

theorem erdosStraus_iff_primes :
    ErdosStraus ↔ ∀ p : ℕ, p.Prime → Solvable p := by
  constructor
  · intro h p hp
    exact h p hp.two_le
  · intro h n hn
    obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    obtain ⟨k,hk⟩ := hpd
    have hkpos : 0 < k := by
      by_contra hh
      have : k = 0 := by omega
      simp [this] at hk
      omega
    obtain ⟨x,y,z,hxyz⟩ := h p hp
    refine ⟨k*x,k*y,k*z,?_⟩
    simpa [hk, Nat.mul_comm] using isSolution_scale hxyz hkpos

theorem solvable_two : Solvable 2 := by
  exact ⟨1,2,2,by norm_num [IsSolution]⟩

theorem solvable_three_mod_four (k : ℕ) :
    Solvable (4*k+3) := by
  refine ⟨k+1,2*(4*k+3)*(k+1),2*(4*k+3)*(k+1),?_⟩
  refine ⟨by omega,by positivity,by positivity,?_⟩
  ring

#print axioms NormalizedII.isSolution
#print axioms erdosStraus_iff_primes
#print axioms solvable_two
#print axioms solvable_three_mod_four

theorem one_mod_four_suffices
    (h : ∀ p : ℕ, p.Prime → p % 4 = 1 → Solvable p) :
    ErdosStraus := by
  apply erdosStraus_iff_primes.mpr
  intro p hp
  rcases hp.eq_two_or_odd with htwo | hodd
  · subst p
    exact solvable_two
  · by_cases h1 : p % 4 = 1
    · exact h p hp h1
    · have h3 : p % 4 = 3 := by omega
      have he : p = 4 * (p / 4) + 3 := by omega
      rw [he]
      exact solvable_three_mod_four (p / 4)

/-- A conditional implication; this does not assert HD. -/
theorem hd_implies_es (h : HD) : ErdosStraus := by
  apply one_mod_four_suffices
  intro p hp hm
  obtain ⟨δ,r,s,t,hn,_⟩ := h p hp hm
  exact ⟨δ*r*s,p*δ*r*t,p*r*s*t,hn.isSolution⟩

/-- A conditional implication; this does not assert HN. -/
theorem hn_implies_es (h : HN) : ErdosStraus := by
  apply one_mod_four_suffices
  intro p hp hm
  obtain ⟨x,y,z,he,_,_,_⟩ := h p hp hm
  exact ⟨x,y,z,he⟩

#print axioms one_mod_four_suffices
#print axioms hd_implies_es
#print axioms hn_implies_es

end ES
