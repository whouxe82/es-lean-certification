import ES.EdgeClassification

/-!
# The graph of all integral bridge orientations

Vertices are multisets of three positive integer ES denominators. An edge is
witnessed by arbitrary ordered listings of its source and target; consequently
all six coordinate orientations, with repetitions when coordinates coincide,
are included. This file separates a general graph combinator from the concrete
arithmetic edge-classification theorem used to instantiate it.
-/
namespace ES.MatchingGraph

/-- A denominator triple modulo permutation, retaining multiplicity. -/
def triple (x y z : ℕ) : Multiset ℕ := {x}+{y}+{z}

@[simp] lemma mem_triple {a x y z : ℕ} :
    a ∈ triple x y z ↔ a=x ∨ a=y ∨ a=z := by
  simp [triple, or_assoc]

/-- One arbitrary ordered integral bridge step between positive ES solutions. -/
structure Step (p k : ℕ) where
  x : ℕ
  y : ℕ
  z : ℕ
  X : ℕ
  Y : ℕ
  Z : ℕ
  source : ES.IsSolution p x y z
  target : ES.IsSolution p X Y Z
  cleared : ES.Matching.ClearedBridge p k x y z X Y Z

def Step.src {p k : ℕ} (e : Step p k) : Multiset ℕ := triple e.x e.y e.z
def Step.dst {p k : ℕ} (e : Step p k) : Multiset ℕ := triple e.X e.Y e.Z

/-- This relation quantifies over every ordering, rather than selecting one. -/
def Directed (p k : ℕ) (A B : Multiset ℕ) : Prop :=
  ∃ e : Step p k, e.src=A ∧ e.dst=B

/-- The undirected integral bridge graph, including inverse traversals. -/
def Adjacent (p k : ℕ) (A B : Multiset ℕ) : Prop :=
  Directed p k A B ∨ Directed p k B A

lemma pair_eq_cases {a b c d : ℕ}
    (h : ({a}+{b} : Multiset ℕ)={c}+{d}) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have ha : a=c ∨ a=d := by
    have hm : a ∈ ({a}+{b} : Multiset ℕ) := by simp
    rw [h] at hm
    simpa using hm
  rcases ha with hac | had
  · left
    refine ⟨hac,?_⟩
    rw [hac] at h
    have hh : ({b}:Multiset ℕ)={d} := add_left_cancel h
    simpa using hh
  · right
    refine ⟨had,?_⟩
    rw [had] at h
    have hh : ({d}+{b}:Multiset ℕ)={d}+{c} := by
      exact h.trans (add_comm _ _)
    have hh' : ({b}:Multiset ℕ)={c} := add_left_cancel hh
    simpa using hh'

lemma outer_pair_eq {x y z a b c : ℕ}
    (h : triple x y z=triple a b c) (hy : y=b) :
    ({x}+{z}:Multiset ℕ)={a}+{c} := by
  have hh : ({y}+({x}+{z}):Multiset ℕ)={y}+({a}+{c}) := by
    calc
      _ = triple x y z := by unfold triple; simp only [add_assoc,add_comm,add_left_comm]
      _ = triple a b c := h
      _ = _ := by unfold triple; rw [hy]; simp only [add_assoc,add_comm,add_left_comm]
  exact add_left_cancel hh

lemma tail_pair_eq {x y z a b c : ℕ}
    (h : triple x y z=triple a b c) (hx : x=a) :
    ({y}+{z}:Multiset ℕ)={b}+{c} := by
  have hh : ({x}+({y}+{z}):Multiset ℕ)={x}+({b}+{c}) := by
    calc
      _ = triple x y z := by unfold triple; simp only [add_assoc,add_comm,add_left_comm]
      _ = triple a b c := h
      _ = _ := by unfold triple; rw [hx]; simp only [add_assoc,add_comm,add_left_comm]
  exact add_left_cancel hh

lemma solution_swap_last {p x y z : ℕ} (h : ES.IsSolution p x y z) :
    ES.IsSolution p x z y := by
  refine ⟨h.1,h.2.2.1,h.2.1,?_⟩
  nlinarith [h.2.2.2]

lemma small_coordinate_unique {p x y z a b c : ℕ}
    (ht : ES.IsSolution p a b c) (h : triple x y z=triple a b c)
    (hx : 2*x<p) (ha : 2*a<p) : x=a := by
  have hm : x ∈ triple a b c := by rw [←h]; simp
  rcases mem_triple.mp hm with he | he | he
  · exact he
  · subst x
    exact False.elim (ES.Matching.not_two_small ht ha hx)
  · subst x
    exact False.elim (ES.Matching.not_two_small (solution_swap_last ht) ha hx)

lemma isTypeI_iff_filter_card (p x y z : ℕ) :
    ES.Matching.IsTypeI p x y z ↔
      ((triple x y z).filter (fun a => p ∣ a)).card=1 := by
  by_cases hx : p ∣ x <;> by_cases hy : p ∣ y <;> by_cases hz : p ∣ z <;>
    simp [ES.Matching.IsTypeI,triple,Multiset.filter_singleton,hx,hy,hz]

lemma isTypeI_of_same_triple {p x y z a b c : ℕ}
    (h : triple x y z=triple a b c) (ht : ES.Matching.IsTypeI p x y z) :
    ES.Matching.IsTypeI p a b c := by
  rw [isTypeI_iff_filter_card] at ht ⊢
  rwa [←h]

/-- Pivot equality plus a common source multiset determines the target multiset. -/
lemma target_eq_of_same_pivot {p k : ℕ} (hp : 0<p) (e f : Step p k)
    (hs : e.src=f.src) (hy : e.y=f.y) : e.dst=f.dst := by
  have hX : e.X=f.X := by
    apply Nat.eq_of_mul_eq_mul_left hp
    rw [e.cleared.1,f.cleared.1,hy]
  have hpair := outer_pair_eq hs hy
  rcases pair_eq_cases hpair with ⟨hx,hz⟩ | ⟨hx,hz⟩
  · have hY : e.Y=f.Y := by
      apply Nat.eq_of_mul_eq_mul_left e.source.2.1
      calc
        e.y*e.Y = e.x*(e.y+p*k) := e.cleared.2.1
        _ = f.x*(f.y+p*k) := by rw [hx,hy]
        _ = f.y*f.Y := f.cleared.2.1.symm
        _ = e.y*f.Y := by rw [hy]
    have hZ : e.Z=f.Z := by
      apply Nat.eq_of_mul_eq_mul_left e.source.2.1
      calc
        e.y*e.Z = e.z*(e.y+p*k) := e.cleared.2.2
        _ = f.z*(f.y+p*k) := by rw [hz,hy]
        _ = f.y*f.Z := f.cleared.2.2.symm
        _ = e.y*f.Z := by rw [hy]
    simp only [Step.dst,triple,hX,hY,hZ]
  · have hY : e.Y=f.Z := by
      apply Nat.eq_of_mul_eq_mul_left e.source.2.1
      calc
        e.y*e.Y = e.x*(e.y+p*k) := e.cleared.2.1
        _ = f.z*(f.y+p*k) := by rw [hx,hy]
        _ = f.y*f.Z := f.cleared.2.2.symm
        _ = e.y*f.Z := by rw [hy]
    have hZ : e.Z=f.Y := by
      apply Nat.eq_of_mul_eq_mul_left e.source.2.1
      calc
        e.y*e.Z = e.z*(e.y+p*k) := e.cleared.2.2
        _ = f.x*(f.y+p*k) := by rw [hz,hy]
        _ = f.y*f.Y := f.cleared.2.1.symm
        _ = e.y*f.Y := by rw [hy]
    simp only [Step.dst,triple,hX,hY,hZ]
    simp only [add_assoc,add_comm,add_left_comm]

/-- A common target and the distinguished first coordinate determine the source
multiset, including the possible interchange of the two other coordinates. -/
lemma source_eq_of_same_first {p k : ℕ} (e f : Step p k)
    (ht : e.dst=f.dst) (hX : e.X=f.X) : e.src=f.src := by
  have hy : e.y=f.y := by
    have he := e.cleared.1
    have hf := f.cleared.1
    rw [hX] at he
    omega
  have hpos : 0 < e.y+p*k := by have := e.source.2.1; positivity
  have hpair := tail_pair_eq ht hX
  rcases pair_eq_cases hpair with ⟨hY,hZ⟩ | ⟨hY,hZ⟩
  · have hx : e.x=f.x := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc
        e.x*(e.y+p*k) = e.y*e.Y := e.cleared.2.1.symm
        _ = f.y*f.Y := by rw [hy,hY]
        _ = f.x*(f.y+p*k) := f.cleared.2.1
        _ = f.x*(e.y+p*k) := by rw [hy]
    have hz : e.z=f.z := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc
        e.z*(e.y+p*k) = e.y*e.Z := e.cleared.2.2.symm
        _ = f.y*f.Z := by rw [hy,hZ]
        _ = f.z*(f.y+p*k) := f.cleared.2.2
        _ = f.z*(e.y+p*k) := by rw [hy]
    simp only [Step.src,triple,hx,hy,hz]
  · have hx : e.x=f.z := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc
        e.x*(e.y+p*k) = e.y*e.Y := e.cleared.2.1.symm
        _ = f.y*f.Z := by rw [hy,hY]
        _ = f.z*(f.y+p*k) := f.cleared.2.2
        _ = f.z*(e.y+p*k) := by rw [hy]
    have hz : e.z=f.x := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc
        e.z*(e.y+p*k) = e.y*e.Z := e.cleared.2.2.symm
        _ = f.y*f.Y := by rw [hy,hZ]
        _ = f.x*(f.y+p*k) := f.cleared.2.1
        _ = f.x*(e.y+p*k) := by rw [hy]
    simp only [Step.src,triple,hx,hy,hz]
    simp only [add_assoc,add_comm,add_left_comm]

/-- Explicit arithmetic properties needed by the generic graph combinator. -/
def EdgeProperties (p k : ℕ) : Prop := ∀ e : Step p k,
  (p ∣ e.x → e.y≤e.x) ∧ (p ∣ e.z → e.y≤e.z) ∧
  2*e.X<p ∧ ES.Matching.IsTypeI p e.X e.Y e.Z

lemma pivot_minimum {p k : ℕ} (H : EdgeProperties p k) (e : Step p k)
    {a : ℕ} (ha : a ∈ e.src) (hd : p ∣ a) : e.y≤a := by
  rcases mem_triple.mp ha with hx | hy | hz
  · subst a; exact (H e).1 hd
  · subst a; exact le_rfl
  · subst a; exact (H e).2.1 hd

lemma outgoing_unique_of_properties {p k : ℕ} (hp : 0<p) (H : EdgeProperties p k)
    {A B C : Multiset ℕ} (he : Directed p k A B) (hf : Directed p k A C) : B=C := by
  obtain ⟨e,hes,het⟩ := he
  obtain ⟨f,hfs,hft⟩ := hf
  have hs : e.src=f.src := hes.trans hfs.symm
  have hfy : f.y ∈ e.src := by rw [hs]; simp [Step.src]
  have hey : e.y ∈ f.src := by rw [←hs]; simp [Step.src]
  have hy : e.y=f.y := le_antisymm
    (pivot_minimum H e hfy (ES.Matching.pivot_divisible f.cleared))
    (pivot_minimum H f hey (ES.Matching.pivot_divisible e.cleared))
  exact het.symm.trans ((target_eq_of_same_pivot hp e f hs hy).trans hft)

lemma incoming_unique_of_properties {p k : ℕ} (H : EdgeProperties p k)
    {A B C : Multiset ℕ} (he : Directed p k B A) (hf : Directed p k C A) : B=C := by
  obtain ⟨e,hes,het⟩ := he
  obtain ⟨f,hfs,hft⟩ := hf
  have ht : e.dst=f.dst := het.trans hft.symm
  have hX : e.X=f.X := small_coordinate_unique f.target ht (H e).2.2.1 (H f).2.2.1
  exact hes.symm.trans ((source_eq_of_same_first e f ht hX).trans hfs)

lemma no_two_steps_of_properties {p k : ℕ} (hp : p.Prime) (hpk : p=4*k+1)
    (H : EdgeProperties p k) {A B C : Multiset ℕ}
    (he : Directed p k A B) (hf : Directed p k B C) : False := by
  obtain ⟨e,hes,het⟩ := he
  obtain ⟨f,hfs,hft⟩ := hf
  have hmid : e.dst=f.src := het.trans hfs.symm
  have hfI : ES.Matching.IsTypeI p f.x f.y f.z :=
    isTypeI_of_same_triple hmid (H e).2.2.2
  exact ES.Matching.typeI_no_outgoing hp hpk f.source hfI f.target f.cleared

/-- Generic combination theorem; its arithmetic properties are explicit
hypotheses here and must be discharged for the concrete graph theorem. -/
theorem degree_at_most_one_of_properties {p k : ℕ} (hp : p.Prime) (hpk : p=4*k+1)
    (H : EdgeProperties p k) {A B C : Multiset ℕ}
    (he : Adjacent p k A B) (hf : Adjacent p k A C) : B=C := by
  rcases he with he | he <;> rcases hf with hf | hf
  · exact outgoing_unique_of_properties hp.pos H he hf
  · exact False.elim (no_two_steps_of_properties hp hpk H hf he)
  · exact False.elim (no_two_steps_of_properties hp hpk H he hf)
  · exact incoming_unique_of_properties H he hf

/-- The concrete arithmetic classifier discharges every hypothesis of the
combinator, for every ordered integral edge at the given prime. -/
theorem edge_properties {p k : ℕ} (hp : p.Prime) (hpk : p=4*k+1) :
    EdgeProperties p k := by
  intro e
  exact ES.Matching.edge_properties hp hpk e.source e.target e.cleared

/-- FULL all-orientation graph matching theorem: every multiset vertex has at
most one distinct adjacent vertex. No normalization or existence premise is
assumed; the only input restrictions are primality and p=4k+1. -/
theorem degree_at_most_one {p k : ℕ} (hp : p.Prime) (hpk : p=4*k+1)
    {A B C : Multiset ℕ} (he : Adjacent p k A B) (hf : Adjacent p k A C) : B=C :=
  degree_at_most_one_of_properties hp hpk (edge_properties hp hpk) he hf

/-- The graph has no self-loops. -/
theorem no_self_edge {p k : ℕ} (hp : p.Prime) (hpk : p=4*k+1)
    (A : Multiset ℕ) : ¬Adjacent p k A A := by
  intro h
  rcases h with h | h <;>
    exact no_two_steps_of_properties hp hpk (edge_properties hp hpk) h h

lemma adjacent_symm {p k : ℕ} {A B : Multiset ℕ}
    (h : Adjacent p k A B) : Adjacent p k B A := h.symm

/-- Ambient multiset graph; multisets that are not positive ES triples are isolated. -/
def graph {p k : ℕ} (hp : p.Prime) (hpk : p=4*k+1) : SimpleGraph (Multiset ℕ) where
  Adj := Adjacent p k
  symm := by intro A B h; exact adjacent_symm h
  loopless := no_self_edge hp hpk

/-- Formulation using Mathlib's SimpleGraph object. -/
theorem graph_neighbors_unique {p k : ℕ} (hp : p.Prime) (hpk : p=4*k+1)
    {A B C : Multiset ℕ} (he : (graph hp hpk).Adj A B)
    (hf : (graph hp hpk).Adj A C) : B=C := degree_at_most_one hp hpk he hf

/-- The same directed relation stated with the literal rational map. -/
def LiteralDirected (p k : ℕ) (A B : Multiset ℕ) : Prop :=
  ∃ x y z X Y Z : ℕ,
    ES.IsSolution p x y z ∧ ES.IsSolution p X Y Z ∧
    triple x y z=A ∧ triple X Y Z=B ∧
    ESBridge.bridge (p:ℚ) k ((x:ℚ),(y:ℚ),(z:ℚ))=
      ((X:ℚ),(Y:ℚ),(Z:ℚ))

/-- The all-orientation graph encoding has exactly the literal-map edges. -/
theorem directed_iff_literal {p k : ℕ} (hp : 0<p) (A B : Multiset ℕ) :
    Directed p k A B ↔ LiteralDirected p k A B := by
  constructor
  · rintro ⟨e,hA,hB⟩
    exact ⟨e.x,e.y,e.z,e.X,e.Y,e.Z,e.source,e.target,hA,hB,
      ES.Matching.bridge_eq_of_cleared hp e.source.2.1 e.cleared⟩
  · rintro ⟨x,y,z,X,Y,Z,hs,ht,hA,hB,hb⟩
    exact ⟨⟨x,y,z,X,Y,Z,hs,ht,
      ES.Matching.cleared_of_bridge_eq hp hs.2.1 hb⟩,hA,hB⟩

theorem adjacent_iff_literal {p k : ℕ} (hp : 0<p) (A B : Multiset ℕ) :
    Adjacent p k A B ↔ LiteralDirected p k A B ∨ LiteralDirected p k B A := by
  simp only [Adjacent,directed_iff_literal hp]

theorem no_directed_self {p k : ℕ} (hp : p.Prime) (hpk : p=4*k+1)
    (A : Multiset ℕ) : ¬Directed p k A A := by
  intro h
  exact no_self_edge hp hpk A (Or.inl h)

/-- Vertices of the actual ES graph, with precisely the positive solution
multisets and no additional ambient isolated multisets. -/
def Vertex (p : ℕ) := {A : Multiset ℕ //
  ∃ x y z : ℕ, ES.IsSolution p x y z ∧ A=triple x y z}

/-- The undirected integral bridge graph restricted to genuine ES vertices. -/
def solutionGraph {p k : ℕ} (hp : p.Prime) (hpk : p=4*k+1) :
    SimpleGraph (Vertex p) where
  Adj A B := Adjacent p k A.val B.val
  symm := by intro A B h; exact adjacent_symm h
  loopless := by intro A; exact no_self_edge hp hpk A.val

/-- Every genuine ES vertex has at most one neighbor under all integral bridge
orientations and inverse traversals. -/
theorem solutionGraph_neighbors_unique {p k : ℕ} (hp : p.Prime) (hpk : p=4*k+1)
    {A B C : Vertex p} (he : (solutionGraph hp hpk).Adj A B)
    (hf : (solutionGraph hp hpk).Adj A C) : B=C := by
  apply Subtype.ext
  exact degree_at_most_one hp hpk he hf

#print axioms target_eq_of_same_pivot
#print axioms source_eq_of_same_first
#print axioms degree_at_most_one_of_properties
#print axioms degree_at_most_one
#print axioms no_self_edge
#print axioms graph_neighbors_unique
#print axioms directed_iff_literal
#print axioms adjacent_iff_literal
#print axioms no_directed_self
#print axioms solutionGraph_neighbors_unique
end ES.MatchingGraph
