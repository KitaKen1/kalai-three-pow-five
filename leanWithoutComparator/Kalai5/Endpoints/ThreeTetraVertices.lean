import Kalai5.Endpoints.RareRowRidges

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- With exactly three tetrahedra and otherwise square pyramids, each
vertex lies in zero or two tetrahedra. -/
theorem IsCSPolytope5.three_tetra_vertex_pattern
    {F A B C v : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hs : {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (4,6,4)} = {A,B,C})
    (htypes : ∀ T ∈ faces P, T ⊆ F → dim T = 3 →
      tri3 P T = (4,6,4) ∨ tri3 P T = (5,8,5))
    (hv : v ∈ vset P F) :
    (v ⊆ A ∧ v ⊆ B ∧ ¬ v ⊆ C) ∨
    (v ⊆ A ∧ ¬ v ⊆ B ∧ v ⊆ C) ∨
    (¬ v ⊆ A ∧ v ⊆ B ∧ v ⊆ C) ∨
    (¬ v ⊆ A ∧ ¬ v ⊆ B ∧ ¬ v ⊆ C) := by
  have he : (((hP.below_finite F 3).toFinset.filter (fun T => v ⊆ T)).filter
      (fun T => tri3 P T = (4,6,4))) = ({A,B,C} : Finset (Set E5)).filter (fun T => v ⊆ T) := by
    ext T
    have ht : (T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (4,6,4)) ↔
        T = A ∨ T = B ∨ T = C := by
      change T ∈ {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (4,6,4)} ↔ _
      rw [hs]
      rfl
    simp only [Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_ofPred_eq,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hp := hP.tetra_through_even hF h4 hv.1 hv.2.2 htypes
  rw [he] at hp
  by_cases ha : v ⊆ A <;> by_cases hb : v ⊆ B <;> by_cases hc : v ⊆ C <;>
    simp [Finset.filter_insert,Finset.filter_singleton,ha,hb,hc,hAB,hAC,hBC] at hp ⊢

/-- The three tetrahedra use six vertices, with two vertices in every
pairwise intersection. -/
theorem IsCSPolytope5.three_tetra_vertex_counts
    {F A B C : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hs : {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (4,6,4)} = {A,B,C})
    (htypes : ∀ T ∈ faces P, T ⊆ F → dim T = 3 →
      tri3 P T = (4,6,4) ∨ tri3 P T = (5,8,5)) :
    (vset P A ∪ vset P B ∪ vset P C).ncard = 6 ∧
      (vset P A ∩ vset P B).ncard = 2 ∧
      (vset P A ∩ vset P C).ncard = 2 ∧
      (vset P B ∩ vset P C).ncard = 2 := by
  have hA : A ∈ faces P ∧ A ⊆ F ∧ dim A = 3 ∧ tri3 P A = (4,6,4) := by
    change A ∈ {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (4,6,4)}
    rw [hs]; exact Or.inl rfl
  have hB : B ∈ faces P ∧ B ⊆ F ∧ dim B = 3 ∧ tri3 P B = (4,6,4) := by
    change B ∈ {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (4,6,4)}
    rw [hs]; exact Or.inr (Or.inl rfl)
  have hC : C ∈ faces P ∧ C ⊆ F ∧ dim C = 3 ∧ tri3 P C = (4,6,4) := by
    change C ∈ {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (4,6,4)}
    rw [hs]; exact Or.inr (Or.inr rfl)
  have ha : (vset P A).ncard = 4 := congrArg Prod.fst hA.2.2.2
  have hb : (vset P B).ncard = 4 := congrArg Prod.fst hB.2.2.2
  have hc : (vset P C).ncard = 4 := congrArg Prod.fst hC.2.2.2
  have hpat := fun {v : Set E5} (hv : v ∈ vset P F) =>
    hP.three_tetra_vertex_pattern hF h4 hAB hAC hBC hs htypes hv
  have htri : (vset P A ∩ vset P B) ∩ vset P C = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    rintro v ⟨⟨hvA,hvB⟩,hvC⟩
    have hp := hpat (vset_mono' hA.2.1 hvA)
    have ha := hvA.2.1
    have hb := hvB.2.1
    have hc := hvC.2.1
    tauto
  have heA : (vset P A ∩ vset P B) ∪ (vset P A ∩ vset P C) = vset P A := by
    ext v
    constructor
    · exact fun h => h.elim And.left And.left
    · intro hvA
      have hp := hpat (vset_mono' hA.2.1 hvA)
      rcases hp with hp | hp | hp | hp
      · exact Or.inl ⟨hvA,⟨hvA.1,hp.2.1,hvA.2.2⟩⟩
      · exact Or.inr ⟨hvA,⟨hvA.1,hp.2.2,hvA.2.2⟩⟩
      · exact False.elim (hp.1 hvA.2.1)
      · exact False.elim (hp.1 hvA.2.1)
  have heB : (vset P A ∩ vset P B) ∪ (vset P B ∩ vset P C) = vset P B := by
    ext v
    constructor
    · exact fun h => h.elim And.right And.left
    · intro hvB
      have hp := hpat (vset_mono' hB.2.1 hvB)
      rcases hp with hp | hp | hp | hp
      · exact Or.inl ⟨⟨hvB.1,hp.1,hvB.2.2⟩,hvB⟩
      · exact False.elim (hp.2.1 hvB.2.1)
      · exact Or.inr ⟨hvB,⟨hvB.1,hp.2.2,hvB.2.2⟩⟩
      · exact False.elim (hp.2.1 hvB.2.1)
  have heC : (vset P A ∩ vset P C) ∪ (vset P B ∩ vset P C) = vset P C := by
    ext v
    constructor
    · exact fun h => h.elim And.right And.right
    · intro hvC
      have hp := hpat (vset_mono' hC.2.1 hvC)
      rcases hp with hp | hp | hp | hp
      · exact False.elim (hp.2.2 hvC.2.1)
      · exact Or.inl ⟨⟨hvC.1,hp.1,hvC.2.2⟩,hvC⟩
      · exact Or.inr ⟨⟨hvC.1,hp.2.1,hvC.2.2⟩,hvC⟩
      · exact False.elim (hp.2.2 hvC.2.1)
  have hd1 : Disjoint (vset P A ∩ vset P B) (vset P A ∩ vset P C) := by
    rw [Set.disjoint_left]
    exact fun v h1 h2 => (Set.eq_empty_iff_forall_notMem.1 htri v) ⟨h1,h2.2⟩
  have hd2 : Disjoint (vset P A ∩ vset P B) (vset P B ∩ vset P C) := by
    rw [Set.disjoint_left]
    exact fun v h1 h2 => (Set.eq_empty_iff_forall_notMem.1 htri v) ⟨h1,h2.2⟩
  have hd3 : Disjoint (vset P A ∩ vset P C) (vset P B ∩ vset P C) := by
    rw [Set.disjoint_left]
    exact fun v h1 h2 => (Set.eq_empty_iff_forall_notMem.1 htri v) ⟨⟨h1.1,h2.1⟩,h1.2⟩
  have c1 := Set.ncard_union_eq hd1 (hP.vset_finite A |>.inter_of_left _) (hP.vset_finite A |>.inter_of_left _)
  have c2 := Set.ncard_union_eq hd2 (hP.vset_finite A |>.inter_of_left _) (hP.vset_finite B |>.inter_of_left _)
  have c3 := Set.ncard_union_eq hd3 (hP.vset_finite A |>.inter_of_left _) (hP.vset_finite B |>.inter_of_left _)
  rw [heA,ha] at c1
  rw [heB,hb] at c2
  rw [heC,hc] at c3
  have hab : (vset P A ∩ vset P B).ncard = 2 := by omega
  have hac : (vset P A ∩ vset P C).ncard = 2 := by omega
  have hbc : (vset P B ∩ vset P C).ncard = 2 := by omega
  have hsub : vset P C ⊆ vset P A ∪ vset P B := by
    rw [← heC]; exact Set.union_subset
      (fun _ h => Or.inl h.1) (fun _ h => Or.inr h.1)
  have hsum := Set.ncard_union_add_ncard_inter (vset P A) (vset P B) (hP.vset_finite A) (hP.vset_finite B)
  rw [ha,hb,hab] at hsum
  exact ⟨by rw [Set.union_eq_left.2 hsub]; omega,hab,hac,hbc⟩

end Kalai5
