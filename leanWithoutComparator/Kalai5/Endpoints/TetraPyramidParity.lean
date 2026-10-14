import Kalai5.Endpoints.PyramidVertexDegree

/-!
# The parity obstruction for two tetrahedra and square pyramids

At a vertex, a tetrahedron contributes degree 3.  A square pyramid contributes
degree 4 minus its base incidence.  Quadrilateral base incidences occur twice,
and the vertex-figure degree sum is even.  Thus the number of tetrahedra through
each vertex is even.  If there are exactly two tetrahedra they have identical
vertex sets, contradicting that they are different faces.
-/

namespace Kalai5

open Set
open scoped Classical

noncomputable def quadAt (P F v : Set E5) : ℕ :=
  {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 2 ∧ cnt P Q 0 = 4 ∧ v ⊆ Q}.ncard

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.quadAt_le (F v : Set E5) : quadAt P F v ≤ q4 P F :=
  Set.ncard_le_ncard (fun Q hQ => ⟨hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2.1⟩)
    (hP.faces_finite.subset fun Q hQ => hQ.1)

lemma IsCSPolytope5.quadAt_eq_sum (F v : Set E5) :
    (quadAt P F v : ℤ) = ∑ Q ∈ (hP.below_finite F 2).toFinset,
      if cnt P Q 0 = 4 ∧ v ⊆ Q then (1 : ℤ) else 0 := by
  rw [Finset.sum_boole]
  congr 1
  rw [← Set.ncard_coe_finset]
  unfold quadAt
  congr 1
  ext Q
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  tauto

lemma IsCSPolytope5.quadAt_zero_of_not_subset {F v : Set E5} (hv : ¬ v ⊆ F) :
    quadAt P F v = 0 := by
  unfold quadAt
  have he : {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 2 ∧ cnt P Q 0 = 4 ∧ v ⊆ Q} = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro Q hQ
    exact hv (hQ.2.2.2.2.trans hQ.2.1)
  rw [he, Set.ncard_empty]

lemma IsCSPolytope5.quadAt_single {F Q : Set E5}
    (he : {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 2 ∧ cnt P Q 0 = 4} = {Q}) (v : Set E5) :
    quadAt P F v = if v ⊆ Q then 1 else 0 := by
  have hs : {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 2 ∧ cnt P Q 0 = 4 ∧ v ⊆ Q} =
      {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 2 ∧ cnt P Q 0 = 4} ∩ {Q | v ⊆ Q} := by
    ext Q
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  unfold quadAt
  rw [hs, he]
  by_cases h : v ⊆ Q <;> simp [h]

/-- Each quadrilateral through a vertex is counted in two 3-faces of a facet. -/
lemma IsCSPolytope5.sum_quadAt {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (v : Set E5) :
    ∑ T ∈ (hP.below_finite F 3).toFinset, (quadAt P T v : ℤ) = 2 * quadAt P F v := by
  rw [Finset.sum_congr rfl fun T _ => hP.quadAt_eq_sum T v,
    hP.sum_below_comm F 2 3 (fun Q => if cnt P Q 0 = 4 ∧ v ⊆ Q then (1 : ℤ) else 0),
    hP.quadAt_eq_sum F v, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [Set.Finite.mem_toFinset] at hQ
  rw [hP.twoface_in_facet hF h4 hQ.1 hQ.2.1 hQ.2.2]
  push_cast
  ring

lemma IsCSPolytope5.sum_quadAt_through {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (v : Set E5) :
    ∑ T ∈ (hP.below_finite F 3).toFinset.filter (fun T => v ⊆ T), (quadAt P T v : ℤ) =
      2 * quadAt P F v := by
  rw [Finset.sum_filter]
  have he : ∀ T ∈ (hP.below_finite F 3).toFinset,
      (if v ⊆ T then (quadAt P T v : ℤ) else 0) = quadAt P T v := by
    intro T _
    by_cases hvT : v ⊆ T
    · rw [if_pos hvT]
    · rw [if_neg hvT, hP.quadAt_zero_of_not_subset hvT, Nat.cast_zero]
  rw [Finset.sum_congr rfl he]
  exact hP.sum_quadAt hF h4 v

/-- A tetrahedron/pyramid complex has an even number of tetrahedra at every vertex. -/
theorem IsCSPolytope5.tetra_through_even_of_local {F v : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hv : v ∈ faces P) (hv0 : dim v = 0)
    (htypes : ∀ T ∈ faces P, T ⊆ F → dim T = 3 → v ⊆ T →
      tri3 P T = (4, 6, 4) ∨ tri3 P T = (5, 8, 5)) :
    ((((hP.below_finite F 3).toFinset.filter (fun T => v ⊆ T)).filter
      (fun T => tri3 P T = (4, 6, 4))).card : ℤ) % 2 = 0 := by
  set S := (hP.below_finite F 3).toFinset.filter (fun T => v ⊆ T) with hS
  have hpoint : ∀ T ∈ S,
      (vdeg P T v : ℤ) + quadAt P T v + (if tri3 P T = (4, 6, 4) then (1 : ℤ) else 0) = 4 := by
    intro T hT
    rw [hS, Finset.mem_filter, Set.Finite.mem_toFinset] at hT
    obtain ⟨⟨hTf, hTF, hT3⟩, hvT⟩ := hT
    rcases htypes T hTf hTF hT3 hvT with ht | ht
    · have htc := ht
      simp only [tri3, Prod.mk.injEq] at htc
      have hd := hP.vdeg_eq_three hTf hT3 (by omega) hv hvT hv0
      have hq : quadAt P T v = 0 := by
        have := hP.quadAt_le T v
        rw [hP.q4_464 hTf hT3 ht] at this
        omega
      rw [hd, hq, if_pos ht]
      norm_num
    · have hq := (hP.q4_585 hTf hT3 ht).1
      obtain ⟨Q, hset⟩ := Set.ncard_eq_one.1 hq
      have hQ : Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ cnt P Q 0 = 4 := by
        have hm : Q ∈ {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ cnt P Q 0 = 4} := by
          rw [hset]; simp
        exact hm
      have hd := hP.vdeg_square_pyramid hTf hT3 ht hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2 hv hvT hv0
      rw [hd, hP.quadAt_single hset v, ht]
      norm_num only [show (5, 8, 5) ≠ (4, 6, 4) by decide, ite_false]
      split_ifs <;> norm_num
  have hs := Finset.sum_congr rfl hpoint
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_boole,
    Finset.sum_const, nsmul_eq_mul] at hs
  have hd := hP.vertex_parity hF h4 hv hv0
  have hq := hP.sum_quadAt_through hF h4 v
  change ∑ T ∈ S, (vdeg P T v : ℤ) = _ at hd
  change ∑ T ∈ S, (quadAt P T v : ℤ) = _ at hq
  rw [hd, hq] at hs
  change ((S.filter (fun T => tri3 P T = (4, 6, 4))).card : ℤ) % 2 = 0
  omega

/-- Global version of the local vertex-parity obstruction. -/
theorem IsCSPolytope5.tetra_through_even {F v : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hv : v ∈ faces P) (hv0 : dim v = 0)
    (htypes : ∀ T ∈ faces P, T ⊆ F → dim T = 3 →
      tri3 P T = (4, 6, 4) ∨ tri3 P T = (5, 8, 5)) :
    ((((hP.below_finite F 3).toFinset.filter (fun T => v ⊆ T)).filter
      (fun T => tri3 P T = (4, 6, 4))).card : ℤ) % 2 = 0 :=
  hP.tetra_through_even_of_local hF h4 hv hv0 (fun T hT hTF hT3 _ => htypes T hT hTF hT3)

/-- A facet cannot have exactly two tetrahedral 3-faces with every other
3-face a square pyramid.  No bound on its number of vertices is needed. -/
theorem IsCSPolytope5.not_two_tetrahedra_pyramids {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hcnt : tcnt P F (4, 6, 4) = 2)
    (htypes : ∀ T ∈ faces P, T ⊆ F → dim T = 3 →
      tri3 P T = (4, 6, 4) ∨ tri3 P T = (5, 8, 5)) : False := by
  obtain ⟨A, B, hAB, hA, hB⟩ := hP.exists_two_of_tcnt hcnt.ge
  have hpair := hP.tset_eq_pair hcnt hAB hA hB
  have hsub : vset P A ⊆ vset P B := by
    intro v hv
    refine ⟨hv.1, ?_, hv.2.2⟩
    by_contra hvB
    have he : ((hP.below_finite F 3).toFinset.filter (fun T => v ⊆ T)).filter
        (fun T => tri3 P T = (4, 6, 4)) = {A} := by
      ext T
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨hTf, hTF, hT3⟩, hvT⟩, ht⟩
        have hm : T ∈ ({A, B} : Set (Set E5)) := by rw [← hpair]; exact ⟨hTf, hTF, hT3, ht⟩
        rcases (show T = A ∨ T = B by simpa using hm) with h | h
        · exact h
        · exact False.elim (hvB (h ▸ hvT))
      · rintro rfl
        exact ⟨⟨⟨hA.1, hA.2.1, hA.2.2.1⟩, hv.2.1⟩, hA.2.2.2⟩
    have hp := hP.tetra_through_even hF h4 hv.1 hv.2.2 htypes
    rw [he, Finset.card_singleton] at hp
    norm_num at hp
  exact hAB (hP.eq_of_subset_of_dim_le hA.1 hB.1
    (hP.subset_of_vset hA.1 hB.1 hsub) (by rw [hA.2.2.1, hB.2.2.1]))

/-- A tetrahedron, one other 3-face, and square pyramids cannot bound a facet.
Outside the exceptional face, vertex parity forces the tetrahedron to have no
vertices; hence the tetrahedron is contained in that distinct 3-face. -/
theorem IsCSPolytope5.not_tetrahedron_exception_pyramids {F A B : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hA : A ∈ faces P) (hAF : A ⊆ F) (hA3 : dim A = 3) (htA : tri3 P A = (4, 6, 4))
    (hB : B ∈ faces P) (hB3 : dim B = 3) (hAB : A ≠ B)
    (htypes : ∀ T ∈ faces P, T ⊆ F → dim T = 3 →
      T = A ∨ T = B ∨ tri3 P T = (5, 8, 5)) : False := by
  have hsub : vset P A ⊆ vset P B := by
    intro v hv
    refine ⟨hv.1, ?_, hv.2.2⟩
    by_contra hvB
    have htlocal : ∀ T ∈ faces P, T ⊆ F → dim T = 3 → v ⊆ T →
        tri3 P T = (4, 6, 4) ∨ tri3 P T = (5, 8, 5) := by
      intro T hT hTF hT3 hvT
      rcases htypes T hT hTF hT3 with rfl | rfl | ht
      · exact Or.inl htA
      · exact False.elim (hvB hvT)
      · exact Or.inr ht
    have he : ((hP.below_finite F 3).toFinset.filter (fun T => v ⊆ T)).filter
        (fun T => tri3 P T = (4, 6, 4)) = {A} := by
      ext T
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨hT, hTF, hT3⟩, hvT⟩, ht⟩
        rcases htypes T hT hTF hT3 with h | rfl | hpyr
        · exact h
        · exact False.elim (hvB hvT)
        · rw [hpyr] at ht
          norm_num at ht
      · rintro rfl
        exact ⟨⟨⟨hA, hAF, hA3⟩, hv.2.1⟩, htA⟩
    have hp := hP.tetra_through_even_of_local hF h4 hv.1 hv.2.2 htlocal
    rw [he, Finset.card_singleton] at hp
    norm_num at hp
  exact hAB (hP.eq_of_subset_of_dim_le hA hB (hP.subset_of_vset hA hB hsub) (by omega))

/-- Profile form of the obstruction, specialized to a triangular bipyramid. -/
theorem IsCSPolytope5.not_one_tetrahedron_bipyramid_pyramids {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (ht : tcnt P F (4, 6, 4) = 1) (hb : tcnt P F (5, 9, 6) = 1)
    (htypes : ∀ T ∈ faces P, T ⊆ F → dim T = 3 →
      tri3 P T = (4, 6, 4) ∨ tri3 P T = (5, 8, 5) ∨ tri3 P T = (5, 9, 6)) : False := by
  obtain ⟨A, hsA⟩ := Set.ncard_eq_one.1 ht
  obtain ⟨B, hsB⟩ := Set.ncard_eq_one.1 hb
  have hA : A ∈ faces P ∧ A ⊆ F ∧ dim A = 3 ∧ tri3 P A = (4, 6, 4) := by
    have : A ∈ {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (4, 6, 4)} := by
      rw [hsA]; simp
    exact this
  have hB : B ∈ faces P ∧ B ⊆ F ∧ dim B = 3 ∧ tri3 P B = (5, 9, 6) := by
    have : B ∈ {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (5, 9, 6)} := by
      rw [hsB]; simp
    exact this
  have hAB : A ≠ B := by
    intro he
    have hh := hA.2.2.2
    rw [he, hB.2.2.2] at hh
    norm_num at hh
  apply hP.not_tetrahedron_exception_pyramids hF h4 hA.1 hA.2.1 hA.2.2.1 hA.2.2.2
    hB.1 hB.2.2.1 hAB
  intro T hT hTF hT3
  rcases htypes T hT hTF hT3 with ht | ht | ht
  · left
    have hm : T ∈ {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (4, 6, 4)} :=
      ⟨hT, hTF, hT3, ht⟩
    rw [hsA] at hm
    exact hm
  · exact Or.inr (Or.inr ht)
  · right; left
    have hm : T ∈ {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (5, 9, 6)} :=
      ⟨hT, hTF, hT3, ht⟩
    rw [hsB] at hm
    exact hm

end Kalai5
