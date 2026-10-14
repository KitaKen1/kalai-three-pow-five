import Kalai5.Endpoints.UniversalRidge

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Three forced common vertices make the intersection of distinct ridges
a polygon. -/
theorem IsCSPolytope5.ridge_inter_polygon_of_vertex_budget
    {F T R : Set E5} (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3)
    (hR : R ∈ faces P) (hRF : R ⊆ F) (hR3 : dim R = 3) (hTR : T ≠ R)
    (hv : cnt P F 0 + 3 ≤ cnt P T 0 + cnt P R 0) :
    T ∩ R ∈ faces P ∧ dim (T ∩ R) = 2 := by
  obtain ⟨hc,hs⟩ := hP.cnt_add_le hTF hRF (rfl : T ∩ R = T ∩ R)
  have hu := Set.ncard_le_ncard hs (hP.vset_finite F)
  rw [← cnt_eq_vset] at hu
  have hi3 : 3 ≤ cnt P (T ∩ R) 0 := by omega
  have hne : (T ∩ R).Nonempty := by
    obtain ⟨v,hv⟩ := Set.nonempty_of_ncard_ne_zero
      (show (vset P (T ∩ R)).ncard ≠ 0 by rw [← cnt_eq_vset]; omega)
    exact hv.1.1.mono hv.2.1
  have hI := inter_mem_faces_of_nonempty hT hR hne
  have hIT : T ∩ R ∈ faces T := mem_faces_of_subset (face_subset hT) hI inter_subset_left
  have hITne : T ∩ R ≠ T := by
    intro he
    exact hTR (hP.eq_of_subset_of_dim_le hT hR
      (by rw [← he]; exact inter_subset_right) (by omega))
  have hd := dim_lt_of_mem_faces_ne hIT hITne
  refine ⟨hI,?_⟩
  by_contra hn
  have := hP.cnt_le_two_of_dim_le_one hI (by omega)
  omega

/-- A ridge containing all but at most one vertex bounds the number of
other ridges by its polygon count. -/
theorem IsCSPolytope5.near_pyramid_ridge_count
    {F T : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3)
    (hv : cnt P F 0 ≤ cnt P T 0 + 1) : cnt P F 3 ≤ cnt P T 2 + 1 := by
  let A : Set (Set E5) := {R | R ∈ faces P ∧ R ⊆ F ∧ dim R = 3} \ {T}
  have hf : ∀ R ∈ A, T ∩ R ∈ faces P ∧ dim (T ∩ R) = 2 := by
    rintro R ⟨⟨hR,hRF,hR3⟩,hRT⟩
    change R ≠ T at hRT
    have hr4 := hP.four_le_cnt_three hR hR3
    exact hP.ridge_inter_polygon_of_vertex_budget hT hTF hT3 hR hRF hR3 hRT.symm (by omega)
  have hi : Set.InjOn (fun R => T ∩ R) A := by
    rintro R hR S hS he
    change T ∩ R = T ∩ S at he
    obtain ⟨hQ,hQ2⟩ := hf R hR
    have hQS : T ∩ R ⊆ S := by rw [he]; exact inter_subset_right
    exact hP.ridge_partner_unique_inside hF hF4 hQ (inter_subset_left.trans hTF) hQ2
      hT hTF hT3 inter_subset_left hR.1.1 hR.1.2.1 hR.1.2.2 inter_subset_right hR.2
      hS.1.1 hS.1.2.1 hS.1.2.2 hQS hS.2
  have hs : (fun R => T ∩ R) '' A ⊆ {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2} := by
    rintro Q ⟨R,hR,rfl⟩
    exact ⟨(hf R hR).1,inter_subset_left,(hf R hR).2⟩
  have hb := Set.ncard_le_ncard hs (hP.below_finite T 2)
  rw [hi.ncard_image] at hb
  have hc : A.ncard = cnt P F 3 - 1 := Set.ncard_sdiff_singleton_of_mem ⟨hT,hTF,hT3⟩
  change A.ncard ≤ cnt P T 2 at hb
  omega

theorem IsCSPolytope5.v_no_7116 {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8,19,19,8,39⟩) :
    tcnt P F (7,11,6) = 0 := by
  by_contra hz
  obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (7,11,6))
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  have hr : cnt P F 3 = 8 := congrArg Row.r hR
  have ht7 : cnt P T 0 = 7 := congrArg Prod.fst ht
  have htp : cnt P T 2 = 6 := congrArg (fun t => t.2.2) ht
  have hb := hP.near_pyramid_ridge_count hF h4 hT hTF hT3 (by omega)
  omega

theorem IsCSPolytope5.q55_v_nine {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8,19,19,8,39⟩) :
    9 ≤ q55w P F + 2 * exc P F := by
  by_contra hn
  have h1 := hP.v_weight_eight_seven_one hF h4 hR (by omega)
  have h0 := hP.v_no_7116 hF h4 hR
  omega

end Kalai5
