import Kalai5.Endpoints.PrismTriangles
import Kalai5.Endpoints.NearPyramidRidge

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- In an at-most-eight-vertex facet, a triangular prism excludes every
quadrilateral between two square pyramids. -/
theorem IsCSPolytope5.prism_b55_zero_of_eight {F T : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 ≤ 8)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (ht : tri3 P T = (6,9,5)) :
    (b55set P F).ncard = 0 := by
  by_contra hn
  obtain ⟨Q,hQB⟩ := Set.nonempty_of_ncard_ne_zero hn
  have hQ := hQB.1
  have hQF := hQB.2.1
  have hQ2 := hQB.2.2.1
  have hQ4 := hQB.2.2.2.1
  have hT6 : cnt P T 0 = 6 := congrArg Prod.fst ht
  have hQnotT : ¬ Q ⊆ T := by
    intro hQT
    have he := hP.b55_pyr Q hQB T hT hQT hTF hT3
    have hn5 : cnt P T 0 = 5 := congrArg Prod.fst he
    omega
  obtain ⟨R,S,hR,hR3,hRF,hQR,hS,hS3,hSF,hQS,hRS,_⟩ := hP.exists_two_three hF hF4 hQ hQF hQ2
  have hR5 : cnt P R 0 = 5 := congrArg Prod.fst (hP.b55_pyr Q hQB R hR hQR hRF hR3)
  have hS5 : cnt P S 0 = 5 := congrArg Prod.fst (hP.b55_pyr Q hQB S hS hQS hSF hS3)
  have hTR : T ≠ R := by intro he; rw [he] at hT6; omega
  have hTS : T ≠ S := by intro he; rw [he] at hT6; omega
  obtain ⟨hI,hI2⟩ := hP.ridge_inter_polygon_of_vertex_budget hT hTF hT3 hR hRF hR3 hTR (by omega)
  obtain ⟨hJ,hJ2⟩ := hP.ridge_inter_polygon_of_vertex_budget hT hTF hT3 hS hSF hS3 hTS (by omega)
  have hI3 : cnt P (T ∩ R) 0 = 3 := by
    have hne : Q ≠ T ∩ R := by intro he; apply hQnotT; rw [he]; exact inter_subset_left
    have hb := hP.polygon_pair_vertex_budget hQ hQR hQ2 hI inter_subset_right hI2 hne
    have hl := hP.three_le_cnt hI hI2
    omega
  have hJ3 : cnt P (T ∩ S) 0 = 3 := by
    have hne : Q ≠ T ∩ S := by intro he; apply hQnotT; rw [he]; exact inter_subset_left
    have hb := hP.polygon_pair_vertex_budget hQ hQS hQ2 hJ inter_subset_right hJ2 hne
    have hl := hP.three_le_cnt hJ hJ2
    omega
  have hIJ : T ∩ R ≠ T ∩ S := by
    intro he
    have hIS : T ∩ R ⊆ S := by rw [he]; exact inter_subset_right
    exact hRS (hP.ridge_partner_unique_inside hF hF4 hI (inter_subset_left.trans hTF) hI2
      hT hTF hT3 inter_subset_left hR hRF hR3 inter_subset_right hTR.symm
      hS hSF hS3 hIS hTS.symm)
  have hd := hP.prism_triangles_vertex_disjoint hT hT3 ht hI inter_subset_left hI2 hI3
    hJ inter_subset_left hJ2 hJ3 hIJ
  have hRQ := hP.inter_three_eq hQ hQ2 hR hR3 hS hS3 hRS hQR hQS
  have he : (T ∩ R) ∩ (T ∩ S) = Q ∩ T := by
    rw [← hRQ]; ext x; simp only [Set.mem_inter_iff]; tauto
  have hz : cnt P (Q ∩ T) 0 = 0 := by
    rw [cnt_eq_vset,← he,vset_inter',Set.disjoint_iff_inter_eq_empty.1 hd,Set.ncard_empty]
  obtain ⟨hc,hs⟩ := hP.cnt_add_le hQF hTF (rfl : Q ∩ T = Q ∩ T)
  have hb := Set.ncard_le_ncard hs (hP.vset_finite F)
  rw [← cnt_eq_vset] at hb
  omega

/-- V has a prism: its flag difference needs a positive ridge event, and
the seven-vertex event is excluded by the near-pyramid ridge count. -/
theorem IsCSPolytope5.v_prism_positive {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8,19,19,8,39⟩) :
    1 ≤ tcnt P F (6,9,5) := by
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  have hp : cnt P F 2 = 19 := congrArg Row.p hR
  have hj : incid P F 0 3 = 39 := congrArg Row.J hR
  obtain ⟨_,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  have hzero := hP.v_no_7116 hF h4 hR
  omega

/-- The actual Q55 weight of V is twelve, without any global endpoint
assumption or exhaustive eight-vertex catalogue. -/
theorem IsCSPolytope5.v_weight_twelve {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8,19,19,8,39⟩) :
    q4 P F = 4 ∧ big2 P F = 0 ∧ (b55set P F).ncard = 0 ∧
      q55w P F + 2 * exc P F = 12 := by
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (hP.v_prism_positive hF h4 hR)
  have hb := hP.prism_b55_zero_of_eight hF h4 hn.le hT hTF hT3 ht
  have hq := hP.b55_add_three_le_of_prism (hP.v_prism_positive hF h4 hR)
  have he := hP.exc_eq_faceRow hF h4
  rw [hR] at he
  norm_num at he
  have hbound := hP.q4_add_big_le_exc F
  have hz : big2 P F = 0 := by omega
  have hqe := hP.exc_eq_q4_of_big F hz
  have hw := hP.q55w_eq_b55 F
  exact ⟨by omega,hz,hb,by omega⟩

end Kalai5
