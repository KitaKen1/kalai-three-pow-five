import Kalai5.Endpoints.FullNinePolygon
import Kalai5.Endpoints.FullCrossVertices
import Kalai5.Endpoints.RidgeNonadjacentCapacity

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Two six-vertex ridges in eight vertices meet in a quadrilateral
when the facet contains no polygon with five or more vertices. -/
theorem IsCSPolytope5.six_ridges_inter_four_of_no_big {F T R : Set E5}
    (hF8 : cnt P F 0 = 8) (hz : big2 P F = 0)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (hT6 : cnt P T 0 = 6)
    (hR : R ∈ faces P) (hRF : R ⊆ F) (hR3 : dim R = 3) (hR6 : cnt P R 0 = 6)
    (hne : T ≠ R) : cnt P (T ∩ R) 0 = 4 := by
  obtain ⟨hs,hu⟩ := hP.cnt_add_le hTF hRF (rfl : T ∩ R = T ∩ R)
  have hc := Set.ncard_le_ncard hu (hP.vset_finite F)
  rw [← cnt_eq_vset] at hc
  obtain ⟨hI,hI2⟩ := hP.ridge_inter_polygon_of_vertex_budget hT hTF hT3 hR hRF hR3 hne (by omega)
  by_contra hn
  have hfin : {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 2 ∧ 5 ≤ cnt P Q 0}.Finite :=
    hP.faces_finite.subset fun Q hQ => hQ.1
  have hp : 0 < big2 P F := (Set.ncard_pos hfin).2
    ⟨T ∩ R,hI,inter_subset_left.trans hTF,hI2,by omega⟩
  omega

/-- Equality in the vertex union budget identifies the complement. -/
theorem IsCSPolytope5.ridge_union_covers_complement {F T R : Set E5}
    (hRF : R ⊆ F) (hTF : T ⊆ F)
    (he : cnt P T 0 + cnt P R 0 = cnt P F 0 + cnt P (T ∩ R) 0) :
    vset P F \ vset P T ⊆ vset P R := by
  have hu := Set.ncard_union_add_ncard_inter (vset P T) (vset P R)
    (hP.vset_finite T) (hP.vset_finite R)
  rw [← vset_inter',← cnt_eq_vset,← cnt_eq_vset,← cnt_eq_vset] at hu
  have hs : vset P T ∪ vset P R ⊆ vset P F :=
    Set.union_subset (vset_mono' hTF) (vset_mono' hRF)
  have heq := Set.eq_of_subset_of_ncard_le hs (by rw [← cnt_eq_vset]; omega) (hP.vset_finite F)
  intro v hv
  exact (show v ∈ vset P T ∪ vset P R from heq.symm ▸ hv.1).resolve_left hv.2

/-- A second six-vertex ridge covers both cross vertices. Its small
neighbour cannot share a ridge with either sign of the other full facet. -/
theorem IsCSPolytope5.full_six_partner_avoids_both (hv : fvec P 0 = 16)
    {F H T R X : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hT : T ∈ faces P) (hT3 : dim T = 3) (hT6 : cnt P T 0 = 6)
    (hTI : T = F ∩ H)
    (hRF : R ⊆ F) (hR6 : cnt P R 0 = 6) (hi4 : cnt P (T ∩ R) 0 = 4)
    (hX : X ∈ faces P) (hX4 : dim X = 4) (hX7 : cnt P X 0 = 7) (hRX : R ⊆ X) :
    ∀ S ∈ faces P, dim S = 3 → S ⊆ X → (¬ S ⊆ H) ∧ (¬ S ⊆ -H) := by
  have hFP : F ≠ P := hP.ne_of_dim_ne' (by rw [hF4]; decide)
  have hHP : H ≠ P := hP.ne_of_dim_ne' (by rw [hH4]; decide)
  have hXP : X ≠ P := hP.ne_of_dim_ne' (by rw [hX4]; decide)
  have hTF : T ⊆ F := hTI ▸ inter_subset_left
  have hTH : T ⊆ H := hTI ▸ inter_subset_right
  have hcov := hP.ridge_union_covers_complement hRF hTF (by omega)
  obtain ⟨hcF,hcH⟩ := hP.full_cross_complements hF hFP (by omega) hH hHP (by omega) hTI
  have hcross : (vset P (F ∩ -H)).ncard = 2 := by
    rw [← hcF,Set.ncard_sdiff (vset_mono' hTF) (hP.vset_finite T),
      ← cnt_eq_vset,← cnt_eq_vset,hF8,hT6]
  intro S hS hS3 hSX
  constructor
  · intro hSH
    have hST : S ⊆ T := hP.subset_of_vset hS hT (by
      intro v hvS
      have hvH : v ∈ vset P H := vset_mono' hSH hvS
      have hvF : v ∈ vset P F := by
        rcases hP.vertex_mem_or_neg_mem_of_full hF hFP (by omega) hvS.1 hvS.2.2 with h | h
        · exact ⟨hvS.1,h,hvS.2.2⟩
        · have hnF : -v ∈ vset P F :=
            ⟨neg_mem_faces hP.symm hvS.1,h,by rw [dim_neg]; exact hvS.2.2⟩
          have hnT : -v ∉ vset P T := fun hn =>
            hP.vset_no_antipodes hH hHP hvH (vset_mono' hTH hn)
          exact False.elim (hP.vset_no_antipodes hX hXP (vset_mono' hSX hvS)
            (vset_mono' hRX (hcov ⟨hnF,hnT⟩)))
      rw [hTI,vset_inter']
      exact ⟨hvF,hvH⟩)
    have he : S = T := hP.eq_of_subset_of_dim_le hS hT hST (by omega)
    have hTX : T ⊆ X := he ▸ hSX
    obtain ⟨hc,hu⟩ := hP.cnt_add_le hTX hRX (rfl : T ∩ R = T ∩ R)
    have hb := Set.ncard_le_ncard hu (hP.vset_finite X)
    rw [← cnt_eq_vset] at hb
    omega
  · intro hSH
    have hinter : cnt P (R ∩ S) 0 ≤ 2 := by
      rw [cnt_eq_vset]
      have hs : R ∩ S ⊆ F ∩ -H := fun x hx => ⟨hRF hx.1,hSH hx.2⟩
      have hb := Set.ncard_le_ncard (vset_mono' hs) (hP.vset_finite (F ∩ -H))
      omega
    have hlo := hP.four_le_cnt_three hS hS3
    obtain ⟨hc,hu⟩ := hP.cnt_add_le hRX hSX (rfl : R ∩ S = R ∩ S)
    have hb := Set.ncard_le_ncard hu (hP.vset_finite X)
    rw [← cnt_eq_vset] at hb
    omega

end Kalai5
