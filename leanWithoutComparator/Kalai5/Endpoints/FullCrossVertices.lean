import Kalai5.Endpoints.UniversalRidge

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.neg_mem_vset {F v : Set E5} (hv : v ∈ vset P F) :
    -v ∈ vset P (-F) :=
  ⟨neg_mem_faces hP.symm hv.1, Set.neg_subset_neg.2 hv.2.1, by rw [dim_neg]; exact hv.2.2⟩

/-- The vertices of a face outside a full facet lie in its antipode. -/
theorem IsCSPolytope5.vset_sdiff_full {F H : Set E5}
    (hH : H ∈ faces P) (hHP : H ≠ P) (hh : 2 * cnt P H 0 = fvec P 0) :
    vset P F \ vset P H = vset P (F ∩ -H) := by
  rw [vset_inter']
  ext v
  constructor
  · rintro ⟨hv,hn⟩
    refine ⟨hv, hv.1, ?_, hv.2.2⟩
    rcases hP.vertex_mem_or_neg_mem_of_full hH hHP hh hv.1 hv.2.2 with h | h
    · exact False.elim (hn ⟨hv.1,h,hv.2.2⟩)
    · exact neg_subset_iff.2 h
  · rintro ⟨hv,hvn⟩
    refine ⟨hv,fun hvh => ?_⟩
    obtain ⟨x,hx⟩ := hv.1.1
    exact Set.disjoint_left.1 (hP.disjoint_neg_of_full hH hHP hh) (hvh.2.1 hx) (hvn.2.1 hx)

/-- The two opposite cross intersections have the same two-vertex complement
description. -/
theorem IsCSPolytope5.full_cross_complements {F H T : Set E5}
    (hF : F ∈ faces P) (hFP : F ≠ P) (hf : 2 * cnt P F 0 = fvec P 0)
    (hH : H ∈ faces P) (hHP : H ≠ P) (hh : 2 * cnt P H 0 = fvec P 0)
    (hT : T = F ∩ H) :
    vset P F \ vset P T = vset P (F ∩ -H) ∧
    vset P (-H) \ vset P (-T) = vset P (F ∩ -H) := by
  constructor
  · have he : vset P F \ vset P T = vset P F \ vset P H := by
      rw [hT,vset_inter']; ext v; simp only [Set.mem_sdiff,Set.mem_inter_iff]; tauto
    rw [he]
    exact hP.vset_sdiff_full hH hHP hh
  · have hnT : -T = -H ∩ -F := by rw [hT]; ext x; simp [and_comm]
    have he : vset P (-H) \ vset P (-T) = vset P (-H) \ vset P (-F) := by
      rw [hnT,vset_inter']; ext v; simp only [Set.mem_sdiff,Set.mem_inter_iff]; tauto
    rw [he]
    rw [hP.vset_sdiff_full (neg_mem_faces hP.symm hF)
      (by intro he; apply hFP; apply Set.Subset.antisymm (face_subset hF)
          intro x hx; have hn := hP.symm x hx; rw [← he] at hn; simpa using hn)
      (by rw [hP.cnt_neg]; exact hf),neg_neg,inter_comm]

/-- Equality in the vertex budget identifies all vertices outside the shared
ridge. -/
theorem IsCSPolytope5.pyramid_covers_complement {F T R : Set E5}
    (hRF : R ⊆ F) (hTF : T ⊆ F)
    (hF8 : cnt P F 0 = 8) (hT6 : cnt P T 0 = 6)
    (hR5 : cnt P R 0 = 5) (hi3 : cnt P (T ∩ R) 0 = 3) :
    vset P F \ vset P T ⊆ vset P R := by
  have hu := Set.ncard_union_add_ncard_inter (vset P T) (vset P R)
    (hP.vset_finite T) (hP.vset_finite R)
  rw [← vset_inter',← cnt_eq_vset,← cnt_eq_vset,← cnt_eq_vset,hT6,hR5,hi3] at hu
  have hs : vset P T ∪ vset P R ⊆ vset P F :=
    Set.union_subset (vset_mono' hTF) (vset_mono' hRF)
  have he := Set.eq_of_subset_of_ncard_le hs (by rw [← cnt_eq_vset,hF8]; omega) (hP.vset_finite F)
  intro v hv
  have hm : v ∈ vset P T ∪ vset P R := he.symm ▸ hv.1
  exact hm.resolve_left hv.2

/-- A square pyramid covering both vertices outside a shared six-vertex
ridge has a seven-vertex neighbour which cannot meet either sign of the
other full facet in a ridge. -/
theorem IsCSPolytope5.full_pyramid_partner_obstruction (hv : fvec P 0 = 16)
    {F H T R X : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hHr : cnt P H 3 = 8)
    (hT : T ∈ faces P) (hT3 : dim T = 3) (hT6 : cnt P T 0 = 6)
    (hTp : cnt P T 2 = 7) (hTI : T = F ∩ H)
    (hRF : R ⊆ F) (hR5 : cnt P R 0 = 5) (hi3 : cnt P (T ∩ R) 0 = 3)
    (hX : X ∈ faces P) (hX4 : dim X = 4) (hX7 : cnt P X 0 = 7) (hRX : R ⊆ X) :
    ∀ S ∈ faces P, dim S = 3 → S ⊆ X → (¬ S ⊆ H) ∧ (¬ S ⊆ -H) := by
  have hFP : F ≠ P := hP.ne_of_dim_ne' (by rw [hF4]; decide)
  have hHP : H ≠ P := hP.ne_of_dim_ne' (by rw [hH4]; decide)
  have hXP : X ≠ P := hP.ne_of_dim_ne' (by rw [hX4]; decide)
  have hTF : T ⊆ F := hTI ▸ inter_subset_left
  have hTH : T ⊆ H := hTI ▸ inter_subset_right
  have hcov := hP.pyramid_covers_complement hRF hTF hF8 hT6 hR5 hi3
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
    have hnH : -H ∈ faces P := neg_mem_faces hP.symm hH
    have hnH4 : dim (-H) = 4 := by rw [dim_neg,hH4]
    have hXH : X ≠ -H := by intro he; rw [he,hP.cnt_neg,hH8] at hX7; omega
    have hSI : S = X ∩ -H := hP.three_face_eq_inter hX hX4 hnH hnH4 hXH hS hS3 hSX hSH
    have hAS : vset P (F ∩ -H) ⊆ vset P S := by
      intro v hvA
      rw [hSI,vset_inter']
      exact ⟨vset_mono' hRX (hcov (hcF.symm ▸ hvA)),vset_mono' inter_subset_right hvA⟩
    have hS5 : 5 ≤ cnt P S 0 := by
      have hlo := hP.four_le_cnt_three hS hS3
      by_contra hno
      have hS4 : cnt P S 0 = 4 := by omega
      have hSnT : S ≠ -T := by intro he; rw [he,hP.cnt_neg,hT6] at hS4; omega
      have hi := hP.universal_ridge_tetra_inter hnH hnH4
        (neg_mem_faces hP.symm hT) (Set.neg_subset_neg.2 hTH) (by rw [dim_neg,hT3])
        (by rw [hP.cnt_neg,hP.cnt_neg,hTp,hHr]) hS hSH hS3 hS4 hSnT
      have ha : vset P (F ∩ -H) ⊆ vset P S \ vset P (-T) := by
        intro v hvA
        exact ⟨hAS hvA,(hcH.symm ▸ hvA).2⟩
      have hb := Set.ncard_le_ncard ha (hP.vset_finite S).sdiff
      have hd : (vset P S \ vset P (-T)).ncard = 1 := by
        have he : vset P S \ vset P (-T) = vset P S \ vset P (-T ∩ S) := by
          rw [vset_inter']; ext v; simp only [Set.mem_sdiff,Set.mem_inter_iff]; tauto
        rw [he,Set.ncard_sdiff (vset_mono' inter_subset_right) (hP.vset_finite (-T ∩ S)),
          ← cnt_eq_vset,← cnt_eq_vset,hS4,hi]
      rw [hcross,hd] at hb
      omega
    have hinter : cnt P (R ∩ S) 0 ≤ 2 := by
      rw [cnt_eq_vset]
      have hs : R ∩ S ⊆ F ∩ -H := fun x hx => ⟨hRF hx.1,hSH hx.2⟩
      have hb := Set.ncard_le_ncard (vset_mono' hs) (hP.vset_finite (F ∩ -H))
      omega
    obtain ⟨hc,hu⟩ := hP.cnt_add_le hRX hSX (rfl : R ∩ S = R ∩ S)
    have hb := Set.ncard_le_ncard hu (hP.vset_finite X)
    rw [← cnt_eq_vset] at hb
    omega

end Kalai5
