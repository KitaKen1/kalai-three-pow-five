import Kalai5.Endpoints.FullCrossVertices
import Kalai5.Endpoints.RidgeNonadjacentCapacity

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- A pyramid covering the two vertices outside a six-vertex shared ridge
blocks the positive full neighbour. Any ridge shared with the negative
neighbour must be a tetrahedron nonadjacent to the opposite shared ridge. -/
theorem IsCSPolytope5.full_pyramid_partner_nonadjacent (hv : fvec P 0 = 16)
    {F H T R X : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hT : T ∈ faces P) (hT3 : dim T = 3) (hT6 : cnt P T 0 = 6)
    (hTI : T = F ∩ H)
    (hRF : R ⊆ F) (hR5 : cnt P R 0 = 5) (hi3 : cnt P (T ∩ R) 0 = 3)
    (hX : X ∈ faces P) (hX4 : dim X = 4) (hX7 : cnt P X 0 = 7) (hRX : R ⊆ X) :
    ∀ S ∈ faces P, dim S = 3 → S ⊆ X → (¬ S ⊆ H) ∧ (S ⊆ -H → cnt P S 0 = 4 ∧ dim (-T ∩ S) ≠ 2) := by
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
    have hinter : cnt P (R ∩ S) 0 ≤ 2 := by
      rw [cnt_eq_vset]
      have hs : R ∩ S ⊆ F ∩ -H := fun x hx => ⟨hRF hx.1,hSH hx.2⟩
      have hb := Set.ncard_le_ncard (vset_mono' hs) (hP.vset_finite (F ∩ -H))
      omega
    have hS4 : cnt P S 0 = 4 := by
      have hlo := hP.four_le_cnt_three hS hS3
      obtain ⟨hc,hu⟩ := hP.cnt_add_le hRX hSX (rfl : R ∩ S = R ∩ S)
      have hb := Set.ncard_le_ncard hu (hP.vset_finite X)
      rw [← cnt_eq_vset] at hb
      omega
    refine ⟨hS4,?_⟩
    intro hdim
    have hne : (-T ∩ S).Nonempty := by
      by_contra he
      have heq : -T ∩ S = ∅ := Set.not_nonempty_iff_eq_empty.1 he
      rw [heq] at hdim
      unfold dim at hdim
      rw [vectorSpan_empty,finrank_bot] at hdim
      omega
    have hI := inter_mem_faces_of_nonempty (neg_mem_faces hP.symm hT) hS hne
    have hlo := hP.three_le_cnt hI hdim
    have ha : vset P (F ∩ -H) ⊆ vset P S \ vset P (-T) := by
      intro v hvA
      exact ⟨hAS hvA,(hcH.symm ▸ hvA).2⟩
    have hb := Set.ncard_le_ncard ha (hP.vset_finite S).sdiff
    have he : vset P S \ vset P (-T) = vset P S \ vset P (-T ∩ S) := by
      rw [vset_inter']; ext v; simp only [Set.mem_sdiff,Set.mem_inter_iff]; tauto
    rw [hcross,he,Set.ncard_sdiff (vset_mono' inter_subset_right) (hP.vset_finite (-T ∩ S)),
      ← cnt_eq_vset,← cnt_eq_vset,hS4] at hb
    omega

end Kalai5
