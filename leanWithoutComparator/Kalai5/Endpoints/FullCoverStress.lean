import Kalai5.Endpoints.WeightR35

/-!
# Full-cover configurations force positive stress

A quadrilateral covered by two 3-faces of a full facet has at least four facets
above it.  The polygon-star inequality therefore gives `G ≥ 2`.  This packages
the existing full-cover geometry as a reusable obstruction to `G = 0`, and
applies it to the row `R₁₉ = zRow` without a new catalogue or LP assumption.
-/

namespace Kalai5

open Set
open scoped Classical

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.two_le_G_of_full_quad_cover {F Q R S : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hfull : 2 * cnt P F 0 = fvec P 0)
    (hQ : Q ∈ faces P) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hR : R ∈ faces P) (hR3 : dim R = 3) (hRF : R ⊆ F)
    (hS : S ∈ faces P) (hS3 : dim S = 3) (hSF : S ⊆ F)
    (hRS : R ≠ S) (hQR : Q ⊆ R) (hQS : Q ⊆ S)
    (hcover : vset P F ⊆ vset P R ∪ vset P S) :
    2 ≤ (flagDataOf P).G := by
  obtain ⟨W, hPW, hcp⟩ := hP.exists_vertFinset
  have hcov : ∀ w ∈ W, w ∈ F → w ∈ R ∨ w ∈ S := by
    intro w hw hwF
    have hface : ({w} : Set E5) ∈ faces P := by
      rw [hPW]
      exact singleton_mem_faces_of_extreme (hcp w hw)
    have hmem : ({w} : Set E5) ∈ vset P F :=
      ⟨hface, by simpa using hwF, dim_singleton w⟩
    rcases hcover hmem with ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
  have hlink := hP.four_le_up_of_cover hPW hcp hF h4 hfull hQ hQ2
    hR hR3 hS hS3 hRS hQR hQS hRF hSF hcov
  have hstar := hP.polygon_star hQ hQ2
  rw [hP.up_three_eq_up_four hQ hQ2, hQ4] at hstar
  push_cast at hstar
  omega

/-- At sixteen vertices an `R₁₉` facet forces `G ≥ 2`. -/
theorem IsCSPolytope5.two_le_G_of_zRow (h16 : fvec P 0 = 16)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = zRow) : 2 ≤ (flagDataOf P).G := by
  have hn : cnt P F 0 = 8 := by
    simp only [faceRow, zRow, Row.mk.injEq] at hR
    exact hR.1
  obtain ⟨R, S, Q, hRf, hRF, hR3, hSf, hSF, hS3, hRS, hQf, hQ2, hQR, hQS, hQ4, hcov⟩ :=
    hP.r19_cover hF h4 hR
  exact hP.two_le_G_of_full_quad_cover hF h4 (by omega) hQf hQ2 hQ4
    hRf hR3 hRF hSf hS3 hSF hRS hQR hQS hcov

/-- The row exclusion required by the `G = 0` branch of the few-full endpoint. -/
theorem IsCSPolytope5.zRow_not_mem_of_G_eq_zero (h16 : fvec P 0 = 16)
    (hG : (flagDataOf P).G = 0) : zRow ∉ facetRows P := by
  intro hmem
  obtain ⟨F, hF, h4, hR⟩ := hP.mem_facetRows hmem
  have := hP.two_le_G_of_zRow h16 hF h4 hR
  omega

/-- Under `G = 0`, every quadrilateral has a triangular upper link. -/
lemma IsCSPolytope5.quad_up_eq_three_of_G_eq_zero (hG : (flagDataOf P).G = 0)
    {Q : Set E5} (hQ : Q ∈ faces P) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4) :
    {F | F ∈ faces P ∧ Q ⊆ F ∧ dim F = 4}.ncard = 3 := by
  have hstar := hP.polygon_star hQ hQ2
  rw [hP.up_three_eq_up_four hQ hQ2, hQ4, hG] at hstar
  have := hP.three_le_up hQ hQ2
  push_cast at hstar
  omega

/-- A numerical vertex cover suffices for the full-cover stress obstruction. -/
lemma IsCSPolytope5.two_le_G_of_full_quad_counts {F Q R S : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hfull : 2 * cnt P F 0 = fvec P 0)
    (hQ : Q ∈ faces P) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hR : R ∈ faces P) (hR3 : dim R = 3) (hRF : R ⊆ F)
    (hS : S ∈ faces P) (hS3 : dim S = 3) (hSF : S ⊆ F)
    (hRS : R ≠ S) (hQR : Q ⊆ R) (hQS : Q ⊆ S)
    (hcount : cnt P F 0 + 4 ≤ cnt P R 0 + cnt P S 0) :
    2 ≤ (flagDataOf P).G := by
  have hI := hP.inter_three_eq hQ hQ2 hR hR3 hS hS3 hRS hQR hQS
  obtain ⟨hc, hu⟩ := hP.cnt_add_le hRF hSF hI
  have heq := Set.eq_of_subset_of_ncard_le hu
    (show (vset P F).ncard ≤ (vset P R ∪ vset P S).ncard by
      rw [← cnt_eq_vset]; omega) (hP.vset_finite F)
  exact hP.two_le_G_of_full_quad_cover hF h4 hfull hQ hQ2 hQ4
    hR hR3 hRF hS hS3 hSF hRS hQR hQS heq.symm.subset

/-- With `G = 0`, the three quadrilaterals of a triangular prism in a facet
must have three distinct square pyramids as partners. -/
theorem IsCSPolytope5.three_le_pyramids_of_prism_G0 (h16 : fvec P 0 = 16)
    (hG : (flagDataOf P).G = 0) {F T : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3)
    (ht : tri3 P T = (6, 9, 5)) : 3 ≤ tcnt P F (5, 8, 5) := by
  have htc := ht
  simp only [tri3, Prod.mk.injEq] at htc
  let X : Set (Set E5) :=
    {S | S ∈ faces P ∧ S ⊆ F ∧ dim S = 3 ∧ tri3 P S ≠ (5, 8, 5)}
  have hTX : T ∈ X := ⟨hT, hTF, hT3, by rw [ht]; decide⟩
  have hX : ∀ S ∈ X, S ≠ T → ∀ Q ∈ ntri P T, ¬ Q ⊆ S := by
    rintro S ⟨hS, hSF, hS3, hs⟩ hST Q hQ hQS
    have hQ4 : cnt P Q 0 = 4 := by
      have := hP.cnt_zero_add_one_le hT hT3 hQ.1 hQ.2.1 hQ.2.2.1
      have := hQ.2.2.2
      omega
    have hlink := hP.quad_up_eq_three_of_G_eq_zero hG hQ.1 hQ.2.2.1 hQ4
    have hn := hP.non5_le_one h16 hF h4 hQ.1 (hQ.2.1.trans hTF) hQ.2.2.1 hQ4 hlink
    have hS5 : cnt P S 0 = 5 := by
      by_contra hne
      have hsub : ({S, T} : Set (Set E5)) ⊆ non5 P F Q := by
        intro U hU
        rcases (show U = S ∨ U = T by simpa using hU) with rfl | rfl
        · exact ⟨hS, hSF, hS3, hQS, hne⟩
        · exact ⟨hT, hTF, hT3, hQ.2.1, by omega⟩
      have := Set.ncard_le_ncard hsub (hP.non5_finite F Q)
      rw [Set.ncard_pair hST] at this
      omega
    have hqpos : 0 < q4 P S :=
      (Set.ncard_pos (hP.faces_finite.subset fun Q' hQ' => hQ'.1)).2
        ⟨Q, hQ.1, hQS, hQ.2.2.1, hQ4⟩
    have hin := hP.tri3_mem_fv8 hS hS3 (by omega)
    simp only [fv8, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with h | h | h | h | h | h | h | h | h | h | h | h
    all_goals first
      | exact hs h
      | (rw [(hP.q4_596 hS hS3 h).1] at hqpos; omega)
      | (simp only [tri3, Prod.mk.injEq] at h; omega)
  have hbound := hP.ntri_le hF h4 hT hTF hT3 X hTX hX
  have hsub : nsimp P F \ X ⊆
      {S | S ∈ faces P ∧ S ⊆ F ∧ dim S = 3 ∧ tri3 P S = (5, 8, 5)} := by
    rintro S ⟨⟨hS, hSF, hS3, -⟩, hnot⟩
    refine ⟨hS, hSF, hS3, ?_⟩
    by_contra hne
    exact hnot ⟨hS, hSF, hS3, hne⟩
  have hle := Set.ncard_le_ncard hsub (hP.faces_finite.subset fun S hS => hS.1)
  change (nsimp P F \ X).ncard ≤ tcnt P F (5, 8, 5) at hle
  rw [hP.ntri_ncard T, (hP.q4_695 hT hT3 ht).1, (hP.q4_695 hT hT3 ht).2] at hbound
  omega

/-- A seven-vertex 3-face and a square pyramid of a full eight-vertex facet
force a full cover, hence positive stress. -/
lemma IsCSPolytope5.two_le_G_of_T7_pyramid (h16 : fvec P 0 = 16)
    {F T Y : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hn : cnt P F 0 = 8)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (hT7 : cnt P T 0 = 7)
    (hY : Y ∈ faces P) (hYF : Y ⊆ F) (hY3 : dim Y = 3) (hy : tri3 P Y = (5, 8, 5)) :
    2 ≤ (flagDataOf P).G := by
  obtain ⟨Q, hQ, hQT⟩ := hP.pyr_quad_sub hn hT hTF hT3 hT7 hY hYF hY3 hy
  have hyc := hy
  simp only [tri3, Prod.mk.injEq] at hyc
  have hQ4 : cnt P Q 0 = 4 := by
    have := hP.cnt_zero_add_one_le hY hY3 hQ.1 hQ.2.1 hQ.2.2.1
    have := hQ.2.2.2
    omega
  have hTY : T ≠ Y := fun h => by rw [h] at hT7; omega
  exact hP.two_le_G_of_full_quad_counts hF h4 (by omega) hQ.1 hQ.2.2.1 hQ4
    hT hT3 hTF hY hY3 hYF hTY hQT hQ.2.1 (by omega)

/-- The second full-row exclusion required by the `G = 0` branch. -/
theorem IsCSPolytope5.r35Row_not_mem_of_G_eq_zero (h16 : fvec P 0 = 16)
    (hG : (flagDataOf P).G = 0) : r35Row ∉ facetRows P := by
  intro hmem
  obtain ⟨F, hF, h4, hR⟩ := hP.mem_facetRows hmem
  have hn : cnt P F 0 = 8 := by
    simp only [faceRow, r35Row, Row.mk.injEq] at hR
    exact hR.1
  obtain ⟨-, hc⟩ := hP.r35_types hF h4 hR
  rcases hc with ⟨hy, hp⟩ | ⟨hy, h7, -⟩ | ⟨hy, h7, -⟩
  · obtain ⟨T, hT, hTF, hT3, ht⟩ := hP.exists_of_tcnt (F := F) (t := (6, 9, 5)) (by omega)
    have := hP.three_le_pyramids_of_prism_G0 h16 hG hF h4 hT hTF hT3 ht
    omega
  all_goals
    obtain ⟨T, hT, hTF, hT3, ht⟩ := hP.exists_of_tcnt (F := F) (t := (7, 11, 6)) (by omega)
    obtain ⟨Y, hY, hYF, hY3, hy'⟩ := hP.exists_of_tcnt (F := F) (t := (5, 8, 5)) (by omega)
    have hT7 : cnt P T 0 = 7 := by simp only [tri3, Prod.mk.injEq] at ht; exact ht.1
    have := hP.two_le_G_of_T7_pyramid h16 hF h4 hn hT hTF hT3 hT7 hY hYF hY3 hy'
    omega

end Kalai5
