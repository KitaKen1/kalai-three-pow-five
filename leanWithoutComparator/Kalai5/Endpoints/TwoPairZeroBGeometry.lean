import Kalai5.Endpoints.TwoPairZeroBDisjoint

/-! Geometric helpers for the mixed quadrilaterals of profile B. -/
namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.quad_unique_of_q4_le_one {J Q R : Set E5}
    (hq : q4 P J ≤ 1)
    (hQ : Q ∈ faces P) (hQJ : Q ⊆ J) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hR : R ∈ faces P) (hRJ : R ⊆ J) (hR2 : dim R = 2) (hR4 : cnt P R 0 = 4) : Q = R := by
  exact (Set.ncard_le_one (hP.faces_finite.subset fun T (hT : T ∈
    {T | T ∈ faces P ∧ T ⊆ J ∧ dim T = 2 ∧ cnt P T 0 = 4}) => hT.1)).1 hq
      Q ⟨hQ,hQJ,hQ2,hQ4⟩ R ⟨hR,hRJ,hR2,hR4⟩

lemma IsCSPolytope5.two_pair_zero_H20_eq_or_neg
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hG : (flagDataOf P).G = 0) (hlt : (faces P).ncard < 243)
    {H X : Set E5} (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : faceRow P H = OnePairProfile.fullRow 20)
    (hX : X ∈ faces P) (hX4 : dim X = 4) (hX8 : faceRow P X = OnePairProfile.fullRow 20) : X = H ∨ X = -H := by
  let S := (hP.kfaces_finite 4).toFinset.filter (fun F => faceRow P F = OnePairProfile.fullRow 20)
  have hn : S.card = 2 := by
    let cost : Row → ℕ := fun R => if R = OnePairProfile.fullRow 20 then 1 else 0
    have hp := (hP.two_pair_zero_profileB hv hh hc hG hlt).1
    have hs : ((facetRows P).map cost).sum = 2 := by
      rw [(hp.map cost).sum_eq]
      decide +kernel
    rw [hP.facetRows_sum] at hs
    simpa only [cost,Finset.card_filter,S] using hs
  have hneg : -H ≠ H := fun he =>
    (hP.ne_of_dim_ne' (by rw [hH4]; decide)) (hP.eq_of_neg_eq hH he)
  have hHS : H ∈ S := by
    simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hH, hH4⟩, hH8⟩
  have hNS : -H ∈ S := by
    simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨neg_mem_faces hP.symm hH, by rw [dim_neg, hH4]⟩, by rw [hP.faceRow_neg, hH8]⟩
  have hXS : X ∈ S := by
    simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hX, hX4⟩, hX8⟩
  have heq : ({H, -H} : Finset (Set E5)) = S := Finset.eq_of_subset_of_card_le
    (by intro F hF; rcases Finset.mem_insert.1 hF with rfl | hF
        · exact hHS
        · exact Finset.mem_singleton.1 hF ▸ hNS)
    (by rw [hn, Finset.card_pair hneg.symm])
  rw [← heq, Finset.mem_insert, Finset.mem_singleton] at hXS
  exact hXS

theorem IsCSPolytope5.Y_apex_in_third_of_G_zero
    (hv : fvec P 0 = 16) (hG : (flagDataOf P).G = 0)
    {Y Z K X Q : Set E5}
    (hY : Y ∈ faces P) (hY4 : dim Y = 4) (hYrow : faceRow P Y = excRow)
    (hZ : Z ∈ faces P) (hZ4 : dim Z = 4) (hYZ : Y ≠ Z)
    (hK : K ∈ faces P) (hK3 : dim K = 3) (hK6 : cnt P K 0 = 6) (hKI : K = Y ∩ Z)
    (hX : X ∈ faces P) (hX4 : dim X = 4) (hXY : X ≠ Y) (hXZ : X ≠ Z)
    (hQ : Q ∈ faces P) (hQK : Q ⊆ K) (hQX : Q ⊆ X) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4) :
    dim (Y ∩ X) = 3 ∧ cnt P (Y ∩ X) 0 = 5 ∧ K ∩ X = Q ∧
      (vset P Y \ vset P K).ncard = 1 ∧ vset P Y \ vset P K ⊆ vset P X := by
  have hKY : K ⊆ Y := hKI ▸ inter_subset_left
  have hKZ : K ⊆ Z := hKI ▸ inter_subset_right
  have hthree := hP.quad_up_eq_three_of_G_eq_zero
    hG hQ hQ2 hQ4
  have hT : Y ∩ X ∈ faces P :=
    inter_mem_faces_of_nonempty hY hX (hQ.1.mono (subset_inter (hQK.trans hKY) hQX))
  have hT3 := hP.facet_inter_dim_three_of_up_three hQ hQ2 hY hY4 (hQK.trans hKY)
    hX hX4 hQX hXY.symm hthree
  have hKT : K ≠ Y ∩ X := by
    intro he
    have hKX : K ⊆ X := he ▸ inter_subset_right
    have h2 := hP.ridge_two hK hK3
    have hs : ({Y, Z, X} : Set (Set E5)) ⊆ {F | F ∈ faces P ∧ K ⊆ F ∧ dim F = 4} := by
      intro F hF
      rcases hF with rfl | rfl | rfl
      · exact ⟨hY, hKY, hY4⟩
      · exact ⟨hZ, hKZ, hZ4⟩
      · exact ⟨hX, hKX, hX4⟩
    have hl := Set.ncard_le_ncard hs (hP.above_finite K 4)
    rw [Set.ncard_eq_three.2 ⟨Y, Z, X, hYZ, hXY.symm, hXZ.symm, rfl⟩, h2] at hl
    omega
  have hT5 := hP.five_vertices_beside_six hv hY hY4 hK hKY hK3 hK6
    hT inter_subset_left hT3 hKT hQ hQK (subset_inter (hQK.trans hKY) hQX) hQ2 hQ4 hthree
  have hi := hP.inter_three_eq hQ hQ2 hK hK3 hT hT3 hKT hQK
    (subset_inter (hQK.trans hKY) hQX)
  have hiX : K ∩ X = Q := by
    rw [← hi]
    ext x
    simp only [Set.mem_inter_iff]
    exact ⟨fun h => ⟨h.1, hKY h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  obtain ⟨-, hd, hn⟩ := hP.seven_vertex_ridge_cover (congrArg Row.n hYrow)
    hK6 hT5 hQ4 hKY inter_subset_left hi
  refine ⟨hT3, hT5, hiX, hn, ?_⟩
  rw [hd]
  exact fun _ hv => ⟨hv.1.1, hv.1.2.1.trans inter_subset_right, hv.1.2.2⟩

lemma IsCSPolytope5.four_vertex_inter_tetra_of_quad_le_one {H J R : Set E5}
    (hH : H ∈ faces P) (_hH4 : dim H = 4)
    (hJ : J ∈ faces P) (hJ4 : dim J = 4) (hq : q4 P J ≤ 1)
    (hcnt : cnt P (H ∩ J) 0 = 4)
    (hR : R ∈ faces P) (hRJ : R ⊆ J) (hR2 : dim R = 2) (hR4 : cnt P R 0 = 4)
    (hnH : ¬ R ⊆ H) :
    H ∩ J ∈ faces P ∧ dim (H ∩ J) = 3 ∧ tri3 P (H ∩ J) = (4, 6, 4) := by
  have hne : (H ∩ J).Nonempty := by
    obtain ⟨v, hv⟩ := Set.nonempty_of_ncard_ne_zero
      (show (vset P (H ∩ J)).ncard ≠ 0 by rw [← cnt_eq_vset, hcnt]; decide)
    exact hv.1.1.mono hv.2.1
  have hI := inter_mem_faces_of_nonempty hH hJ hne
  have hIJ : H ∩ J ∈ faces J := mem_faces_of_subset (face_subset hJ) hI inter_subset_right
  have hneJ : H ∩ J ≠ J := by
    intro he
    exact hnH (hRJ.trans (by rw [← he]; exact inter_subset_left))
  have hdim := dim_lt_of_mem_faces_ne hIJ hneJ
  have h3 : dim (H ∩ J) = 3 := by
    by_contra hn3
    by_cases h2 : dim (H ∩ J) = 2
    · have he := hP.quad_unique_of_q4_le_one hq hI inter_subset_right h2 hcnt hR hRJ hR2 hR4
      exact hnH (he ▸ inter_subset_left)
    · have := hP.cnt_le_two_of_dim_le_one hI (by omega)
      omega
  refine ⟨hI, h3, ?_⟩
  have hi := hP.tri3_mem_fv8 hI h3 (by omega)
  simp only [fv8,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with h | h | h | h | h | h | h | h | h | h | h | h
  · exact h
  all_goals
    have hn := congrArg Prod.fst h
    change cnt P (H ∩ J) 0 = _ at hn
    omega

end Kalai5
