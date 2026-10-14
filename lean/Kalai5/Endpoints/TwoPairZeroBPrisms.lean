import Kalai5.Endpoints.TwoPairZeroBQuads

/-! The Y facets still pair across their triangular prisms in profile B. -/
namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.two_pair_zero_prism_Y
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hG : (flagDataOf P).G = 0) (hlt : (faces P).ncard < 243)
    {F K : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hK : K ∈ faces P) (hKF : K ⊆ F) (hK3 : dim K = 3)
    (ht : tri3 P K = (6,9,5)) : faceRow P F = excRow := by
  have hK6 : cnt P K 0 = 6 := congrArg Prod.fst ht
  have hq := (hP.q4_695 hK hK3 ht).1
  rcases hP.two_pair_zero_B_rows hv hh hc hG hlt hF hF4 with h | h | h | h | h
  · have hF6 : cnt P F 0 = 6 := congrArg Row.n h
    have := hP.cnt_zero_lt hK hF hKF (by rintro rfl; omega)
    omega
  · exact h
  · rcases hP.J_three_types hF hF4 h K hK hKF hK3 with h | h | h <;>
      have := congrArg Prod.fst h <;> change cnt P K 0 = _ at this <;> omega
  · have := hP.two_pair_zero_H_small_ridges hv hh hc hG hlt hF hF4
      (by omega) (by omega) h K hK hKF hK3
    omega
  · have := hP.two_pair_zero_H_small_ridges hv hh hc hG hlt hF hF4
      (by omega) (by omega) h K hK hKF hK3
    omega

theorem IsCSPolytope5.two_pair_zero_prism_exists
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hG : (flagDataOf P).G = 0) (hlt : (faces P).ncard < 243)
    {Q : Set E5} (hQ : Q ∈ faces P) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4) :
    Nonempty (OnePairPrism P Q) := by
  have htwo := hP.two_pair_zero_quad_two_Y hv hh hc hG hlt hQ hQ2 hQ4
  obtain ⟨Y,hY⟩ := Finset.card_pos.1 (show 0 <
    ((hP.above_finite Q 4).toFinset.filter (fun F => faceRow P F = excRow)).card by omega)
  rw [Finset.mem_filter,Set.Finite.mem_toFinset] at hY
  obtain ⟨K,hK,hKY,hK3,ht,_,hbase⟩ := hP.Y_prism_base hY.1.1 hY.1.2.2 hY.2
  obtain ⟨Z,hZ,hZ4,hZY,hKZ⟩ := hP.exists_other_facet hK hK3 hKY
  have hZrow := hP.two_pair_zero_prism_Y hv hh hc hG hlt hZ hZ4 hK hKZ hK3 ht
  have hKI := hP.three_face_eq_inter hY.1.1 hY.1.2.2 hZ hZ4 hZY.symm hK hK3 hKY hKZ
  exact ⟨⟨Y,Z,K,hY.1.1,hY.1.2.2,hY.2,hZ,hZ4,hZrow,hZY.symm,hK,hK3,ht,hKI,
    hbase Q hQ hY.1.2.1 hQ2 hQ4⟩⟩

end Kalai5
