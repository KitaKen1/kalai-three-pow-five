import Kalai5.Endpoints.R35FullSixObstruction

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Double-count the R35--A incidences. Each R35 needs two distinct
A neighbours, whereas the unique six-vertex ridge of A serves only one. -/
theorem IsCSPolytope5.r35_a_supply_bound
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hz : ∀ A ∈ faces P, dim A = 4 → faceRow P A = G2S4.aRow → big2 P A = 0)
    (hpartner : ∀ F ∈ faces P, dim F = 4 → faceRow P F = r35Row →
      ∀ T ∈ faces P, T ⊆ F → dim T = 3 → tri3 P T = (6,10,6) →
        ∃ A, A ∈ faces P ∧ dim A = 4 ∧ faceRow P A = G2S4.aRow ∧ T ⊆ A) :
    2 * ((facetRows P).map fun R => if R = r35Row then 1 else 0).sum ≤
      ((facetRows P).map fun R => if R = G2S4.aRow then 1 else 0).sum := by
  let Fs := (hP.kfaces_finite 4).toFinset
  let Src := Fs.filter (fun F => faceRow P F = r35Row)
  let Dst := Fs.filter (fun A => faceRow P A = G2S4.aRow)
  let rel := fun F A => ∃ T ∈ faces P, T ⊆ F ∧ T ⊆ A ∧ dim T = 3 ∧ tri3 P T = (6,10,6)
  have mFs : ∀ {F}, F ∈ Fs ↔ F ∈ faces P ∧ dim F = 4 := fun {F} => by
    rw [Set.Finite.mem_toFinset]; rfl
  have mSrc : ∀ {F}, F ∈ Src ↔ (F ∈ faces P ∧ dim F = 4) ∧ faceRow P F = r35Row := fun {F} => by
    rw [Finset.mem_filter,mFs]
  have mDst : ∀ {F}, F ∈ Dst ↔ (F ∈ faces P ∧ dim F = 4) ∧ faceRow P F = G2S4.aRow := fun {F} => by
    rw [Finset.mem_filter,mFs]
  have row : ∀ F ∈ Src, 2 ≤ (Dst.filter (rel F)).card := by
    intro F hFS
    obtain ⟨⟨hF,hF4⟩,hFR⟩ := mSrc.1 hFS
    let B := (hP.below_finite F 3).toFinset.filter (fun T => tri3 P T = (6,10,6))
    have hBc : B.card = 2 := by
      rw [← hP.tcnt_eq_card]
      exact (hP.r35_six_ridge_counts_of_sixteen_mod_four hv (by rw [hh]) hF hF4 hFR).2
    have hcover : B ⊆ (Dst.filter (rel F)).image (fun A => F ∩ A) := by
      intro T hTB
      obtain ⟨hTb,ht⟩ := Finset.mem_filter.1 hTB
      rw [Set.Finite.mem_toFinset] at hTb
      obtain ⟨hT,hTF,hT3⟩ := hTb
      obtain ⟨A,hA,hA4,hAR,hTA⟩ := hpartner F hF hF4 hFR T hT hTF hT3 ht
      have hFA : F ≠ A := by
        intro he
        have hn := congrArg Row.n hFR
        have hm := congrArg Row.n hAR
        change cnt P F 0 = 8 at hn
        change cnt P A 0 = 7 at hm
        rw [he] at hn
        omega
      exact Finset.mem_image.2 ⟨A,Finset.mem_filter.2
        ⟨mDst.2 ⟨⟨hA,hA4⟩,hAR⟩,T,hT,hTF,hTA,hT3,ht⟩,
        (hP.three_face_eq_inter hF hF4 hA hA4 hFA hT hT3 hTF hTA).symm⟩
    have hb := (Finset.card_le_card hcover).trans Finset.card_image_le
    omega
  have col : ∀ A ∈ Dst, (Src.filter (fun F => rel F A)).card ≤ 1 := by
    intro A hAD
    obtain ⟨⟨hA,hA4⟩,hAR⟩ := mDst.1 hAD
    have hA7 : cnt P A 0 = 7 := congrArg Row.n hAR
    apply Finset.card_le_one.2
    intro F hFS H hHS
    obtain ⟨hFS,T,hT,hTF,hTA,hT3,ht⟩ := Finset.mem_filter.1 hFS
    obtain ⟨hHS,U,hU,hUH,hUA,hU3,hu⟩ := Finset.mem_filter.1 hHS
    obtain ⟨⟨hF,hF4⟩,hFR⟩ := mSrc.1 hFS
    obtain ⟨⟨hH,hH4⟩,hHR⟩ := mSrc.1 hHS
    have hF8 : cnt P F 0 = 8 := congrArg Row.n hFR
    have hH8 : cnt P H 0 = 8 := congrArg Row.n hHR
    have he := hP.six_vertex_ridge_unique_of_seven_no_big hA7 (hz A hA hA4 hAR)
      hT hTA hT3 (congrArg Prod.fst ht) hU hUA hU3 (congrArg Prod.fst hu)
    exact hP.ridge_neighbour_unique hA hA4 hF hF4
      (by intro he; rw [he] at hF8; omega) hH hH4
      (by intro he; rw [he] at hH8; omega) hT hT3 hTA hTF (he.symm ▸ hUH)
  have hr := Finset.sum_le_sum row
  have hc := Finset.sum_le_sum col
  have hs : ∑ F ∈ Src, (Dst.filter (rel F)).card = ∑ A ∈ Dst, (Src.filter (fun F => rel F A)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hs,Finset.sum_const,smul_eq_mul] at hr
  rw [Finset.sum_const,smul_eq_mul,mul_one] at hc
  have hsc : ((facetRows P).map fun R => if R = r35Row then 1 else 0).sum = Src.card := by
    rw [hP.facetRows_sum,Finset.card_filter]
  have hdc : ((facetRows P).map fun R => if R = G2S4.aRow then 1 else 0).sum = Dst.card := by
    rw [hP.facetRows_sum,Finset.card_filter]
  omega

end Kalai5
