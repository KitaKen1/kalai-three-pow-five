import Kalai5.Endpoints.TwoPairZeroBPrisms

/-! Distinct quadrilaterals of H20 give disjoint mixed sets. -/
namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.two_pair_zero_H_shared_quad_unique
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 4) (hG : (flagDataOf P).G = 0) (hlt : (faces P).ncard < 243)
    {F X Q R : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hrow : faceRow P F = OnePairProfile.fullRow 20)
    (hX : X ∈ faces P) (hX4 : dim X = 4) (hFX : F ≠ X)
    (hQ : Q ∈ faces P) (hQF : Q ⊆ F) (hQX : Q ⊆ X) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hR : R ∈ faces P) (hRF : R ⊆ F) (hRX : R ⊆ X) (hR2 : dim R = 2) (hR4 : cnt P R 0 = 4) :
    Q = R := by
  apply hP.shared_quad_unique hF hF4 hX hX4 hFX ?_ hQ hQF hQX hQ2 hQ4 hR hRF hRX hR2 hR4
  exact hP.two_pair_zero_H_small_ridges hv hh hc hG hlt hF hF4
    (by omega) (by omega) hrow

/-- Two known Y facets exhaust the Y facets over a quadrilateral. -/
lemma IsCSPolytope5.two_pair_zero_quad_Y_exhaust
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 4) (hG : (flagDataOf P).G = 0) (hlt : (faces P).ncard < 243)
    {Q Y Z X : Set E5} (hQ : Q ∈ faces P) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hY : Y ∈ faces P) (hY4 : dim Y = 4) (hYr : faceRow P Y = excRow) (hQY : Q ⊆ Y)
    (hZ : Z ∈ faces P) (hZ4 : dim Z = 4) (hZr : faceRow P Z = excRow) (hQZ : Q ⊆ Z) (hYZ : Y ≠ Z)
    (hX : X ∈ faces P) (hX4 : dim X = 4) (hXr : faceRow P X = excRow) (hQX : Q ⊆ X) :
    X = Y ∨ X = Z := by
  let S := (hP.above_finite Q 4).toFinset.filter (fun F => faceRow P F = excRow)
  have hcard : S.card = 2 := hP.two_pair_zero_quad_two_Y hv hh hc hG hlt hQ hQ2 hQ4
  have mem (F : Set E5) (hf : F ∈ faces P) (hd : dim F = 4) (hr : faceRow P F = excRow)
      (hq : Q ⊆ F) : F ∈ S := by
    simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hf, hq, hd⟩, hr⟩
  have he : ({Y, Z} : Finset (Set E5)) = S := Finset.eq_of_subset_of_card_le
    (by intro F hF; rcases Finset.mem_insert.1 hF with rfl | hF
        · exact mem _ hY hY4 hYr hQY
        · exact Finset.mem_singleton.1 hF ▸ mem Z hZ hZ4 hZr hQZ)
    (by rw [hcard, Finset.card_pair hYZ])
  have hm := mem X hX hX4 hXr hQX
  rwa [← he, Finset.mem_insert, Finset.mem_singleton] at hm

lemma IsCSPolytope5.two_pair_zero_mixed_disjoint
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 4) (hG : (flagDataOf P).G = 0) (hlt : (faces P).ncard < 243)
    {H Q R : Set E5} (hH : H ∈ faces P) (hH4 : dim H = 4)
    (hHr : faceRow P H = OnePairProfile.fullRow 20)
    (hQ : Q ∈ faces P) (hQH : Q ⊆ H) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hR : R ∈ faces P) (hRH : R ⊆ H) (hR2 : dim R = 2) (hR4 : cnt P R 0 = 4) (hQR : Q ≠ R)
    (a : OnePairPrism P Q) (b : OnePairPrism P R) : Disjoint a.mixed b.mixed := by
  have hH8 : cnt P H 0 = 8 := congrArg Row.n hHr
  have neq (X : Set E5) (hr : faceRow P X = excRow) : H ≠ X := by
    have hx : cnt P X 0 = 7 := congrArg Row.n hr
    intro he; rw [he] at hH8; omega
  have hqaY : Q ⊆ a.Y := a.hQK.trans (a.hKI ▸ inter_subset_left)
  have hqaZ : Q ⊆ a.Z := a.hQK.trans (a.hKI ▸ inter_subset_right)
  have hrbY : R ⊆ b.Y := b.hQK.trans (b.hKI ▸ inter_subset_left)
  rw [Set.disjoint_left]
  intro T ha hb
  have haY : T ⊆ a.Y := ha.2.1.trans (a.hKI ▸ inter_subset_left)
  have haZ : T ⊆ a.Z := ha.2.1.trans (a.hKI ▸ inter_subset_right)
  have hbY : T ⊆ b.Y := hb.2.1.trans (b.hKI ▸ inter_subset_left)
  rcases hP.two_pair_zero_quad_Y_exhaust hv hh hc hG hlt ha.1 ha.2.2.1 ha.2.2.2.1
    a.hY a.hY4 a.hYrow haY a.hZ a.hZ4 a.hZrow haZ a.hYZ b.hY b.hY4 b.hYrow hbY with he | he
  · exact hQR (hP.two_pair_zero_H_shared_quad_unique hv hh hc hG hlt
      hH hH4 hHr a.hY a.hY4 (neq a.Y a.hYrow) hQ hQH hqaY hQ2 hQ4
      hR hRH (he ▸ hrbY) hR2 hR4)
  · exact hQR (hP.two_pair_zero_H_shared_quad_unique hv hh hc hG hlt
      hH hH4 hHr a.hZ a.hZ4 (neq a.Z a.hZrow) hQ hQH hqaZ hQ2 hQ4
      hR hRH (he ▸ hrbY) hR2 hR4)


end Kalai5
