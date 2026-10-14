import Kalai5.Endpoints.TwoPairPositiveV12Profiles

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Two facets with a given row necessarily form an antipodal pair. -/
theorem IsCSPolytope5.two_row_facets_eq_or_neg {R : Row}
    (hc : ((facetRows P).map fun S => if S = R then 1 else 0).sum = 2)
    {F H : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4) (hFR : faceRow P F = R)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hHR : faceRow P H = R) : H = F ∨ H = -F := by
  let S := (hP.kfaces_finite 4).toFinset.filter (fun X => faceRow P X = R)
  have hn : S.card = 2 := by
    rw [hP.facetRows_sum] at hc
    simpa only [S,Finset.card_filter] using hc
  have hneg : -F ≠ F := fun he =>
    (hP.ne_of_dim_ne' (by rw [hF4]; decide)) (hP.eq_of_neg_eq hF he)
  have hFS : F ∈ S := by
    simp only [S,Finset.mem_filter,Set.Finite.mem_toFinset]
    exact ⟨⟨hF,hF4⟩,hFR⟩
  have hNS : -F ∈ S := by
    simp only [S,Finset.mem_filter,Set.Finite.mem_toFinset]
    exact ⟨⟨neg_mem_faces hP.symm hF,by rw [dim_neg,hF4]⟩,by rw [hP.faceRow_neg,hFR]⟩
  have hHS : H ∈ S := by
    simp only [S,Finset.mem_filter,Set.Finite.mem_toFinset]
    exact ⟨⟨hH,hH4⟩,hHR⟩
  have he : ({F,-F} : Finset (Set E5)) = S := Finset.eq_of_subset_of_card_le
    (by intro X hX; rcases Finset.mem_insert.1 hX with rfl | hX
        · exact hFS
        · exact Finset.mem_singleton.1 hX ▸ hNS)
    (by rw [hn,Finset.card_pair hneg.symm])
  rw [← he,Finset.mem_insert,Finset.mem_singleton] at hHS
  exact hHS

/-- A row occurring only in an antipodal pair cannot supply an exclusive
ridge type: every ridge has a second, non-antipodal facet. -/
theorem IsCSPolytope5.ridge_types_transfer_of_two_row {R : Row}
    (hc : ((facetRows P).map fun S => if S = R then 1 else 0).sum = 2)
    (A : Set (ℕ × ℕ × ℕ))
    (hother : ∀ F ∈ faces P, dim F = 4 → faceRow P F ≠ R →
      ∀ T ∈ faces P, T ⊆ F → dim T = 3 → tri3 P T ∈ A)
    {F T : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) : tri3 P T ∈ A := by
  by_contra hn
  have hFR : faceRow P F = R := by
    by_contra hne
    exact hn (hother F hF hF4 hne T hT hTF hT3)
  obtain ⟨H,hH,hH4,hHF,hTH⟩ := hP.exists_other_facet hT hT3 hTF
  have hHR : faceRow P H = R := by
    by_contra hne
    exact hn (hother H hH hH4 hne T hT hTH hT3)
  rcases hP.two_row_facets_eq_or_neg hc hF hF4 hFR hH hH4 hHR with he | he
  · exact hHF he
  · obtain ⟨x,hx⟩ := hT.1
    have hxneg : -x ∈ F := by
      have hh := hTH hx
      rwa [he,Set.mem_neg] at hh
    exact (hP.ne_of_dim_ne' (by rw [hF4]; decide))
      (hP.eq_of_mem_of_neg_mem hF (hTF hx) hxneg)

/-- The small rows accompanying both remaining G4S2 profiles have only
tetrahedral, square-pyramidal and triangular-prismatic ridges. -/
theorem IsCSPolytope5.g4s2_small_ridge_types
    {F T : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = excRow ∨ faceRow P F = ⟨7,17,18,8,36⟩)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) :
    tri3 P T = (4,6,4) ∨ tri3 P T = (5,8,5) ∨ tri3 P T = (6,9,5) := by
  have hn : cnt P F 0 = 7 := hR.elim (congrArg Row.n) (congrArg Row.n)
  obtain ⟨hm,he⟩ := hP.facet_rowX hF h4 hn.le
  have hcheck : ∀ X ∈ smallRowsX,
      (X.1 = excRow ∨ X.1 = ⟨7,17,18,8,36⟩) →
      X.2.1 = [2,3,0,1,0,0,0] ∨ X.2.1 = [4,4,0,0,0,0,0] := by decide +kernel
  have hp := hcheck _ hm (by change rowOf F = _ ∨ rowOf F = _; rw [he]; exact hR)
  have hmem : T ∈ (hP.below_finite F 3).toFinset := by
    rw [Set.Finite.mem_toFinset]; exact ⟨hT,hTF,hT3⟩
  rcases hp with hp | hp
  all_goals
    obtain ⟨_,_,h3,_,h5,h6,h7⟩ := hP.profile_counts hF h4 hn.le hp
    rcases hP.tri3_cases hF h4 hn.le hmem with ht | ht | ht | ht | ht | ht | ht
    · exact Or.inl ht
    · exact Or.inr (Or.inl ht)
    · exact False.elim (not_of_filter_card_zero h3 hmem ht)
    · exact Or.inr (Or.inr ht)
    · exact False.elim (not_of_filter_card_zero h5 hmem ht)
    · exact False.elim (not_of_filter_card_zero h6 hmem ht)
    · exact False.elim (not_of_filter_card_zero h7 hmem ht)

theorem IsCSPolytope5.r35_has_special_ridge {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = r35Row) :
    1 ≤ tcnt P F (6,10,6) ∨ 1 ≤ tcnt P F (7,11,6) := by
  have hR' := hR
  simp only [faceRow,r35Row,Row.mk.injEq] at hR'
  obtain ⟨h0,h1,h2,h3,hJ⟩ := hR'
  obtain ⟨X,hX,hX1,hX2⟩ := hP.facet_types_r7 hF h4 (by omega)
  rw [h0,h1,h2,h3,hJ] at hX1
  rcases smallRowsX_r35dual X hX hX1 with hp | hp | hp <;>
    rw [hp] at hX2 <;>
    simp only [fv7,List.map_cons,List.map_nil,List.cons.injEq] at hX2 <;> omega

end Kalai5
