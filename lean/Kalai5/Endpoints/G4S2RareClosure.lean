import Kalai5.Endpoints.RareRowRidges

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Profile A has only one antipodal pair of R35 facets. Their necessary
special ridge has no possible second facet. -/
theorem IsCSPolytope5.g4s2_A_profile_false
    (hp : (facetRows P).Perm
      (TwoPairPositiveProfile.g4s2PairsA ++ TwoPairPositiveProfile.g4s2PairsA)) : False := by
  let A : Set (ℕ × ℕ × ℕ) := {(4,6,4),(5,8,5),(6,9,5)}
  have hc : ((facetRows P).map fun S => if S = r35Row then 1 else 0).sum = 2 := by
    rw [(hp.map _).sum_eq]
    decide +kernel
  have hother : ∀ F ∈ faces P, dim F = 4 → faceRow P F ≠ r35Row →
      ∀ T ∈ faces P, T ⊆ F → dim T = 3 → tri3 P T ∈ A := by
    intro F hF h4 hne T hT hTF hT3
    have hm : faceRow P F ∈ facetRows P := by
      rw [hP.facetRows_eq]
      exact List.mem_map.2 ⟨F,Finset.mem_toList.2 (by
        rw [Set.Finite.mem_toFinset]; exact ⟨hF,h4⟩),rfl⟩
    have hr : faceRow P F = excRow ∨ faceRow P F = ⟨7,17,18,8,36⟩ ∨
        faceRow P F = r35Row ∨ faceRow P F = r0Row := by
      simpa only [TwoPairPositiveProfile.g4s2PairsA,r35Row,r0Row,List.mem_append,
        List.mem_cons,List.not_mem_nil,or_false,or_self,or_self_left,or_assoc] using hp.mem_iff.1 hm
    have ht : tri3 P T = (4,6,4) ∨ tri3 P T = (5,8,5) ∨ tri3 P T = (6,9,5) := by
      rcases hr with hy | hd | hr | hr
      · exact hP.g4s2_small_ridge_types hF h4 (Or.inl hy) hT hTF hT3
      · exact hP.g4s2_small_ridge_types hF h4 (Or.inr hd) hT hTF hT3
      · exact False.elim (hne hr)
      · exact hP.r0_type_cases hF h4 hr hT hTF hT3
    exact ht
  have hmem : r35Row ∈ facetRows P := hp.mem_iff.2 (by decide +kernel)
  obtain ⟨F,hF,h4,hR⟩ := hP.mem_facetRows hmem
  have hz (t : ℕ × ℕ × ℕ) (ht : t ∉ A) : tcnt P F t = 0 := by
    by_contra hn
    obtain ⟨T,hT,hTF,hT3,he⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F t)
    have hh := hP.ridge_types_transfer_of_two_row hc A hother hF h4 hT hTF hT3
    exact ht (he ▸ hh)
  have h6 := hz (6,10,6) (by decide +kernel)
  have h7 := hz (7,11,6) (by decide +kernel)
  have hs := hP.r35_has_special_ridge hF h4 hR
  omega

theorem IsCSPolytope5.fewFull18_positive_g4s2_A_ne
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ≠ TwoPairPositiveProfile.g4s2PairsA := by
  intro he
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  rw [he] at hp
  exact hP.g4s2_A_profile_false hp

/-- Only C remains in the G4S2 cell. -/
theorem IsCSPolytope5.fewFull18_positive_g4s2_unique_C
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243)
    (hG : (flagDataOf P).G = 4) (hS : (flagDataOf P).Gs = 2) :
    positivePairRows P = TwoPairPositiveProfile.g4s2PairsC := by
  have hm := hP.fewFull18_positive_g4s2_two_profiles hv hh h1 h6 hlt hG hS
  have hn := hP.fewFull18_positive_g4s2_A_ne hv hh h1 h6 hlt
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  exact hm.resolve_left hn

end Kalai5
