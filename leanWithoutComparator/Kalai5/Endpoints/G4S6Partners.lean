import Kalai5.Endpoints.TwoPairPositiveG4S6

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.g4s6_small_no_6117
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = excRow ∨ faceRow P F = ⟨7,17,18,8,36⟩) :
    tcnt P F (6,11,7) = 0 := by
  rcases hR with hR | hR
  · have hn : cnt P F 0 = 7 := congrArg Row.n hR
    obtain ⟨hm,he⟩ := hP.facet_rowX hF h4 hn.le
    have hp := smallRowsX_exc _ hm (by change rowOf F = excRow; rw [he,hR])
    obtain ⟨_,_,_,_,_,hc,_⟩ := hP.profile_counts hF h4 hn.le hp
    rw [hP.tcnt_eq_card]
    exact hc
  · have hn : cnt P F 0 = 7 := congrArg Row.n hR
    obtain ⟨hm,he⟩ := hP.facet_rowX hF h4 hn.le
    have hcheck : ∀ X ∈ smallRowsX, X.1 = (⟨7,17,18,8,36⟩ : Row) →
        X.2.1 = [4,4,0,0,0,0,0] := by decide +kernel
    have hp := hcheck _ hm (by change rowOf F = _; rw [he,hR])
    obtain ⟨_,_,_,_,_,hc,_⟩ := hP.profile_counts hF h4 hn.le hp
    rw [hP.tcnt_eq_card]
    exact hc

theorem IsCSPolytope5.fewFull18_positive_g4s6_rows
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243)
    (hG : (flagDataOf P).G = 4) (hS : (flagDataOf P).Gs = 6)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    faceRow P F = excRow ∨ faceRow P F = ⟨7,17,18,8,36⟩ ∨
      faceRow P F = ⟨8,20,20,8,39⟩ := by
  have hp := hP.fewFull18_positive_g4s6_profile hv hh h1 h6 hlt hG hS
  have hm : faceRow P F ∈ facetRows P := by
    rw [hP.facetRows_eq]
    exact List.mem_map.2 ⟨F,Finset.mem_toList.2 (by
      rw [Set.Finite.mem_toFinset]; exact ⟨hF,h4⟩),rfl⟩
  have hm' := hp.mem_iff.1 hm
  simpa only [TwoPairPositiveProfile.g4s6Pairs,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,or_self,or_self_left,or_assoc] using hm'

theorem IsCSPolytope5.fewFull18_positive_g4s6_6117_forces_C
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243)
    (hG : (flagDataOf P).G = 4) (hS : (flagDataOf P).Gs = 6)
    {F T : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (ht : tri3 P T = (6,11,7)) :
    faceRow P F = ⟨8,20,20,8,39⟩ := by
  have hi := hP.one_le_tcnt hT hTF hT3
  rw [ht] at hi
  rcases hP.fewFull18_positive_g4s6_rows hv hh h1 h6 hlt hG hS hF h4 with hY | hR | hC
  · have hz := hP.g4s6_small_no_6117 hF h4 (Or.inl hY)
    omega
  · have hz := hP.g4s6_small_no_6117 hF h4 (Or.inr hR)
    omega
  · exact hC

/-- Every full facet has a distinct, non-antipodal full partner through its
unique (6,11,7) ridge. -/
theorem IsCSPolytope5.fewFull18_positive_g4s6_C_partner
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243)
    (hG : (flagDataOf P).G = 4) (hS : (flagDataOf P).Gs = 6)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hn : cnt P F 0 = 8) :
    ∃ H T, H ∈ faces P ∧ dim H = 4 ∧ H ≠ F ∧ H ≠ -F ∧
      faceRow P H = ⟨8,20,20,8,39⟩ ∧
      T ∈ faces P ∧ dim T = 3 ∧ tri3 P T = (6,11,7) ∧ T = F ∩ H ∧
      (∀ U ∈ faces P, U ⊆ F → dim U = 3 → tri3 P U = (6,11,7) → U = T) ∧
      (∀ L ∈ faces P, dim L = 4 → L ≠ F → T ⊆ L → L = H) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hc,_,_⟩ :=
    hP.fewFull18_positive_g4s6_full_profile hv hh h1 h6 hlt hG hS hF h4 hn
  obtain ⟨T,hsT⟩ := Set.ncard_eq_one.1 hc
  have hT : T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (6,11,7) := by
    have hm : T ∈ {U | U ∈ faces P ∧ U ⊆ F ∧ dim U = 3 ∧ tri3 P U = (6,11,7)} := by
      rw [hsT]; exact Set.mem_singleton _
    exact hm
  obtain ⟨H,hH,hH4,hHF,hTH⟩ := hP.exists_other_facet hT.1 hT.2.2.1 hT.2.1
  have hHC := hP.fewFull18_positive_g4s6_6117_forces_C hv hh h1 h6 hlt hG hS
    hH hH4 hT.1 hTH hT.2.2.1 hT.2.2.2
  have hneg : H ≠ -F := by
    intro he
    have hd := hP.disjoint_neg_of_full hF (hP.ne_of_dim_ne' (by rw [h4]; decide)) (by omega)
    obtain ⟨x,hx⟩ := hT.1.1
    exact Set.disjoint_left.1 hd (hT.2.1 hx) (he ▸ hTH hx)
  refine ⟨H,T,hH,hH4,hHF,hneg,hHC,hT.1,hT.2.2.1,hT.2.2.2,
    hP.three_face_eq_inter hF h4 hH hH4 hHF.symm hT.1 hT.2.2.1 hT.2.1 hTH,?_,?_⟩
  · intro U hU hUF hU3 hu
    have hm : U ∈ {U | U ∈ faces P ∧ U ⊆ F ∧ dim U = 3 ∧ tri3 P U = (6,11,7)} :=
      ⟨hU,hUF,hU3,hu⟩
    rw [hsT] at hm
    exact hm
  · intro L hL hL4 hLF hTL
    exact hP.ridge_neighbour_unique hF h4 hL hL4 hLF hH hH4 hHF hT.1 hT.2.2.1 hT.2.1 hTL hTH

end Kalai5
