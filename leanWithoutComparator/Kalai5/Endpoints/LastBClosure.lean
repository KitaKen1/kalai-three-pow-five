import Kalai5.Endpoints.LastBSplitEdges

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The last proposed B boundary forces at least twenty edges, whereas
its row has nineteen. No labelled graph or external certificate is used. -/
theorem IsCSPolytope5.last_b_ridge_profile_false {F : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8) (hF19 : cnt P F 1 = 19)
    (hprof : fv8.map (tcnt P F) = [3,3,1,1,0,0,0,0,0,0,0,0]) : False := by
  have hcnt := hprof
  simp only [fv8,List.map_cons,List.map_nil,List.cons.injEq] at hcnt
  obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (5,9,6))
  obtain ⟨R,hR,hRF,hR3,hr⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (6,9,5))
  obtain ⟨hA,hA2,hA3,hcover⟩ := hP.bipyr_prism_vertex_cover hF8 hT hTF hT3 ht hR hRF hR3 hr
  obtain ⟨Q,U,V,hQU,hQV,hUV,hset⟩ := Set.ncard_eq_three.1 (hP.q4_695 hR hR3 hr).1
  let q : Fin 3 → Set E5 := ![Q,U,V]
  have hqinj : Function.Injective q := by
    intro i j h
    fin_cases i <;> fin_cases j <;> dsimp [q] at h
    all_goals first | rfl | exact (hQU h).elim | exact (hQV h).elim |
      exact (hUV h).elim | exact (hQU h.symm).elim | exact (hQV h.symm).elim |
      exact (hUV h.symm).elim
  have mem (S : Set E5) (hS : S ∈ ({Q,U,V} : Set (Set E5))) :
      S ∈ faces P ∧ S ⊆ R ∧ dim S = 2 ∧ cnt P S 0 = 4 := by
    have hm : S ∈ {S | S ∈ faces P ∧ S ⊆ R ∧ dim S = 2 ∧ cnt P S 0 = 4} := by
      rw [hset]; exact hS
    exact hm
  have hq : ∀ i, q i ∈ faces P ∧ q i ⊆ R ∧ dim (q i) = 2 ∧ cnt P (q i) 0 = 4 := by
    intro i
    apply mem
    fin_cases i <;> simp [q]
  have hex : ∀ i, ∃ Y a,
      (Y ∈ faces P ∧ Y ⊆ F ∧ dim Y = 3 ∧ tri3 P Y = (5,8,5)) ∧ q i = R ∩ Y ∧
      (a ∈ vset P T ∧ a ∉ vset P R ∧ vset P Y = insert a (vset P (q i))) := by
    intro i
    obtain ⟨Y,hY,hYF,hY3,hy,hQI⟩ := hP.last_b_prism_quad_pyramid hF hF4 hF8 hprof
      hR hRF hR3 hr (hq i).1 (hq i).2.1 (hq i).2.2.1 (hq i).2.2.2
    obtain ⟨a,ha⟩ := hP.bipyr_prism_pyramid_apex hcover hYF hy (hq i).2.2.2 hQI
    exact ⟨Y,a,⟨hY,hYF,hY3,hy⟩,hQI,ha⟩
  choose y a hy hqi ha using hex
  have htwo : (vset P T \ vset P R).ncard = 2 := by
    have hc := Set.ncard_inter_add_ncard_sdiff_eq_ncard (vset P T) (vset P R) (hP.vset_finite T)
    rw [← vset_inter',← cnt_eq_vset,← cnt_eq_vset,hA3] at hc
    have hT5 : cnt P T 0 = 5 := congrArg Prod.fst ht
    omega
  have hpair : ∃ i j : Fin 3, i ≠ j ∧ a i = a j := by
    by_cases h01 : a 0 = a 1
    · exact ⟨0,1,by decide,h01⟩
    by_cases h02 : a 0 = a 2
    · exact ⟨0,2,by decide,h02⟩
    by_cases h12 : a 1 = a 2
    · exact ⟨1,2,by decide,h12⟩
    have hs : ({a 0,a 1,a 2} : Set (Set E5)) ⊆ vset P T \ vset P R := by
      rintro v (rfl | rfl | rfl)
      all_goals exact ⟨(ha _).1,(ha _).2.1⟩
    have hc := Set.ncard_le_ncard hs (hP.vset_finite T).sdiff
    rw [Set.ncard_eq_three.2 ⟨a 0,a 1,a 2,h01,h02,h12,rfl⟩,htwo] at hc
    omega
  obtain ⟨i,j,hij,he⟩ := hpair
  have hnot : ¬ ∀ k, a k = a i := by
    intro hall
    apply hP.bipyr_prism_common_apex_false hF hF4 hT hTF hT3 ht hR hR3 hr hA hA2 hA3
      q y hqinj hq hy hqi (ha i).1 (ha i).2.1
    intro k
    rw [(ha k).2.2,hall k]
  push Not at hnot
  obtain ⟨k,hk⟩ := hnot
  have h20 := hP.bipyr_prism_split_apices_edges hTF ht hR hRF hR3 hr hA hA2 hA3
    q y a hqinj hq hy hqi ha i j k hij he hk.symm
  omega

/-- All positive two-pair candidates at the last endpoint are impossible. -/
theorem IsCSPolytope5.fewFull18_positive_last_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) : False := by
  obtain ⟨hp,hstructure⟩ := hP.fewFull18_positive_last_b_structure hv hh h1 h6 hlt
  have hm : G2S4.bRow ∈ facetRows P := hp.mem_iff.2 (List.mem_append_left _ (by decide +kernel))
  obtain ⟨F,hF,hF4,hB⟩ := hP.mem_facetRows hm
  have hF8 : cnt P F 0 = 8 := congrArg Row.n hB
  have hF19 : cnt P F 1 = 19 := congrArg Row.e hB
  exact hP.last_b_ridge_profile_false hF hF4 hF8 hF19 (hstructure F hF hF4 hF8)

end Kalai5
