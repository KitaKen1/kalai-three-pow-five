import Kalai5.Pyramid.FullPyramidGeneral
import Kalai5.Endpoints.FullPolygonRowBudget

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- If a ridge misses exactly one vertex of its facet, that vertex is
an apex and every other vertex lies in the ridge. -/
theorem IsCSPolytope5.pyramid_apex_of_vertex_difference_one {F T : Set E5}
    (hTF : T ⊆ F) (hc : cnt P F 0 = cnt P T 0 + 1) :
    ∃ v, v ∈ faces P ∧ dim v = 0 ∧ v ⊆ F ∧ ¬ v ⊆ T ∧
      ∀ w ∈ faces P, dim w = 0 → w ⊆ F → w ≠ v → w ⊆ T := by
  have hn : (vset P F \ vset P T).ncard = 1 := by
    rw [Set.ncard_sdiff (vset_mono' hTF) (hP.vset_finite T),← cnt_eq_vset,← cnt_eq_vset,hc]
    omega
  obtain ⟨v,he⟩ := Set.ncard_eq_one.1 hn
  have hv : v ∈ vset P F \ vset P T := by rw [he]; exact Set.mem_singleton v
  refine ⟨v,hv.1.1,hv.1.2.2,hv.1.2.1,fun hs => hv.2 ⟨hv.1.1,hs,hv.1.2.2⟩,?_⟩
  intro w hw hw0 hwF hwv
  by_contra hwT
  have hm : w ∈ vset P F \ vset P T := ⟨⟨hw,hwF,hw0⟩,fun h => hwT h.2.1⟩
  rw [he,Set.mem_singleton_iff] at hm
  exact hwv hm

/-- A full pyramid forces four-divisibility of the total facet count. -/
theorem IsCSPolytope5.full_pyramid_facet_mod_four {F T : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hfull : 2 * cnt P F 0 = fvec P 0)
    (hT : T ∈ faces P) (hT3 : dim T = 3) (hTF : T ⊆ F)
    (hc : cnt P F 0 = cnt P T 0 + 1) : fvec P 4 % 4 = 0 := by
  obtain ⟨v,hv,hv0,hvF,hvT,hall⟩ := hP.pyramid_apex_of_vertex_difference_one hTF hc
  obtain ⟨V,L,hL,hR,hLP⟩ := hP.full_pyramid_bipyramid_model hF h4 hfull hv hv0 hvF hT hT3 hTF hvT hall
  have he : fvec P 4 = 2 * fvec (convexHull ℝ (V : Set (E 4))) 3 := by
    rw [← hLP,fvec_image_of_injective L hL,fvec_bipyr_facets hR.zero_mem_interior]
  obtain ⟨m,hm⟩ := hR.even_fvec 3 (by norm_num)
  omega

/-- At sixteen vertices and a facet count congruent to two modulo four,
a seven-vertex ridge would make its eight-vertex facet a full pyramid. -/
theorem IsCSPolytope5.seven_vertex_threeface_false
    (hv : fvec P 0 = 16) (hmod : fvec P 4 % 4 = 2)
    {T : Set E5} (hT : T ∈ faces P) (hT3 : dim T = 3) (hT7 : cnt P T 0 = 7) : False := by
  obtain ⟨F,hF,h4,hFP,hTF⟩ := hP.exists_other_facet hT hT3 (face_subset hT)
  have hbound := hP.two_mul_cnt_le hF hFP
  have hlt := hP.cnt_zero_lt hT hF hTF (by intro he; rw [he,h4] at hT3; omega)
  have hF8 : cnt P F 0 = 8 := by omega
  have he := hP.full_pyramid_facet_mod_four hF h4 (by omega) hT hT3 hTF (by omega)
  omega

theorem IsCSPolytope5.threeface_vertices_le_six_of_sixteen_mod_four
    (hv : fvec P 0 = 16) (hmod : fvec P 4 % 4 = 2)
    {T : Set E5} (hT : T ∈ faces P) (hT3 : dim T = 3) : cnt P T 0 ≤ 6 := by
  obtain ⟨F,hF,h4,hFP,hTF⟩ := hP.exists_other_facet hT hT3 (face_subset hT)
  have hbound := hP.two_mul_cnt_le hF hFP
  have hlt := hP.cnt_zero_lt hT hF hTF (by intro he; rw [he,h4] at hT3; omega)
  by_contra hn
  exact hP.seven_vertex_threeface_false hv hmod hT hT3 (by omega)

theorem IsCSPolytope5.tcnt_seven_zero_of_sixteen_mod_four
    (hv : fvec P 0 = 16) (hmod : fvec P 4 % 4 = 2) (F : Set E5) (e p : ℕ) :
    tcnt P F (7,e,p) = 0 := by
  by_contra hn
  obtain ⟨T,hT,_,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (7,e,p))
  exact hP.seven_vertex_threeface_false hv hmod hT hT3 (congrArg Prod.fst ht)

theorem IsCSPolytope5.r35_prism_one_of_sixteen_mod_four
    (hv : fvec P 0 = 16) (hmod : fvec P 4 % 4 = 2)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = r35Row) :
    tcnt P F (6,9,5) = 1 := by
  have he := hP.r35_event_one hF h4 hR
  rw [hP.tcnt_seven_zero_of_sixteen_mod_four hv hmod] at he
  omega

theorem IsCSPolytope5.big2_zero_of_r35_sixteen_mod_four
    (hv : fvec P 0 = 16) (hmod : fvec P 4 % 4 = 2) (hm : r35Row ∈ facetRows P)
    (X : Set E5) : big2 P X = 0 := by
  obtain ⟨F,hF,h4,hR⟩ := hP.mem_facetRows hm
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  have ht := hP.r35_prism_one_of_sixteen_mod_four hv hmod hF h4 hR
  have he := hP.exc_eq_faceRow hF h4
  rw [hR] at he
  norm_num [r35Row] at he
  exact hP.big2_zero_of_full_facet hF h4 (by omega)
    (hP.big2_zero_of_prism_exc_le_four (by omega) (by omega)) X

set_option maxHeartbeats 2000000 in
/-- The full-pyramid obstruction fixes all three six-vertex ridges of R35. -/
theorem IsCSPolytope5.r35_six_ridge_counts_of_sixteen_mod_four
    (hv : fvec P 0 = 16) (hmod : fvec P 4 % 4 = 2)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = r35Row) :
    tcnt P F (6,9,5) = 1 ∧ tcnt P F (6,10,6) = 2 := by
  have hpr := hP.r35_prism_one_of_sixteen_mod_four hv hmod hF h4 hR
  have hpy : tcnt P F (5,8,5) = 1 := by
    obtain ⟨_,hc⟩ := hP.r35_types hF h4 hR
    rcases hc with h | h | h <;> omega
  have hz1 := hP.tcnt_seven_zero_of_sixteen_mod_four hv hmod F 11 6
  have hz2 := hP.tcnt_seven_zero_of_sixteen_mod_four hv hmod F 12 7
  have hz3 := hP.tcnt_seven_zero_of_sixteen_mod_four hv hmod F 13 8
  have hz4 := hP.tcnt_seven_zero_of_sixteen_mod_four hv hmod F 14 9
  have hz5 := hP.tcnt_seven_zero_of_sixteen_mod_four hv hmod F 15 10
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  have hr : cnt P F 3 = 7 := congrArg Row.r hR
  have hp : cnt P F 2 = 17 := congrArg Row.p hR
  have hj : incid P F 0 3 = 35 := congrArg Row.J hR
  obtain ⟨c1,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  exact ⟨hpr,by omega⟩

end Kalai5
