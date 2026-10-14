import Kalai5.Endpoints.LastBCommonApex
import Kalai5.Endpoints.CrossEdgeStars

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.bipyr_prism_core_edges {T R : Set E5}
    (ht : tri3 P T = (5,9,6)) (hr : tri3 P R = (6,9,5))
    (hA : T ∩ R ∈ faces P) (hA2 : dim (T ∩ R) = 2) (hA3 : cnt P (T ∩ R) 0 = 3) :
    (edgeSet P T ∪ edgeSet P R).ncard = 15 := by
  have he : edgeSet P T ∩ edgeSet P R = edgeSet P (T ∩ R) := by
    ext e
    simp only [edgeSet,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.subset_inter_iff]
    tauto
  have hc := Set.ncard_union_add_ncard_inter (edgeSet P T) (edgeSet P R)
    (hP.below_finite T 1) (hP.below_finite R 1)
  rw [he] at hc
  change (edgeSet P T ∪ edgeSet P R).ncard + cnt P (T ∩ R) 1 = cnt P T 1 + cnt P R 1 at hc
  rw [hP.cnt_one_of_two hA hA2,hA3] at hc
  have hte : cnt P T 1 = 9 := congrArg (fun t => t.2.1) ht
  have hre : cnt P R 1 = 9 := congrArg (fun t => t.2.1) hr
  omega

/-- When two prism quadrilaterals use one apex and a third uses the other,
their cross edges add at least five edges to the fifteen-edge core. -/
theorem IsCSPolytope5.bipyr_prism_split_apices_edges {F T R : Set E5}
    (hTF : T ⊆ F) (ht : tri3 P T = (5,9,6))
    (hR : R ∈ faces P) (hRF : R ⊆ F) (hR3 : dim R = 3) (hr : tri3 P R = (6,9,5))
    (hA : T ∩ R ∈ faces P) (hA2 : dim (T ∩ R) = 2) (hA3 : cnt P (T ∩ R) 0 = 3)
    (q y a : Fin 3 → Set E5) (hqinj : Function.Injective q)
    (hq : ∀ i, q i ∈ faces P ∧ q i ⊆ R ∧ dim (q i) = 2 ∧ cnt P (q i) 0 = 4)
    (hy : ∀ i, y i ∈ faces P ∧ y i ⊆ F ∧ dim (y i) = 3 ∧ tri3 P (y i) = (5,8,5))
    (hqi : ∀ i, q i = R ∩ y i)
    (ha : ∀ i, a i ∈ vset P T ∧ a i ∉ vset P R ∧ vset P (y i) = insert (a i) (vset P (q i)))
    (i j k : Fin 3) (hij : i ≠ j) (he : a i = a j) (hne : a i ≠ a k) :
    20 ≤ cnt P F 1 := by
  have hR6 : cnt P R 0 = 6 := congrArg Prod.fst hr
  have hcover := (hP.six_vertex_quad_pair hR6 (hq i).1 (hq i).2.1 (hq i).2.2.1 (hq i).2.2.2
    (hq j).1 (hq j).2.1 (hq j).2.2.1 (hq j).2.2.2 (fun h => hij (hqinj h))).1
  have hedge (l : Fin 3) (v : Set E5) (hv : v ∈ vset P (q l)) :
      ∃ e, e ∈ edgeSet P F ∧ vset P e = {a l,v} := by
    have hap : a l ∈ vset P (y l) := by rw [(ha l).2.2]; exact Or.inl rfl
    obtain ⟨e,heF,hev⟩ := hP.square_pyramid_apex_edge (hy l).1 (hy l).2.2.1 (hy l).2.2.2
      (hq l).1 (by rw [hqi l]; exact inter_subset_right) (hq l).2.2.1 (hq l).2.2.2
      hap (fun h => (ha l).2.1 (vset_mono' (hq l).2.1 h)) (ha l).2.2 hv
    exact ⟨e,⟨heF.1,heF.2.1.trans (hy l).2.1,heF.2.2⟩,hev⟩
  let U := vset P R \ vset P T
  let V := vset P (q k) \ vset P T
  have hU3 : U.ncard = 3 := by
    have hc := Set.ncard_inter_add_ncard_sdiff_eq_ncard (vset P R) (vset P T) (hP.vset_finite R)
    rw [Set.inter_comm,← vset_inter',← cnt_eq_vset,← cnt_eq_vset,hA3,hR6] at hc
    change 3 + U.ncard = 6 at hc
    omega
  have hV2 : V.ncard = 2 := by
    have hc := hP.prism_triangle_quad_inter_two hR hR3 hr hA inter_subset_right hA2 hA3
      (hq k).1 (hq k).2.1 (hq k).2.2.1 (hq k).2.2.2
    have heq : (T ∩ R) ∩ q k = q k ∩ T := by
      ext v; exact ⟨fun h => ⟨h.2,h.1.1⟩,fun h => ⟨⟨h.2,(hq k).2.1 h.1⟩,h.1⟩⟩
    rw [heq,cnt_eq_vset,vset_inter'] at hc
    have hs := Set.ncard_inter_add_ncard_sdiff_eq_ncard (vset P (q k)) (vset P T) (hP.vset_finite (q k))
    rw [hc,← cnt_eq_vset,(hq k).2.2.2] at hs
    change 2 + V.ncard = 4 at hs
    omega
  apply hP.edges_twenty_of_cross_stars hTF hRF
    (hP.bipyr_prism_core_edges ht hr hA hA2 hA3).ge
    (show U ⊆ vset P R from fun _ h => h.1)
    (show V ⊆ vset P R from fun _ h => vset_mono' (hq k).2.1 h.1)
    (show ∀ v ∈ U, v ∉ vset P T from fun _ h => h.2)
    (show ∀ v ∈ V, v ∉ vset P T from fun _ h => h.2)
    (by omega) (by omega) (ha i).2.1 (ha k).2.1 hne
  · intro v hv
    have hm : v ∈ vset P (q i) ∪ vset P (q j) := hcover.symm ▸ hv.1
    rcases hm with hm | hm
    · exact hedge i v hm
    · rw [he]; exact hedge j v hm
  · intro v hv
    exact hedge k v hv.1

end Kalai5
