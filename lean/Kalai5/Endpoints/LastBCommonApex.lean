import Kalai5.Endpoints.LastBApexTriangles

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Three pyramids on the prism quadrilaterals cannot all use the same
apex: their three triangles and the prism triangle would avoid the other
bipyramid vertex, leaving too few polygons incident to that vertex. -/
theorem IsCSPolytope5.bipyr_prism_common_apex_false {F T R a : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (ht : tri3 P T = (5,9,6))
    (hR : R ∈ faces P) (hR3 : dim R = 3) (hr : tri3 P R = (6,9,5))
    (hA : T ∩ R ∈ faces P) (hA2 : dim (T ∩ R) = 2) (hA3 : cnt P (T ∩ R) 0 = 3)
    (q y : Fin 3 → Set E5) (hqinj : Function.Injective q)
    (hq : ∀ i, q i ∈ faces P ∧ q i ⊆ R ∧ dim (q i) = 2 ∧ cnt P (q i) 0 = 4)
    (hy : ∀ i, y i ∈ faces P ∧ y i ⊆ F ∧ dim (y i) = 3 ∧ tri3 P (y i) = (5,8,5))
    (hqi : ∀ i, q i = R ∩ y i)
    (haT : a ∈ vset P T) (haR : a ∉ vset P R)
    (hvs : ∀ i, vset P (y i) = insert a (vset P (q i))) : False := by
  have hi (i : Fin 3) := hP.bipyr_prism_pyramid_triangle hT hT3 ht hR hR3 hr hA hA2 hA3
    (hq i).1 (hq i).2.1 (hq i).2.2.1 (hq i).2.2.2
    (hy i).1 (hy i).2.2.1 (hy i).2.2.2 haT haR (hvs i)
  have hyt (i : Fin 3) : y i ≠ T := by
    intro he
    have hte : cnt P T 1 = 9 := congrArg (fun t => t.2.1) ht
    have hye : cnt P (y i) 1 = 8 := congrArg (fun t => t.2.1) (hy i).2.2.2
    rw [he] at hye
    omega
  have hinj : Function.Injective (fun i => T ∩ y i) := by
    intro i j he
    change T ∩ y i = T ∩ y j at he
    have hey : y i = y j := hP.ridge_partner_unique_inside hF hF4 (hi i).1
      (inter_subset_left.trans hTF) (hi i).2.1 hT hTF hT3 inter_subset_left
      (hy i).1 (hy i).2.1 (hy i).2.2.1 inter_subset_right (hyt i)
      (hy j).1 (hy j).2.1 (hy j).2.2.1 (by rw [he]; exact inter_subset_right) (hyt j)
    apply hqinj
    rw [hqi i,hqi j,hey]
  have haA : a ∉ vset P (T ∩ R) := fun h => haR (vset_mono' inter_subset_right h)
  have hsub : insert a (vset P (T ∩ R)) ⊆ vset P T :=
    Set.insert_subset_iff.2 ⟨haT,vset_mono' inter_subset_left⟩
  have hc : (vset P T \ insert a (vset P (T ∩ R))).ncard = 1 := by
    rw [Set.ncard_sdiff hsub ((hP.vset_finite (T ∩ R)).insert a),
      Set.ncard_insert_of_notMem haA (hP.vset_finite (T ∩ R)),← cnt_eq_vset,← cnt_eq_vset,hA3]
    have hT5 : cnt P T 0 = 5 := congrArg Prod.fst ht
    omega
  obtain ⟨u,hu⟩ := Set.nonempty_of_ncard_ne_zero (by omega :
    (vset P T \ insert a (vset P (T ∩ R))).ncard ≠ 0)
  have huA : u ∉ vset P (T ∩ R) := fun h => hu.2 (Or.inr h)
  have hui (i : Fin 3) : u ∉ vset P (T ∩ y i) := by
    intro hm
    rw [(hi i).2.2.2] at hm
    exact hm.elim (fun he => hu.2 (Or.inl he)) (fun h => huA h.1)
  let D : Finset (Set E5) := insert (T ∩ R) (Finset.univ.image (fun i => T ∩ y i))
  have hnot : T ∩ R ∉ Finset.univ.image (fun i => T ∩ y i) := by
    rintro hm
    obtain ⟨i,_,he⟩ := Finset.mem_image.1 hm
    have hai : a ∈ vset P (T ∩ y i) := by rw [(hi i).2.2.2]; exact Or.inl rfl
    exact haA (he ▸ hai)
  have hDc : D.card = 4 := by
    rw [Finset.card_insert_of_notMem hnot,Finset.card_image_of_injective _ hinj]
    decide
  have hd : ∀ Q ∈ D, Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ ¬ u ⊆ Q := by
    intro Q hQD
    rcases Finset.mem_insert.1 hQD with rfl | hQI
    · exact ⟨hA,inter_subset_left,hA2,fun h => huA ⟨hu.1.1,h,hu.1.2.2⟩⟩
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.1 hQI
      exact ⟨(hi i).1,inter_subset_left,(hi i).2.1,fun h => hui i ⟨hu.1.1,h,hu.1.2.2⟩⟩
  have hcap := hP.polygons_avoiding_vertex_capacity hT hT3 hu.1.1 hu.1.2.1 hu.1.2.2 D hd
  have hT6 : cnt P T 2 = 6 := congrArg (fun t => t.2.2) ht
  omega

end Kalai5
