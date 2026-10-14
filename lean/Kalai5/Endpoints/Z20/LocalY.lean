import Kalai5.Endpoints.Z20.Local

/-!
# Quadrilaterals in facets with few vertices

* `q4 P G`, `big2 P G`: the 2-faces of `P` inside `G` with four, resp. at least five, vertices;
  `q4 + 2 big2 ≤ exc` (`IsCSPolytope5.q4_add_big_le_exc`), with `exc = q4` when `big2 = 0`.
* Double counting: `2 q4 P F = Σ_{3-faces T ⊆ F} q4 P T` for a facet `F`.
* 3-faces with face numbers `(4,6,4)` have no quadrilateral; with `(5,8,5)` exactly one and no
  larger polygon.
* The facet profile of a facet with at most seven vertices (`smallX_classification`) counts its
  3-faces by face numbers; sums over the 3-faces group along the profile (`sum_of_cover`).
-/

namespace Kalai5

open Set

/-- A sum over a finite set grouped along a list containing all values. -/
lemma sum_of_cover {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β) {L : List β}
    (hL : L.Nodup) (hall : ∀ x ∈ s, f x ∈ L) (g : β → ℤ) :
    ∑ x ∈ s, g (f x) = (L.map fun t => ((s.filter fun x => f x = t).card : ℤ) * g t).sum := by
  rw [← Finset.sum_fiberwise_of_maps_to' (t := L.toFinset)
    (fun x hx => List.mem_toFinset.2 (hall x hx)) g]
  rw [List.sum_toFinset _ hL]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-- If the fibres over a list cover a finite set, every value lies in the list. -/
lemma all_mem_of_cover {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β) {L : List β}
    (hL : L.Nodup) (hcov : (L.map fun t => (s.filter fun x => f x = t).card).sum = s.card) :
    ∀ x ∈ s, f x ∈ L := by
  classical
  have h1 : (s.filter fun x => f x ∈ L).card =
      (L.map fun t => (s.filter fun x => f x = t).card).sum := by
    rw [← List.sum_toFinset _ hL]
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := L.toFinset) (fun x hx => by
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      exact List.mem_toFinset.2 hx.2)]
    refine Finset.sum_congr rfl fun t ht => ?_
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, -⟩, h⟩; exact ⟨hx, h⟩
    · rintro ⟨hx, h⟩; exact ⟨⟨hx, h ▸ List.mem_toFinset.1 ht⟩, h⟩
  have h2 : (s.filter fun x => f x ∈ L).card = s.card := by rw [h1, hcov]
  exact Finset.filter_card_eq h2

/-- Quadrilaterals of `P` inside `G`. -/
noncomputable def q4 (P G : Set E5) : ℕ :=
  {Q | Q ∈ faces P ∧ Q ⊆ G ∧ dim Q = 2 ∧ cnt P Q 0 = 4}.ncard

/-- 2-faces of `P` inside `G` with at least five vertices. -/
noncomputable def big2 (P G : Set E5) : ℕ :=
  {Q | Q ∈ faces P ∧ Q ⊆ G ∧ dim Q = 2 ∧ 5 ≤ cnt P Q 0}.ncard

/-- Face numbers `(f₀, f₁, f₂)` of a face. -/
noncomputable def tri3 (P T : Set E5) : ℕ × ℕ × ℕ := (cnt P T 0, cnt P T 1, cnt P T 2)

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.q4_eq_card (G : Set E5) :
    q4 P G = ((hP.below_finite G 2).toFinset.filter fun Q => cnt P Q 0 = 4).card := by
  classical
  rw [← Set.ncard_coe_finset]
  unfold q4
  congr 1
  ext Q
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
  tauto

lemma IsCSPolytope5.big2_eq_card (G : Set E5) :
    big2 P G = ((hP.below_finite G 2).toFinset.filter fun Q => 5 ≤ cnt P Q 0).card := by
  classical
  rw [← Set.ncard_coe_finset]
  unfold big2
  congr 1
  ext Q
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
  tauto

/-- **Polygon excess bounds quadrilaterals**: `q4 + 2 big2 ≤ exc`. -/
lemma IsCSPolytope5.q4_add_big_le_exc (G : Set E5) :
    (q4 P G : ℤ) + 2 * big2 P G ≤ exc P G := by
  classical
  rw [hP.exc_eq_sum G, hP.q4_eq_card, hP.big2_eq_card, ← Finset.sum_boole, ← Finset.sum_boole,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun Q hQ => ?_
  rw [Set.Finite.mem_toFinset] at hQ
  have := hP.three_le_cnt hQ.1 hQ.2.2
  split_ifs <;> omega

/-- Without polygons of five or more vertices the excess counts the quadrilaterals. -/
lemma IsCSPolytope5.exc_eq_q4_of_big (G : Set E5) (hb : big2 P G = 0) :
    exc P G = q4 P G := by
  classical
  rw [hP.big2_eq_card, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hb
  rw [hP.exc_eq_sum G, hP.q4_eq_card, ← Finset.sum_boole]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  have h5 := hb hQ
  rw [Set.Finite.mem_toFinset] at hQ
  have := hP.three_le_cnt hQ.1 hQ.2.2
  split_ifs <;> omega

/-- **Double counting quadrilaterals** in a facet: `2 q4 P F = Σ_{3-faces T ⊆ F} q4 P T`. -/
lemma IsCSPolytope5.two_q4_facet {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    2 * (q4 P F : ℤ) = ∑ T ∈ (hP.below_finite F 3).toFinset, (q4 P T : ℤ) := by
  classical
  have hq : ∀ G, (q4 P G : ℤ) =
      ∑ Q ∈ (hP.below_finite G 2).toFinset, if cnt P Q 0 = 4 then (1 : ℤ) else 0 := by
    intro G
    rw [hP.q4_eq_card, Finset.sum_boole]
  rw [Finset.sum_congr rfl fun T _ => hq T, hP.sum_below_comm F 2 3, hq F, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [Set.Finite.mem_toFinset] at hQ
  rw [hP.twoface_in_facet hF h4 hQ.1 hQ.2.1 hQ.2.2]
  push_cast
  ring

/-- A 3-face with face numbers `(4,6,4)` has no quadrilateral. -/
lemma IsCSPolytope5.q4_464 {T : Set E5} (hT : T ∈ faces P) (h3 : dim T = 3)
    (ht : tri3 P T = (4, 6, 4)) : q4 P T = 0 := by
  have he := hP.exc_threeface hT h3
  simp only [tri3, Prod.mk.injEq] at ht
  rw [ht.2.1, ht.2.2] at he
  have := hP.q4_add_big_le_exc T
  have hb : (0 : ℤ) ≤ big2 P T := by positivity
  omega

/-- A 3-face with face numbers `(5,8,5)` (a square pyramid) has exactly one quadrilateral and no
larger polygon. -/
lemma IsCSPolytope5.q4_585 {T : Set E5} (hT : T ∈ faces P) (h3 : dim T = 3)
    (ht : tri3 P T = (5, 8, 5)) : q4 P T = 1 ∧ big2 P T = 0 := by
  have he := hP.exc_threeface hT h3
  simp only [tri3, Prod.mk.injEq] at ht
  rw [ht.2.1, ht.2.2] at he
  have hle := hP.q4_add_big_le_exc T
  have hb0 : big2 P T = 0 := by
    have : (0 : ℤ) ≤ q4 P T := by positivity
    omega
  have hq := hP.exc_eq_q4_of_big T hb0
  refine ⟨?_, hb0⟩
  omega

/-- For a facet `F`, `facetCnt F t` counts the 3-faces of `P` inside `F` with face numbers `t`. -/
lemma IsCSPolytope5.facetCnt_eq_card {F : Set E5} (hF : F ∈ faces P) (t : ℕ × ℕ × ℕ) :
    facetCnt F t = ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = t).card := by
  classical
  obtain ⟨V, hV⟩ := hP.polytope
  have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
  rw [← Set.ncard_coe_finset]
  unfold facetCnt
  congr 1
  ext T
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
  unfold tri3 triBelow
  constructor
  · rintro ⟨hT, hd, ht⟩
    have hT' := (mem_faces_face_iff hF').1 hT
    refine ⟨⟨hV ▸ hT'.1, hT'.2, hd⟩, ?_⟩
    rw [hV, ← cnt_face_eq hF' hT'.2 0, ← cnt_face_eq hF' hT'.2 1, ← cnt_face_eq hF' hT'.2 2]
    exact ht
  · rintro ⟨⟨hT, hTF, hd⟩, ht⟩
    refine ⟨(mem_faces_face_iff hF').2 ⟨hV ▸ hT, hTF⟩, hd, ?_⟩
    rw [cnt_face_eq hF' hTF 0, cnt_face_eq hF' hTF 1, cnt_face_eq hF' hTF 2, ← hV]
    exact ht

/-- The extended row of a facet with at most seven vertices is in the catalogue, and its row is
the row of the facet in `P`. -/
lemma IsCSPolytope5.facet_rowX {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hn : cnt P F 0 ≤ 7) : rowXOf F ∈ smallRowsX ∧ rowOf F = faceRow P F := by
  classical
  obtain ⟨V, hV⟩ := hP.polytope
  have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
  have hFS : F = convexHull ℝ ((V.filter (· ∈ F) : Finset E5) : Set E5) :=
    face_eq_convexHull_filter hF'
  have hrowF : rowOf F = faceRow P F := by rw [rowOf_face hF', ← hV]
  have hreal : IsRealRowX (rowXOf F) := ⟨5, F, ⟨_, hFS⟩, h4, rfl⟩
  refine ⟨smallX_classification _ hreal ?_, hrowF⟩
  show (rowOf F).n ≤ 7
  rw [hrowF]
  exact hn

/-- The 3-faces of a facet with at most seven vertices: all face numbers lie in `fv7`, and the
counts are the facet profile. -/
lemma IsCSPolytope5.facet_profile {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hn : cnt P F 0 ≤ 7) :
    (∀ T ∈ (hP.below_finite F 3).toFinset, tri3 P T ∈ fv7) ∧
      (rowXOf F).2.1 = fv7.map fun t =>
        ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = t).card := by
  classical
  obtain ⟨hmem, hrow⟩ := hP.facet_rowX hF h4 hn
  have hprof : (rowXOf F).2.1 = fv7.map fun t =>
      ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = t).card := by
    show fv7.map (facetCnt F) = _
    exact List.map_congr_left fun t _ => hP.facetCnt_eq_card hF t
  refine ⟨all_mem_of_cover _ _ fv7_nodup ?_, hprof⟩
  have hcov := (smallRowsX_cover _ hmem).1
  rw [hprof] at hcov
  rw [hcov]
  show (rowOf F).r = _
  rw [hrow]
  simp only [faceRow]
  rw [cnt, Set.ncard_eq_toFinset_card _ (hP.below_finite F 3)]

end cs

end Kalai5
