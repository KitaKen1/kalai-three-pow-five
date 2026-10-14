import Kalai5.Gale.Affine
import Kalai5.Foundations

/-!
# Faces of `conv W` as index sets

For points `W : Fin n → E k`, a nonempty `F ⊆ Fin n` is a **face index** (`IsFaceIdx W F`) when
some affine function vanishes on `W(F)` and is positive at the other points.  Faces of
`conv (range W)` correspond exactly to face indices (`G ↦ idx W G`, `F ↦ conv W(F)`), so face
numbers become counts of index sets (`fvec_eq_card`, `flag2_zero_three_eq`).
-/

namespace Kalai5.Gale

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {k n : ℕ} (W : Fin n → E k)

/-- `F` indexes the vertex set of a face. -/
def IsFaceIdx (F : Finset (Fin n)) : Prop :=
  ∃ a ∈ affVals W, (∀ j ∈ F, a j = 0) ∧ ∀ j ∉ F, 0 < a j

open Classical in
/-- Indices of the points lying in `G`. -/
noncomputable def idx (G : Set (E k)) : Finset (Fin n) := Finset.univ.filter fun j => W j ∈ G

variable {W}

lemma mem_idx {G : Set (E k)} {j : Fin n} : j ∈ idx W G ↔ W j ∈ G := by
  classical simp [idx]

lemma coe_image_univ : ((Finset.univ.image W : Finset (E k)) : Set (E k)) = range W := by
  classical simp

lemma dim_convexHull (s : Set (E k)) : dim (convexHull ℝ s) = finrank ℝ (vectorSpan ℝ s) := by
  unfold dim
  rw [← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]

/-- A face is the convex hull of the points it contains. -/
lemma face_eq_conv_idx {G : Set (E k)} (hG : G ∈ faces (convexHull ℝ (range W))) :
    G = convexHull ℝ (W '' ↑(idx W G)) := by
  classical
  rw [← coe_image_univ] at hG
  refine (face_eq_convexHull_filter hG).trans ?_
  congr 1
  ext x
  simp only [Finset.coe_filter, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
    Set.mem_image, Finset.mem_coe, mem_idx]
  constructor
  · rintro ⟨⟨a, rfl⟩, h⟩; exact ⟨a, h, rfl⟩
  · rintro ⟨a, h, rfl⟩; exact ⟨⟨a, rfl⟩, h⟩

/-- The points of a face form a face index. -/
lemma isFaceIdx_idx {G : Set (E k)} (hG : G ∈ faces (convexHull ℝ (range W))) :
    IsFaceIdx W (idx W G) := by
  obtain ⟨l, hl⟩ := exists_functional hG
  obtain ⟨x0, hx0⟩ := hG.1
  have hx0' := hx0
  rw [hl] at hx0'
  set u := -(InnerProductSpace.toDual ℝ (E k)).symm l
  have hu : ∀ x, ⟪u, x⟫ = -l x := fun x => by
    simp [u, inner_neg_left, InnerProductSpace.toDual_symm_apply]
  refine ⟨evalMap W (u, l x0), evalMap_mem_affVals W _, fun j hj => ?_, fun j hj => ?_⟩
  · rw [mem_idx, hl] at hj
    rw [evalMap_apply, hu]
    have h1 := hj.2 x0 hx0'.1
    have h2 := hx0'.2 (W j) hj.1
    simp only
    linarith
  · rw [mem_idx, hl] at hj
    have hWQ : W j ∈ convexHull ℝ (range W) := subset_convexHull ℝ _ (mem_range_self j)
    simp only [Set.mem_ofPred_eq, not_and, not_forall, not_le] at hj
    obtain ⟨y, hy, hlt⟩ := hj hWQ
    have := hx0'.2 y hy
    rw [evalMap_apply, hu]
    simp only
    linarith

lemma idx_nonempty {G : Set (E k)} (hG : G ∈ faces (convexHull ℝ (range W))) :
    (idx W G).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have := face_eq_conv_idx hG
  rw [h, Finset.coe_empty, Set.image_empty, convexHull_empty] at this
  exact Set.not_nonempty_empty (this ▸ hG.1)

/-- A face index spans a face, whose points are exactly the indexed ones. -/
lemma conv_mem_faces {F : Finset (Fin n)} (hF : F.Nonempty) (h : IsFaceIdx W F) :
    convexHull ℝ (W '' ↑F) ∈ faces (convexHull ℝ (range W)) ∧
      idx W (convexHull ℝ (W '' ↑F)) = F := by
  obtain ⟨a, ⟨⟨u, c⟩, rfl⟩, h0, hpos⟩ := h
  have hval : ∀ j, evalMap W (u, c) j = ⟪u, W j⟫ + c := fun j => rfl
  let l : StrongDual ℝ (E k) := -(innerSL ℝ u)
  have hl : ∀ x, l x = -⟪u, x⟫ := fun x => by simp [l]
  have hQ : ∀ x ∈ convexHull ℝ (range W), 0 ≤ ⟪u, x⟫ + c := by
    intro x hx
    have hconv : Convex ℝ ((innerSL ℝ u).toLinearMap ⁻¹' Set.Ici (-c)) :=
      (convex_Ici _).linear_preimage _
    have hsub : range W ⊆ (innerSL ℝ u).toLinearMap ⁻¹' Set.Ici (-c) := by
      rintro _ ⟨j, rfl⟩
      simp only [Set.mem_preimage, Set.mem_Ici, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
      by_cases hj : j ∈ F
      · have := h0 j hj; rw [hval] at this; linarith
      · have := hpos j hj; rw [hval] at this; linarith
    have := convexHull_min hsub hconv hx
    simp only [Set.mem_preimage, Set.mem_Ici, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply] at this
    linarith
  set G := {x ∈ convexHull ℝ (range W) | ∀ y ∈ convexHull ℝ (range W), l y ≤ l x} with hGdef
  obtain ⟨j0, hj0⟩ := hF
  have hGW : ∀ j, W j ∈ G ↔ j ∈ F := by
    intro j
    constructor
    · rintro ⟨-, hmax⟩
      by_contra hj
      have := hmax (W j0) (subset_convexHull ℝ _ (mem_range_self j0))
      rw [hl, hl] at this
      have h1 := hpos j hj
      have h2 := h0 j0 hj0
      rw [hval] at h1 h2
      linarith
    · intro hj
      refine ⟨subset_convexHull ℝ _ (mem_range_self j), fun y hy => ?_⟩
      rw [hl, hl]
      have h1 := hQ y hy
      have h2 := h0 j hj
      rw [hval] at h2
      linarith
  have hGface : G ∈ faces (convexHull ℝ (range W)) :=
    ⟨⟨W j0, (hGW j0).2 hj0⟩, fun _ => ⟨l, rfl⟩⟩
  have hidx : idx W G = F := by
    ext j; rw [mem_idx, hGW]
  have hGeq : G = convexHull ℝ (W '' ↑F) := by
    have := face_eq_conv_idx hGface
    rwa [hidx] at this
  rw [← hGeq]
  exact ⟨hGface, hidx⟩

/-! ### Counting faces by index sets -/

open Classical in
/-- The `d`-dimensional faces counted by their index sets. -/
theorem fvec_eq_card (d : ℕ) :
    fvec (convexHull ℝ (range W)) d = (Finset.univ.filter fun F : Finset (Fin n) =>
      F.Nonempty ∧ IsFaceIdx W F ∧ finrank ℝ (vectorSpan ℝ (W '' ↑F)) = d).card := by
  unfold fvec
  rw [← Set.ncard_coe_finset]
  symm
  refine Set.ncard_congr (fun F _ => convexHull ℝ (W '' ↑F)) ?_ ?_ ?_
  · intro F hF
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hF
    exact ⟨(conv_mem_faces hF.1 hF.2.1).1, by rw [dim_convexHull]; exact hF.2.2⟩
  · intro F F' hF hF' heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hF hF'
    rw [← (conv_mem_faces hF.1 hF.2.1).2, ← (conv_mem_faces hF'.1 hF'.2.1).2, heq]
  · rintro G ⟨hG, hd⟩
    refine ⟨idx W G, ?_, (face_eq_conv_idx hG).symm⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    refine ⟨idx_nonempty hG, isFaceIdx_idx hG, ?_⟩
    rw [← dim_convexHull, ← face_eq_conv_idx hG]
    exact hd

open Classical in
/-- Vertex–facet incidences counted by index sets, when every point is a vertex. -/
theorem flag2_zero_three_eq (hinj : Function.Injective W) (hvert : ∀ j, IsFaceIdx W {j}) :
    flag2 (convexHull ℝ (range W)) 0 3 =
      ∑ F ∈ (Finset.univ.filter fun F : Finset (Fin n) =>
        F.Nonempty ∧ IsFaceIdx W F ∧ finrank ℝ (vectorSpan ℝ (W '' ↑F)) = 3), F.card := by
  classical
  set T := Finset.univ.filter fun F : Finset (Fin n) =>
    F.Nonempty ∧ IsFaceIdx W F ∧ finrank ℝ (vectorSpan ℝ (W '' ↑F)) = 3
  have hcard : ∑ F ∈ T, F.card = ((Finset.univ ×ˢ T).filter fun p => p.1 ∈ p.2).card := by
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [Finset.sum_boole]
    simp
  rw [hcard, flag2, ← Set.ncard_coe_finset]
  symm
  refine Set.ncard_congr (fun p _ => (({W p.1} : Set (E k)), convexHull ℝ (W '' ↑p.2))) ?_ ?_ ?_
  · rintro ⟨j, F⟩ hp
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, true_and, T,
      Finset.mem_filter, Set.mem_ofPred_eq] at hp
    obtain ⟨⟨hF, hFi, hd⟩, hj⟩ := hp
    have hjf := conv_mem_faces (Finset.singleton_nonempty j) (hvert j)
    simp only [Finset.coe_singleton, Set.image_singleton, convexHull_singleton] at hjf
    refine ⟨hjf.1, (conv_mem_faces hF hFi).1, ?_, dim_singleton _, ?_⟩
    · rw [Set.singleton_subset_iff]
      exact subset_convexHull ℝ _ (mem_image_of_mem W (Finset.mem_coe.2 hj))
    · rw [dim_convexHull]; exact hd
  · rintro ⟨j, F⟩ ⟨j', F'⟩ hp hp' heq
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, true_and, T,
      Finset.mem_filter, Set.mem_ofPred_eq] at hp hp'
    simp only [Prod.mk.injEq, Set.singleton_eq_singleton_iff] at heq
    refine Prod.ext (hinj heq.1) ?_
    rw [← (conv_mem_faces hp.1.1 hp.1.2.1).2, ← (conv_mem_faces hp'.1.1 hp'.1.2.1).2, heq.2]
  · rintro ⟨G1, G2⟩ ⟨hG1, hG2, hsub, hd1, hd3⟩
    obtain ⟨x, rfl⟩ := eq_singleton_of_dim_eq_zero hG1.1 hd1
    have hx := face_eq_conv_idx hG1
    obtain ⟨j, hj⟩ := idx_nonempty hG1
    have hxj : W j = x := by
      have := mem_idx.1 hj
      exact this
    refine ⟨(j, idx W G2), ?_, ?_⟩
    · simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, true_and, T,
        Finset.mem_filter, Set.mem_ofPred_eq]
      refine ⟨⟨idx_nonempty hG2, isFaceIdx_idx hG2, ?_⟩, ?_⟩
      · rw [← dim_convexHull, ← face_eq_conv_idx hG2]; exact hd3
      · rw [mem_idx, hxj]; exact hsub rfl
    · simp only [Prod.mk.injEq]
      exact ⟨by rw [hxj], (face_eq_conv_idx hG2).symm⟩

end Kalai5.Gale
