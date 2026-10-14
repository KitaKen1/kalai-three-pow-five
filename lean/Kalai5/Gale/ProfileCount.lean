import Kalai5.Gale.Count
import Kalai5.Gale.CombX

/-!
# The extended row of `conv W` from the bit-sliced face vectors

Faces of `conv W` correspond to face indices, and containment of faces to containment of index
sets (`conv_subset_conv_iff`).  Hence the faces below (above) the face with mask `S` are the face
masks disjoint from the complement of `S` (containing `S`), and the facet and vertex profiles are
read off the bit-sliced vectors: `rowXOf (conv W) = (tab n).rowX …` (`rowXOf_eq`).
-/

namespace Kalai5.Gale

open Set Module

variable {n k : ℕ}

/-! ### Faces with a property, counted by their index sets -/

section faces

variable {W : Fin n → E k}

open Classical in
/-- The `d`-faces with a property `Φ`, counted by their index sets. -/
theorem ncard_faces_filter_eq_card (d : ℕ) (Φ : Set (E k) → Prop) :
    {G | G ∈ faces (convexHull ℝ (range W)) ∧ dim G = d ∧ Φ G}.ncard =
      (Finset.univ.filter fun F : Finset (Fin n) =>
        (F.Nonempty ∧ IsFaceIdx W F ∧ finrank ℝ (vectorSpan ℝ (W '' ↑F)) = d) ∧
          Φ (convexHull ℝ (W '' ↑F))).card := by
  rw [← Set.ncard_coe_finset]
  symm
  refine Set.ncard_congr (fun F _ => convexHull ℝ (W '' ↑F)) ?_ ?_ ?_
  · intro F hF
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hF
    exact ⟨(conv_mem_faces hF.1.1 hF.1.2.1).1, by rw [dim_convexHull]; exact hF.1.2.2, hF.2⟩
  · intro F F' hF hF' heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hF hF'
    rw [← (conv_mem_faces hF.1.1 hF.1.2.1).2, ← (conv_mem_faces hF'.1.1 hF'.1.2.1).2, heq]
  · rintro G ⟨hG, hd, hΦ⟩
    refine ⟨idx W G, ?_, (face_eq_conv_idx hG).symm⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    refine ⟨⟨idx_nonempty hG, isFaceIdx_idx hG, ?_⟩, ?_⟩
    · rw [← dim_convexHull, ← face_eq_conv_idx hG]; exact hd
    · rw [← face_eq_conv_idx hG]; exact hΦ

/-- **Containment of faces is containment of index sets.** -/
lemma conv_subset_conv_iff {F F' : Finset (Fin n)} (hF : F.Nonempty) (hFi : IsFaceIdx W F) :
    convexHull ℝ (W '' ↑F') ⊆ convexHull ℝ (W '' ↑F) ↔ F' ⊆ F := by
  constructor
  · intro h j hj
    have hmem : W j ∈ convexHull ℝ (W '' ↑F) :=
      h (subset_convexHull ℝ _ (Set.mem_image_of_mem W (Finset.mem_coe.2 hj)))
    rw [← (conv_mem_faces hF hFi).2, mem_idx]
    exact hmem
  · intro h
    exact convexHull_mono (Set.image_mono (Finset.coe_subset.2 h))

open Classical in
/-- Faces below a face, counted by index sets. -/
lemma cnt_conv_eq_card {F : Finset (Fin n)} (hF : F.Nonempty) (hFi : IsFaceIdx W F) (j : ℕ) :
    cnt (convexHull ℝ (range W)) (convexHull ℝ (W '' ↑F)) j =
      (Finset.univ.filter fun F' : Finset (Fin n) =>
        (F'.Nonempty ∧ IsFaceIdx W F' ∧ finrank ℝ (vectorSpan ℝ (W '' ↑F')) = j) ∧
          F' ⊆ F).card := by
  have e : {G | G ∈ faces (convexHull ℝ (range W)) ∧ G ⊆ convexHull ℝ (W '' ↑F) ∧ dim G = j} =
      {G | G ∈ faces (convexHull ℝ (range W)) ∧ dim G = j ∧ G ⊆ convexHull ℝ (W '' ↑F)} := by
    ext G; simp only [Set.mem_ofPred_eq]; tauto
  have h := ncard_faces_filter_eq_card (W := W) j (fun G => G ⊆ convexHull ℝ (W '' ↑F))
  rw [cnt, e, h]
  congr 1
  ext F'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr_right fun _ => conv_subset_conv_iff hF hFi

open Classical in
/-- Faces above a face, counted by index sets. -/
lemma upIn_conv_eq_card (F : Finset (Fin n)) (j : ℕ) :
    upIn (convexHull ℝ (range W)) (convexHull ℝ (W '' ↑F)) j =
      (Finset.univ.filter fun F' : Finset (Fin n) =>
        (F'.Nonempty ∧ IsFaceIdx W F' ∧ finrank ℝ (vectorSpan ℝ (W '' ↑F')) = j) ∧
          F ⊆ F').card := by
  have e : {G | G ∈ faces (convexHull ℝ (range W)) ∧ convexHull ℝ (W '' ↑F) ⊆ G ∧ dim G = j} =
      {G | G ∈ faces (convexHull ℝ (range W)) ∧ dim G = j ∧ convexHull ℝ (W '' ↑F) ⊆ G} := by
    ext G; simp only [Set.mem_ofPred_eq]; tauto
  have h := ncard_faces_filter_eq_card (W := W) j (fun G => convexHull ℝ (W '' ↑F) ⊆ G)
  rw [upIn, e, h]
  congr 1
  ext F'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr_right fun h' => conv_subset_conv_iff h'.1 h'.2.1

end faces

/-! ### Masks -/

lemma ofMask_subset_iff {S S' : ℕ} :
    ofMask n S' ⊆ ofMask n S ↔ ∀ j < n, (cmask n S).testBit j = true → S'.testBit j = false := by
  constructor
  · intro h j hj hc
    rw [cmask_testBit hj] at hc
    by_contra hS'
    have h1 : (⟨j, hj⟩ : Fin n) ∈ ofMask n S' := mem_ofMask.2 (by simpa using hS')
    have h2 := mem_ofMask.1 (h h1)
    simp only at h2
    rw [h2] at hc
    exact absurd hc (by simp)
  · intro h j hj
    rw [mem_ofMask] at hj ⊢
    by_contra hS
    have := h j j.2 (by rw [cmask_testBit j.2]; simpa using hS)
    rw [hj] at this
    exact absurd this (by simp)

lemma subset_ofMask_iff {S S' : ℕ} :
    ofMask n S ⊆ ofMask n S' ↔ ∀ j < n, S.testBit j = true → S'.testBit j = true := by
  constructor
  · intro h j hj hS
    have hmem : (⟨j, hj⟩ : Fin n) ∈ ofMask n S := mem_ofMask.2 hS
    have := mem_ofMask.1 (h hmem)
    simpa using this
  · intro h j hj
    rw [mem_ofMask] at hj ⊢
    exact h j j.2 hj

/-- Counting subsets through a boolean predicate on masks. -/
lemma card_filter_eq_length (P : Finset (Fin n) → Prop) {inst : DecidablePred P} (q : ℕ → Bool)
    (hq : ∀ S < 2 ^ n, q S = true ↔ P (ofMask n S)) :
    (Finset.univ.filter P).card = ((List.range (2 ^ n)).filter q).length := by
  classical
  rw [length_filter_range]
  have h1 : (Finset.range (2 ^ n)).filter (fun S => q S = true) =
      (Finset.range (2 ^ n)).filter (fun S => P (ofMask n S)) := by
    apply Finset.filter_congr
    intro S hS; exact hq S (Finset.mem_range.1 hS)
  rw [h1]
  have h2 : Finset.univ.filter P = ((Finset.range (2 ^ n)).filter fun S => P (ofMask n S)).image
      (ofMask n) := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hF
      obtain ⟨S, hS, rfl⟩ := exists_ofMask F
      exact ⟨S, ⟨hS, hF⟩, rfl⟩
    · rintro ⟨S, ⟨-, hS⟩, rfl⟩; exact hS
  rw [h2, Finset.card_image_of_injOn (ofMask_injOn.mono (by
    intro S hS; simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hS
    simpa using hS.1))]

lemma count_map_bitsList {α : Type*} [BEq α] (N x : ℕ) (f : ℕ → α) (t : α) :
    ((bitsList N x).map f).count t =
      ((List.range N).filter fun S => f S == t && x.testBit S).length := by
  unfold bitsList
  rw [List.count, List.countP_map, List.countP_filter, List.countP_eq_length_filter]
  rfl

/-! ### Faces below and above a face mask -/

variable {W : Fin n → E 4} {g : Fin n → Fin 2 → ℝ} {c : Fin n → ℕ} {m : ℕ}

section bits

variable (hspan : affineSpan ℝ (range W) = ⊤) (hg : IsGale W g) (hc : CodeFor g c m)
  (hcomp : ∀ S < 2 ^ n, ((tab n).covV (circuits (List.ofFn c))).testBit S = true ∨
    ((tab n).farV (candidates (List.ofFn c))).testBit S = true)
include hspan hg hc hcomp

lemma cnt_ofMask_eq {S : ℕ} (hS0 : (ofMask n S).Nonempty) (hfi : IsFaceIdx W (ofMask n S))
    (j : ℕ) :
    cnt (convexHull ℝ (range W)) (convexHull ℝ (W '' ↑(ofMask n S))) j =
      cntB (2 ^ n) ((tab n).dimV ((tab n).faceV (circuits (List.ofFn c))) (rkOf c) j &&&
        (tab n).disjV (cmask n S)) := by
  classical
  rw [cnt_conv_eq_card hS0 hfi]
  exact card_filter_eq_cntB _ _ fun S' hS' => by
    rw [Nat.testBit_land, Bool.and_eq_true, dimV_iff hspan hg hc hcomp j hS', tab_disjV_testBit,
      ofMask_subset_iff]
    exact and_congr_right fun _ => ⟨fun h => h.2, fun h => ⟨hS', h⟩⟩

lemma upIn_ofMask_eq (S : ℕ) (j : ℕ) :
    upIn (convexHull ℝ (range W)) (convexHull ℝ (W '' ↑(ofMask n S))) j =
      cntB (2 ^ n) ((tab n).dimV ((tab n).faceV (circuits (List.ofFn c))) (rkOf c) j &&&
        (tab n).supV S) := by
  classical
  rw [upIn_conv_eq_card (ofMask n S) j]
  exact card_filter_eq_cntB _ _ fun S' hS' => by
    rw [Nat.testBit_land, Bool.and_eq_true, dimV_iff hspan hg hc hcomp j hS', tab_supV_testBit,
      subset_ofMask_iff]
    exact and_congr_right fun _ => ⟨fun h => h.2, fun h => ⟨hS', h⟩⟩

lemma triBelow_ofMask {S : ℕ} (hS0 : (ofMask n S).Nonempty) (hfi : IsFaceIdx W (ofMask n S)) :
    triBelow (convexHull ℝ (range W)) (convexHull ℝ (W '' ↑(ofMask n S))) =
      (tab n).below ((tab n).faceV (circuits (List.ofFn c))) (rkOf c) S := by
  simp only [triBelow, Tab.below, tab_n, cnt_ofMask_eq hspan hg hc hcomp hS0 hfi]

lemma triAbove_ofMask (S : ℕ) :
    triAbove (convexHull ℝ (range W)) (convexHull ℝ (W '' ↑(ofMask n S))) =
      (tab n).above ((tab n).faceV (circuits (List.ofFn c))) (rkOf c) S := by
  simp only [triAbove, Tab.above, tab_n, upIn_ofMask_eq hspan hg hc hcomp S]

/-- **The facet profile from the bit-sliced vectors.** -/
theorem facetCnt_eq (t : ℕ × ℕ × ℕ) :
    facetCnt (convexHull ℝ (range W)) t =
      ((bitsList (2 ^ n) ((tab n).dimV ((tab n).faceV (circuits (List.ofFn c))) (rkOf c) 3)).map
        ((tab n).below ((tab n).faceV (circuits (List.ofFn c))) (rkOf c))).count t := by
  classical
  have h := ncard_faces_filter_eq_card (W := W) 3
    (fun G => triBelow (convexHull ℝ (range W)) G = t)
  rw [facetCnt, h, count_map_bitsList]
  refine card_filter_eq_length _ _ fun S hS => ?_
  rw [Bool.and_eq_true, beq_iff_eq, dimV_iff hspan hg hc hcomp 3 hS]
  constructor
  · rintro ⟨h2, h1⟩
    exact ⟨h1, by rw [triBelow_ofMask hspan hg hc hcomp h1.1 h1.2.1]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [← triBelow_ofMask hspan hg hc hcomp h1.1 h1.2.1]; exact h2, h1⟩

/-- **The vertex profile from the bit-sliced vectors.** -/
theorem vertCnt_eq (t : ℕ × ℕ × ℕ) :
    vertCnt (convexHull ℝ (range W)) t =
      ((bitsList (2 ^ n) ((tab n).dimV ((tab n).faceV (circuits (List.ofFn c))) (rkOf c) 0)).map
        ((tab n).above ((tab n).faceV (circuits (List.ofFn c))) (rkOf c))).count t := by
  classical
  have h := ncard_faces_filter_eq_card (W := W) 0
    (fun G => triAbove (convexHull ℝ (range W)) G = t)
  rw [vertCnt, h, count_map_bitsList]
  refine card_filter_eq_length _ _ fun S hS => ?_
  rw [Bool.and_eq_true, beq_iff_eq, dimV_iff hspan hg hc hcomp 0 hS]
  constructor
  · rintro ⟨h2, h1⟩
    exact ⟨h1, by rw [triAbove_ofMask hspan hg hc hcomp S]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [← triAbove_ofMask hspan hg hc hcomp S]; exact h2, h1⟩

end bits

/-- **The extended row of `conv W` is the extended row of the bit-sliced face vectors.** -/
theorem rowXOf_eq (hspan : affineSpan ℝ (range W) = ⊤) (hinj : Function.Injective W)
    (hvert : ∀ j, IsFaceIdx W {j}) (hg : IsGale W g) (hc : CodeFor g c m)
    (hcomp : ∀ S < 2 ^ n, ((tab n).covV (circuits (List.ofFn c))).testBit S = true ∨
      ((tab n).farV (candidates (List.ofFn c))).testBit S = true) :
    rowXOf (convexHull ℝ (range W)) =
      (tab n).rowX ((tab n).faceV (circuits (List.ofFn c))) (rkOf c) := by
  unfold rowXOf Tab.rowX Tab.facetProf Tab.vertProf
  rw [rowOf_eq hspan hinj hvert hg hc hcomp]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · exact List.map_congr_left fun t _ => facetCnt_eq hspan hg hc hcomp t
  · exact List.map_congr_left fun t _ => vertCnt_eq hspan hg hc hcomp t

end Kalai5.Gale
