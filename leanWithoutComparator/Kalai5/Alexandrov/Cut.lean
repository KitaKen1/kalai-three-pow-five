import Kalai5.Alexandrov.PolyBasic

/-!
# The cut lemma

For a convex polygon `Q = conv W` and an affine function `ℓ = ⟪·, d⟫ - β` which does not vanish on
all of `W`:

  `#(edges whose endpoints have opposite signs) + #(vertices with ℓ = 0) ≤ 2`

(`cut_lemma`, stated as a sum over the edges, the form used at a vertex figure).

Proof: the vertices with `ℓ = 0` and the crossing points of the cut edges are distinct extreme points
of `Q ∩ {ℓ ≥ 0}` lying on the line `ℓ = 0`; a set of extreme points on a line has at most two
elements (`card_le_two_of_line`).
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

lemma edges_finite (V : Finset (E n)) :
    {F | F ∈ faces (convexHull ℝ (V : Set (E n))) ∧ dim F = 1}.Finite :=
  (faces_finite_convexHull V).subset fun _ h => h.1

/-- The edges of `conv V`. -/
noncomputable def edgeFinset (V : Finset (E n)) : Finset (Set (E n)) := (edges_finite V).toFinset

lemma mem_edgeFinset {V : Finset (E n)} {F : Set (E n)} :
    F ∈ edgeFinset V ↔ F ∈ faces (convexHull ℝ (V : Set (E n))) ∧ dim F = 1 :=
  Set.Finite.mem_toFinset _

open Classical in
/-- **A polygon vertex lies on exactly two edges.** -/
lemma card_edges_at {V : Finset (E n)} (hcp : ConvPos V)
    (h2 : dim (convexHull ℝ (V : Set (E n))) = 2) {x : E n} (hx : x ∈ V) :
    ((edgeFinset V).filter fun F => x ∈ F).card = 2 := by
  classical
  rw [← card_nbrs hcp h2 hx]
  symm
  refine Finset.card_bij (fun y _ => convexHull ℝ ({x, y} : Set (E n))) ?_ ?_ ?_
  · intro y hy
    obtain ⟨hyV, hyx, F, hF, hF1, hxF, hyF⟩ := mem_nbrs.1 hy
    have hseg := edge_eq_segment hF hF1 (hcp x hx) (hcp y hyV) (Ne.symm hyx) hxF hyF
    rw [Finset.mem_filter, mem_edgeFinset, ← hseg]
    exact ⟨⟨hF, hF1⟩, hxF⟩
  · intro y hy y' hy' h
    obtain ⟨hy'V, hy'x, -⟩ := mem_nbrs.1 hy'
    obtain ⟨hyV, -, -⟩ := mem_nbrs.1 hy
    have hy'mem : y' ∈ convexHull ℝ ({x, y} : Set (E n)) := by
      rw [h]; exact subset_convexHull ℝ _ (by simp)
    have hsub : convexHull ℝ ({x, y} : Set (E n)) ⊆ convexHull ℝ (V : Set (E n)) :=
      convexHull_min (by
        rintro z (rfl | rfl)
        · exact subset_convexHull ℝ _ (by exact_mod_cast hx)
        · exact subset_convexHull ℝ _ (by exact_mod_cast hyV)) (convex_convexHull ℝ _)
    have hext : y' ∈ (convexHull ℝ ({x, y} : Set (E n))).extremePoints ℝ :=
      inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hy'mem, hcp y' hy'V⟩
    have := extremePoints_convexHull_subset hext
    rcases this with h1 | h1
    · exact absurd h1 hy'x
    · exact (Set.mem_singleton_iff.1 h1).symm
  · intro F hF
    rw [Finset.mem_filter, mem_edgeFinset] at hF
    obtain ⟨⟨hFf, hF1⟩, hxF⟩ := hF
    obtain ⟨p, q, hp, hq, hpq, hseg, hiff⟩ := filter_mem_edge hcp hFf hF1
    rcases (hiff x hx).1 hxF with rfl | rfl
    · exact ⟨q, mem_nbrs.2 ⟨hq, Ne.symm hpq, F, hFf, hF1, hxF, (hiff q hq).2 (Or.inr rfl)⟩,
        hseg.symm⟩
    · exact ⟨p, mem_nbrs.2 ⟨hp, hpq, F, hFf, hF1, hxF, (hiff p hp).2 (Or.inl rfl)⟩,
        by rw [hseg, Set.pair_comm]⟩

open Classical in
/-- Double counting of vertex–edge incidences in a polygon. -/
lemma sum_card_filter_edges {V : Finset (E n)} (hcp : ConvPos V)
    (h2 : dim (convexHull ℝ (V : Set (E n))) = 2) (S : Finset (E n)) (hS : S ⊆ V) :
    ∑ F ∈ edgeFinset V, (S.filter fun x => x ∈ F).card = 2 * S.card := by
  classical
  calc ∑ F ∈ edgeFinset V, (S.filter fun x => x ∈ F).card
        = ∑ F ∈ edgeFinset V, ∑ x ∈ S, if x ∈ F then 1 else 0 := by
          refine Finset.sum_congr rfl fun F _ => ?_
          rw [Finset.card_filter]
    _ = ∑ x ∈ S, ∑ F ∈ edgeFinset V, if x ∈ F then 1 else 0 := Finset.sum_comm
    _ = ∑ x ∈ S, 2 := by
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [← Finset.card_filter]
          exact card_edges_at hcp h2 (hS hx)
    _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

open Classical in
/-- **The cut lemma.** -/
theorem cut_lemma {W : Finset (E n)} (hcp : ConvPos W)
    (h2 : dim (convexHull ℝ (W : Set (E n))) = 2) (d : E n) (β : ℝ) (hne : ∃ z ∈ W, ⟪z, d⟫ ≠ β) :
    ∑ Φ ∈ edgeFinset W, (2 * (((W.filter fun x => x ∈ Φ ∧ β < ⟪x, d⟫).card) *
        (W.filter fun x => x ∈ Φ ∧ ⟪x, d⟫ < β).card) +
      (W.filter fun x => x ∈ Φ ∧ ⟪x, d⟫ = β).card) ≤ 4 := by
  classical
  set Q := convexHull ℝ (W : Set (E n)) with hQ
  set W0 := W.filter fun x => ⟪x, d⟫ = β with hW0
  -- the cut edges
  set cut : Set (E n) → Prop := fun Φ =>
    ∃ x ∈ W, x ∈ Φ ∧ β < ⟪x, d⟫ ∧ ∃ y ∈ W, y ∈ Φ ∧ ⟪y, d⟫ < β with hcutdef
  set C := (edgeFinset W).filter cut with hC
  -- per edge: `Pos * Neg` is the indicator of `cut`
  have hprod : ∀ Φ ∈ edgeFinset W,
      ((W.filter fun x => x ∈ Φ ∧ β < ⟪x, d⟫).card) *
        (W.filter fun x => x ∈ Φ ∧ ⟪x, d⟫ < β).card = if cut Φ then 1 else 0 := by
    intro Φ hΦ
    rw [mem_edgeFinset] at hΦ
    obtain ⟨p, q, hp, hq, hpq, -, hiff⟩ := filter_mem_edge hcp hΦ.1 hΦ.2
    have hsub : ∀ (P : E n → Prop) [DecidablePred P],
        (W.filter fun x => x ∈ Φ ∧ P x) ⊆ {p, q} := by
      intro P _ x hx
      rw [Finset.mem_filter] at hx
      rcases (hiff x hx.1).1 hx.2.1 with rfl | rfl <;> simp
    have hdisj : Disjoint (W.filter fun x => x ∈ Φ ∧ β < ⟪x, d⟫)
        (W.filter fun x => x ∈ Φ ∧ ⟪x, d⟫ < β) := by
      rw [Finset.disjoint_filter]
      intro x _ h1 h2'
      linarith [h1.2, h2'.2]
    have hsum : (W.filter fun x => x ∈ Φ ∧ β < ⟪x, d⟫).card +
        (W.filter fun x => x ∈ Φ ∧ ⟪x, d⟫ < β).card ≤ 2 := by
      rw [← Finset.card_union_of_disjoint hdisj]
      refine (Finset.card_le_card (Finset.union_subset (hsub _) (hsub _))).trans ?_
      exact Finset.card_le_two
    by_cases hc : cut Φ
    · rw [if_pos hc]
      obtain ⟨x, hxW, hxΦ, hx, y, hyW, hyΦ, hy⟩ := hc
      have h1 : 1 ≤ (W.filter fun x => x ∈ Φ ∧ β < ⟪x, d⟫).card :=
        Finset.card_pos.2 ⟨x, Finset.mem_filter.2 ⟨hxW, hxΦ, hx⟩⟩
      have h2' : 1 ≤ (W.filter fun x => x ∈ Φ ∧ ⟪x, d⟫ < β).card :=
        Finset.card_pos.2 ⟨y, Finset.mem_filter.2 ⟨hyW, hyΦ, hy⟩⟩
      have e1 : (W.filter fun x => x ∈ Φ ∧ β < ⟪x, d⟫).card = 1 := by omega
      have e2 : (W.filter fun x => x ∈ Φ ∧ ⟪x, d⟫ < β).card = 1 := by omega
      rw [e1, e2]
    · rw [if_neg hc]
      by_contra hne0
      apply hc
      have h1 : (W.filter fun x => x ∈ Φ ∧ β < ⟪x, d⟫).card ≠ 0 := fun h => hne0 (by rw [h, zero_mul])
      have h2' : (W.filter fun x => x ∈ Φ ∧ ⟪x, d⟫ < β).card ≠ 0 := fun h => hne0 (by rw [h, mul_zero])
      obtain ⟨x, hx⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero h1)
      obtain ⟨y, hy⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero h2')
      rw [Finset.mem_filter] at hx hy
      exact ⟨x, hx.1, hx.2.1, hx.2.2, y, hy.1, hy.2.1, hy.2.2⟩
  have hZ : ∀ Φ ∈ edgeFinset W, (W.filter fun x => x ∈ Φ ∧ ⟪x, d⟫ = β).card =
      (W0.filter fun x => x ∈ Φ).card := by
    intro Φ _
    rw [hW0, Finset.filter_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    tauto
  have hsplit : ∑ Φ ∈ edgeFinset W, (2 * (((W.filter fun x => x ∈ Φ ∧ β < ⟪x, d⟫).card) *
        (W.filter fun x => x ∈ Φ ∧ ⟪x, d⟫ < β).card) +
      (W.filter fun x => x ∈ Φ ∧ ⟪x, d⟫ = β).card) = 2 * C.card + 2 * W0.card := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_congr rfl hprod,
      Finset.sum_congr rfl hZ, sum_card_filter_edges hcp h2 W0 (Finset.filter_subset _ _),
      ← Finset.card_filter]
  rw [hsplit]
  suffices hmain : C.card + W0.card ≤ 2 by omega
  -- the degenerate case: `d` is orthogonal to the plane
  by_cases hdeg : ∀ y ∈ vectorSpan ℝ Q, ⟪y, d⟫ = 0
  · obtain ⟨z₀, hz₀W, hz₀⟩ := hne
    have hconst : ∀ x ∈ W, ⟪x, d⟫ = ⟪z₀, d⟫ := by
      intro x hx
      have := hdeg (x - z₀) (vsub_mem_vectorSpan ℝ (subset_convexHull ℝ _ (by exact_mod_cast hx))
        (subset_convexHull ℝ _ (by exact_mod_cast hz₀W)))
      rw [inner_sub_left] at this; linarith
    have hW0e : W0 = ∅ := by
      rw [hW0, Finset.filter_eq_empty_iff]
      intro x hx; rw [hconst x hx]; exact hz₀
    have hCe : C = ∅ := by
      rw [hC, Finset.filter_eq_empty_iff]
      rintro Φ - ⟨x, hxW, -, hx, y, hyW, -, hy⟩
      rw [hconst x hxW] at hx; rw [hconst y hyW] at hy; linarith
    rw [hW0e, hCe]; simp
  push_neg at hdeg
  obtain ⟨y₀, hy₀, hy₀d⟩ := hdeg
  -- the line `ℓ = 0` in the plane
  set U := vectorSpan ℝ Q ⊓ (ℝ ∙ d)ᗮ with hU
  have hUdim : finrank ℝ U ≤ 1 := by
    have hlt : U < vectorSpan ℝ Q := by
      refine lt_of_le_of_ne inf_le_left fun h => hy₀d ?_
      have : y₀ ∈ U := by rw [h]; exact hy₀
      exact (Submodule.mem_orthogonal_singleton_iff_inner_left.1 (Submodule.mem_inf.1 this).2)
    have := Submodule.finrank_lt_finrank_of_lt hlt
    have h2' : finrank ℝ (vectorSpan ℝ Q) = 2 := h2
    omega
  -- crossing points
  have hends : ∀ Φ ∈ C, ∃ pq : E n × E n, pq.1 ∈ W ∧ pq.1 ∈ Φ ∧ β < ⟪pq.1, d⟫ ∧
      pq.2 ∈ W ∧ pq.2 ∈ Φ ∧ ⟪pq.2, d⟫ < β := by
    intro Φ hΦ
    obtain ⟨x, hxW, hxΦ, hx, y, hyW, hyΦ, hy⟩ := (Finset.mem_filter.1 hΦ).2
    exact ⟨(x, y), hxW, hxΦ, hx, hyW, hyΦ, hy⟩
  choose! ends hends' using hends
  set tt : Set (E n) → ℝ := fun Φ =>
    (⟪(ends Φ).1, d⟫ - β) / (⟪(ends Φ).1, d⟫ - ⟪(ends Φ).2, d⟫) with htt
  set cross : Set (E n) → E n := fun Φ =>
    (ends Φ).1 + tt Φ • ((ends Φ).2 - (ends Φ).1) with hcross
  have htt01 : ∀ Φ ∈ C, 0 < tt Φ ∧ tt Φ < 1 := by
    intro Φ hΦ
    obtain ⟨-, -, h1, -, -, h2'⟩ := hends' Φ hΦ
    have hden : 0 < ⟪(ends Φ).1, d⟫ - ⟪(ends Φ).2, d⟫ := by linarith
    refine ⟨div_pos (by linarith) hden, (div_lt_one hden).2 (by linarith)⟩
  have hcross_val : ∀ Φ ∈ C, ⟪cross Φ, d⟫ = β := by
    intro Φ hΦ
    obtain ⟨-, -, h1, -, -, h2'⟩ := hends' Φ hΦ
    have hden : ⟪(ends Φ).1, d⟫ - ⟪(ends Φ).2, d⟫ ≠ 0 := by linarith
    simp only [hcross, htt, inner_add_left, real_inner_smul_left, inner_sub_left]
    field_simp
    ring
  have hseg : ∀ Φ ∈ C, Φ = convexHull ℝ {(ends Φ).1, (ends Φ).2} := by
    intro Φ hΦ
    obtain ⟨h1W, h1Φ, h1, h2W, h2Φ, h2'⟩ := hends' Φ hΦ
    have hΦe := mem_edgeFinset.1 (Finset.mem_filter.1 hΦ).1
    exact edge_eq_segment hΦe.1 hΦe.2 (hcp _ h1W) (hcp _ h2W) (by
      intro h; rw [h] at h1; linarith) h1Φ h2Φ
  have hcross_open : ∀ Φ ∈ C, cross Φ ∈ openSegment ℝ (ends Φ).1 (ends Φ).2 := by
    intro Φ hΦ
    rw [openSegment_eq_image']
    exact ⟨tt Φ, htt01 Φ hΦ, rfl⟩
  have hcross_mem : ∀ Φ ∈ C, cross Φ ∈ Φ := by
    intro Φ hΦ
    have h : cross Φ ∈ convexHull ℝ ({(ends Φ).1, (ends Φ).2} : Set (E n)) :=
      segment_subset_convexHull (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        (openSegment_subset_segment ℝ _ _ (hcross_open Φ hΦ))
    rwa [← hseg Φ hΦ] at h
  have hΦface : ∀ Φ ∈ C, Φ ∈ faces Q := fun Φ hΦ =>
    (mem_edgeFinset.1 (Finset.mem_filter.1 hΦ).1).1
  have hcrossQ : ∀ Φ ∈ C, cross Φ ∈ Q := fun Φ hΦ => face_subset (hΦface Φ hΦ) (hcross_mem Φ hΦ)
  have hendsQ : ∀ Φ ∈ C, (ends Φ).1 ∈ Q ∧ (ends Φ).2 ∈ Q := fun Φ hΦ =>
    ⟨subset_convexHull ℝ _ (by exact_mod_cast (hends' Φ hΦ).1),
      subset_convexHull ℝ _ (by exact_mod_cast (hends' Φ hΦ).2.2.2.1)⟩
  -- a crossing point is not a vertex
  have hcross_notW : ∀ Φ ∈ C, cross Φ ∉ W := by
    intro Φ hΦ hW
    have hne' : (ends Φ).1 ≠ (ends Φ).2 := by
      intro h; have := (hends' Φ hΦ).2.2.1; rw [h] at this; linarith [(hends' Φ hΦ).2.2.2.2.2]
    have := (mem_extremePoints.1 (hcp _ hW)).2 _ (hendsQ Φ hΦ).1 _ (hendsQ Φ hΦ).2
      (hcross_open Φ hΦ)
    exact hne' (this.1.trans this.2.symm)
  -- crossing points of different edges are different
  have hcross_inj : Set.InjOn cross (C : Set (Set (E n))) := by
    intro Φ hΦ Φ' hΦ' h
    have hsub : ∀ {Ψ Ψ'}, Ψ ∈ C → Ψ' ∈ C → cross Ψ = cross Ψ' → Ψ ⊆ Ψ' := by
      intro Ψ Ψ' hΨ hΨ' heq
      have hcΨ' : cross Ψ ∈ Ψ' := heq ▸ hcross_mem Ψ' hΨ'
      have hext := (hΦface Ψ' hΨ').2.isExtreme
      have h1 := hext.left_mem_of_mem_openSegment (hendsQ Ψ hΨ).1 (hendsQ Ψ hΨ).2 hcΨ'
        (hcross_open Ψ hΨ)
      have h2' := hext.right_mem_of_mem_openSegment (hendsQ Ψ hΨ).1 (hendsQ Ψ hΨ).2 hcΨ'
        (hcross_open Ψ hΨ)
      rw [hseg Ψ hΨ]
      exact convexHull_pair_subset (face_convex (convex_convexHull ℝ _) (hΦface Ψ' hΨ')) h1 h2'
    exact Subset.antisymm (hsub hΦ hΦ' h) (hsub hΦ' hΦ h.symm)
  -- the point set on the line
  set P0 := W0 ∪ C.image cross with hP0
  have hdisj : Disjoint W0 (C.image cross) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨Φ, hΦ, rfl⟩ := Finset.mem_image.1 hx'
    exact hcross_notW Φ hΦ (Finset.mem_filter.1 hx).1
  have hcard : P0.card = W0.card + C.card := by
    rw [hP0, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hcross_inj]
  have hP0Q : ∀ z ∈ P0, z ∈ Q ∧ ⟪z, d⟫ = β := by
    intro z hz
    rcases Finset.mem_union.1 hz with hz | hz
    · obtain ⟨hzW, hzd⟩ := Finset.mem_filter.1 hz
      exact ⟨subset_convexHull ℝ _ (by exact_mod_cast hzW), hzd⟩
    · obtain ⟨Φ, hΦ, rfl⟩ := Finset.mem_image.1 hz
      exact ⟨hcrossQ Φ hΦ, hcross_val Φ hΦ⟩
  set K := Q ∩ {z | β ≤ ⟪z, d⟫} with hK
  have hle : P0.card ≤ 2 := by
    refine card_le_two_of_line (K := K) ?_ ?_ ?_
    · intro z hz
      obtain ⟨hzQ, hzd⟩ := hP0Q z hz
      exact ⟨hzQ, by rw [Set.mem_setOf_eq, hzd]⟩
    · intro z hz y₁ hy₁ y₂ hy₂ hzseg
      rcases Finset.mem_union.1 hz with hz | hz
      · obtain ⟨hzW, -⟩ := Finset.mem_filter.1 hz
        exact ((mem_extremePoints.1 (hcp z hzW)).2 y₁ hy₁.1 y₂ hy₂.1 hzseg).1
      · obtain ⟨Φ, hΦ, rfl⟩ := Finset.mem_image.1 hz
        have hext := (hΦface Φ hΦ).2.isExtreme
        have hy₁Φ := hext.left_mem_of_mem_openSegment hy₁.1 hy₂.1 (hcross_mem Φ hΦ) hzseg
        -- the values at `y₁, y₂` are `≥ β` and average to `β`
        obtain ⟨a, b, ha, hb, hab, hzab⟩ := hzseg
        have hval := hcross_val Φ hΦ
        rw [← hzab, inner_add_left, real_inner_smul_left, real_inner_smul_left] at hval
        have hy₁v : ⟪y₁, d⟫ = β := by
          have h1 : β ≤ ⟪y₁, d⟫ := hy₁.2
          have h2' : β ≤ ⟪y₂, d⟫ := hy₂.2
          have hβ : a * β + b * β = β := by rw [← add_mul, hab, one_mul]
          have hsum0 : a * (⟪y₁, d⟫ - β) + b * (⟪y₂, d⟫ - β) = 0 := by
            rw [mul_sub, mul_sub]; linarith
          have hA : 0 ≤ a * (⟪y₁, d⟫ - β) := mul_nonneg ha.le (by linarith)
          have hB : 0 ≤ b * (⟪y₂, d⟫ - β) := mul_nonneg hb.le (by linarith)
          have hA0 : a * (⟪y₁, d⟫ - β) = 0 := by linarith
          rcases mul_eq_zero.1 hA0 with h | h
          · exact absurd h ha.ne'
          · linarith
        -- on the segment, `ℓ = 0` only at the crossing point
        rw [hseg Φ hΦ, convexHull_pair, segment_eq_image'] at hy₁Φ
        obtain ⟨r, -, rfl⟩ := hy₁Φ
        obtain ⟨-, -, h1, -, -, h2'⟩ := hends' Φ hΦ
        have hden : ⟪(ends Φ).1, d⟫ - ⟪(ends Φ).2, d⟫ ≠ 0 := by linarith
        rw [inner_add_left, real_inner_smul_left, inner_sub_left] at hy₁v
        have hr : r = tt Φ := by
          simp only [htt]
          field_simp
          linarith
        rw [hr]
    · intro z₁ hz₁ z₂ hz₂ z₃ hz₃ h12 h13 h23
      have hmem : ∀ {z z'}, z ∈ P0 → z' ∈ P0 → z' - z ∈ U := by
        intro z z' hz hz'
        obtain ⟨hzQ, hzd⟩ := hP0Q z hz
        obtain ⟨hz'Q, hz'd⟩ := hP0Q z' hz'
        refine Submodule.mem_inf.2 ⟨vsub_mem_vectorSpan ℝ hz'Q hzQ, ?_⟩
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_left, hzd, hz'd, sub_self]
      exact between_of_finrank_le_one hUdim (hmem hz₁ hz₂) (hmem hz₁ hz₃) h12 h13 h23
  omega

end Kalai5
