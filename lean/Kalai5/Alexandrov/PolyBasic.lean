import Kalai5.Rigidity.FaceFacts

/-!
# Basic facts on polygons (and vertex cones) for Alexandrov's theorem

* `nbrs V x`: the neighbours of the vertex `x` of `conv V` (vertices on a common edge);
  a polygon vertex has two (`card_nbrs`).
* `pos_of_nbrs`, `nonneg_of_nbrs`: a linear form positive (nonnegative) on the edge directions at
  `x` is positive (nonnegative) on all of `V - x` (the vertex cone, `cone_edges`).
* `between_of_collinear`, `card_le_two_of_line`: of three distinct points on a line one lies between
  the other two, so a set of extreme points on a line has at most two elements.
* `filter_mem_edge`: an edge contains exactly two vertices.
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

open Classical in
/-- The neighbours of `x` in `conv V`. -/
noncomputable def nbrs (V : Finset (E n)) (x : E n) : Finset (E n) :=
  V.filter fun y => y ≠ x ∧ ∃ F ∈ faces (convexHull ℝ (V : Set (E n))), dim F = 1 ∧ x ∈ F ∧ y ∈ F

lemma mem_nbrs {V : Finset (E n)} {x y : E n} :
    y ∈ nbrs V x ↔ y ∈ V ∧ y ≠ x ∧
      ∃ F ∈ faces (convexHull ℝ (V : Set (E n))), dim F = 1 ∧ x ∈ F ∧ y ∈ F := by
  classical
  unfold nbrs
  rw [Finset.mem_filter]

lemma nbrs_eq_filter {V : Finset (E n)} {x : E n}
    [DecidablePred fun y => y ≠ x ∧ ∃ F ∈ faces (convexHull ℝ (V : Set (E n))), dim F = 1 ∧
      x ∈ F ∧ y ∈ F] :
    nbrs V x = V.filter fun y => y ≠ x ∧
      ∃ F ∈ faces (convexHull ℝ (V : Set (E n))), dim F = 1 ∧ x ∈ F ∧ y ∈ F := by
  ext y
  rw [mem_nbrs, Finset.mem_filter]

lemma mem_nbrs_symm {V : Finset (E n)} {x y : E n} (hx : x ∈ V) (h : y ∈ nbrs V x) :
    x ∈ nbrs V y := by
  obtain ⟨hy, hyx, F, hF, hF1, hxF, hyF⟩ := mem_nbrs.1 h
  exact mem_nbrs.2 ⟨hx, Ne.symm hyx, F, hF, hF1, hyF, hxF⟩

/-- **A vertex of a polygon has exactly two neighbours.** -/
lemma card_nbrs {V : Finset (E n)} (hcp : ConvPos V)
    (h2 : dim (convexHull ℝ (V : Set (E n))) = 2) {x : E n} (hx : x ∈ V) : (nbrs V x).card = 2 := by
  classical
  rw [nbrs_eq_filter]
  exact card_neighbours hcp h2 hx

/-- The vertex cone, in terms of `nbrs`. -/
lemma nbrs_cone {V : Finset (E n)} (hcp : ConvPos V) {x z : E n} (hx : x ∈ V) (hz : z ∈ V) :
    ∃ μ : E n → ℝ, (∀ y, 0 ≤ μ y) ∧ z - x = ∑ y ∈ nbrs V x, μ y • (y - x) := by
  classical
  obtain ⟨μ, hμ, h⟩ := cone_edges hcp hx hz
  refine ⟨μ, hμ, ?_⟩
  rw [nbrs_eq_filter]
  exact h

lemma inner_sum_smul {s : Finset (E n)} (μ : E n → ℝ) (f : E n → E n) (d : E n) :
    ⟪∑ y ∈ s, μ y • f y, d⟫ = ∑ y ∈ s, μ y * ⟪f y, d⟫ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [real_inner_smul_left]

/-- A linear form which is positive on the edge directions at `x` is positive on `V \ {x}`. -/
lemma pos_of_nbrs {V : Finset (E n)} (hcp : ConvPos V) {x : E n} (hx : x ∈ V) (d : E n)
    (h : ∀ y ∈ nbrs V x, 0 < ⟪y - x, d⟫) {z : E n} (hz : z ∈ V) (hzx : z ≠ x) :
    0 < ⟪z - x, d⟫ := by
  obtain ⟨μ, hμ, hsum⟩ := nbrs_cone hcp hx hz
  have hval : ⟪z - x, d⟫ = ∑ y ∈ nbrs V x, μ y * ⟪y - x, d⟫ := by
    rw [hsum, inner_sum_smul]
  have hnn : ∀ y ∈ nbrs V x, 0 ≤ μ y * ⟪y - x, d⟫ := fun y hy => mul_nonneg (hμ y) (h y hy).le
  rcases (Finset.sum_nonneg hnn).lt_or_eq with hlt | heq
  · rwa [hval]
  · exfalso
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 heq.symm
    have hμ0 : ∀ y ∈ nbrs V x, μ y = 0 := fun y hy => by
      rcases mul_eq_zero.1 (hall y hy) with h0 | h0
      · exact h0
      · exact absurd h0 (h y hy).ne'
    have : z - x = 0 := by
      rw [hsum]
      exact Finset.sum_eq_zero fun y hy => by rw [hμ0 y hy, zero_smul]
    exact hzx (sub_eq_zero.1 this)

/-- A linear form which is nonnegative on the edge directions at `x` is nonnegative on `V`. -/
lemma nonneg_of_nbrs {V : Finset (E n)} (hcp : ConvPos V) {x : E n} (hx : x ∈ V) (d : E n)
    (h : ∀ y ∈ nbrs V x, 0 ≤ ⟪y - x, d⟫) {z : E n} (hz : z ∈ V) : 0 ≤ ⟪z - x, d⟫ := by
  obtain ⟨μ, hμ, hsum⟩ := nbrs_cone hcp hx hz
  rw [hsum, inner_sum_smul]
  exact Finset.sum_nonneg fun y hy => mul_nonneg (hμ y) (h y hy)

/-- If the form is nonnegative on the edge directions at `x` and vanishes at `z - x`, then `z - x`
is a nonnegative combination of the edge directions on which the form vanishes. -/
lemma cone_of_zero {V : Finset (E n)} (hcp : ConvPos V) {x : E n} (hx : x ∈ V) (d : E n)
    (h : ∀ y ∈ nbrs V x, 0 ≤ ⟪y - x, d⟫) {z : E n} (hz : z ∈ V) (h0 : ⟪z - x, d⟫ = 0) :
    ∃ μ : E n → ℝ, (∀ y, 0 ≤ μ y) ∧
      z - x = ∑ y ∈ (nbrs V x).filter (fun y => ⟪y - x, d⟫ = 0), μ y • (y - x) := by
  classical
  obtain ⟨μ, hμ, hsum⟩ := nbrs_cone hcp hx hz
  have hnn : ∀ y ∈ nbrs V x, 0 ≤ μ y * ⟪y - x, d⟫ := fun y hy => mul_nonneg (hμ y) (h y hy)
  have hall : ∀ y ∈ nbrs V x, μ y * ⟪y - x, d⟫ = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg hnn).1 ?_
    rw [← inner_sum_smul, ← hsum, h0]
  refine ⟨μ, hμ, ?_⟩
  rw [hsum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun y hy => ?_
  split_ifs with hy0
  · rfl
  · rcases mul_eq_zero.1 (hall y hy) with h1 | h1
    · rw [h1, zero_smul]
    · exact absurd h1 hy0

/-! ### Points on a line -/

/-- Of three distinct collinear points, one lies strictly between the two others. -/
lemma between_of_collinear {z₁ z₂ z₃ : E n} (μ : ℝ) (h : z₃ - z₁ = μ • (z₂ - z₁))
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    z₁ ∈ openSegment ℝ z₂ z₃ ∨ z₂ ∈ openSegment ℝ z₁ z₃ ∨ z₃ ∈ openSegment ℝ z₁ z₂ := by
  rcases lt_trichotomy μ 0 with hμ | hμ | hμ
  · left
    rw [openSegment_eq_image']
    refine ⟨1 / (1 - μ), ⟨div_pos one_pos (by linarith), ?_⟩, ?_⟩
    · rw [div_lt_one (by linarith)]; linarith
    · have h32 : z₃ - z₂ = (1 - μ) • (z₁ - z₂) := by
        have : z₃ - z₂ = (z₃ - z₁) + (z₁ - z₂) := by abel
        rw [this, h, sub_smul, one_smul, smul_sub, smul_sub]; abel
      dsimp only
      rw [h32, smul_smul, div_mul_cancel₀ _ (by linarith : (1 - μ) ≠ 0), one_smul]
      abel
  · rw [hμ, zero_smul, sub_eq_zero] at h; exact absurd h.symm h13
  · rcases lt_trichotomy μ 1 with hμ1 | hμ1 | hμ1
    · right; right
      rw [openSegment_eq_image']
      refine ⟨μ, ⟨hμ, hμ1⟩, ?_⟩
      dsimp only
      rw [← h]; abel
    · rw [hμ1, one_smul, sub_left_inj] at h; exact absurd h.symm h23
    · right; left
      rw [openSegment_eq_image']
      refine ⟨1 / μ, ⟨div_pos one_pos hμ, by rw [div_lt_one hμ]; exact hμ1⟩, ?_⟩
      dsimp only
      rw [h, smul_smul, div_mul_cancel₀ _ hμ.ne', one_smul]
      abel

/-- Three distinct points whose differences lie in a subspace of dimension `≤ 1`. -/
lemma between_of_finrank_le_one {U : Submodule ℝ (E n)} (hU : finrank ℝ U ≤ 1) {z₁ z₂ z₃ : E n}
    (h₂ : z₂ - z₁ ∈ U) (h₃ : z₃ - z₁ ∈ U) (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    z₁ ∈ openSegment ℝ z₂ z₃ ∨ z₂ ∈ openSegment ℝ z₁ z₃ ∨ z₃ ∈ openSegment ℝ z₁ z₂ := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 hU
  obtain ⟨c₂, hc₂⟩ := hv ⟨_, h₂⟩
  obtain ⟨c₃, hc₃⟩ := hv ⟨_, h₃⟩
  have e₂ : c₂ • (v : E n) = z₂ - z₁ := by rw [← Submodule.coe_smul, hc₂]
  have e₃ : c₃ • (v : E n) = z₃ - z₁ := by rw [← Submodule.coe_smul, hc₃]
  have hc₂0 : c₂ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at e₂
    exact h12 (sub_eq_zero.1 e₂.symm).symm
  refine between_of_collinear (c₃ / c₂) ?_ h12 h13 h23
  rw [← e₂, ← e₃, smul_smul, div_mul_cancel₀ _ hc₂0]

/-- **A set of extreme points on a line has at most two elements.** -/
lemma card_le_two_of_line {S : Finset (E n)} {K : Set (E n)} (hSK : (S : Set (E n)) ⊆ K)
    (hext : ∀ z ∈ S, ∀ y₁ ∈ K, ∀ y₂ ∈ K, z ∈ openSegment ℝ y₁ y₂ → y₁ = z)
    (hline : ∀ z₁ ∈ S, ∀ z₂ ∈ S, ∀ z₃ ∈ S, z₁ ≠ z₂ → z₁ ≠ z₃ → z₂ ≠ z₃ →
      z₁ ∈ openSegment ℝ z₂ z₃ ∨ z₂ ∈ openSegment ℝ z₁ z₃ ∨ z₃ ∈ openSegment ℝ z₁ z₂) :
    S.card ≤ 2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 hcon
  rcases hline a ha b hb c hc hab hac hbc with h | h | h
  · exact hab (hext a ha b (hSK hb) c (hSK hc) h).symm
  · exact hab (hext b hb a (hSK ha) c (hSK hc) h)
  · exact hac (hext c hc a (hSK ha) b (hSK hb) h)

/-! ### Edges -/

/-- **An edge contains exactly its two endpoints among the vertices.** -/
lemma filter_mem_edge {V : Finset (E n)} (hcp : ConvPos V) {F : Set (E n)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E n)))) (hF1 : dim F = 1) :
    ∃ p q, p ∈ V ∧ q ∈ V ∧ p ≠ q ∧ F = convexHull ℝ {p, q} ∧
      ∀ x ∈ V, x ∈ F ↔ x = p ∨ x = q := by
  obtain ⟨p, q, hp, hq, hpq, hpF, hqF, -⟩ := exists_ends_of_edge hF hF1
  have hpV : p ∈ V := by exact_mod_cast extremePoints_convexHull_subset hp
  have hqV : q ∈ V := by exact_mod_cast extremePoints_convexHull_subset hq
  have hseg := edge_eq_segment hF hF1 hp hq hpq hpF hqF
  refine ⟨p, q, hpV, hqV, hpq, hseg, fun x hx => ⟨fun hxF => ?_, ?_⟩⟩
  · have hxe : x ∈ F.extremePoints ℝ :=
      inter_extremePoints_subset_extremePoints_of_subset (face_subset hF) ⟨hxF, hcp x hx⟩
    rw [hseg] at hxe
    have := extremePoints_convexHull_subset hxe
    simpa using this
  · rintro (rfl | rfl)
    · exact hpF
    · exact hqF

end Kalai5
