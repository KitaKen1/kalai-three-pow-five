import Kalai5.FullProd.SideEdges

/-!
# Auxiliary facts for the `Δ2 × Δ2` facet with one extra antipodal pair

* **Combinatorics** (`card_le_cells_add_five`): index the 36 candidate side edges by pairs
  `(p, q)` of ordered pairs `p = (i, i')`, `q = (j, j')` of distinct elements of `Fin 3`
  (`Idx`).  A set `B` of candidates such that no two members have distinct same-sign first
  components and distinct same-sign second components has `|B| ≤ |first(B)| + |second(B)| + 5`,
  where `first(i,i',j,j') = (i, j)` and `second = (i', j')`.  Proof: the twelve "triangles"
  `(sgn p, sgn q, j - i)` give `|B| ≤ 12`; `B ↪ first(B) × second(B)`; arithmetic.
* **Geometry**: an extreme point in a segment of the set is an endpoint; three distinct extreme
  points are not collinear; a functional exposing exactly three non-collinear vertices also yields
  an edge between two of them after a small perturbation (`segment_mem_faces_of_functional3`).
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-! ### Ordered pairs of distinct indices -/

/-- Ordered pairs `(i, i')` of distinct elements of `Fin 3`. -/
abbrev Idx := {t : Fin 3 × Fin 3 // t.1 ≠ t.2}

/-- The third element of `Fin 3`. -/
def third (i i' : Fin 3) : Fin 3 := if i ≠ 0 ∧ i' ≠ 0 then 0 else if i ≠ 1 ∧ i' ≠ 1 then 1 else 2

lemma third_ne (p : Idx) : third p.1.1 p.1.2 ≠ p.1.1 ∧ third p.1.1 p.1.2 ≠ p.1.2 := by
  revert p; decide

lemma eq_or_eq_or_third (p : Idx) (k : Fin 3) :
    k = p.1.1 ∨ k = p.1.2 ∨ k = third p.1.1 p.1.2 := by
  revert p k; decide

/-- The swapped pair `(i', i)`. -/
def Idx.swap (p : Idx) : Idx := ⟨(p.1.2, p.1.1), fun h => p.2 h.symm⟩

lemma third_swap (p : Idx) : third p.swap.1.1 p.swap.1.2 = third p.1.1 p.1.2 := by
  revert p; decide

/-- The sign of the permutation `(i, i', i'')`: `true` for the cyclic orders. -/
def Idx.sgn (p : Idx) : Bool := decide ((p.1.2 : ℕ) = ((p.1.1 : ℕ) + 1) % 3)

/-- The triangle of a candidate. -/
def tri (c : Idx × Idx) : Bool × Bool × Fin 3 := (c.1.sgn, c.2.sgn, c.2.1.1 - c.1.1.1)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
lemma tri_conflict : ∀ c d : Idx × Idx, tri c = tri d → c ≠ d →
    c.1 ≠ d.1 ∧ c.1.sgn = d.1.sgn ∧ c.2 ≠ d.2 ∧ c.2.sgn = d.2.sgn := by
  decide

/-- First cell `(i, j)` and second cell `(i', j')` of a candidate. -/
def cellF (c : Idx × Idx) : Fin 3 × Fin 3 := (c.1.1.1, c.2.1.1)
def cellS (c : Idx × Idx) : Fin 3 × Fin 3 := (c.1.1.2, c.2.1.2)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
lemma cells_inj : ∀ c d : Idx × Idx, cellF c = cellF d → cellS c = cellS d → c = d := by
  decide

/-- **The combinatorial core**: `|B| ≤ |first(B)| + |second(B)| + 5` for a conflict-free `B`. -/
theorem card_le_cells_add_five (B : Finset (Idx × Idx))
    (hB : ∀ c ∈ B, ∀ d ∈ B, c.1 ≠ d.1 → c.1.sgn = d.1.sgn → c.2 ≠ d.2 → c.2.sgn = d.2.sgn → False) :
    B.card ≤ (B.image cellF).card + (B.image cellS).card + 5 := by
  classical
  -- at most one candidate per triangle
  have h12 : B.card ≤ 12 := by
    have hinj : Set.InjOn tri (B : Set (Idx × Idx)) := by
      intro c hc d hd hcd
      by_contra hne
      obtain ⟨h1, h2, h3, h4⟩ := tri_conflict c d hcd hne
      exact hB c hc d hd h1 h2 h3 h4
    have := Finset.card_le_card_of_injOn tri (t := Finset.univ) (fun _ _ => Finset.mem_coe.2
      (Finset.mem_univ _)) hinj
    simpa using this
  -- `B ↪ first(B) × second(B)`
  have hprod : B.card ≤ (B.image cellF).card * (B.image cellS).card := by
    rw [← Finset.card_product]
    refine Finset.card_le_card_of_injOn (fun c => (cellF c, cellS c)) ?_ ?_
    · intro c hc
      exact Finset.mem_coe.2 (Finset.mem_product.2
        ⟨Finset.mem_image_of_mem _ hc, Finset.mem_image_of_mem _ hc⟩)
    · intro c _ d _ h
      simp only [Prod.mk.injEq] at h
      exact cells_inj c d h.1 h.2
  have hf : (B.image cellF).card ≤ 9 := by
    have := Finset.card_le_univ (B.image cellF); simpa using this
  have hs : (B.image cellS).card ≤ 9 := by
    have := Finset.card_le_univ (B.image cellS); simpa using this
  set f := (B.image cellF).card
  set s := (B.image cellS).card
  by_cases h7 : 7 ≤ f + s
  · omega
  · have hf6 : f ≤ 6 := by omega
    have hs6 : s ≤ 6 := by omega
    interval_cases f <;> interval_cases s <;> omega

/-! ### Extreme points and segments -/

section geom

variable {d : ℕ}

/-- An extreme point lying in a segment of the set is one of its endpoints. -/
lemma eq_of_extreme_mem_segment {K : Set (E d)} {z a b : E d} (hz : z ∈ K.extremePoints ℝ)
    (ha : a ∈ K) (hb : b ∈ K) (hzs : z ∈ segment ℝ a b) : z = a ∨ z = b := by
  rcases (mem_extremePoints_iff_forall_segment.1 hz).2 a ha b hb hzs with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

/-- Three distinct extreme points of a convex set are not collinear. -/
lemma extreme_not_collinear {K : Set (E d)} {p q r : E d}
    (hp : p ∈ K.extremePoints ℝ) (hq : q ∈ K.extremePoints ℝ) (hr : r ∈ K.extremePoints ℝ)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (t : ℝ) (ht : r = t • p + (1 - t) • q) : False := by
  have hpK := hp.1; have hqK := hq.1; have hrK := hr.1
  rcases le_or_gt t 0 with h0 | h0
  · -- `q` lies between `r` and `p`
    have h1 : (1 - t) ≠ 0 := by linarith
    have h1p : 0 < 1 - t := by linarith
    have hq' : q = (1 - t)⁻¹ • r + (-t * (1 - t)⁻¹) • p := by
      have e : (1 - t) • q = r - t • p := by rw [ht]; module
      calc q = (1 - t)⁻¹ • ((1 - t) • q) := by rw [smul_smul, inv_mul_cancel₀ h1, one_smul]
        _ = (1 - t)⁻¹ • (r - t • p) := by rw [e]
        _ = (1 - t)⁻¹ • r + (-t * (1 - t)⁻¹) • p := by rw [smul_sub, smul_smul]; module
    have hseg : q ∈ segment ℝ r p := by
      refine ⟨(1 - t)⁻¹, -t * (1 - t)⁻¹, (inv_pos.2 h1p).le,
        mul_nonneg (by linarith) (inv_pos.2 h1p).le, ?_, hq'.symm⟩
      field_simp; ring
    rcases eq_of_extreme_mem_segment hq hrK hpK hseg with h | h
    · exact hqr h
    · exact hpq h.symm
  · rcases le_or_gt t 1 with h1 | h1
    · -- `r` lies between `p` and `q`
      have hseg : r ∈ segment ℝ p q := ⟨t, 1 - t, h0.le, by linarith, by ring, ht.symm⟩
      rcases eq_of_extreme_mem_segment hr hpK hqK hseg with h | h
      · exact hpr h.symm
      · exact hqr h.symm
    · -- `p` lies between `r` and `q`
      have ht0 : t ≠ 0 := ne_of_gt h0
      have hp' : p = t⁻¹ • r + ((t - 1) * t⁻¹) • q := by
        have e : t • p = r - (1 - t) • q := by rw [ht]; module
        calc p = t⁻¹ • (t • p) := by rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
          _ = t⁻¹ • (r - (1 - t) • q) := by rw [e]
          _ = t⁻¹ • r + ((t - 1) * t⁻¹) • q := by rw [smul_sub, smul_smul]; module
      have hseg : p ∈ segment ℝ r q := by
        refine ⟨t⁻¹, (t - 1) * t⁻¹, (inv_pos.2 h0).le,
          mul_nonneg (by linarith) (inv_pos.2 h0).le, ?_, hp'.symm⟩
        field_simp; ring
      rcases eq_of_extreme_mem_segment hp hrK hqK hseg with h | h
      · exact hpr h
      · exact hpq h

/-- **Edges from a functional exposing three non-collinear vertices.** -/
lemma segment_mem_faces_of_functional3 {P : Set (E d)} {X : Finset (E d)}
    (hPX : P = convexHull ℝ (X : Set (E d))) (L : E d) {p q r : E d} (hp : p ∈ X) (hq : q ∈ X)
    (hr : r ∈ X) (hpq : p ≠ q) (hrspan : r ∉ Submodule.span ℝ ({p, q} : Set (E d)))
    (hle : ∀ v ∈ X, ⟪v, L⟫ ≤ 1) (hp1 : ⟪p, L⟫ = 1) (hq1 : ⟪q, L⟫ = 1)
    (heq : ∀ v ∈ X, ⟪v, L⟫ = 1 → v = p ∨ v = q ∨ v = r) :
    segment ℝ p q ∈ faces P ∧ dim (segment ℝ p q) = 1 := by
  classical
  set K := Submodule.span ℝ ({p, q} : Set (E d)) with hK
  set N := r - K.starProjection r with hN
  have hNK : N ∈ Kᗮ := K.sub_starProjection_mem_orthogonal r
  have hpN : ⟪p, N⟫ = 0 := by
    have : p ∈ K := Submodule.subset_span (by simp)
    exact Submodule.inner_right_of_mem_orthogonal this hNK
  have hqN : ⟪q, N⟫ = 0 := by
    have : q ∈ K := Submodule.subset_span (by simp)
    exact Submodule.inner_right_of_mem_orthogonal this hNK
  have hrN : ⟪r, N⟫ = ‖N‖ ^ 2 := by
    have h1 : ⟪K.starProjection r, N⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (K.starProjection_apply_mem r) hNK
    have h2 : r = N + K.starProjection r := by rw [hN]; abel
    calc ⟪r, N⟫ = ⟪N + K.starProjection r, N⟫ := by rw [← h2]
      _ = ‖N‖ ^ 2 := by rw [inner_add_left, h1, add_zero, real_inner_self_eq_norm_sq]
  have hNne : N ≠ 0 := by
    intro h0
    apply hrspan
    have : r = K.starProjection r := by rw [← sub_eq_zero, ← hN, h0]
    rw [this]
    exact K.starProjection_apply_mem r
  have hNpos : 0 < ‖N‖ ^ 2 := by positivity
  -- choose a small perturbation
  set S := X.filter fun v => ⟪v, L⟫ < 1 with hS
  obtain ⟨ε, hε, hεS⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ v ∈ S, ε * |⟪v, N⟫| < 1 - ⟪v, L⟫ := by
    by_cases hSe : S.Nonempty
    · set δ : E d → ℝ := fun v => (1 - ⟪v, L⟫) / (1 + |⟪v, N⟫|) with hδ
      obtain ⟨v0, hv0, hmin⟩ := S.exists_min_image δ hSe
      have hpos : ∀ v ∈ S, 0 < δ v := fun v hv => by
        have := (Finset.mem_filter.1 hv).2
        exact div_pos (by linarith) (by positivity)
      refine ⟨δ v0, hpos v0 hv0, fun v hv => ?_⟩
      have h1 := hmin v hv
      have h2 := (Finset.mem_filter.1 hv).2
      have h3 : δ v * (1 + |⟪v, N⟫|) = 1 - ⟪v, L⟫ := by
        rw [hδ]; field_simp
      have h4 : 0 ≤ |⟪v, N⟫| := abs_nonneg _
      nlinarith [hpos v hv, hpos v0 hv0]
    · refine ⟨1, one_pos, fun v hv => absurd ⟨v, hv⟩ hSe⟩
  set M := L - ε • N with hM
  have hMv : ∀ v, ⟪v, M⟫ = ⟪v, L⟫ - ε * ⟪v, N⟫ := fun v => by
    rw [hM, inner_sub_right, real_inner_smul_right]
  have hrM : ⟪r, M⟫ < 1 := by
    have hr1 : ⟪r, L⟫ ≤ 1 := hle r hr
    rw [hMv, hrN]
    nlinarith
  have hSM : ∀ v ∈ X, ⟪v, L⟫ < 1 → ⟪v, M⟫ < 1 := by
    intro v hv hlt
    have h1 := hεS v (Finset.mem_filter.2 ⟨hv, hlt⟩)
    rw [hMv]
    have h2 : -(ε * ⟪v, N⟫) ≤ ε * |⟪v, N⟫| := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) hε.le
    linarith
  refine (segment_mem_faces_of_functional hPX M hp hq hpq ?_ ?_ ?_ ?_).imp_right And.left
  · intro v hv
    rcases lt_or_eq_of_le (hle v hv) with hlt | heq1
    · exact (hSM v hv hlt).le
    · rcases heq v hv heq1 with rfl | rfl | rfl
      · rw [hMv, hpN, mul_zero, sub_zero, hp1]
      · rw [hMv, hqN, mul_zero, sub_zero, hq1]
      · exact hrM.le
  · rw [hMv, hpN, mul_zero, sub_zero, hp1]
  · rw [hMv, hqN, mul_zero, sub_zero, hq1]
  · intro v hv hv1
    rcases lt_or_eq_of_le (hle v hv) with hlt | heq1
    · exact absurd hv1 (ne_of_lt (hSM v hv hlt))
    · rcases heq v hv heq1 with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hv1 (ne_of_lt hrM)

end geom

end Kalai5
