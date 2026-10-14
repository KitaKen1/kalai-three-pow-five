import Kalai5.Alexandrov.FaceCount

/-!
# The face lemma: the translation case and the plane algebra

* `trans_count`: an in-plane translation `σ v w = ⟪w - v, c⟫` (not zero on all edges) has
  `2 #same + Σ zerC ≤ 4`.
* `plane_center`: a nonzero skew form on a plane is nondegenerate, and every in-plane velocity is
  cancelled at a centre (`∃ u, ⟪y, A u⟫ = -⟪y, γ⟫` for all in-plane `y`).
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

section trans

variable {T : Finset (E n)} (hcp : ConvPos T) (h2 : dim (convexHull ℝ (T : Set (E n))) = 2)
  (c : E n) (hnc : ∃ v ∈ T, ∃ w ∈ nbrs T v, ⟪w - v, c⟫ ≠ 0)
include hcp h2 hnc

lemma trans_zer_ne_two : ∀ v ∈ T, zerC T (fun v w => ⟪w - v, c⟫) v ≠ 2 := by
  classical
  intro v hv hZ
  obtain ⟨v₀, hv₀, w₀, hw₀, hne⟩ := hnc
  have hall : ∀ w ∈ nbrs T v, ⟪w - v, c⟫ = 0 := by
    have hsub : (nbrs T v).filter (fun w => ⟪w - v, c⟫ = 0) = nbrs T v :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        (by rw [card_nbrs hcp h2 hv]; unfold zerC at hZ; beta_reduce at hZ; omega)
    intro w hw
    rw [← hsub] at hw
    exact (Finset.mem_filter.1 hw).2
  have hconst : ∀ p ∈ T, ⟪p - v, c⟫ = 0 := by
    intro p hp
    obtain ⟨μ, -, hsum⟩ := nbrs_cone hcp hv hp
    rw [hsum, inner_sum_smul]
    exact Finset.sum_eq_zero fun y hy => by rw [hall y hy, mul_zero]
  apply hne
  have h1 := hconst w₀ (mem_nbrs.1 hw₀).1
  have h2' := hconst v₀ hv₀
  rw [inner_sub_left] at h1 h2' ⊢
  linarith

/-- A vertex contributing to the count is a minimum or a maximum of `⟪·, c⟫`. -/
lemma trans_level {v : E n} (hv : v ∈ T)
    (h : 1 ≤ zerC T (fun v w => ⟪w - v, c⟫) v ∨ posC T (fun v w => ⟪w - v, c⟫) v = 2 ∨
      negC T (fun v w => ⟪w - v, c⟫) v = 2) :
    (∀ p ∈ T, ⟪v, c⟫ ≤ ⟪p, c⟫) ∨ (∀ p ∈ T, ⟪p, c⟫ ≤ ⟪v, c⟫) := by
  classical
  set σ : E n → E n → ℝ := fun v w => ⟪w - v, c⟫ with hσ
  have h3 := pos_neg_zer hcp h2 σ hv
  have hZ2 := trans_zer_ne_two hcp h2 c hnc v hv
  -- no neighbour below / above
  have hnoneg : negC T σ v = 0 → ∀ p ∈ T, ⟪v, c⟫ ≤ ⟪p, c⟫ := by
    intro h0 p hp
    have hnn : ∀ y ∈ nbrs T v, 0 ≤ ⟪y - v, c⟫ := by
      intro y hy
      by_contra hlt
      push_neg at hlt
      have : y ∈ (nbrs T v).filter (fun w => σ v w < 0) := Finset.mem_filter.2 ⟨hy, hlt⟩
      unfold negC at h0
      rw [Finset.card_eq_zero] at h0
      rw [h0] at this
      exact Finset.notMem_empty _ this
    have := nonneg_of_nbrs hcp hv c hnn hp
    rw [inner_sub_left] at this; linarith
  have hnopos : posC T σ v = 0 → ∀ p ∈ T, ⟪p, c⟫ ≤ ⟪v, c⟫ := by
    intro h0 p hp
    have hnn : ∀ y ∈ nbrs T v, 0 ≤ ⟪y - v, -c⟫ := by
      intro y hy
      by_contra hlt
      push_neg at hlt
      rw [inner_neg_right, neg_neg_iff_pos] at hlt
      have : y ∈ (nbrs T v).filter (fun w => 0 < σ v w) := Finset.mem_filter.2 ⟨hy, hlt⟩
      unfold posC at h0
      rw [Finset.card_eq_zero] at h0
      rw [h0] at this
      exact Finset.notMem_empty _ this
    have := nonneg_of_nbrs hcp hv (-c) hnn hp
    rw [inner_neg_right, inner_sub_left] at this; linarith
  rcases h with h | h | h
  · -- one zero neighbour: the other one decides
    by_cases hn : negC T σ v = 0
    · exact Or.inl (hnoneg hn)
    · have : posC T σ v = 0 := by omega
      exact Or.inr (hnopos this)
  · exact Or.inl (hnoneg (by omega))
  · exact Or.inr (hnopos (by omega))

/-- **The translation case of the face lemma.** -/
theorem trans_count :
    2 * (sameC T fun v w => ⟪w - v, c⟫).card + ∑ v ∈ T, zerC T (fun v w => ⟪w - v, c⟫) v ≤ 4 := by
  classical
  set σ : E n → E n → ℝ := fun v w => ⟪w - v, c⟫ with hσ
  set σ' : E n → E n → ℝ := fun v w => ⟪w - v, -c⟫ with hσ'
  obtain ⟨v₀, hv₀, w₀, hw₀, hne⟩ := hnc
  have hTne : T.Nonempty := ⟨v₀, hv₀⟩
  obtain ⟨pm, hpm, hmin⟩ := T.exists_min_image (fun p => ⟪p, c⟫) hTne
  obtain ⟨pM, hpM, hmax⟩ := T.exists_max_image (fun p => ⟪p, c⟫) hTne
  set m := ⟪pm, c⟫ with hm
  set M := ⟪pM, c⟫ with hM
  have hmM : m < M := by
    have h1 := hmin w₀ (mem_nbrs.1 hw₀).1
    have h2' := hmax w₀ (mem_nbrs.1 hw₀).1
    have h3 := hmin v₀ hv₀
    have h4 := hmax v₀ hv₀
    rw [inner_sub_left] at hne
    by_contra h; push_neg at h
    apply hne; linarith
  have hnc' : ∃ v ∈ T, ∃ w ∈ nbrs T v, ⟪w - v, c⟫ ≠ 0 := ⟨v₀, hv₀, w₀, hw₀, hne⟩
  have hnc'' : ∃ v ∈ T, ∃ w ∈ nbrs T v, ⟪w - v, -c⟫ ≠ 0 :=
    ⟨v₀, hv₀, w₀, hw₀, by rwa [inner_neg_right, neg_ne_zero]⟩
  -- the counts for `-c`
  have hswap : ∀ v, posC T σ' v = negC T σ v ∧ zerC T σ' v = zerC T σ v := by
    intro v
    unfold posC negC zerC
    constructor
    · congr 1
      refine Finset.filter_congr fun w _ => ?_
      simp only [hσ, hσ', inner_neg_right]
      constructor <;> intro h <;> linarith
    · congr 1
      refine Finset.filter_congr fun w _ => ?_
      simp only [hσ, hσ', inner_neg_right, neg_eq_zero]
  -- the contribution of a vertex
  set g : E n → ℕ := fun v => 2 * (if v ∈ sameC T σ then 1 else 0) + zerC T σ v with hg
  have hsum_g : 2 * (sameC T σ).card + ∑ v ∈ T, zerC T σ v = ∑ v ∈ T, g v := by
    have hsub : sameC T σ ⊆ T := fun v hv => (mem_sameC.1 hv).1
    simp only [hg, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hsub]
  rw [hsum_g]
  -- at the minimum, `same` means `posC = 2`
  have hglow : ∀ v ∈ T, ⟪v, c⟫ = m →
      g v = 2 * (if posC T σ v = 2 then 1 else 0) + zerC T σ v := by
    intro v hv hvm
    have hneg0 : negC T σ v ≠ 2 := by
      intro h
      have hlt : ∃ w ∈ nbrs T v, ⟪w - v, c⟫ < 0 := by
        obtain ⟨w, hw⟩ := Finset.card_pos.1 (by unfold negC at h; omega :
          0 < ((nbrs T v).filter fun w => σ v w < 0).card)
        exact ⟨w, (Finset.mem_filter.1 hw).1, (Finset.mem_filter.1 hw).2⟩
      obtain ⟨w, hw, hwlt⟩ := hlt
      have := hmin w (mem_nbrs.1 hw).1
      rw [inner_sub_left, hvm] at hwlt; linarith
    simp only [hg, mem_sameC]
    by_cases hp : posC T σ v = 2
    · rw [if_pos ⟨hv, Or.inl hp⟩, if_pos hp]
    · rw [if_neg (by rintro ⟨-, h | h⟩ <;> contradiction), if_neg hp]
  have hghigh : ∀ v ∈ T, ⟪v, c⟫ = M →
      g v = 2 * (if posC T σ' v = 2 then 1 else 0) + zerC T σ' v := by
    intro v hv hvM
    have hpos0 : posC T σ v ≠ 2 := by
      intro h
      obtain ⟨w, hw⟩ := Finset.card_pos.1 (by unfold posC at h; omega :
          0 < ((nbrs T v).filter fun w => 0 < σ v w).card)
      have hwlt := (Finset.mem_filter.1 hw).2
      have := hmax w (mem_nbrs.1 (Finset.mem_filter.1 hw).1).1
      simp only [hσ, inner_sub_left, hvM] at hwlt; linarith
    obtain ⟨e1, e2⟩ := hswap v
    simp only [hg, mem_sameC, e1, e2]
    by_cases hn : negC T σ v = 2
    · rw [if_pos ⟨hv, Or.inr hn⟩, if_pos hn]
    · rw [if_neg (by rintro ⟨-, h | h⟩ <;> contradiction), if_neg hn]
  have hgmid : ∀ v ∈ T, ⟪v, c⟫ ≠ m → ⟪v, c⟫ ≠ M → g v = 0 := by
    intro v hv hvm hvM
    have hlev : ¬ (1 ≤ zerC T σ v ∨ posC T σ v = 2 ∨ negC T σ v = 2) := by
      intro h
      rcases trans_level hcp h2 c hnc' hv h with hl | hl
      · exact hvm (le_antisymm (hl pm hpm) (hmin v hv))
      · exact hvM (le_antisymm (hmax v hv) (hl pM hpM))
    push_neg at hlev
    simp only [hg, mem_sameC]
    rw [if_neg (by rintro ⟨-, h | h⟩ <;> [exact hlev.2.1 h; exact hlev.2.2 h])]
    omega
  -- split the sum by levels
  rw [← Finset.sum_filter_add_sum_filter_not T (fun v => ⟪v, c⟫ = m)]
  rw [← Finset.sum_filter_add_sum_filter_not (T.filter fun v => ¬ ⟪v, c⟫ = m)
    (fun v => ⟪v, c⟫ = M)]
  have hA : ∑ v ∈ T.filter (fun v => ⟪v, c⟫ = m), g v ≤ 2 := by
    rw [Finset.sum_congr rfl fun v hv => hglow v (Finset.mem_filter.1 hv).1
      (Finset.mem_filter.1 hv).2]
    exact min_level_count hcp h2 c hnc' hmin
  have hB : ∑ v ∈ (T.filter fun v => ¬ ⟪v, c⟫ = m).filter (fun v => ⟪v, c⟫ = M), g v ≤ 2 := by
    have hfil : (T.filter fun v => ¬ ⟪v, c⟫ = m).filter (fun v => ⟪v, c⟫ = M) =
        T.filter (fun v => ⟪v, -c⟫ = -M) := by
      ext v
      simp only [Finset.mem_filter, inner_neg_right, neg_inj]
      constructor
      · rintro ⟨⟨hv, -⟩, hvM⟩; exact ⟨hv, hvM⟩
      · rintro ⟨hv, hvM⟩; exact ⟨⟨hv, by rw [hvM]; exact hmM.ne'⟩, hvM⟩
    rw [hfil, Finset.sum_congr rfl fun v hv => hghigh v (Finset.mem_filter.1 hv).1
      (by have := (Finset.mem_filter.1 hv).2; rw [inner_neg_right, neg_inj] at this; exact this)]
    exact min_level_count hcp h2 (-c) hnc'' (m := -M)
      (fun p hp => by rw [inner_neg_right]; exact neg_le_neg (hmax p hp))
  have hC : ∑ v ∈ (T.filter fun v => ¬ ⟪v, c⟫ = m).filter (fun v => ¬ ⟪v, c⟫ = M), g v = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    simp only [Finset.mem_filter] at hv
    exact hgmid v hv.1.1 hv.1.2 hv.2
  omega

end trans

/-! ### Skew forms on a plane -/

/-- A nonzero skew form on a plane: the plane is spanned by a pair with nonzero value, the form is
nondegenerate, and every linear form is represented. -/
theorem plane_center {U : Submodule ℝ (E n)} (hU : finrank ℝ U = 2) {A : E n →ₗ[ℝ] E n}
    (hskew : ∀ x ∈ U, ∀ y ∈ U, ⟪A x, y⟫ = -⟪x, A y⟫) {x₀ y₀ : E n} (hx₀ : x₀ ∈ U)
    (hy₀ : y₀ ∈ U) (hδ : ⟪A x₀, y₀⟫ ≠ 0) :
    (∀ x ∈ U, x ≠ 0 → ∃ y ∈ U, ⟪A x, y⟫ ≠ 0) ∧
    (∀ γ : E n, ∃ u ∈ U, ∀ y ∈ U, ⟪y, A u⟫ = -⟪y, γ⟫) := by
  set δ := ⟪A x₀, y₀⟫ with hδdef
  have hAxx : ∀ x ∈ U, ⟪A x, x⟫ = 0 := by
    intro x hx
    have := hskew x hx x hx
    rw [real_inner_comm (A x) x] at this
    linarith
  have hyx : ⟪A y₀, x₀⟫ = -δ := by
    rw [hskew y₀ hy₀ x₀ hx₀, real_inner_comm]
  -- independence
  have hli : LinearIndependent ℝ ![x₀, y₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : ⟪A x₀, s • x₀ + t • y₀⟫ = 0 := by rw [hst, inner_zero_right]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hAxx x₀ hx₀, mul_zero,
      zero_add] at h1
    have ht : t = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hδ
    have h2 : ⟪A y₀, s • x₀ + t • y₀⟫ = 0 := by rw [hst, inner_zero_right]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hAxx y₀ hy₀, mul_zero,
      add_zero, hyx] at h2
    refine ⟨?_, ht⟩
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd (neg_eq_zero.1 h) hδ
  have hspan : Submodule.span ℝ {x₀, y₀} = U := by
    have hle : Submodule.span ℝ {x₀, y₀} ≤ U := by
      rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact hx₀
      · exact hy₀
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    have h := finrank_span_eq_card hli
    rw [show Set.range ![x₀, y₀] = {x₀, y₀} by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union]] at h
    rw [h, Fintype.card_fin, hU]
  have hcoord : ∀ y ∈ U, ∃ p q : ℝ, p • x₀ + q • y₀ = y := by
    intro y hy
    rw [← hspan] at hy
    exact Submodule.mem_span_pair.1 hy
  refine ⟨fun x hx hx0 => ?_, fun γ => ?_⟩
  · obtain ⟨p, q, rfl⟩ := hcoord x hx
    by_contra hcon
    push_neg at hcon
    have e1 := hcon x₀ hx₀
    have e2 := hcon y₀ hy₀
    simp only [map_add, map_smul, inner_add_left, real_inner_smul_left, hAxx x₀ hx₀,
      hAxx y₀ hy₀, hyx] at e1 e2
    have hq : q = 0 := by
      have : q * δ = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hδ
    have hp : p = 0 := by
      have : p * δ = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hδ
    apply hx0
    rw [hp, hq, zero_smul, zero_smul, add_zero]
  · refine ⟨(-⟪y₀, γ⟫ / δ) • x₀ + (⟪x₀, γ⟫ / δ) • y₀,
      U.add_mem (U.smul_mem _ hx₀) (U.smul_mem _ hy₀), fun y hy => ?_⟩
    obtain ⟨p, q, rfl⟩ := hcoord y hy
    have hu : (-⟪y₀, γ⟫ / δ) • x₀ + (⟪x₀, γ⟫ / δ) • y₀ ∈ U :=
      U.add_mem (U.smul_mem _ hx₀) (U.smul_mem _ hy₀)
    have k1 : ⟪x₀, A ((-⟪y₀, γ⟫ / δ) • x₀ + (⟪x₀, γ⟫ / δ) • y₀)⟫ = -⟪x₀, γ⟫ := by
      rw [← neg_neg ⟪x₀, A _⟫, ← hskew x₀ hx₀ _ hu]
      simp only [inner_add_right, real_inner_smul_right, hAxx x₀ hx₀]
      rw [← hδdef]
      field_simp
      ring
    have k2 : ⟪y₀, A ((-⟪y₀, γ⟫ / δ) • x₀ + (⟪x₀, γ⟫ / δ) • y₀)⟫ = -⟪y₀, γ⟫ := by
      rw [← neg_neg ⟪y₀, A _⟫, ← hskew y₀ hy₀ _ hu]
      simp only [inner_add_right, real_inner_smul_right, hAxx y₀ hy₀, hyx]
      field_simp
      ring
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, k1, k2, inner_add_left,
      real_inner_smul_left, real_inner_smul_left]
    ring

end Kalai5
