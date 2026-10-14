import Kalai5.FullProd.TF18d

/-!
# TF18+: loose adjacency and the parallel tie

* `adj_opp_loose`: if the upper end of the corner interval of an opposite-sign candidate exceeds `1`
  (`Aop + Sabs > 1`), both its endpoints are adjacent to `z` (a member close to the corner with
  value `> 1`, then tilting).  Likewise `adj_same_loose` for same-sign candidates.
* `not_both_up_par`: in the parallel case, a pair `p` with `Wc` vanishing off `p` and
  `Wc p.1 - Wc p.2 = 1` cannot have both opposite-sign candidates `(s0, p)`, `(oth s0, p)` as
  non-edges: at `τ = τm`, `β = 0` the two values sum to `2 (Wm p.1 - Wm p.2) < 2`, and an affine
  interpolation in `τ` gives a member with value in `(-1, 1)`.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- A parameter close to `1` making `A + t S > 1` when `A + S > 1`. -/
lemma exists_t_gt {A S : ℝ} (hS : 0 ≤ S) (h : 1 < A + S) :
    ∃ t : ℝ, -1 < t ∧ t < 1 ∧ 1 < A + t * S := by
  by_cases hA : 1 < A
  · exact ⟨0, by norm_num, by norm_num, by simpa using hA⟩
  · push_neg at hA
    have hSpos : 0 < S := by linarith
    set g := A + S - 1 with hg
    refine ⟨1 - g / (2 * S), ?_, ?_, ?_⟩
    · have : g / (2 * S) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    · have : 0 < g / (2 * S) := div_pos (by linarith) (by positivity)
      linarith
    · have e : A + (1 - g / (2 * S)) * S = 1 + g / 2 := by
        field_simp; ring
      rw [e]; linarith

namespace T18

variable {P F : Set E5} (T : T18 P F)

section cs

variable (hP : IsCSPolytope5 P) (hF : F ∈ faces P) (h4 : dim F = 4)
include hP hF h4

/-- **Loose adjacency** for an opposite-sign candidate. -/
lemma adj_opp_loose (c : Fin 2 × Pr) (h : 1 < T.Aop c + T.Sabs c.2) :
    (segment ℝ T.z (T.x c.1 c.2.1.1) ∈ faces P ∧ dim (segment ℝ T.z (T.x c.1 c.2.1.1)) = 1) ∧
    (segment ℝ T.z (-T.x (oth c.1) c.2.1.2) ∈ faces P ∧
      dim (segment ℝ T.z (-T.x (oth c.1) c.2.1.2)) = 1) := by
  obtain ⟨t, ht1, ht2, hval⟩ := exists_t_gt (T.Sabs_nonneg c.2) h
  set β : Fin 4 → ℝ := fun j => t * sgnR (T.Wc j) with hβ
  obtain ⟨hb1, hb2⟩ := sgn_bounds ht2 ht1 T.Wc
  have hC : 1 < T.Aop c + ∑ j ∈ c.2.rest, β j * T.Wc j := by
    rw [hβ, sum_sgn]; simpa [Sabs] using hval
  set C := T.Aop c + ∑ j ∈ c.2.rest, β j * T.Wc j with hCdef
  set K := T.Kop c β with hK
  set τ := min T.τm ((C - 1) / (2 * (|K| + 1))) with hτ
  have hden : 0 < 2 * (|K| + 1) := by positivity
  have hτ0 : 0 < τ := lt_min T.τmpos (div_pos (by linarith) hden)
  have hτ1 : τ ≤ T.τm := min_le_left _ _
  have hτK : τ * |K| ≤ (C - 1) / 2 := by
    have h1 : τ * |K| ≤ (C - 1) / (2 * (|K| + 1)) * |K| :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg K)
    have h2 : (C - 1) / (2 * (|K| + 1)) * |K| ≤ (C - 1) / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hden (by norm_num)]
      nlinarith [abs_nonneg K]
    linarith
  obtain ⟨hx, hnx⟩ := T.xvals_opp' c hτ0 hτ1 hb1 hb2
  refine T.adj_of_pattern hP hF h4 _ hx hnx (T.val_fst_opp c.1 c.2 τ β)
    (T.val_snd_opp c.1 c.2 τ β) ?_
  rw [T.val_opp, ← hCdef, ← hK]
  have := neg_abs_le K
  nlinarith [hτ0.le]

/-- **Loose adjacency** for a same-sign candidate. -/
lemma adj_same_loose (hγ : 0 < T.γ (oth T.s0)) (p : Pr)
    (h : 1 < T.Asm p + |T.Zc (oth T.s0)| + T.Sabs p) :
    (segment ℝ T.z (T.x T.s0 p.1.1) ∈ faces P ∧ dim (segment ℝ T.z (T.x T.s0 p.1.1)) = 1) ∧
    (segment ℝ T.z (-T.x T.s0 p.1.2) ∈ faces P ∧
      dim (segment ℝ T.z (-T.x T.s0 p.1.2)) = 1) := by
  have hS : 0 ≤ |T.Zc (oth T.s0)| + T.Sabs p := add_nonneg (abs_nonneg _) (T.Sabs_nonneg p)
  obtain ⟨t, ht1, ht2, hval⟩ := exists_t_gt hS (by linarith : 1 < T.Asm p + (|T.Zc (oth T.s0)| + T.Sabs p))
  set α := t * sgnR (T.Zc (oth T.s0)) with hα
  have hα1 : α < 1 := by
    rcases sgnR_cases (T.Zc (oth T.s0)) with e | e <;> rw [hα, e] <;> linarith
  have hα2 : -1 < α := by
    rcases sgnR_cases (T.Zc (oth T.s0)) with e | e <;> rw [hα, e] <;> linarith
  set β : Fin 4 → ℝ := fun j => t * sgnR (T.Wc j) with hβ
  obtain ⟨hb1, hb2⟩ := sgn_bounds ht2 ht1 T.Wc
  obtain ⟨hx, hnx⟩ := T.xvals_same' hγ p hα1 hα2 hb1 hb2
  refine T.adj_of_pattern hP hF h4 _ hx hnx (T.val_fst_same p α β) (T.val_snd_same p α β) ?_
  rw [T.val_same, sum_sgn]
  have e : α * T.Zc (oth T.s0) = t * |T.Zc (oth T.s0)| := by
    rw [hα, mul_assoc, sgnR_mul]
  rw [e]
  simp only [Sabs] at hval
  nlinarith [hval]

/-- **The parallel tie**: both opposite-sign candidates of a pair cannot be non-edges. -/
lemma not_both_up_par (hpar : T.γ (oth T.s0) = 0) (p : Pr) (hA : T.Asm p = 1)
    (hrest : ∀ d ∈ p.rest, T.Wc d = 0) (hk : 0 < T.Wc p.1.1) (hk' : T.Wc p.1.2 < 0)
    (h0 : ¬ (T.side (T.s0, p) ∈ faces P ∧ dim (T.side (T.s0, p)) = 1))
    (h1 : ¬ (T.side (oth T.s0, p) ∈ faces P ∧ dim (T.side (oth T.s0, p)) = 1)) : False := by
  have hZc : ∀ s, T.Zc s = 0 := by
    intro s
    by_cases hs : s = T.s0
    · rw [hs]; exact T.Zc_s0
    · rw [eq_oth_of_ne hs]; simp [T18.Zc, hpar]
  set β0 : Fin 4 → ℝ := fun _ => 0 with hβ0
  have hb1 : ∀ j, β0 j < 1 := fun j => by simp [hβ0]
  have hb2 : ∀ j, -1 < β0 j := fun j => by simp [hβ0]
  have hsum0 : ∀ q : Pr, ∑ j ∈ q.rest, β0 j * T.Wc j = 0 := fun q => by simp [hβ0]
  have hAop : ∀ s, T.Aop (s, p) = 1 := by
    intro s; simp only [T18.Aop, hZc, sub_zero]; rw [← hA]; simp [T18.Asm]
  -- the derivative terms
  have hWd : ∀ d, T.Wd d = (T.κ2 d / T.δ d) * T.Wc d := by
    intro d
    simp only [T18.Wd, T18.Wc]
    field_simp [(T.δpos d).ne']
  have hdk : T.Wd p.1.1 < 0 := by
    rw [hWd]; exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (T.κ2neg _) (T.δpos _)) hk
  have hdk' : 0 < T.Wd p.1.2 := by
    rw [hWd]; exact mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos (T.κ2neg _) (T.δpos _)) hk'
  have hsumd : ∀ q : Pr, ∑ j ∈ q.rest, β0 j * T.Wd j = 0 := fun q => by simp [hβ0]
  have hK : ∀ s, T.Kop (s, p) β0 = T.Zd s - T.Zd (oth s) + (T.Wd p.1.1 - T.Wd p.1.2) := by
    intro s; simp only [T18.Kop, hsumd, add_zero]
  -- one of the two values at `τm` is `< 1`
  have hsumK : T.Kop (T.s0, p) β0 + T.Kop (oth T.s0, p) β0 < 0 := by
    rw [hK, hK, oth_oth]; linarith
  -- a candidate with `K < 0` and `Aop = 1` gives an edge
  have hedge : ∀ s, T.Kop (s, p) β0 < 0 →
      (T.side (s, p) ∈ faces P ∧ dim (T.side (s, p)) = 1) := by
    intro s hneg
    set K := T.Kop (s, p) β0 with hKdef
    set τ := min T.τm (1 / (2 * (-K))) with hτ
    have hτ0 : 0 < τ := lt_min T.τmpos (by apply div_pos one_pos; linarith)
    have hτ1 : τ ≤ T.τm := min_le_left _ _
    have hτK : τ * (-K) ≤ 1 / 2 := by
      have h1 : τ * (-K) ≤ 1 / (2 * (-K)) * (-K) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
      have hK0 : K ≠ 0 := hneg.ne
      have h2 : 1 / (2 * (-K)) * (-K) = 1 / 2 := by field_simp
      linarith
    obtain ⟨hx, hnx⟩ := T.xvals_opp' (s, p) hτ0 hτ1 hb1 hb2
    refine T.edge_of_pattern hP hF h4 _ hx hnx (T.val_fst_opp s p τ β0) (T.val_snd_opp s p τ β0) ?_
    rw [T.val_opp, hsum0, add_zero, hAop, ← hKdef, abs_lt]
    constructor <;> nlinarith [hτ0]
  rcases lt_or_ge (T.Kop (T.s0, p) β0) 0 with hn | hn
  · exact h0 (hedge _ hn)
  · have : T.Kop (oth T.s0, p) β0 < 0 := by linarith
    exact h1 (hedge _ this)

end cs

end T18

end Kalai5
