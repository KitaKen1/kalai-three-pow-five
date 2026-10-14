import Kalai5.FullPrism.Tets
import Kalai5.FullProd.ReprMN
import Kalai5.FullProd.QF20

/-!
# A facet `Δ1 × Δ3` with one extra antipodal pair: the data

A prism facet `F` (row `tRow`) of a cs 5-polytope with 18 vertices: vertices `x s k`
(`s < 2`, `k < 4`), side functionals `h s`, `g k`, and the **corner representation**
`cF = Σ γ s • h s + Σ δ k • g k` with `γ ≥ 0`, `γ s0 = 0`, `δ > 0`; moving along the kernel vector
`(κ1, κ2)` gives the positive representations `(γ + τ κ1, δ + τ κ2)`, `τ ∈ (0, τm]`.

The potential functionals `Lv τ u v = Σ u s (γ + τκ1) s • h s + Σ v k (δ + τκ2) k • g k` take the
value `u s * w1 + v k * w2` at `x s k` (`w1 + w2 = 1`).
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-! ### Index helpers -/

/-- Ordered pairs of distinct indices of `Δ3`. -/
abbrev Pr := {p : Fin 4 × Fin 4 // p.1 ≠ p.2}

/-- The other index of `Δ1`. -/
def oth (s : Fin 2) : Fin 2 := if s = 0 then 1 else 0

lemma oth_ne (s : Fin 2) : oth s ≠ s := by fin_cases s <;> decide

lemma oth_oth (s : Fin 2) : oth (oth s) = s := by fin_cases s <;> decide

lemma eq_oth_of_ne {s i : Fin 2} (h : i ≠ s) : i = oth s := by
  fin_cases s <;> fin_cases i <;> first | rfl | exact absurd rfl h

/-- The swapped pair. -/
def Pr.swap (p : Pr) : Pr := ⟨(p.1.2, p.1.1), p.2.symm⟩

/-- The two indices other than those of `p`. -/
def Pr.rest (p : Pr) : Finset (Fin 4) := Finset.univ.filter fun d => d ≠ p.1.1 ∧ d ≠ p.1.2

lemma Pr.rest_swap (p : Pr) : p.swap.rest = p.rest := by
  ext d; simp [Pr.rest, Pr.swap, and_comm]

lemma Pr.sum_split (p : Pr) (f : Fin 4 → ℝ) :
    ∑ j, f j = f p.1.1 + f p.1.2 + ∑ j ∈ p.rest, f j := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j = p.1.1 ∨ j = p.1.2)]
  have e1 : Finset.univ.filter (fun j : Fin 4 => j = p.1.1 ∨ j = p.1.2) = {p.1.1, p.1.2} := by
    ext j; simp
  have e2 : Finset.univ.filter (fun j : Fin 4 => ¬ (j = p.1.1 ∨ j = p.1.2)) = p.rest := by
    ext j; simp [Pr.rest, not_or]
  rw [e1, e2, Finset.sum_pair p.2]

/-- The potential `1` at `p.1`, `-1` at `p.2`, `β` elsewhere. -/
def potv (p : Pr) (β : Fin 4 → ℝ) (d : Fin 4) : ℝ :=
  if d = p.1.1 then 1 else if d = p.1.2 then -1 else β d

lemma potv_fst (p : Pr) (β : Fin 4 → ℝ) : potv p β p.1.1 = 1 := by simp [potv]

lemma potv_snd (p : Pr) (β : Fin 4 → ℝ) : potv p β p.1.2 = -1 := by
  simp [potv, Ne.symm p.2]

lemma potv_rest (p : Pr) (β : Fin 4 → ℝ) {d : Fin 4} (hd : d ∈ p.rest) : potv p β d = β d := by
  simp only [Pr.rest, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  simp [potv, hd.1, hd.2]

lemma potv_le_one (p : Pr) {β : Fin 4 → ℝ} (hβ : ∀ j, β j < 1) (d : Fin 4) : potv p β d ≤ 1 := by
  unfold potv; split_ifs <;> linarith [hβ d]

lemma neg_potv_le_one (p : Pr) {β : Fin 4 → ℝ} (hβ : ∀ j, -1 < β j) (d : Fin 4) :
    -potv p β d ≤ 1 := by
  unfold potv; split_ifs <;> linarith [hβ d]

lemma eq_of_potv_eq_one (p : Pr) {β : Fin 4 → ℝ} (hβ : ∀ j, β j < 1) {d : Fin 4}
    (h : potv p β d = 1) : d = p.1.1 := by
  unfold potv at h; split_ifs at h with h1 h2 <;> first | exact h1 | linarith [hβ d]

lemma eq_of_neg_potv_eq_one (p : Pr) {β : Fin 4 → ℝ} (hβ : ∀ j, -1 < β j) {d : Fin 4}
    (h : -potv p β d = 1) : d = p.1.2 := by
  unfold potv at h; split_ifs at h with h1 h2 <;> first | exact h2 | linarith [hβ d]

lemma sum_potv (p : Pr) (β W : Fin 4 → ℝ) :
    ∑ j, potv p β j * W j = W p.1.1 - W p.1.2 + ∑ j ∈ p.rest, β j * W j := by
  rw [p.sum_split, potv_fst, potv_snd,
    Finset.sum_congr rfl fun j hj => by rw [potv_rest p β hj]]
  ring

/-- The potential `1` at `s`, `-1` at the other index. -/
def potu (s : Fin 2) (i : Fin 2) : ℝ := if i = s then 1 else -1

lemma sum_potu (s : Fin 2) (Z : Fin 2 → ℝ) : ∑ i, potu s i * Z i = Z s - Z (oth s) := by
  fin_cases s <;> simp [potu, oth, Fin.sum_univ_two] <;> ring

/-- The potential `0` at `s0`, `α` at the other index. -/
def potS (s0 : Fin 2) (α : ℝ) (i : Fin 2) : ℝ := if i = s0 then 0 else α

lemma sum_potS (s0 : Fin 2) (α : ℝ) (Z : Fin 2 → ℝ) : ∑ i, potS s0 α i * Z i = α * Z (oth s0) := by
  fin_cases s0 <;> simp [potS, oth, Fin.sum_univ_two]

/-! ### The data of a `Δ1 × Δ3` facet -/

/-- The data of a `Δ1 × Δ3` facet `F` of `P`, with the corner representation of `cF`. -/
structure TFacet (P F : Set E5) where
  x : Fin 2 → Fin 4 → E5
  cF : E5
  h : Fin 2 → E5
  g : Fin 4 → E5
  γ : Fin 2 → ℝ
  δ : Fin 4 → ℝ
  κ1 : Fin 2 → ℝ
  κ2 : Fin 4 → ℝ
  s0 : Fin 2
  τm : ℝ
  inj : ∀ s k s' k', x s k = x s' k' → s = s' ∧ k = k'
  ext : ∀ s k, x s k ∈ P.extremePoints ℝ
  memF : ∀ s k, x s k ∈ F
  all : ∀ z ∈ P.extremePoints ℝ, z ∈ F → ∃ s k, z = x s k
  cF_le : ∀ y ∈ P, ⟪y, cF⟫ ≤ 1
  cF_eq : ∀ y ∈ P, (y ∈ F ↔ ⟪y, cF⟫ = 1)
  h0 : ∀ s k i, i ≠ s → ⟪x s k, h i⟫ = 0
  hpos : ∀ s k, 0 < ⟪x s k, h s⟫
  g0 : ∀ s k j, j ≠ k → ⟪x s k, g j⟫ = 0
  gpos : ∀ s k, 0 < ⟪x s k, g k⟫
  γnn : ∀ s, 0 ≤ γ s
  γs0 : γ s0 = 0
  δpos : ∀ k, 0 < δ k
  κ1pos : ∀ s, 0 < κ1 s
  κ2neg : ∀ k, κ2 k < 0
  ker : ∑ i, κ1 i • h i + ∑ j, κ2 j • g j = 0
  rep : cF = ∑ i, γ i • h i + ∑ j, δ j • g j
  τmpos : 0 < τm
  τmδ : ∀ k, 0 < δ k + τm * κ2 k

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.tFacet {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = tRow) : Nonempty (TFacet P F) := by
  classical
  obtain ⟨x, R, C, hinj, hx, hall, hR, hC, hxR, hxC⟩ := hP.prism_facet hF h4 hrow
  have hFP : F ≠ P := hP.ne_of_dim_ne (by rw [h4]; norm_num)
  have hxP : ∀ s k, x s k ∈ P := fun s k => (hx s k).1.1
  obtain ⟨cF, hcFle, hcF⟩ := hP.exists_dual hF hFP
  choose cR hcRle hcR using fun i =>
    hP.exists_dual (hR i).1 (hP.ne_of_dim_ne (by rw [(hR i).2.2]; norm_num))
  choose cC hcCle hcC using fun j =>
    hP.exists_dual (hC j).1 (hP.ne_of_dim_ne (by rw [(hC j).2.2]; norm_num))
  set h : Fin 2 → E5 := fun i => cF - cR i with hh
  set g : Fin 4 → E5 := fun j => cF - cC j with hg
  have hcFx : ∀ s k, ⟪x s k, cF⟫ = 1 := fun s k => (hcF _ (hxP s k)).1 (hx s k).2
  have hh0 : ∀ s k i, i ≠ s → ⟪x s k, h i⟫ = 0 := by
    intro s k i hi
    rw [hh, inner_sub_right, hcFx, (hcR i _ (hxP s k)).1 ((hxR s k i).2 (Ne.symm hi)), sub_self]
  have hhpos : ∀ s k, 0 < ⟪x s k, h s⟫ := by
    intro s k
    have h1 := hcRle s _ (hxP s k)
    have h2 : ⟪x s k, cR s⟫ ≠ 1 := fun he => (hxR s k s).1 ((hcR s _ (hxP s k)).2 he) rfl
    rw [hh, inner_sub_right, hcFx]
    have := lt_of_le_of_ne h1 h2
    linarith
  have hg0 : ∀ s k j, j ≠ k → ⟪x s k, g j⟫ = 0 := by
    intro s k j hj
    rw [hg, inner_sub_right, hcFx, (hcC j _ (hxP s k)).1 ((hxC s k j).2 (Ne.symm hj)), sub_self]
  have hgpos : ∀ s k, 0 < ⟪x s k, g k⟫ := by
    intro s k
    have h1 := hcCle k _ (hxP s k)
    have h2 : ⟪x s k, cC k⟫ ≠ 1 := fun he => (hxC s k k).1 ((hcC k _ (hxP s k)).2 he) rfl
    rw [hg, inner_sub_right, hcFx]
    have := lt_of_le_of_ne h1 h2
    linarith
  obtain ⟨γ, δ, κ1, κ2, s0, τm, hγ, hγ0, hδ, hκ1, hκ2, hker, hrep, hτm, hτmδ⟩ :=
    exists_corner_repr (m := 2) (n := 4) (by norm_num) h g x cF hh0 hhpos hg0 hgpos hcFx
  exact ⟨⟨x, cF, h, g, γ, δ, κ1, κ2, s0, τm, hinj, fun s k => (hx s k).1, fun s k => (hx s k).2,
    hall, hcFle, hcF, hh0, hhpos, hg0, hgpos, hγ, hγ0, hδ, hκ1, hκ2, hker, hrep, hτm, hτmδ⟩⟩

end cs

namespace TFacet

variable {P F : Set E5} (T : TFacet P F)

lemma xP (s : Fin 2) (k : Fin 4) : T.x s k ∈ P := (T.ext s k).1

lemma cFx (s : Fin 2) (k : Fin 4) : ⟪T.x s k, T.cF⟫ = 1 := (T.cF_eq _ (T.xP s k)).1 (T.memF s k)

/-- The representation at `τ`. -/
noncomputable def γt (τ : ℝ) (s : Fin 2) : ℝ := T.γ s + τ * T.κ1 s
noncomputable def δt (τ : ℝ) (k : Fin 4) : ℝ := T.δ k + τ * T.κ2 k

lemma γt_pos {τ : ℝ} (hτ : 0 < τ) (s : Fin 2) : 0 < T.γt τ s :=
  add_pos_of_nonneg_of_pos (T.γnn s) (mul_pos hτ (T.κ1pos s))

lemma γt_nonneg {τ : ℝ} (hτ : 0 ≤ τ) (s : Fin 2) : 0 ≤ T.γt τ s :=
  add_nonneg (T.γnn s) (mul_nonneg hτ (T.κ1pos s).le)

lemma δt_pos {τ : ℝ} (hτ : τ ≤ T.τm) (k : Fin 4) : 0 < T.δt τ k := by
  unfold δt
  have h1 := T.τmδ k
  have h2 := T.κ2neg k
  have : T.τm * T.κ2 k ≤ τ * T.κ2 k := by nlinarith
  linarith

lemma rep_t (τ : ℝ) : T.cF = ∑ i, T.γt τ i • T.h i + ∑ j, T.δt τ j • T.g j := by
  have e : ∑ i, T.γt τ i • T.h i + ∑ j, T.δt τ j • T.g j =
      (∑ i, T.γ i • T.h i + ∑ j, T.δ j • T.g j) + τ • (∑ i, T.κ1 i • T.h i + ∑ j, T.κ2 j • T.g j) := by
    simp only [γt, δt, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum, smul_smul]
    abel
  rw [e, T.ker, smul_zero, add_zero, T.rep]

/-- The potential functional at `τ`. -/
noncomputable def Lv (τ : ℝ) (u : Fin 2 → ℝ) (v : Fin 4 → ℝ) : E5 :=
  ∑ i, (u i * T.γt τ i) • T.h i + ∑ j, (v j * T.δt τ j) • T.g j

/-- The weights at `x s k`. -/
noncomputable def w1 (τ : ℝ) (s : Fin 2) (k : Fin 4) : ℝ := T.γt τ s * ⟪T.x s k, T.h s⟫
noncomputable def w2 (τ : ℝ) (s : Fin 2) (k : Fin 4) : ℝ := T.δt τ k * ⟪T.x s k, T.g k⟫

lemma val (y : E5) (τ : ℝ) (u : Fin 2 → ℝ) (v : Fin 4 → ℝ) :
    ⟪y, T.Lv τ u v⟫ =
      ∑ i, u i * (T.γt τ i * ⟪y, T.h i⟫) + ∑ j, v j * (T.δt τ j * ⟪y, T.g j⟫) := by
  simp only [Lv, inner_add_right, inner_sum, real_inner_smul_right, mul_assoc]

lemma val_x (τ : ℝ) (s : Fin 2) (k : Fin 4) (u : Fin 2 → ℝ) (v : Fin 4 → ℝ) :
    ⟪T.x s k, T.Lv τ u v⟫ = u s * T.w1 τ s k + v k * T.w2 τ s k := by
  have := inner_evalMN T.h T.g T.x T.h0 T.g0 (fun i => u i * T.γt τ i) (fun j => v j * T.δt τ j) s k
  simp only [Lv, w1, w2] at this ⊢
  rw [this]
  ring

lemma Lv_one (τ : ℝ) : T.Lv τ (fun _ => 1) (fun _ => 1) = T.cF := by
  simp only [Lv, one_mul]
  exact (T.rep_t τ).symm

lemma w_sum (τ : ℝ) (s : Fin 2) (k : Fin 4) : T.w1 τ s k + T.w2 τ s k = 1 := by
  have h1 := T.val_x τ s k (fun _ => 1) (fun _ => 1)
  rw [T.Lv_one, T.cFx] at h1
  linarith

lemma w1_pos {τ : ℝ} (hτ : 0 < τ) (s : Fin 2) (k : Fin 4) : 0 < T.w1 τ s k :=
  mul_pos (T.γt_pos hτ s) (T.hpos s k)

lemma w2_pos {τ : ℝ} (hτ : τ ≤ T.τm) (s : Fin 2) (k : Fin 4) : 0 < T.w2 τ s k :=
  mul_pos (T.δt_pos hτ k) (T.gpos s k)

lemma w1_s0 (k : Fin 4) : T.w1 0 T.s0 k = 0 := by
  simp [w1, γt, T.γs0]

lemma w1_oth_pos (hγ : 0 < T.γ (oth T.s0)) (k : Fin 4) : 0 < T.w1 0 (oth T.s0) k := by
  simp only [w1, γt, zero_mul, add_zero]
  exact mul_pos hγ (T.hpos _ k)

/-- **Admissibility of the opposite-sign potentials** at `τ ∈ (0, τm]`. -/
lemma xvals_opp (s : Fin 2) (p : Pr) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ T.τm) {β : Fin 4 → ℝ}
    (hβ1 : ∀ j, β j < 1) (hβ2 : ∀ j, -1 < β j) (s' : Fin 2) (k : Fin 4) :
    (⟪T.x s' k, T.Lv τ (potu s) (potv p β)⟫ ≤ 1 ∧
      (⟪T.x s' k, T.Lv τ (potu s) (potv p β)⟫ = 1 → s' = s ∧ k = p.1.1)) ∧
    (⟪-T.x s' k, T.Lv τ (potu s) (potv p β)⟫ ≤ 1 ∧
      (⟪-T.x s' k, T.Lv τ (potu s) (potv p β)⟫ = 1 → s' = oth s ∧ k = p.1.2)) := by
  rw [inner_neg_left, T.val_x]
  have hu1 : potu s s' ≤ 1 := by unfold potu; split_ifs <;> norm_num
  have hu2 : -potu s s' ≤ 1 := by unfold potu; split_ifs <;> norm_num
  obtain ⟨h1, h2⟩ := conv_le_one (T.w1_pos hτ0 s' k) (T.w2_pos hτ1 s' k) (T.w_sum τ s' k) hu1
    (potv_le_one p hβ1 k)
  obtain ⟨h3, h4⟩ := conv_le_one (T.w1_pos hτ0 s' k) (T.w2_pos hτ1 s' k) (T.w_sum τ s' k) hu2
    (neg_potv_le_one p hβ2 k)
  refine ⟨⟨h1, fun he => ?_⟩, ⟨by linarith, fun he => ?_⟩⟩
  · obtain ⟨e1, e2⟩ := h2 he
    refine ⟨?_, eq_of_potv_eq_one p hβ1 e2⟩
    by_contra hne
    have : potu s s' = -1 := by simp [potu, hne]
    linarith
  · obtain ⟨e1, e2⟩ := h4 (by linarith)
    refine ⟨?_, eq_of_neg_potv_eq_one p hβ2 e2⟩
    have hne : s' ≠ s := by
      intro heq
      have : potu s s' = 1 := by simp [potu, heq]
      linarith
    exact eq_oth_of_ne hne

lemma val_fst_opp (s : Fin 2) (p : Pr) (τ : ℝ) (β : Fin 4 → ℝ) :
    ⟪T.x s p.1.1, T.Lv τ (potu s) (potv p β)⟫ = 1 := by
  have hu : potu s s = 1 := by simp [potu]
  rw [T.val_x, potv_fst, hu, one_mul, one_mul]
  exact T.w_sum τ s p.1.1

lemma val_snd_opp (s : Fin 2) (p : Pr) (τ : ℝ) (β : Fin 4 → ℝ) :
    ⟪-T.x (oth s) p.1.2, T.Lv τ (potu s) (potv p β)⟫ = 1 := by
  have hu : potu s (oth s) = -1 := by simp [potu, oth_ne s]
  rw [inner_neg_left, T.val_x, potv_snd, hu]
  linarith [T.w_sum τ (oth s) p.1.2]

/-- **Admissibility of the same-sign potentials** (at the corner, when `γ` is positive on the other
side). -/
lemma xvals_same (hγ : 0 < T.γ (oth T.s0)) (p : Pr) {α : ℝ} (hα1 : α < 1) (hα2 : -1 < α)
    {β : Fin 4 → ℝ} (hβ1 : ∀ j, β j < 1) (hβ2 : ∀ j, -1 < β j) (s' : Fin 2) (k : Fin 4) :
    (⟪T.x s' k, T.Lv 0 (potS T.s0 α) (potv p β)⟫ ≤ 1 ∧
      (⟪T.x s' k, T.Lv 0 (potS T.s0 α) (potv p β)⟫ = 1 → s' = T.s0 ∧ k = p.1.1)) ∧
    (⟪-T.x s' k, T.Lv 0 (potS T.s0 α) (potv p β)⟫ ≤ 1 ∧
      (⟪-T.x s' k, T.Lv 0 (potS T.s0 α) (potv p β)⟫ = 1 → s' = T.s0 ∧ k = p.1.2)) := by
  rw [inner_neg_left, T.val_x]
  by_cases hs : s' = T.s0
  · subst hs
    have hw2 : T.w2 0 T.s0 k = 1 := by have := T.w_sum 0 T.s0 k; rw [T.w1_s0] at this; linarith
    rw [T.w1_s0, hw2, mul_zero, zero_add, mul_one]
    refine ⟨⟨potv_le_one p hβ1 k, fun he => ⟨rfl, eq_of_potv_eq_one p hβ1 he⟩⟩,
      ⟨neg_potv_le_one p hβ2 k, fun he => ⟨rfl, eq_of_neg_potv_eq_one p hβ2 he⟩⟩⟩
  · have hso : s' = oth T.s0 := eq_oth_of_ne hs
    have hpot : potS T.s0 α s' = α := by simp [potS, hs]
    rw [hpot]
    have hw1 : 0 < T.w1 0 s' k := by rw [hso]; exact T.w1_oth_pos hγ k
    obtain ⟨h1, h2⟩ := conv_le_one hw1 (T.w2_pos T.τmpos.le s' k) (T.w_sum 0 s' k) hα1.le
      (potv_le_one p hβ1 k)
    obtain ⟨h3, h4⟩ := conv_le_one hw1 (T.w2_pos T.τmpos.le s' k) (T.w_sum 0 s' k)
      (show -α ≤ 1 by linarith) (neg_potv_le_one p hβ2 k)
    refine ⟨⟨h1, fun he => absurd (h2 he).1 hα1.ne⟩, ⟨by linarith, fun he => ?_⟩⟩
    have := (h4 (by linarith)).1
    linarith

lemma val_fst_same (p : Pr) (α : ℝ) (β : Fin 4 → ℝ) :
    ⟪T.x T.s0 p.1.1, T.Lv 0 (potS T.s0 α) (potv p β)⟫ = 1 := by
  rw [T.val_x, potv_fst, T.w1_s0, mul_zero, zero_add, one_mul]
  have := T.w_sum 0 T.s0 p.1.1
  rw [T.w1_s0] at this
  linarith

lemma val_snd_same (p : Pr) (α : ℝ) (β : Fin 4 → ℝ) :
    ⟪-T.x T.s0 p.1.2, T.Lv 0 (potS T.s0 α) (potv p β)⟫ = 1 := by
  rw [inner_neg_left, T.val_x, potv_snd, T.w1_s0, mul_zero, zero_add]
  have := T.w_sum 0 T.s0 p.1.2
  rw [T.w1_s0] at this
  linarith

end TFacet

end Kalai5
