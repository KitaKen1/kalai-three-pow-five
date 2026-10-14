import Kalai5.Polar.Basic

/-!
# Alternating cell counts of hyperplane arrangements

Let `C₀` be a nonempty convex set which is (algebraically) open inside a subspace `L₀`, and let
`a₁, …, aₘ` be vectors.  For a sign vector `σ` the *cell* is
`{x ∈ C₀ | sign ⟪aᵢ, x⟫ = σᵢ for all i}`, and its *span* is
`L₀ ∩ {⟪aᵢ, ·⟫ = 0 for σᵢ = 0}`.  Then (`arrangement_count`)

  `Σ_{σ, cell nonempty} (-1)^(dim span σ) = (-1)^(dim L₀)`.

Adding one hyperplane splits a cell either not at all, or into a positive part, a negative part
(same dimension) and a wall (one dimension less), and `(-1)^k + (-1)^k + (-1)^(k-1) = (-1)^k`.
This is the combinatorial core of our proof of the Euler–Poincaré relation.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {d : ℕ}

/-- Dimension of a subspace, as a plain function of the subspace (convenient for rewriting). -/
noncomputable def sdim (S : Submodule ℝ (E d)) : ℕ := Module.finrank ℝ S

/-- `C` lies in `L` and is algebraically open there. -/
def RelOpen (L : Submodule ℝ (E d)) (C : Set (E d)) : Prop :=
  C ⊆ L ∧ ∀ x ∈ C, ∀ w ∈ L, ∃ ε : ℝ, 0 < ε ∧ x + ε • w ∈ C

/-- The cell of a sign vector inside `C₀`. -/
def cell (C0 : Set (E d)) {m : ℕ} (a : Fin m → E d) (σ : Fin m → SignType) : Set (E d) :=
  {x | x ∈ C0 ∧ ∀ i, SignType.sign ⟪a i, x⟫ = σ i}

/-- The span of a cell: `L₀ ∩ {⟪aᵢ, ·⟫ = 0 whenever σᵢ = 0}`. -/
def cellSpan (L0 : Submodule ℝ (E d)) {m : ℕ} (a : Fin m → E d) (σ : Fin m → SignType) :
    Submodule ℝ (E d) where
  carrier := {x | x ∈ L0 ∧ ∀ i, σ i = 0 → ⟪a i, x⟫ = 0}
  add_mem' := fun hx hy =>
    ⟨L0.add_mem hx.1 hy.1, fun i hi => by rw [inner_add_right, hx.2 i hi, hy.2 i hi, add_zero]⟩
  zero_mem' := ⟨L0.zero_mem, fun i _ => inner_zero_right _⟩
  smul_mem' := fun c _ hx =>
    ⟨L0.smul_mem c hx.1, fun i hi => by rw [real_inner_smul_right, hx.2 i hi, mul_zero]⟩

lemma mem_cellSpan {L0 : Submodule ℝ (E d)} {m : ℕ} {a : Fin m → E d} {σ : Fin m → SignType}
    {x : E d} : x ∈ cellSpan L0 a σ ↔ x ∈ L0 ∧ ∀ i, σ i = 0 → ⟪a i, x⟫ = 0 := Iff.rfl

/-! ### Signs -/

lemma sign_combo {p q t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) {σ : SignType}
    (hp : SignType.sign p = σ) (hq : SignType.sign q = σ) : SignType.sign (t * p + s * q) = σ := by
  rcases lt_trichotomy p 0 with hp0 | hp0 | hp0
  · rw [sign_neg hp0] at hp; subst hp
    have hq0 : q < 0 := sign_eq_neg_one_iff.1 hq
    apply sign_neg
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, show s = 1 by linarith]; linarith
    · nlinarith [mul_neg_of_pos_of_neg h hp0, mul_nonpos_of_nonneg_of_nonpos hs hq0.le]
  · rw [hp0, sign_zero] at hp; subst hp
    have hq0 : q = 0 := sign_eq_zero_iff.1 hq
    rw [hp0, hq0, mul_zero, mul_zero, add_zero, sign_zero]
  · rw [sign_pos hp0] at hp; subst hp
    have hq0 : 0 < q := sign_eq_one_iff.1 hq
    apply sign_pos
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, show s = 1 by linarith]; linarith
    · nlinarith [mul_pos h hp0, mul_nonneg hs hq0.le]

lemma sign_add_of_abs_lt {r u : ℝ} (h : |u| < |r|) : SignType.sign (r + u) = SignType.sign r := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · rw [abs_of_neg hr] at h
    rw [sign_neg hr, sign_neg (by linarith [le_abs_self u])]
  · rw [hr, abs_zero] at h; exact absurd h (not_lt.2 (abs_nonneg u))
  · rw [abs_of_pos hr] at h
    rw [sign_pos hr, sign_pos (by linarith [neg_abs_le u])]

/-! ### Cells are convex and relatively open -/

section cells

variable {L0 : Submodule ℝ (E d)} {C0 : Set (E d)}

lemma cell_subset {m : ℕ} (hC0 : RelOpen L0 C0) (a : Fin m → E d) (σ : Fin m → SignType) :
    cell C0 a σ ⊆ cellSpan L0 a σ := by
  rintro x ⟨hx, hs⟩
  refine ⟨hC0.1 hx, fun i hi => ?_⟩
  have := hs i; rw [hi] at this; exact sign_eq_zero_iff.1 this

lemma cell_convex {m : ℕ} (hconv : Convex ℝ C0) (a : Fin m → E d) (σ : Fin m → SignType) :
    Convex ℝ (cell C0 a σ) := by
  intro x hx y hy t s ht hs hts
  refine ⟨hconv hx.1 hy.1 ht hs hts, fun i => ?_⟩
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  exact sign_combo ht hs hts (hx.2 i) (hy.2 i)

/-- Small steps inside a convex algebraically open set. -/
lemma RelOpen.forall_small (hC0 : RelOpen L0 C0) (hconv : Convex ℝ C0) {x : E d} (hx : x ∈ C0)
    {w : E d} (hw : w ∈ L0) : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → t ≤ ε → x + t • w ∈ C0 := by
  obtain ⟨ε, hε, hxε⟩ := hC0.2 x hx w hw
  refine ⟨ε, hε, fun t ht htε => ?_⟩
  have h1 : (0 : ℝ) ≤ 1 - t / ε := by rw [sub_nonneg, div_le_one hε]; exact htε
  have := hconv hx hxε h1 (div_nonneg ht hε.le) (by ring)
  have e : (1 - t / ε) • x + (t / ε) • (x + ε • w) = x + t • w := by
    rw [smul_add, smul_smul, div_mul_cancel₀ t hε.ne', ← add_assoc, ← add_smul, sub_add_cancel,
      one_smul]
  rwa [e] at this

lemma cell_relOpen {m : ℕ} (hC0 : RelOpen L0 C0) (hconv : Convex ℝ C0) (a : Fin m → E d)
    (σ : Fin m → SignType) : RelOpen (cellSpan L0 a σ) (cell C0 a σ) := by
  classical
  refine ⟨cell_subset hC0 a σ, fun x hx w hw => ?_⟩
  obtain ⟨ε₀, hε₀, hsmall⟩ := hC0.forall_small hconv hx.1 hw.1
  set I := Finset.univ.filter fun i => σ i ≠ 0
  set N : ℝ := 1 + ∑ i ∈ I, (|⟪a i, w⟫| + 1) / |⟪a i, x⟫|
  have hxi : ∀ i ∈ I, 0 < |⟪a i, x⟫| := fun i hi => by
    rw [Finset.mem_filter] at hi
    have := hx.2 i
    rw [abs_pos]; intro h; rw [h, sign_zero] at this; exact hi.2 this.symm
  have hterm : ∀ i ∈ I, 0 ≤ (|⟪a i, w⟫| + 1) / |⟪a i, x⟫| := fun i hi => by
    have := hxi i hi; positivity
  have hN : 0 < N := by have := Finset.sum_nonneg hterm; positivity
  set ε := min ε₀ (1 / N)
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  refine ⟨ε, hε, hsmall ε hε.le (min_le_left _ _), fun i => ?_⟩
  rw [inner_add_right, real_inner_smul_right]
  by_cases hi : σ i = 0
  · rw [hw.2 i hi, mul_zero, add_zero]; exact hx.2 i
  · have hiI : i ∈ I := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
    rw [sign_add_of_abs_lt]; · exact hx.2 i
    have hle : (|⟪a i, w⟫| + 1) / |⟪a i, x⟫| < N := by
      have := Finset.single_le_sum hterm hiI; linarith
    rw [div_lt_iff₀ (hxi i hiI)] at hle
    rw [abs_mul, abs_of_pos hε]
    calc ε * |⟪a i, w⟫| ≤ 1 / N * |⟪a i, w⟫| :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _)
      _ < |⟪a i, x⟫| := by
          rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hN]; nlinarith [abs_nonneg ⟪a i, w⟫]

end cells

/-! ### One hyperplane -/

lemma finrank_inf_orthogonal_add_one {L : Submodule ℝ (E d)} {b w : E d} (hwL : w ∈ L)
    (hbw : ⟪b, w⟫ ≠ 0) :
    Module.finrank ℝ ↥(L ⊓ (ℝ ∙ b)ᗮ) + 1 = Module.finrank ℝ L := by
  have hb : b ≠ 0 := fun h => hbw (by rw [h, inner_zero_left])
  have hsup : L ⊔ (ℝ ∙ b)ᗮ = ⊤ := by
    have hbmem : b ∈ L ⊔ (ℝ ∙ b)ᗮ := by
      set c := ⟪b, b⟫ / ⟪b, w⟫
      have h1 : c • w ∈ L := L.smul_mem c hwL
      have h2 : b - c • w ∈ (ℝ ∙ b)ᗮ := by
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
          real_inner_smul_right, div_mul_cancel₀ _ hbw, sub_self]
      have := Submodule.add_mem_sup h1 h2
      rwa [add_sub_cancel] at this
    apply eq_top_iff.2
    rw [← Submodule.sup_orthogonal_of_hasOrthogonalProjection (K := ℝ ∙ b)]
    exact sup_le (by rw [Submodule.span_singleton_le_iff_mem]; exact hbmem) le_sup_right
  have h := Submodule.finrank_sup_add_finrank_inf_eq L (ℝ ∙ b)ᗮ
  have horth := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ b)
  rw [finrank_span_singleton hb] at horth
  rw [hsup, finrank_top] at h
  omega

open Classical in
/-- **Splitting a cell by one hyperplane** preserves the alternating count. -/
lemma three_cells (L : Submodule ℝ (E d)) (C : Set (E d)) (hC : RelOpen L C)
    (hconv : Convex ℝ C) (b : E d) :
    (if {x | x ∈ C ∧ SignType.sign ⟪b, x⟫ = 0}.Nonempty then
        (-1 : ℤ) ^ sdim (L ⊓ (ℝ ∙ b)ᗮ) else 0) +
      (if {x | x ∈ C ∧ SignType.sign ⟪b, x⟫ = -1}.Nonempty then
        (-1 : ℤ) ^ sdim L else 0) +
      (if {x | x ∈ C ∧ SignType.sign ⟪b, x⟫ = 1}.Nonempty then
        (-1 : ℤ) ^ sdim L else 0) =
    if C.Nonempty then (-1 : ℤ) ^ sdim L else 0 := by
  classical
  by_cases hCne : C.Nonempty
  swap
  · have hsub : ∀ s : SignType, ¬ {x | x ∈ C ∧ SignType.sign ⟪b, x⟫ = s}.Nonempty :=
      fun s ⟨x, hx, _⟩ => hCne ⟨x, hx⟩
    rw [if_neg (hsub 0), if_neg (hsub (-1)), if_neg (hsub 1), if_neg hCne]; ring
  rw [if_pos hCne]
  by_cases hperp : ∀ x ∈ L, ⟪b, x⟫ = 0
  · obtain ⟨x0, hx0⟩ := hCne
    have hz : {x | x ∈ C ∧ SignType.sign ⟪b, x⟫ = 0}.Nonempty :=
      ⟨x0, hx0, by rw [hperp x0 (hC.1 hx0), sign_zero]⟩
    have hn : ¬ {x | x ∈ C ∧ SignType.sign ⟪b, x⟫ = -1}.Nonempty := by
      rintro ⟨x, hx, hs⟩; rw [hperp x (hC.1 hx), sign_zero] at hs; exact absurd hs (by decide)
    have hp : ¬ {x | x ∈ C ∧ SignType.sign ⟪b, x⟫ = 1}.Nonempty := by
      rintro ⟨x, hx, hs⟩; rw [hperp x (hC.1 hx), sign_zero] at hs; exact absurd hs (by decide)
    have hL : L ⊓ (ℝ ∙ b)ᗮ = L := inf_eq_left.2 fun x hx =>
      Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hperp x hx)
    rw [if_pos hz, if_neg hn, if_neg hp, hL]; ring
  push_neg at hperp
  obtain ⟨w, hwL, hbw⟩ := hperp
  have hdim : sdim (L ⊓ (ℝ ∙ b)ᗮ) + 1 = sdim L := finrank_inf_orthogonal_add_one hwL hbw
  by_cases hmeet : ∃ x ∈ C, ⟪b, x⟫ = 0
  · obtain ⟨x, hxC, hbx⟩ := hmeet
    obtain ⟨ε, hε, hεC⟩ := hC.2 x hxC w hwL
    obtain ⟨ε', hε', hε'C⟩ := hC.2 x hxC (-w) (L.neg_mem hwL)
    have e1 : ⟪b, x + ε • w⟫ = ε * ⟪b, w⟫ := by
      rw [inner_add_right, real_inner_smul_right, hbx, zero_add]
    have e2 : ⟪b, x + ε' • -w⟫ = -(ε' * ⟪b, w⟫) := by
      rw [inner_add_right, real_inner_smul_right, inner_neg_right, hbx, zero_add]; ring
    have hz : {x | x ∈ C ∧ SignType.sign ⟪b, x⟫ = 0}.Nonempty := ⟨x, hxC, by rw [hbx, sign_zero]⟩
    have hnp : {x | x ∈ C ∧ SignType.sign ⟪b, x⟫ = -1}.Nonempty ∧
        {x | x ∈ C ∧ SignType.sign ⟪b, x⟫ = 1}.Nonempty := by
      rcases lt_or_gt_of_ne hbw with hneg | hpos
      · exact ⟨⟨_, hεC, by rw [e1, sign_neg (mul_neg_of_pos_of_neg hε hneg)]⟩,
          ⟨_, hε'C, by rw [e2, sign_pos (by nlinarith)]⟩⟩
      · exact ⟨⟨_, hε'C, by rw [e2, sign_neg (by nlinarith)]⟩,
          ⟨_, hεC, by rw [e1, sign_pos (mul_pos hε hpos)]⟩⟩
    rw [if_pos hz, if_pos hnp.1, if_pos hnp.2, ← hdim, pow_succ]; ring
  · push_neg at hmeet
    obtain ⟨x0, hx0⟩ := hCne
    have hz : ¬ {x | x ∈ C ∧ SignType.sign ⟪b, x⟫ = 0}.Nonempty := by
      rintro ⟨x, hx, hs⟩; exact hmeet x hx (sign_eq_zero_iff.1 hs)
    -- all points of `C` lie on the same side
    have hsame : ∀ x ∈ C, ∀ y ∈ C, 0 < ⟪b, x⟫ → ⟪b, y⟫ < 0 → False := by
      intro x hx y hy hp hq
      have hpq : 0 < ⟪b, x⟫ - ⟪b, y⟫ := by linarith
      have hmem := hconv hy hx
        (div_nonneg hp.le hpq.le : (0 : ℝ) ≤ ⟪b, x⟫ / (⟪b, x⟫ - ⟪b, y⟫))
        (div_nonneg (neg_nonneg.2 hq.le) hpq.le : (0 : ℝ) ≤ -⟪b, y⟫ / (⟪b, x⟫ - ⟪b, y⟫))
        (by field_simp; ring)
      apply hmeet _ hmem
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      field_simp; ring
    rcases lt_or_gt_of_ne (hmeet x0 hx0) with hneg | hpos
    · have hn : {x | x ∈ C ∧ SignType.sign ⟪b, x⟫ = -1}.Nonempty := ⟨x0, hx0, sign_neg hneg⟩
      have hp : ¬ {x | x ∈ C ∧ SignType.sign ⟪b, x⟫ = 1}.Nonempty := by
        rintro ⟨x, hx, hs⟩; exact hsame x hx x0 hx0 (sign_eq_one_iff.1 hs) hneg
      rw [if_neg hz, if_pos hn, if_neg hp]; ring
    · have hp : {x | x ∈ C ∧ SignType.sign ⟪b, x⟫ = 1}.Nonempty := ⟨x0, hx0, sign_pos hpos⟩
      have hn : ¬ {x | x ∈ C ∧ SignType.sign ⟪b, x⟫ = -1}.Nonempty := by
        rintro ⟨x, hx, hs⟩; exact hsame x0 hx0 x hx hpos (sign_eq_neg_one_iff.1 hs)
      rw [if_neg hz, if_neg hn, if_pos hp]; ring

/-! ### The arrangement count -/

lemma cell_cons (C0 : Set (E d)) {m : ℕ} (a : Fin (m + 1) → E d) (s : SignType)
    (τ : Fin m → SignType) :
    cell C0 a (Fin.cons s τ) = {x | x ∈ cell C0 (Fin.tail a) τ ∧ SignType.sign ⟪a 0, x⟫ = s} := by
  ext x
  simp only [cell, Set.mem_setOf_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.tail]
  tauto

lemma cellSpan_cons_zero (L0 : Submodule ℝ (E d)) {m : ℕ} (a : Fin (m + 1) → E d)
    (τ : Fin m → SignType) :
    cellSpan L0 a (Fin.cons 0 τ) = cellSpan L0 (Fin.tail a) τ ⊓ (ℝ ∙ a 0)ᗮ := by
  ext x
  simp only [mem_cellSpan, Submodule.mem_inf, Submodule.mem_orthogonal_singleton_iff_inner_right,
    Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail, forall_const]
  tauto

lemma cellSpan_cons_ne (L0 : Submodule ℝ (E d)) {m : ℕ} (a : Fin (m + 1) → E d) {s : SignType}
    (hs : s ≠ 0) (τ : Fin m → SignType) :
    cellSpan L0 a (Fin.cons s τ) = cellSpan L0 (Fin.tail a) τ := by
  ext x
  simp only [mem_cellSpan, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail,
    hs, IsEmpty.forall_iff, true_and]

open Classical in
/-- **Alternating cell count of an arrangement.** -/
theorem arrangement_count (L0 : Submodule ℝ (E d)) (C0 : Set (E d)) (hne : C0.Nonempty)
    (hC0 : RelOpen L0 C0) (hconv : Convex ℝ C0) :
    ∀ (m : ℕ) (a : Fin m → E d),
      (∑ σ : Fin m → SignType, if (cell C0 a σ).Nonempty then
          (-1 : ℤ) ^ sdim (cellSpan L0 a σ) else 0) =
        (-1 : ℤ) ^ sdim L0 := by
  classical
  intro m
  induction m with
  | zero =>
    intro a
    have hcell : ∀ σ : Fin 0 → SignType, cell C0 a σ = C0 := fun σ => by
      ext x; simp [cell]
    have hspan : ∀ σ : Fin 0 → SignType, cellSpan L0 a σ = L0 := fun σ => by
      ext x; simp [mem_cellSpan]
    simp only [hcell, if_pos hne, Finset.univ_unique, Finset.sum_singleton]
    rw [hspan]
  | succ m ih =>
    intro a
    have hre : ∀ F : (Fin (m + 1) → SignType) → ℤ,
        ∑ σ, F σ = ∑ τ : Fin m → SignType, ∑ s : SignType, F (Fin.cons s τ) := by
      intro F
      rw [← (Fin.consEquiv fun _ : Fin (m + 1) => SignType).sum_comp, Fintype.sum_prod_type,
        Finset.sum_comm]
      rfl
    rw [hre, ← ih (Fin.tail a)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hsum : ∀ f : SignType → ℤ, ∑ s : SignType, f s = f 0 + f (-1) + f 1 := fun f => by
      rw [SignType.univ_eq]; simp [Finset.sum_insert]; ring
    rw [hsum]
    have h0 := cellSpan_cons_zero L0 a τ
    have hn := cellSpan_cons_ne L0 a (show (-1 : SignType) ≠ 0 by decide) τ
    have hp := cellSpan_cons_ne L0 a (show (1 : SignType) ≠ 0 by decide) τ
    have c0 := cell_cons C0 a 0 τ
    have cn := cell_cons C0 a (-1) τ
    have cp := cell_cons C0 a 1 τ
    simp only [h0, hn, hp, c0, cn, cp]
    exact three_cells _ _ (cell_relOpen hC0 hconv (Fin.tail a) τ)
      (cell_convex hconv (Fin.tail a) τ) (a 0)

end Kalai5
