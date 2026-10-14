import Kalai5.FullProd.UParallel

/-!
# The facet `U` at `(18, 18)`: the concurrent case

If the four product edges of `U` meet at a point `p`:
* normal form (witnesses of `G 2, G 1, G 4, G 3`): `u_A = x 2 - p`, `x 7 = p + τ_A u_A`, and likewise
  `u_B, u_C, u_D` with `x 8, x 4, x 5`, all `τ > 0`, `τ ≠ 1`; the pentagon gives
  `z = x 6 = p + w_C u_C + w_D u_D` with `w_C, w_D > 0` (witnesses of `G 4`, `G 3`);
* `p, u_A, u_B, u_C, u_D` is a basis;
* the functionals with values `1` at `p`, `lpot τ_A a ∈ {0, -2 / max 1 τ_A}` at `u_A`, likewise at
  `u_B`, and `(η_C, η_D) ∈ {(0, 0), (-2 / M_C, 0), (0, -2 / M_D)}` at `(u_C, u_D)`
  (`M = max (max 1 τ) w`) are twelve vertices of the polar (L2); with their negatives that makes
  twenty-four vertices, more than eighteen.
-/

namespace Kalai5

open Set Module Submodule

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The potential on a line through `p`: `0`, or `-2 / max 1 τ` (an endpoint goes to `-1`). -/
noncomputable def lpot (τ : ℝ) (ε : Bool) : ℝ := cond ε 0 (-2 / max 1 τ)

/-- The potential on a line of the pentagon: `0`, or `-2 / max (max 1 τ) w` (lowered). -/
noncomputable def ppot (τ w : ℝ) (on : Bool) : ℝ := cond on (-2 / max (max 1 τ) w) 0

/-- Which line of the pentagon is lowered: `ℓ_C` for `some true`, `ℓ_D` for `some false`. -/
def onC : Option Bool → Bool
  | some true => true
  | _ => false

def onD : Option Bool → Bool
  | some false => true
  | _ => false

lemma onCD_inj {κ κ' : Option Bool} (h1 : onC κ = onC κ') (h2 : onD κ = onD κ') : κ = κ' := by
  rcases κ with _ | ⟨_ | _⟩ <;> rcases κ' with _ | ⟨_ | _⟩ <;> simp_all [onC, onD]

lemma pot_bounds {t M : ℝ} (ht : 0 < t) (htM : t ≤ M) :
    -1 ≤ 1 + t * (-2 / M) ∧ 1 + t * (-2 / M) ≤ 1 := by
  have hM : 0 < M := lt_of_lt_of_le ht htM
  have h1 : t * (-2 / M) = -2 * (t / M) := by ring
  have h2 : t / M ≤ 1 := (div_le_one hM).2 htM
  have h3 : 0 < t / M := div_pos ht hM
  rw [h1]; constructor <;> linarith

lemma pot_eq {M : ℝ} (hM : 0 < M) : 1 + M * (-2 / M) = -1 := by
  have : M * (-2 / M) = -2 := by field_simp
  linarith

lemma lpot_bounds {τ : ℝ} (hτ : 0 < τ) (ε : Bool) :
    (-1 ≤ 1 + lpot τ ε ∧ 1 + lpot τ ε ≤ 1) ∧
      (-1 ≤ 1 + τ * lpot τ ε ∧ 1 + τ * lpot τ ε ≤ 1) := by
  cases ε
  · have h1 := pot_bounds one_pos (le_max_left 1 τ)
    rw [one_mul] at h1
    exact ⟨h1, pot_bounds hτ (le_max_right 1 τ)⟩
  · simp [lpot]

lemma ppot_bounds {τ w : ℝ} (hτ : 0 < τ) (hw : 0 < w) (on : Bool) :
    (-1 ≤ 1 + ppot τ w on ∧ 1 + ppot τ w on ≤ 1) ∧
      (-1 ≤ 1 + τ * ppot τ w on ∧ 1 + τ * ppot τ w on ≤ 1) ∧
      (-1 ≤ 1 + w * ppot τ w on ∧ 1 + w * ppot τ w on ≤ 1) := by
  cases on
  · simp [ppot]
  · have hM1 : (1 : ℝ) ≤ max (max 1 τ) w := le_trans (le_max_left 1 τ) (le_max_left _ w)
    have hMτ : τ ≤ max (max 1 τ) w := le_trans (le_max_right 1 τ) (le_max_left _ w)
    have hMw : w ≤ max (max 1 τ) w := le_max_right _ w
    have h1 := pot_bounds one_pos hM1
    rw [one_mul] at h1
    exact ⟨h1, pot_bounds hτ hMτ, pot_bounds hw hMw⟩

lemma lpot_ne {τ : ℝ} : lpot τ false ≠ 0 := by
  have : (0 : ℝ) < max 1 τ := lt_of_lt_of_le one_pos (le_max_left 1 τ)
  exact div_ne_zero (by norm_num) this.ne'

lemma lpot_inj {τ : ℝ} {ε ε' : Bool} (h : lpot τ ε = lpot τ ε') : ε = ε' := by
  cases ε <;> cases ε'
  · rfl
  · exact absurd h lpot_ne
  · exact absurd h.symm lpot_ne
  · rfl

lemma ppot_ne {τ w : ℝ} : ppot τ w true ≠ 0 := by
  have : (0 : ℝ) < max (max 1 τ) w :=
    lt_of_lt_of_le one_pos (le_trans (le_max_left 1 τ) (le_max_left _ w))
  exact div_ne_zero (by norm_num) this.ne'

lemma ppot_inj {τ w : ℝ} {o o' : Bool} (h : ppot τ w o = ppot τ w o') : o = o' := by
  cases o <;> cases o'
  · rfl
  · exact absurd h.symm ppot_ne
  · exact absurd h ppot_ne
  · rfl

lemma pair_tight {τ π c : ℝ} (hτ1 : τ ≠ 1) (h0 : π + c = 0) (h4 : π + τ * c = 0) :
    π = 0 ∧ c = 0 := by
  have hc : c = 0 := by
    have : (τ - 1) * c = 0 := by linear_combination h4 - h0
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hτ1)
  exact ⟨by linarith, hc⟩

/-- The tight equations on a line through `p` (points `p + u`, `p + τ u`). -/
lemma lpot_tight {τ π a : ℝ} (hτ : 0 < τ) (hτ1 : τ ≠ 1) (ε : Bool)
    (h1 : (1 + lpot τ ε = 1 ∨ 1 + lpot τ ε = -1) → π + a = 0)
    (h2 : (1 + τ * lpot τ ε = 1 ∨ 1 + τ * lpot τ ε = -1) → π + τ * a = 0) :
    (ε = true → π = 0) ∧ (π = 0 → a = 0) := by
  cases ε
  · refine ⟨fun h => absurd h (by decide), fun hπ => ?_⟩
    rcases le_total τ 1 with hle | hge
    · have hm : max 1 τ = 1 := max_eq_left hle
      have := h1 (Or.inr (by simp only [lpot, cond_false, hm]; norm_num))
      linarith
    · have hm : max 1 τ = τ := max_eq_right hge
      have := h2 (Or.inr (by simp only [lpot, cond_false, hm]; exact pot_eq hτ))
      rw [hπ, zero_add] at this
      exact (mul_eq_zero.1 this).resolve_left hτ.ne'
  · have e1 := h1 (Or.inl (by simp [lpot]))
    have e2 := h2 (Or.inl (by simp [lpot]))
    have := pair_tight hτ1 e1 e2
    exact ⟨fun _ => this.1, fun _ => this.2⟩

/-- The tight equations on a lowered line of the pentagon. -/
lemma ppot_tight {τ w π c : ℝ} (hτ : 0 < τ) (hw : 0 < w) (hπ : π = 0)
    (h0 : 1 + ppot τ w true = -1 → π + c = 0)
    (h4 : 1 + τ * ppot τ w true = -1 → π + τ * c = 0)
    (h6 : 1 + w * ppot τ w true = -1 → π + w * c = 0) : c = 0 := by
  subst hπ
  have hval : ppot τ w true = -2 / max (max 1 τ) w := rfl
  rcases max_choice (max 1 τ) w with hm | hm
  · rcases max_choice 1 τ with hm' | hm'
    · have := h0 (by rw [hval, hm, hm']; norm_num)
      linarith
    · have := h4 (by rw [hval, hm, hm']; exact pot_eq hτ)
      rw [zero_add] at this
      exact (mul_eq_zero.1 this).resolve_left hτ.ne'
  · have := h6 (by rw [hval, hm]; exact pot_eq hw)
    rw [zero_add] at this
    exact (mul_eq_zero.1 this).resolve_left hw.ne'

/-- The tight equations on the two lines of the pentagon and at `z`. -/
lemma cd_tight {τC τD wC wD π c δ : ℝ} (hτC : 0 < τC) (hτD : 0 < τD) (hτC1 : τC ≠ 1)
    (hτD1 : τD ≠ 1) (hwC : 0 < wC) (hwD : 0 < wD) (κ : Option Bool)
    (h0 : (1 + ppot τC wC (onC κ) = 1 ∨ 1 + ppot τC wC (onC κ) = -1) → π + c = 0)
    (h4 : (1 + τC * ppot τC wC (onC κ) = 1 ∨ 1 + τC * ppot τC wC (onC κ) = -1) →
      π + τC * c = 0)
    (h1 : (1 + ppot τD wD (onD κ) = 1 ∨ 1 + ppot τD wD (onD κ) = -1) → π + δ = 0)
    (h5 : (1 + τD * ppot τD wD (onD κ) = 1 ∨ 1 + τD * ppot τD wD (onD κ) = -1) →
      π + τD * δ = 0)
    (h6 : (1 + wC * ppot τC wC (onC κ) + wD * ppot τD wD (onD κ) = 1 ∨
      1 + wC * ppot τC wC (onC κ) + wD * ppot τD wD (onD κ) = -1) →
      π + wC * c + wD * δ = 0) :
    π = 0 ∧ c = 0 ∧ δ = 0 := by
  rcases κ with _ | ⟨_ | _⟩
  · -- nothing lowered
    have hC := pair_tight hτC1 (h0 (Or.inl (by simp [ppot, onC])))
      (h4 (Or.inl (by simp [ppot, onC])))
    have hD := pair_tight hτD1 (h1 (Or.inl (by simp [ppot, onD])))
      (h5 (Or.inl (by simp [ppot, onD])))
    exact ⟨hC.1, hC.2, hD.2⟩
  · -- `ℓ_D` lowered
    have hC := pair_tight hτC1 (h0 (Or.inl (by simp [ppot, onC])))
      (h4 (Or.inl (by simp [ppot, onC])))
    have e0 : ppot τC wC (onC (some false)) = 0 := rfl
    refine ⟨hC.1, hC.2, ppot_tight hτD hwD hC.1 (fun h => h1 (Or.inr h)) (fun h => h5 (Or.inr h))
      (fun h => ?_)⟩
    have := h6 (Or.inr (by rw [e0, mul_zero, add_zero]; exact h))
    rw [hC.2, mul_zero, add_zero] at this
    exact this
  · -- `ℓ_C` lowered
    have hD := pair_tight hτD1 (h1 (Or.inl (by simp [ppot, onD])))
      (h5 (Or.inl (by simp [ppot, onD])))
    have e0 : ppot τD wD (onD (some true)) = 0 := rfl
    refine ⟨hD.1, ppot_tight hτC hwC hD.1 (fun h => h0 (Or.inr h)) (fun h => h4 (Or.inr h))
      (fun h => ?_), hD.2⟩
    have := h6 (Or.inr (by rw [e0, mul_zero, add_zero]; exact h))
    rw [hD.2, mul_zero, add_zero] at this
    exact this

namespace UConf

variable {P : Set E5} (C : UConf P) (hP : IsCSPolytope5 P)
include hP

/-- **The concurrent case is impossible** at at most eighteen facets. -/
theorem concurrent_false_of_le (hh : fvec P 4 ≤ 18) {p : E5} {sA sB sC sD : ℝ}
    (hpA : p = C.x 2 + sA • (C.x 7 - C.x 2)) (hpB : p = C.x 3 + sB • (C.x 8 - C.x 3))
    (hpC : p = C.x 0 + sC • (C.x 4 - C.x 0)) (hpD : p = C.x 1 + sD • (C.x 5 - C.x 1)) :
    False := by
  classical
  obtain ⟨ψ1, hψ1⟩ := C.witness hP 1
  obtain ⟨ψ2, hψ2⟩ := C.witness hP 2
  obtain ⟨ψ3, hψ3⟩ := C.witness hP 3
  obtain ⟨ψ4, hψ4⟩ := C.witness hP 4
  have hp3 : ⟪p, ψ3⟫ = 0 :=
    inner_line_eq_zero hpA ((hψ3 2).1 (by decide)) ((hψ3 7).1 (by decide))
  have hp4 : ⟪p, ψ4⟫ = 0 :=
    inner_line_eq_zero hpA ((hψ4 2).1 (by decide)) ((hψ4 7).1 (by decide))
  -- normal form on the four lines
  obtain ⟨τA, hτA, hτA1, h7⟩ := line_normal hpA ((hψ2 2).2 (by decide)) ((hψ2 7).2 (by decide))
    (inner_line_eq_zero hpB ((hψ2 3).1 (by decide)) ((hψ2 8).1 (by decide)))
  obtain ⟨τB, hτB, hτB1, h8⟩ := line_normal hpB ((hψ1 3).2 (by decide)) ((hψ1 8).2 (by decide))
    (inner_line_eq_zero hpA ((hψ1 2).1 (by decide)) ((hψ1 7).1 (by decide)))
  obtain ⟨τC, hτC, hτC1, h4⟩ :=
    line_normal hpC ((hψ4 0).2 (by decide)) ((hψ4 4).2 (by decide)) hp4
  obtain ⟨τD, hτD, hτD1, h5⟩ :=
    line_normal hpD ((hψ3 1).2 (by decide)) ((hψ3 5).2 (by decide)) hp3
  obtain ⟨uA, huA⟩ : ∃ u, u = C.x 2 - p := ⟨_, rfl⟩
  obtain ⟨uB, huB⟩ : ∃ u, u = C.x 3 - p := ⟨_, rfl⟩
  obtain ⟨uC, huC⟩ : ∃ u, u = C.x 0 - p := ⟨_, rfl⟩
  obtain ⟨uD, huD⟩ : ∃ u, u = C.x 1 - p := ⟨_, rfl⟩
  rw [← huA] at h7
  rw [← huB] at h8
  rw [← huC] at h4
  rw [← huD] at h5
  have h2 : C.x 2 = p + uA := by rw [huA]; abel
  have h3 : C.x 3 = p + uB := by rw [huB]; abel
  have h0 : C.x 0 = p + uC := by rw [huC]; abel
  have h1 : C.x 1 = p + uD := by rw [huD]; abel
  -- the pentagon
  have f12 := C.plane (j := 1) (k := 2) (a := 0) (b := 2) (by decide) (by decide)
  obtain ⟨α, β, hz⟩ := mem_span_pair_of_finrank_le f12
    (C.mem_plane (j := 1) (k := 2) (a := 4) (b := 0) (by decide) (by decide))
    (C.mem_plane (j := 1) (k := 2) (a := 1) (b := 0) (by decide) (by decide))
    (C.mem_plane (j := 1) (k := 2) (a := 6) (b := 0) (by decide) (by decide))
    (C.indep (a := 0) (b := 4) (c := 1) (by decide) (by decide) (by decide))
  obtain ⟨wC, hwCdef⟩ : ∃ w : ℝ, w = 1 + α * (τC - 1) - β := ⟨_, rfl⟩
  have h6 : C.x 6 = p + wC • uC + β • uD := by
    have : C.x 6 = C.x 0 + α • (C.x 4 - C.x 0) + β • (C.x 1 - C.x 0) := by
      rw [add_assoc, ← hz]; abel
    rw [this, h4, h0, h1, hwCdef]; module
  -- inner products with the vertices
  have e0 : ∀ y, ⟪C.x 0, y⟫ = ⟪p, y⟫ + ⟪uC, y⟫ := fun y => by rw [h0, inner_add_left]
  have e1 : ∀ y, ⟪C.x 1, y⟫ = ⟪p, y⟫ + ⟪uD, y⟫ := fun y => by rw [h1, inner_add_left]
  have e2 : ∀ y, ⟪C.x 2, y⟫ = ⟪p, y⟫ + ⟪uA, y⟫ := fun y => by rw [h2, inner_add_left]
  have e3 : ∀ y, ⟪C.x 3, y⟫ = ⟪p, y⟫ + ⟪uB, y⟫ := fun y => by rw [h3, inner_add_left]
  have e4 : ∀ y, ⟪C.x 4, y⟫ = ⟪p, y⟫ + τC * ⟪uC, y⟫ := fun y => by
    rw [h4, inner_add_left, real_inner_smul_left]
  have e5 : ∀ y, ⟪C.x 5, y⟫ = ⟪p, y⟫ + τD * ⟪uD, y⟫ := fun y => by
    rw [h5, inner_add_left, real_inner_smul_left]
  have e6 : ∀ y, ⟪C.x 6, y⟫ = ⟪p, y⟫ + wC * ⟪uC, y⟫ + β * ⟪uD, y⟫ := fun y => by
    rw [h6, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have e7 : ∀ y, ⟪C.x 7, y⟫ = ⟪p, y⟫ + τA * ⟪uA, y⟫ := fun y => by
    rw [h7, inner_add_left, real_inner_smul_left]
  have e8 : ∀ y, ⟪C.x 8, y⟫ = ⟪p, y⟫ + τB * ⟪uB, y⟫ := fun y => by
    rw [h8, inner_add_left, real_inner_smul_left]
  -- `z` lies strictly inside the angle at `p`
  have hwC : 0 < wC := by
    have hz4 := (hψ4 6).2 (by decide)
    have hx0 := (hψ4 0).2 (by decide)
    have hx1 := (hψ4 1).1 (by decide)
    rw [e6] at hz4
    rw [e0, hp4, zero_add] at hx0
    rw [e1, hp4, zero_add] at hx1
    simp only [hp4, hx1, mul_zero, add_zero, zero_add] at hz4
    exact (mul_pos_iff_of_pos_right hx0).1 hz4
  have hβ : 0 < β := by
    have hz3 := (hψ3 6).2 (by decide)
    have hx0 := (hψ3 0).1 (by decide)
    have hx1 := (hψ3 1).2 (by decide)
    rw [e6] at hz3
    rw [e0, hp3, zero_add] at hx0
    rw [e1, hp3, zero_add] at hx1
    simp only [hp3, hx0, mul_zero, add_zero, zero_add] at hz3
    exact (mul_pos_iff_of_pos_right hx1).1 hz3
  -- the basis
  have hli : LinearIndependent ℝ ![p, uA, uB, uC, uD] := by
    refine indep5 fun S hp hA hB hC hD => C.span_top hP S ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [h0]; exact add_mem hp hC
    · rw [h1]; exact add_mem hp hD
    · rw [h2]; exact add_mem hp hA
    · rw [h3]; exact add_mem hp hB
    · rw [h4]; exact add_mem hp (smul_mem _ _ hC)
    · rw [h5]; exact add_mem hp (smul_mem _ _ hD)
    · rw [h6]; exact add_mem (add_mem hp (smul_mem _ _ hC)) (smul_mem _ _ hD)
    · rw [h7]; exact add_mem hp (smul_mem _ _ hA)
    · rw [h8]; exact add_mem hp (smul_mem _ _ hB)
  -- the twelve functionals
  have hdual : ∀ (a b : Bool) (κ : Option Bool), ∃ w : E5, ⟪p, w⟫ = 1 ∧ ⟪uA, w⟫ = lpot τA a ∧
      ⟪uB, w⟫ = lpot τB b ∧ ⟪uC, w⟫ = ppot τC wC (onC κ) ∧ ⟪uD, w⟫ = ppot τD β (onD κ) :=
    fun a b κ => exists_dual5 hli _ _ _ _ _
  choose wv hwv using hdual
  have hzb : ∀ κ : Option Bool, -1 ≤ 1 + wC * ppot τC wC (onC κ) + β * ppot τD β (onD κ) ∧
      1 + wC * ppot τC wC (onC κ) + β * ppot τD β (onD κ) ≤ 1 := by
    rintro (_ | ⟨_ | _⟩)
    · show -1 ≤ 1 + wC * 0 + β * 0 ∧ 1 + wC * 0 + β * 0 ≤ 1
      norm_num
    · show -1 ≤ 1 + wC * 0 + β * ppot τD β true ∧ 1 + wC * 0 + β * ppot τD β true ≤ 1
      rw [mul_zero, add_zero]; exact (ppot_bounds hτD hβ true).2.2
    · show -1 ≤ 1 + wC * ppot τC wC true + β * 0 ∧ 1 + wC * ppot τC wC true + β * 0 ≤ 1
      rw [mul_zero, add_zero]; exact (ppot_bounds hτC hwC true).2.2
  have hbd : ∀ a b κ, ∀ i, -1 ≤ ⟪C.x i, wv a b κ⟫ ∧ ⟪C.x i, wv a b κ⟫ ≤ 1 := by
    intro a b κ
    obtain ⟨kp, kA, kB, kC, kD⟩ := hwv a b κ
    have hA := lpot_bounds hτA a
    have hB := lpot_bounds hτB b
    have hC := ppot_bounds hτC hwC (onC κ)
    have hD := ppot_bounds hτD hβ (onD κ)
    refine forall_fin9 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [e0, kp, kC]; exact hC.1
    · rw [e1, kp, kD]; exact hD.1
    · rw [e2, kp, kA]; exact hA.1
    · rw [e3, kp, kB]; exact hB.1
    · rw [e4, kp, kC]; exact hC.2.1
    · rw [e5, kp, kD]; exact hD.2.1
    · rw [e6, kp, kC, kD]; exact hzb κ
    · rw [e7, kp, kA]; exact hA.2
    · rw [e8, kp, kB]; exact hB.2
  have hext : ∀ a b κ, wv a b κ ∈ (polarSet P).extremePoints ℝ := by
    intro a b κ
    obtain ⟨kp, kA, kB, kC, kD⟩ := hwv a b κ
    rw [C.hPX]
    refine mem_extremePoints_polarSet_of_tight (fun y hy => ?_) (fun v hv => ?_)
    · obtain ⟨i, rfl | rfl⟩ := C.memX y hy
      · exact (hbd a b κ i).2
      · rw [inner_neg_left]; linarith [(hbd a b κ i).1]
    · have ht : ∀ i, (⟪C.x i, wv a b κ⟫ = 1 ∨ ⟪C.x i, wv a b κ⟫ = -1) → ⟪C.x i, v⟫ = 0 := by
        rintro i (h | h)
        · exact hv _ (C.xX i).1 h
        · have := hv _ (C.xX i).2 (by rw [inner_neg_left, h]; norm_num)
          rwa [inner_neg_left, neg_eq_zero] at this
      obtain ⟨hπ, hc, hδ⟩ := cd_tight (π := ⟪p, v⟫) (c := ⟪uC, v⟫) (δ := ⟪uD, v⟫)
        hτC hτD hτC1 hτD1 hwC hβ κ
        (fun h => by rw [← e0]; exact ht 0 (by rw [e0, kp, kC]; exact h))
        (fun h => by rw [← e4]; exact ht 4 (by rw [e4, kp, kC]; exact h))
        (fun h => by rw [← e1]; exact ht 1 (by rw [e1, kp, kD]; exact h))
        (fun h => by rw [← e5]; exact ht 5 (by rw [e5, kp, kD]; exact h))
        (fun h => by rw [← e6]; exact ht 6 (by rw [e6, kp, kC, kD]; exact h))
      have tA := lpot_tight (π := ⟪p, v⟫) (a := ⟪uA, v⟫) hτA hτA1 a
        (fun h => by rw [← e2]; exact ht 2 (by rw [e2, kp, kA]; exact h))
        (fun h => by rw [← e7]; exact ht 7 (by rw [e7, kp, kA]; exact h))
      have tB := lpot_tight (π := ⟪p, v⟫) (a := ⟪uB, v⟫) hτB hτB1 b
        (fun h => by rw [← e3]; exact ht 3 (by rw [e3, kp, kB]; exact h))
        (fun h => by rw [← e8]; exact ht 8 (by rw [e8, kp, kB]; exact h))
      exact eq_zero5 hli hπ (tA.2 hπ) (tB.2 hπ) hc hδ
  have hinj : ∀ {a b : Bool} {κ : Option Bool} {a' b' : Bool} {κ' : Option Bool},
      wv a b κ = wv a' b' κ' → a = a' ∧ b = b' ∧ κ = κ' := by
    intro a b κ a' b' κ' h
    obtain ⟨-, kA, kB, kC, kD⟩ := hwv a b κ
    obtain ⟨-, kA', kB', kC', kD'⟩ := hwv a' b' κ'
    rw [h] at kA kB kC kD
    exact ⟨lpot_inj (kA.symm.trans kA'), lpot_inj (kB.symm.trans kB'),
      onCD_inj (ppot_inj (kC.symm.trans kC')) (ppot_inj (kD.symm.trans kD'))⟩
  -- twenty-four vertices of the polar
  obtain ⟨f, hf⟩ : ∃ f : Bool × Bool × Bool × Option Bool → E5, ∀ σ a b κ,
      f (σ, a, b, κ) = cond σ (wv a b κ) (-wv a b κ) := ⟨fun q => cond q.1
        (wv q.2.1 q.2.2.1 q.2.2.2) (-wv q.2.1 q.2.2.1 q.2.2.2), fun _ _ _ _ => rfl⟩
  have hp1 : ∀ a b κ, ⟪p, wv a b κ⟫ = 1 := fun a b κ => (hwv a b κ).1
  have hfinj : Function.Injective f := by
    rintro ⟨σ, a, b, κ⟩ ⟨σ', a', b', κ'⟩ h
    rw [hf, hf] at h
    cases σ <;> cases σ' <;> simp only [cond_true, cond_false] at h
    · obtain ⟨rfl, rfl, rfl⟩ := hinj (neg_injective h); rfl
    · have := congrArg (fun u => ⟪p, u⟫) h
      simp only [inner_neg_right, hp1] at this
      norm_num at this
    · have := congrArg (fun u => ⟪p, u⟫) h
      simp only [inner_neg_right, hp1] at this
      norm_num at this
    · obtain ⟨rfl, rfl, rfl⟩ := hinj h; rfl
  have hall : ∀ w ∈ Finset.univ.image f, w ∈ (polarSet P).extremePoints ℝ := by
    intro w hw
    obtain ⟨⟨σ, a, b, κ⟩, -, rfl⟩ := Finset.mem_image.1 hw
    rw [hf]
    cases σ
    · exact hP.polar.neg_mem_extremePoints (hext a b κ)
    · exact hext a b κ
  have := hP.card_le_of_polar_vertices_of_le hh _ hall
  rw [Finset.card_image_of_injective _ hfinj] at this
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_option] at this

/-- The original equality interface is retained. -/
theorem concurrent_false (hh : fvec P 4 = 18) {p : E5} {sA sB sC sD : ℝ}
    (hpA : p = C.x 2 + sA • (C.x 7 - C.x 2)) (hpB : p = C.x 3 + sB • (C.x 8 - C.x 3))
    (hpC : p = C.x 0 + sC • (C.x 4 - C.x 0)) (hpD : p = C.x 1 + sD • (C.x 5 - C.x 1)) :
    False := C.concurrent_false_of_le hP hh.le hpA hpB hpC hpD

end UConf

end Kalai5
