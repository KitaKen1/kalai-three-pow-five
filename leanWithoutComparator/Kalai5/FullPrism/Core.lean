import Kalai5.Gale.Closure
import Kalai5.Full.Coords

/-!
# The full tetrahedron prism: the common line and the exposed faces

Eight points `v⁺_k = v (2k)`, `v⁻_k = v (2k+1)` (`k < 4`) in `ℝ⁵` with a linear form `u = 1` on all
of them and, for each `k`, a linear form `r_k` vanishing on the six points `v^±_j` (`j ≠ k`) and
positive at `v^±_k` (the side facets of a prism `Δ₃ × I`).

* `normal_form` (the dependency trick, design note `cayley_report.md` §2): the vectors
  `w_k = v⁺_k - c_k v⁻_k` lie on one line `ℝ w`, so `w = α_k v⁺_k + β_k v⁻_k` with `α_k β_k < 0` and
  `α_k + β_k = u(w)` for every `k`.
* `exists_z`: a linear form is determined by its values at the basis `w, v⁻_0, …, v⁻_3`, and these
  values are arbitrary.
-/

namespace Kalai5.FullPrism

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- `v⁺_k`. -/
def vp (v : Fin 8 → E5) (k : Fin 4) : E5 := v ⟨2 * k, by omega⟩

/-- `v⁻_k`. -/
def vm (v : Fin 8 → E5) (k : Fin 4) : E5 := v ⟨2 * k + 1, by omega⟩

/-- The sixteen points `±v_j`. -/
noncomputable def pm16 (v : Fin 8 → E5) (i : Fin 16) : E5 :=
  if h : i.val < 8 then v ⟨i, h⟩ else -v ⟨i.val - 8, by omega⟩

variable {v : Fin 8 → E5} {r : Fin 4 → E5}

/-- The side-facet forms, as a linear map `ℝ⁵ → ℝ⁴`. -/
noncomputable def rMap (r : Fin 4 → E5) : E5 →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun x k := ⟪r k, x⟫
  map_add' x y := by ext k; simp [inner_add_right]
  map_smul' c x := by ext k; simp [real_inner_smul_right]

lemma rMap_apply (x : E5) (k : Fin 4) : rMap r x k = ⟪r k, x⟫ := rfl

section

variable (hr0 : ∀ (k : Fin 4) (j : Fin 8), j.val / 2 ≠ k.val → ⟪r k, v j⟫ = 0)
  (hrp : ∀ k, 0 < ⟪r k, vp v k⟫) (hrm : ∀ k, 0 < ⟪r k, vm v k⟫)
include hr0

lemma r_vp_ne {k l : Fin 4} (h : k ≠ l) : ⟪r l, vp v k⟫ = 0 :=
  hr0 l _ (by simp only; intro h'; apply h; ext; omega)

lemma r_vm_ne {k l : Fin 4} (h : k ≠ l) : ⟪r l, vm v k⟫ = 0 :=
  hr0 l _ (by simp only; intro h'; apply h; ext; omega)

include hrp

/-- The side-facet forms are onto `ℝ⁴`; their common kernel is a line. -/
lemma finrank_ker_rMap : finrank ℝ (LinearMap.ker (rMap r)) = 1 := by
  classical
  have hsurj : Function.Surjective (rMap r) := by
    intro t
    refine ⟨∑ k, (t k / ⟪r k, vp v k⟫) • vp v k, ?_⟩
    ext l
    simp only [rMap_apply, inner_sum, real_inner_smul_right]
    rw [Finset.sum_eq_single l]
    · field_simp [(hrp l).ne']
    · intro k _ hkl
      rw [r_vp_ne hr0 hkl, mul_zero]
    · intro h; exact absurd (Finset.mem_univ l) h
  have h := LinearMap.finrank_range_add_finrank_ker (rMap r)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fin_fun,
    finrank_euclideanSpace_fin] at h
  omega

include hrm

/-- **The common line** (dependency trick). -/
theorem normal_form {u : E5} (hu : ∀ j, ⟪u, v j⟫ = 1) (hne : ∀ k, vp v k ≠ vm v k) :
    ∃ w : E5, w ≠ 0 ∧ (∀ k, ⟪r k, w⟫ = 0) ∧ ∃ α β : Fin 4 → ℝ,
      (∀ k, w = α k • vp v k + β k • vm v k) ∧ (∀ k, α k * β k < 0) ∧
      ∀ k, α k + β k = ⟪u, w⟫ := by
  classical
  -- `w_k = v⁺_k - c_k v⁻_k` is killed by every side-facet form
  obtain ⟨c, hc⟩ : ∃ c : Fin 4 → ℝ, ∀ k, c k = ⟪r k, vp v k⟫ / ⟪r k, vm v k⟫ := ⟨_, fun _ => rfl⟩
  have hcpos : ∀ k, 0 < c k := fun k => by rw [hc]; exact div_pos (hrp k) (hrm k)
  obtain ⟨wk, hwk⟩ : ∃ wk : Fin 4 → E5, ∀ k, wk k = vp v k - c k • vm v k := ⟨_, fun _ => rfl⟩
  have hker : ∀ k, wk k ∈ LinearMap.ker (rMap r) := by
    intro k
    rw [LinearMap.mem_ker]
    ext l
    simp only [rMap_apply, hwk, inner_sub_right, real_inner_smul_right, Pi.zero_apply]
    by_cases hkl : k = l
    · subst hkl
      rw [hc]
      field_simp [(hrm k).ne']
      ring
    · rw [r_vp_ne hr0 hkl, r_vm_ne hr0 hkl, mul_zero, sub_zero]
  have hwk0 : ∀ k, wk k ≠ 0 := by
    intro k h
    rw [hwk] at h
    have h1 : vp v k = c k • vm v k := sub_eq_zero.1 h
    have h2 := congrArg (fun x => ⟪u, x⟫) h1
    simp only [real_inner_smul_right, vp, vm, hu, mul_one] at h2
    apply hne k
    rw [h1, ← h2, one_smul]
  -- the kernel is a line spanned by `w_0`
  have hline : ∀ k, ∃ t : ℝ, t ≠ 0 ∧ wk k = t • wk 0 := by
    intro k
    have h1 := finrank_ker_rMap hr0 hrp
    have hz : (⟨wk 0, hker 0⟩ : LinearMap.ker (rMap r)) ≠ 0 := fun h =>
      hwk0 0 (congrArg Subtype.val h)
    obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' _ hz).1 h1 ⟨wk k, hker k⟩
    have ht' : t • wk 0 = wk k := congrArg Subtype.val ht
    refine ⟨t, fun h0 => hwk0 k ?_, ht'.symm⟩
    rw [← ht', h0, zero_smul]
  choose t ht0 ht using hline
  have hdec : ∀ k, wk 0 = (t k)⁻¹ • vp v k + (-(c k) / t k) • vm v k := by
    intro k
    calc wk 0 = (t k)⁻¹ • (t k • wk 0) := by rw [smul_smul, inv_mul_cancel₀ (ht0 k), one_smul]
      _ = (t k)⁻¹ • (vp v k - c k • vm v k) := by rw [← ht k, hwk]
      _ = (t k)⁻¹ • vp v k + (-(c k) / t k) • vm v k := by
        rw [smul_sub, smul_smul, sub_eq_add_neg, ← neg_smul]
        congr 2
        ring
  refine ⟨wk 0, hwk0 0, fun k => ?_, fun k => (t k)⁻¹, fun k => -(c k) / t k, hdec,
    fun k => ?_, fun k => ?_⟩
  · have := hker 0
    rw [LinearMap.mem_ker] at this
    exact congrFun this k
  · have h1 : 0 < (t k)⁻¹ * (t k)⁻¹ * c k :=
      mul_pos (mul_self_pos.2 (inv_ne_zero (ht0 k))) (hcpos k)
    calc (t k)⁻¹ * (-(c k) / t k) = -((t k)⁻¹ * (t k)⁻¹ * c k) := by field_simp
      _ < 0 := neg_neg_of_pos h1
  · have h := congrArg (fun x => ⟪u, x⟫) (hdec k)
    simp only [inner_add_right, real_inner_smul_right, vp, vm, hu, mul_one] at h
    exact h.symm

/-- **Arbitrary values on the basis `w, v⁻_0, …, v⁻_3`.** -/
theorem exists_z {w : E5} (hw : w ≠ 0) (hrw : ∀ k, ⟪r k, w⟫ = 0) (x : ℝ) (ξ : Fin 4 → ℝ) :
    ∃ z : E5, ⟪z, w⟫ = x ∧ ∀ k, ⟪z, vm v k⟫ = ξ k := by
  classical
  set b : Fin 5 → E5 := Fin.cons w (vm v) with hb
  have hli : LinearIndependent ℝ b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_succ] at hg
    simp only [hb, Fin.cons_zero, Fin.cons_succ] at hg
    have hg' : ∀ l : Fin 4, g l.succ = 0 := by
      intro l
      have h := congrArg (fun y => ⟪r l, y⟫) hg
      simp only [inner_add_right, inner_sum, real_inner_smul_right, inner_zero_right, hrw,
        mul_zero, zero_add] at h
      rw [Finset.sum_eq_single l] at h
      · exact (mul_eq_zero.1 h).resolve_right (hrm l).ne'
      · intro k _ hkl
        rw [r_vm_ne hr0 hkl, mul_zero]
      · intro h'; exact absurd (Finset.mem_univ l) h'
    have h0 : g 0 = 0 := by
      simp only [hg', zero_smul, Finset.sum_const_zero, add_zero] at hg
      exact (smul_eq_zero.1 hg).resolve_right hw
    intro i
    refine Fin.cases h0 (fun l => hg' l) i
  have hsurj : Function.Surjective (coordMapOf b) :=
    LinearMap.injective_iff_surjective.1 (coordMapOf_injective hli)
  obtain ⟨z, hz⟩ := hsurj ((WithLp.equiv 2 (Fin 5 → ℝ)).symm (Fin.cons x ξ))
  refine ⟨z, ?_, fun k => ?_⟩
  · have := congrArg (fun y : E5 => y 0) hz
    simp only [coordMapOf_apply, hb, Fin.cons_zero] at this
    rw [real_inner_comm]
    simpa using this
  · have := congrArg (fun y : E5 => y k.succ) hz
    simp only [coordMapOf_apply, hb, Fin.cons_succ] at this
    rw [real_inner_comm]
    simpa using this

end

end Kalai5.FullPrism
