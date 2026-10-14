import Kalai5.Statement

/-!
# Positive representation of the facet functional of `Δ2 × Δ2`

`exists_pos_repr`: let `h, g : Fin 3 → E5` and points `x a b` with `⟪x a b, h i⟫ = 0` for `i ≠ a`,
`> 0` for `i = a`, and likewise for `g` and `b`.  Then any `cF` with `⟪x a b, cF⟫ = 1` is
`Σ γ i • h i + Σ δ j • g j` with all `γ i, δ j > 0`.

Proof: the map `Ψ (γ, δ) = Σ γ i • h i + Σ δ j • g j` has kernel of dimension one (a kernel
vector is determined by its first coordinate, evaluating at the points `x a b`), so it is onto
`E5`; a kernel vector has the sign pattern `γ > 0 > δ`, and moving along it makes a
representation positive (the constraints `1 = γ a ⟪x a b, h a⟫ + δ b ⟪x a b, g b⟫` keep the
admissible interval nonempty).
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- Evaluating `Σ α i • h i + Σ β j • g j` at `x a b` sees only `h a` and `g b`. -/
lemma inner_eval (h g : Fin 3 → E5) (x : Fin 3 → Fin 3 → E5)
    (hh0 : ∀ a b i, i ≠ a → ⟪x a b, h i⟫ = 0) (hg0 : ∀ a b j, j ≠ b → ⟪x a b, g j⟫ = 0)
    (α β : Fin 3 → ℝ) (a b : Fin 3) :
    ⟪x a b, ∑ i, α i • h i + ∑ j, β j • g j⟫ = α a * ⟪x a b, h a⟫ + β b * ⟪x a b, g b⟫ := by
  rw [inner_add_right, inner_sum, inner_sum]
  rw [Finset.sum_eq_single a (fun i _ hi => by rw [real_inner_smul_right, hh0 a b i hi, mul_zero])
      (fun h' => absurd (Finset.mem_univ a) h'),
    Finset.sum_eq_single b (fun j _ hj => by rw [real_inner_smul_right, hg0 a b j hj, mul_zero])
      (fun h' => absurd (Finset.mem_univ b) h'),
    real_inner_smul_right, real_inner_smul_right]

theorem exists_pos_repr (h g : Fin 3 → E5) (x : Fin 3 → Fin 3 → E5) (cF : E5)
    (hh0 : ∀ a b i, i ≠ a → ⟪x a b, h i⟫ = 0) (hhpos : ∀ a b, 0 < ⟪x a b, h a⟫)
    (hg0 : ∀ a b j, j ≠ b → ⟪x a b, g j⟫ = 0) (hgpos : ∀ a b, 0 < ⟪x a b, g b⟫)
    (hcF : ∀ a b, ⟪x a b, cF⟫ = 1) :
    ∃ γ δ : Fin 3 → ℝ, (∀ a, 0 < γ a) ∧ (∀ b, 0 < δ b) ∧
      cF = ∑ i, γ i • h i + ∑ j, δ j • g j := by
  classical
  -- the map `Ψ`
  let Ψ : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) →ₗ[ℝ] E5 :=
    { toFun := fun z => ∑ i, z.1 i • h i + ∑ j, z.2 j • g j
      map_add' := fun z w => by
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
        abel
      map_smul' := fun c z => by
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
          RingHom.id_apply, smul_add, Finset.smul_sum] }
  have hΨ : ∀ z, Ψ z = ∑ i, z.1 i • h i + ∑ j, z.2 j • g j := fun _ => rfl
  -- evaluation at the points
  have heval : ∀ z a b, ⟪x a b, Ψ z⟫ = z.1 a * ⟪x a b, h a⟫ + z.2 b * ⟪x a b, g b⟫ := by
    intro z a b
    rw [hΨ]
    exact inner_eval h g x hh0 hg0 z.1 z.2 a b
  -- a kernel vector vanishing at the first coordinate is zero
  have hker0 : ∀ z, Ψ z = 0 → z.1 0 = 0 → z = 0 := by
    intro z hz h0
    have hδ : ∀ b, z.2 b = 0 := fun b => by
      have := heval z 0 b
      rw [hz, inner_zero_right, h0, zero_mul, zero_add] at this
      exact (mul_eq_zero.1 this.symm).resolve_right (hgpos 0 b).ne'
    have hγ : ∀ a, z.1 a = 0 := fun a => by
      have := heval z a 0
      rw [hz, inner_zero_right, hδ 0, zero_mul, add_zero] at this
      exact (mul_eq_zero.1 this.symm).resolve_right (hhpos a 0).ne'
    exact Prod.ext (funext hγ) (funext hδ)
  -- dimensions
  have hdom : Module.finrank ℝ ((Fin 3 → ℝ) × (Fin 3 → ℝ)) = 6 := by
    rw [Module.finrank_prod, Module.finrank_fin_fun]
  let π0 : LinearMap.ker Ψ →ₗ[ℝ] ℝ :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0) ∘ₗ LinearMap.fst ℝ _ _ ∘ₗ
      (LinearMap.ker Ψ).subtype
  have hπ0 : Function.Injective π0 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    apply Subtype.ext
    exact hker0 z.1 (LinearMap.mem_ker.1 z.2) hz
  have hkerle : Module.finrank ℝ (LinearMap.ker Ψ) ≤ 1 := by
    have := LinearMap.finrank_le_finrank_of_injective hπ0
    rwa [Module.finrank_self] at this
  have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
  rw [hdom] at hrn
  have hrange : LinearMap.range Ψ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_le (LinearMap.range Ψ)
    rw [finrank_euclideanSpace_fin] at h1 ⊢
    omega
  have hkerpos : 0 < Module.finrank ℝ (LinearMap.ker Ψ) := by
    have h1 := Submodule.finrank_le (LinearMap.range Ψ)
    rw [finrank_euclideanSpace_fin] at h1
    omega
  -- a representation, and a kernel vector
  obtain ⟨z0, hz0⟩ : cF ∈ LinearMap.range Ψ := by rw [hrange]; exact Submodule.mem_top
  have hkerne : LinearMap.ker Ψ ≠ ⊥ := by
    intro hb
    have : Module.finrank ℝ (LinearMap.ker Ψ) = 0 := by rw [hb]; exact finrank_bot ℝ _
    omega
  obtain ⟨κ, hκker, hκne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hkerne
  rw [LinearMap.mem_ker] at hκker
  -- normalize the sign of the kernel vector
  obtain ⟨κ', hκ'ker, hκ'0⟩ : ∃ κ', Ψ κ' = 0 ∧ 0 < κ'.1 0 := by
    have hne0 : κ.1 0 ≠ 0 := fun h0 => hκne (hker0 κ hκker h0)
    rcases lt_or_gt_of_ne hne0 with hneg | hpos
    · refine ⟨-κ, by rw [map_neg, hκker, neg_zero], ?_⟩
      simp only [Prod.fst_neg, Pi.neg_apply]
      linarith
    · exact ⟨κ, hκker, hpos⟩
  have hκδ : ∀ b, κ'.2 b < 0 := fun b => by
    have := heval κ' 0 b
    rw [hκ'ker, inner_zero_right] at this
    have h1 := mul_pos hκ'0 (hhpos 0 b)
    have h2 := hgpos 0 b
    by_contra hge
    push_neg at hge
    nlinarith [mul_nonneg hge h2.le]
  have hκγ : ∀ a, 0 < κ'.1 a := fun a => by
    have := heval κ' a 0
    rw [hκ'ker, inner_zero_right] at this
    have h1 := mul_pos (neg_pos.2 (hκδ 0)) (hgpos a 0)
    have h2 := hhpos a 0
    by_contra hle
    push_neg at hle
    nlinarith [mul_nonneg (neg_nonneg.2 hle) h2.le]
  -- the admissible interval for moving along the kernel
  set xl : Fin 3 → ℝ := fun a => -z0.1 a / κ'.1 a with hxl
  set yu : Fin 3 → ℝ := fun b => z0.2 b / (-κ'.2 b) with hyu
  have hxy : ∀ a b, xl a < yu b := by
    intro a b
    have hra := hκγ a
    have hrb := neg_pos.2 (hκδ b)
    have e1 := heval z0 a b
    rw [hz0, hcF a b] at e1
    have e2 := heval κ' a b
    rw [hκ'ker, inner_zero_right] at e2
    have hη := hhpos a b
    have hθ := hgpos a b
    rw [hxl, hyu]
    simp only
    rw [div_lt_div_iff₀ hra hrb]
    -- `γ° a (-κδ b) + δ° b κγ a > 0`
    have key : (-z0.1 a) * (-κ'.2 b) < z0.2 b * κ'.1 a := by
      have hθ' : 0 < ⟪x a b, g b⟫ := hθ
      have : ⟪x a b, g b⟫ * (z0.2 b * κ'.1 a - (-z0.1 a) * (-κ'.2 b)) = κ'.1 a := by
        linear_combination (-κ'.1 a) * e1 + z0.1 a * e2
      by_contra hle
      push_neg at hle
      have : ⟪x a b, g b⟫ * (z0.2 b * κ'.1 a - (-z0.1 a) * (-κ'.2 b)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hθ'.le (by linarith)
      linarith
    linarith
  obtain ⟨a0, -, ha0⟩ := Finset.exists_max_image Finset.univ xl Finset.univ_nonempty
  obtain ⟨b0, -, hb0⟩ := Finset.exists_min_image Finset.univ yu Finset.univ_nonempty
  set t := (xl a0 + yu b0) / 2 with ht
  have htl : ∀ a, xl a < t := fun a => by
    have := ha0 a (Finset.mem_univ a); have := hxy a0 b0; rw [ht]; linarith
  have htu : ∀ b, t < yu b := fun b => by
    have := hb0 b (Finset.mem_univ b); have := hxy a0 b0; rw [ht]; linarith
  refine ⟨fun a => z0.1 a + t * κ'.1 a, fun b => z0.2 b + t * κ'.2 b, ?_, ?_, ?_⟩
  · intro a
    have h1 := htl a
    rw [hxl] at h1
    simp only at h1
    rw [div_lt_iff₀ (hκγ a)] at h1
    linarith
  · intro b
    have h1 := htu b
    rw [hyu] at h1
    simp only at h1
    rw [lt_div_iff₀ (neg_pos.2 (hκδ b))] at h1
    linarith
  · have e : Ψ (z0 + t • κ') = cF := by rw [map_add, map_smul, hκ'ker, smul_zero, add_zero, hz0]
    rw [← e, hΨ]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]

end Kalai5
