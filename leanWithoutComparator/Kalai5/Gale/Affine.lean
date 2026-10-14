import Kalai5.Faces.LowDim

/-!
# Affine value vectors and Gale vectors

For points `W : Fin n → E k` affinely spanning `E k`, the value vectors `(ℓ (W j))_j` of affine
functions `ℓ` form a subspace `affVals W` of `ℝⁿ` of dimension `k + 1`.  A **Gale diagram** of
`W` is a family `g : Fin n → ℝ²` whose linear relations are exactly `affVals W`
(`IsGale W g`); it exists as soon as `n ≤ k + 3`.

Two dimension counts drive the face computation:

* `finrank_inf_supp_add`: affine value vectors supported on `S` have dimension
  `#S - rank (g '' S)`;
* `finrank_inf_supp_compl_add`: affine value vectors vanishing on `F ≠ ∅` have dimension
  `k - dim (aff W(F))`.
-/

namespace Kalai5.Gale

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

noncomputable section

variable {k n : ℕ}

section evalMap

variable (W : Fin n → E k)

/-- Values `(⟪u, W j⟫ + c)_j` of the affine function `x ↦ ⟪u, x⟫ + c` at the points. -/
def evalMap : (E k × ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun uc j := ⟪uc.1, W j⟫ + uc.2
  map_add' x y := by
    funext j; simp only [Prod.fst_add, Prod.snd_add, inner_add_left, Pi.add_apply]; ring
  map_smul' r x := by
    funext j
    simp only [Prod.smul_fst, Prod.smul_snd, real_inner_smul_left, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

@[simp] lemma evalMap_apply (uc : E k × ℝ) (j : Fin n) : evalMap W uc j = ⟪uc.1, W j⟫ + uc.2 :=
  rfl

/-- Value vectors of affine functions at the points. -/
def affVals : Submodule ℝ (Fin n → ℝ) := LinearMap.range (evalMap W)

lemma evalMap_mem_affVals (uc : E k × ℝ) : evalMap W uc ∈ affVals W := LinearMap.mem_range_self _ _

variable {W}

lemma nonempty_of_affineSpan (hW : affineSpan ℝ (range W) = ⊤) : Nonempty (Fin n) := by
  by_contra hn
  rw [not_nonempty_iff] at hn
  rw [Set.range_eq_empty W, AffineSubspace.span_empty] at hW
  exact (AffineSubspace.bot_ne_top ℝ (E k) (E k)) hW

lemma evalMap_injective (hW : affineSpan ℝ (range W) = ⊤) : Function.Injective (evalMap W) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨u, c⟩ huc
  have h : ∀ j, ⟪u, W j⟫ + c = 0 := fun j => congrFun huc j
  obtain ⟨j0⟩ := nonempty_of_affineSpan hW
  have hv : vectorSpan ℝ (range W) = ⊤ := by
    rw [← direction_affineSpan, hW, AffineSubspace.direction_top]
  have hu : ∀ v ∈ vectorSpan ℝ (range W), ⟪u, v⟫ = 0 := by
    intro v hv
    rw [vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_range_self j0)] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := hx
      show ⟪u, W j -ᵥ W j0⟫ = 0
      rw [vsub_eq_sub, inner_sub_right]; linarith [h j, h j0]
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [real_inner_smul_right, hx, mul_zero]
  have hu0 : u = 0 := inner_self_eq_zero.1 (hu u (by rw [hv]; exact Submodule.mem_top))
  have hc : c = 0 := by have := h j0; rwa [hu0, inner_zero_left, zero_add] at this
  simp [hu0, hc]

lemma finrank_affVals (hW : affineSpan ℝ (range W) = ⊤) : finrank ℝ (affVals W) = k + 1 := by
  rw [affVals, LinearMap.finrank_range_of_inj (evalMap_injective hW), Module.finrank_prod,
    finrank_euclideanSpace_fin, Module.finrank_self]

end evalMap

/-! ### Vectors supported on a set of indices -/

/-- Vectors vanishing outside `S`. -/
def supp (S : Finset (Fin n)) : Submodule ℝ (Fin n → ℝ) where
  carrier := {a | ∀ j ∉ S, a j = 0}
  add_mem' ha hb j hj := by simp [ha j hj, hb j hj]
  zero_mem' _ _ := rfl
  smul_mem' r a ha j hj := by simp [ha j hj]

lemma mem_supp {S : Finset (Fin n)} {a : Fin n → ℝ} : a ∈ supp S ↔ ∀ j ∉ S, a j = 0 := Iff.rfl

lemma finrank_supp (S : Finset (Fin n)) : finrank ℝ (supp S) = S.card := by
  classical
  let e : supp S ≃ₗ[ℝ] (S → ℝ) :=
    { toFun := fun a j => a.1 j
      invFun := fun b => ⟨fun j => if h : j ∈ S then b ⟨j, h⟩ else 0, fun j hj => by simp [hj]⟩
      left_inv := fun a => by
        apply Subtype.ext; funext j
        by_cases h : j ∈ S
        · simp [h]
        · simp [h, a.2 j h]
      right_inv := fun b => by funext ⟨j, h⟩; simp [h]
      map_add' := fun a b => rfl
      map_smul' := fun r a => rfl }
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

/-! ### Gale diagrams -/

/-- `a ↦ ∑ a_j g_j`. -/
def galeMap (g : Fin n → Fin 2 → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  Fintype.linearCombination ℝ g

lemma galeMap_apply (g : Fin n → Fin 2 → ℝ) (a : Fin n → ℝ) : galeMap g a = ∑ j, a j • g j :=
  Fintype.linearCombination_apply ℝ g a

/-- `g` is a Gale diagram of `W`: the linear relations of `g` are the affine value vectors. -/
def IsGale (W : Fin n → E k) (g : Fin n → Fin 2 → ℝ) : Prop :=
  LinearMap.ker (galeMap g) = affVals W

lemma IsGale.mem_iff {W : Fin n → E k} {g : Fin n → Fin 2 → ℝ} (hg : IsGale W g)
    (a : Fin n → ℝ) : a ∈ affVals W ↔ ∑ j, a j • g j = 0 := by
  rw [← hg, LinearMap.mem_ker, galeMap_apply]

/-- **Existence of Gale diagrams in `ℝ²`** for `n ≤ k + 3` points affinely spanning `E k`. -/
theorem exists_isGale {W : Fin n → E k} (hW : affineSpan ℝ (range W) = ⊤) (hn : n ≤ k + 3) :
    ∃ g, IsGale W g := by
  set A := affVals W
  have hq : finrank ℝ ((Fin n → ℝ) ⧸ A) ≤ 2 := by
    have := Submodule.finrank_quotient_add_finrank A
    rw [finrank_affVals hW, Module.finrank_fin_fun] at this
    omega
  set r := finrank ℝ ((Fin n → ℝ) ⧸ A)
  let b := Module.finBasis ℝ ((Fin n → ℝ) ⧸ A)
  let ψ : ((Fin n → ℝ) ⧸ A) →ₗ[ℝ] (Fin 2 → ℝ) :=
    LinearMap.pi fun i : Fin 2 => if h : (i : ℕ) < r then b.coord ⟨i, h⟩ else 0
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    apply b.repr.injective
    ext ⟨i, hi⟩
    have := congrFun (LinearMap.mem_ker.1 hv) ⟨i, by omega⟩
    simp only [ψ, LinearMap.pi_apply, Pi.zero_apply] at this
    rw [dif_pos hi, Basis.coord_apply] at this
    simpa using this
  let Γ := ψ ∘ₗ A.mkQ
  refine ⟨fun j => Γ (Pi.single j 1), ?_⟩
  have hΓ : galeMap (fun j => Γ (Pi.single j 1)) = Γ := by
    refine LinearMap.pi_ext fun i x => ?_
    rw [galeMap, Fintype.linearCombination_apply_single, ← map_smul]
    congr 1
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [IsGale, hΓ, LinearMap.ker_comp, LinearMap.ker_eq_bot.2 hψ, Submodule.comap_bot,
    Submodule.ker_mkQ]

variable {W : Fin n → E k} {g : Fin n → Fin 2 → ℝ}

/-- **Rank count**: affine value vectors supported on `S` form a space of dimension
`#S - rank (g '' S)`. -/
theorem finrank_inf_supp_add (hg : IsGale W g) (S : Finset (Fin n)) :
    finrank ℝ ↥(affVals W ⊓ supp S) + finrank ℝ (Submodule.span ℝ (g '' ↑S)) = S.card := by
  classical
  set φ := (galeMap g).domRestrict (supp S)
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  rw [finrank_supp] at h1
  have hrange : LinearMap.range φ = Submodule.span ℝ (g '' ↑S) := by
    rw [LinearMap.range_domRestrict]
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      rw [galeMap_apply]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hj : j ∈ S
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
      · rw [(mem_supp.1 ha) j hj, zero_smul]; exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      refine ⟨Pi.single j 1, fun i hi => ?_, ?_⟩
      · have hji : i ≠ j := by rintro rfl; exact hi hj
        simp [Pi.single_apply, hji]
      · rw [galeMap, Fintype.linearCombination_apply_single, one_smul]
  have hker : finrank ℝ (LinearMap.ker φ) = finrank ℝ ↥(affVals W ⊓ supp S) := by
    rw [LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq,
      Submodule.map_comap_subtype, hg, inf_comm]
  rw [hrange, hker] at h1
  omega

/-- **Vanishing count**: affine value vectors vanishing on `F ≠ ∅` form a space of dimension
`k - dim (aff W(F))`. -/
theorem finrank_inf_supp_compl_add (hW : affineSpan ℝ (range W) = ⊤) {F : Finset (Fin n)}
    (hF : F.Nonempty) :
    finrank ℝ ↥(affVals W ⊓ supp Fᶜ) + finrank ℝ (vectorSpan ℝ (W '' ↑F)) = k := by
  classical
  obtain ⟨j0, hj0⟩ := hF
  set V := vectorSpan ℝ (W '' ↑F)
  let K : Submodule ℝ (E k × ℝ) :=
    { carrier := {uc | ∀ j ∈ F, ⟪uc.1, W j⟫ + uc.2 = 0}
      add_mem' := fun {x y} hx hy j hj => by
        simp only [Prod.fst_add, Prod.snd_add, inner_add_left]; linarith [hx j hj, hy j hj]
      zero_mem' := fun j _ => by simp
      smul_mem' := fun r x hx j hj => by
        simp only [Prod.smul_fst, Prod.smul_snd, real_inner_smul_left, smul_eq_mul]
        have := hx j hj
        calc r * ⟪x.1, W j⟫ + r * x.2 = r * (⟪x.1, W j⟫ + x.2) := by ring
          _ = 0 := by rw [this, mul_zero] }
  -- the vanishing value vectors are the image of `K`
  have hmap : affVals W ⊓ supp Fᶜ = K.map (evalMap W) := by
    ext a
    simp only [Submodule.mem_inf, Submodule.mem_map, mem_supp, Finset.mem_compl, not_not]
    constructor
    · rintro ⟨⟨uc, rfl⟩, h0⟩
      exact ⟨uc, fun j hj => h0 j hj, rfl⟩
    · rintro ⟨uc, huc, rfl⟩
      exact ⟨evalMap_mem_affVals W uc, fun j hj => huc j hj⟩
  have hK : finrank ℝ ↥(K.map (evalMap W)) = finrank ℝ K :=
    (Submodule.equivMapOfInjective _ (evalMap_injective hW) K).finrank_eq.symm
  -- `K ≃ Vᗮ`
  have hmemV : ∀ j ∈ F, W j - W j0 ∈ V := fun j hj =>
    vsub_mem_vectorSpan ℝ (mem_image_of_mem W (Finset.mem_coe.2 hj))
      (mem_image_of_mem W (Finset.mem_coe.2 hj0))
  have horth : ∀ uc ∈ K, uc.1 ∈ Vᗮ := by
    intro uc huc
    rw [Submodule.mem_orthogonal']
    intro v hv
    rw [show V = vectorSpan ℝ (W '' ↑F) from rfl,
      vectorSpan_eq_span_vsub_set_right ℝ (mem_image_of_mem W (Finset.mem_coe.2 hj0))] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨_, ⟨j, hj, rfl⟩, rfl⟩ := hx
      show ⟪uc.1, W j -ᵥ W j0⟫ = 0
      rw [vsub_eq_sub, inner_sub_right]; linarith [huc j hj, huc j0 hj0]
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [real_inner_smul_right, hx, mul_zero]
  let e : K ≃ₗ[ℝ] Vᗮ :=
    { toFun := fun uc => ⟨uc.1.1, horth uc.1 uc.2⟩
      invFun := fun u => ⟨(u.1, -⟪u.1, W j0⟫), fun j hj => by
        have h := (Submodule.mem_orthogonal' V u.1).1 u.2 _ (hmemV j hj)
        rw [inner_sub_right] at h
        simp only
        linarith⟩
      left_inv := fun uc => by
        have h := uc.2 j0 hj0
        apply Subtype.ext
        simp only
        ext
        · rfl
        · simp only; linarith
      right_inv := fun u => rfl
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl }
  have hV := Submodule.finrank_add_finrank_orthogonal V
  rw [finrank_euclideanSpace_fin] at hV
  rw [hmap, hK, e.finrank_eq]
  omega

end

end Kalai5.Gale
