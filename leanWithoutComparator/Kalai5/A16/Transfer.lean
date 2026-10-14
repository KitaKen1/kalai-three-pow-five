import Kalai5.FullProd.UPolar
import Kalai5.Small.Model

/-!
# A16: polar points with spanning tight sets, and linear transfer

`IsPVs X y`: `⟪x, y⟫ ≤ 1` on `X` and the tight points of `X` span (the hypotheses of L2).  Under an
injective linear map `L`, `IsPVs (L '' X) y → IsPVs X (L† y)`; distinct points stay distinct.  For the
vertex set of a polytope, `IsPVs` points are vertices of the polar, so at most `f₄` of them.
-/

namespace Kalai5.A16

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- `y` is a polar point of `X` whose tight points span. -/
def IsPVs (X : Set E5) (y : E5) : Prop :=
  (∀ x ∈ X, ⟪x, y⟫ ≤ 1) ∧ ∀ v : E5, (∀ x ∈ X, ⟪x, y⟫ = 1 → ⟪x, v⟫ = 0) → v = 0

/-- **Transfer along an injective linear map.** -/
lemma IsPVs.adjoint {L : E5 →ₗ[ℝ] E5} (hL : Function.Injective L) {X : Set E5} {y : E5}
    (hy : IsPVs (L '' X) y) : IsPVs X (LinearMap.adjoint L y) := by
  have hsurj : Function.Surjective L := LinearMap.injective_iff_surjective.1 hL
  refine ⟨fun x hx => ?_, fun v hv => ?_⟩
  · rw [LinearMap.adjoint_inner_right]
    exact hy.1 _ ⟨x, hx, rfl⟩
  · -- the vector `v' = (L⁻¹)† v` is orthogonal to the tight points of `L '' X`
    set e := LinearEquiv.ofBijective L ⟨hL, hsurj⟩
    set v' := LinearMap.adjoint (e.symm : E5 →ₗ[ℝ] E5) v
    have hv' : v' = 0 := by
      refine hy.2 v' fun x hx hxt => ?_
      obtain ⟨x0, hx0, rfl⟩ := hx
      rw [LinearMap.adjoint_inner_right]
      have : (e.symm : E5 →ₗ[ℝ] E5) (L x0) = x0 := e.symm_apply_apply x0
      rw [this]
      refine hv x0 hx0 ?_
      rw [LinearMap.adjoint_inner_right]
      exact hxt
    -- `v = L† v'`
    have : v = LinearMap.adjoint L v' := by
      rw [← LinearMap.comp_apply, ← LinearMap.adjoint_comp]
      have : (e.symm : E5 →ₗ[ℝ] E5).comp L = LinearMap.id :=
        LinearMap.ext fun x => e.symm_apply_apply x
      rw [this, LinearMap.adjoint_id]
      rfl
    rw [this, hv', map_zero]

lemma adjoint_injective {L : E5 →ₗ[ℝ] E5} (hL : Function.Injective L) :
    Function.Injective (LinearMap.adjoint L) := by
  intro y y' h
  have hsurj : Function.Surjective L := LinearMap.injective_iff_surjective.1 hL
  apply ext_inner_left ℝ
  intro x
  obtain ⟨x0, rfl⟩ := hsurj x
  rw [← LinearMap.adjoint_inner_right, h, LinearMap.adjoint_inner_right]

/-- **`IsPVs` points of the vertex set are vertices of the polar.** -/
lemma IsPVs.mem_extremePoints {P : Set E5} {V : Finset E5} (hPV : P = convexHull ℝ (V : Set E5))
    {y : E5} (hy : IsPVs (V : Set E5) y) : y ∈ (polarSet P).extremePoints ℝ := by
  rw [hPV]
  exact mem_extremePoints_polarSet_of_tight (fun x hx => hy.1 x hx) hy.2

/-- `X` has at least `242` distinct nonempty tight sets of finite families of polar points. -/
def CountGoal (X : Set E5) : Prop :=
  ∃ M : Finset (Set E5), 242 ≤ M.card ∧ ∀ m ∈ M, m.Nonempty ∧ ∃ Z : Finset E5, Z.Nonempty ∧
    (∀ y ∈ Z, ∀ x ∈ X, ⟪x, y⟫ ≤ 1) ∧ m = {x ∈ X | ∀ y ∈ Z, ⟪x, y⟫ = 1}

/-- **Transfer of tight sets along an injective linear map.** -/
lemma CountGoal.of_image {L : E5 →ₗ[ℝ] E5} {X : Set E5} (h : CountGoal (L '' X)) :
    CountGoal X := by
  classical
  obtain ⟨M, hM, hMm⟩ := h
  have key : ∀ m ∈ M, L '' (L ⁻¹' m ∩ X) = m := by
    intro m hm
    obtain ⟨-, Z, -, -, hm'⟩ := hMm m hm
    ext x
    constructor
    · rintro ⟨x', ⟨hx', -⟩, rfl⟩
      exact hx'
    · intro hx
      have hx2 := hx
      rw [hm', Set.mem_sep_iff] at hx2
      obtain ⟨⟨x', hx'X, rfl⟩, -⟩ := hx2
      exact ⟨x', ⟨hx, hx'X⟩, rfl⟩
  refine ⟨M.image (fun m => L ⁻¹' m ∩ X), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn]
    · exact hM
    · intro m hm m' hm' he
      rw [← key m hm, ← key m' hm']
      exact congrArg (fun s => L '' s) he
  · intro m' hm'
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hm'
    obtain ⟨⟨x0, hx0⟩, Z, hZ, hZpol, hm'⟩ := hMm m hm
    refine ⟨?_, Z.image (LinearMap.adjoint L), hZ.image _, ?_, ?_⟩
    · have hx0' := hx0
      rw [hm', Set.mem_sep_iff] at hx0'
      obtain ⟨⟨x1, hx1, rfl⟩, -⟩ := hx0'
      exact ⟨x1, hx0, hx1⟩
    · intro y' hy' x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hy'
      rw [LinearMap.adjoint_inner_right]
      exact hZpol y hy _ ⟨x, hx, rfl⟩
    · ext x
      rw [Set.mem_inter_iff, Set.mem_preimage, hm', Set.mem_sep_iff, Set.mem_sep_iff]
      have hall : (∀ y' ∈ Z.image (LinearMap.adjoint L), ⟪x, y'⟫ = 1) ↔
          ∀ y ∈ Z, ⟪L x, y⟫ = 1 := by
        constructor
        · intro h y hy
          rw [← LinearMap.adjoint_inner_right]
          exact h _ (Finset.mem_image_of_mem _ hy)
        · intro h y' hy'
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hy'
          rw [LinearMap.adjoint_inner_right]
          exact h y hy
      rw [hall]
      constructor
      · rintro ⟨⟨-, h⟩, hx⟩
        exact ⟨hx, h⟩
      · rintro ⟨hx, h⟩
        exact ⟨⟨⟨x, hx, rfl⟩, h⟩, hx⟩

end Kalai5.A16
