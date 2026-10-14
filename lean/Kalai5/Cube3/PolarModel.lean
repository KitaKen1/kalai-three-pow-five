import Kalai5.Cube3.Config
import Kalai5.Polar.Basic
import Kalai5.Polar.Faces

/-!
# The actual polar in five independent coordinates

The fourth class offset is forced, not an extra variable. The realization
and faithfulness fields give a linear equivalence with the ambient dual.
Thus vertices counted in this H-description are vertices of the actual polar.
-/

namespace Kalai5.Cube3

open Set Module FullPrism

local notation "⟪" x ", " y "⟫" => inner ℝ x y

noncomputable def offsets (p : E5) : Fin 4 → ℝ :=
  ![p 0, p 1, p 2, p 1 + p 2 - p 0]

noncomputable def planar (p : E5) : E 2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![p 3, p 4]

lemma offsets_balanced (p : E5) : Balanced (offsets p) := by
  simp [Balanced, offsets]

variable {x : Fin 8 → E5} (C : Config x)

namespace Config

noncomputable def value (p : E5) (v : Fin 8) : ℝ :=
  offsets p (C.c v) + ⟪planar p, C.k v⟫

lemma value_eq (p : E5) (v : Fin 8) :
    C.value p v = offsets p (C.c v) + p 3 * C.k v 0 + p 4 * C.k v 1 := by
  rw [value, LemmaB.Eight.inner_E2]
  change offsets p (C.c v) + (p 3 * C.k v 0 + p 4 * C.k v 1) = _
  ring

noncomputable def evaluation : E5 →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := C.value
  map_add' := by
    intro p q
    funext v
    simp only [value_eq, Pi.add_apply]
    generalize C.c v = j
    fin_cases j <;> simp [offsets] <;> ring
  map_smul' := by
    intro t p
    funext v
    simp only [value_eq, Pi.smul_apply, smul_eq_mul]
    generalize C.c v = j
    fin_cases j <;> simp [offsets] <;> ring

lemma evaluation_injective : Function.Injective C.evaluation := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro p hp
  have hpv : ∀ v, C.value p v = 0 := fun v => congrFun hp v
  have hb : planar p = 0 := C.faithful (offsets p) (offsets_balanced p) (planar p) hpv
  have ha : ∀ j, offsets p j = 0 := by
    intro j
    obtain ⟨v, hv⟩ := C.surj j
    have h := hpv v
    simpa only [value, hb, inner_zero_left, add_zero, hv] using h
  ext i
  fin_cases i
  · exact ha 0
  · exact ha 1
  · exact ha 2
  · exact congrArg (fun b : E 2 => b 0) hb
  · exact congrArg (fun b : E 2 => b 1) hb

/-- Realization can be chosen coherently and linearly, and is invertible. -/
theorem exists_polar_equiv : ∃ e : E5 ≃ₗ[ℝ] E5,
    ∀ p v, ⟪e p, x v⟫ = C.value p v := by
  classical
  let B := (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis
  choose z hz using fun i : Fin 5 => C.real (offsets (B i)) (offsets_balanced (B i)) (planar (B i))
  let L : E5 →ₗ[ℝ] E5 := B.constr ℝ z
  have hL : ∀ p v, ⟪L p, x v⟫ = C.value p v := by
    intro p v
    have hmaps : (innerSL ℝ (x v)).toLinearMap.comp L =
        (LinearMap.proj v).comp C.evaluation := by
      apply B.ext
      intro i
      simpa [L, value, evaluation, real_inner_comm] using hz i v
    have h := LinearMap.congr_fun hmaps p
    simpa [real_inner_comm, evaluation] using h
  have hinj : Function.Injective L := by
    intro p q hpq
    apply C.evaluation_injective
    funext v
    change C.value p v = C.value q v
    rw [← hL, ← hL, hpq]
  exact ⟨LinearEquiv.ofInjectiveEndo L hinj, hL⟩

/-- The polar in independent offset and planar coordinates. -/
def polarModel : Set E5 := {p | ∀ v, |C.value p v| ≤ 1}

lemma polarModel_image {e : E5 ≃ₗ[ℝ] E5}
    (he : ∀ p v, ⟪e p, x v⟫ = C.value p v) :
    e '' C.polarModel = polarSet (convexHull ℝ (range (pm16 x))) := by
  ext z
  obtain ⟨p, rfl⟩ := e.surjective z
  rw [e.injective.mem_set_image]
  change (∀ v, |C.value p v| ≤ 1) ↔ _
  let V : Finset E5 := Finset.univ.image (pm16 x)
  have hV : (V : Set E5) = range (pm16 x) := by simp [V]
  rw [← hV, mem_polarSet_convexHull]
  constructor
  · intro h y hy
    have hy' : y ∈ range (pm16 x) := by rw [← hV]; exact hy
    obtain ⟨v, rfl | rfl⟩ := mem_range_pm16.1 hy'
    · rw [real_inner_comm, he]; exact (abs_le.1 (h v)).2
    · rw [inner_neg_left, real_inner_comm, he]; linarith [(abs_le.1 (h v)).1]
  · intro h v
    have hpos := h (x v) (by rw [← Finset.mem_coe, hV]; exact ⟨_, pm16_lo x v⟩)
    have hneg := h (-x v) (by rw [← Finset.mem_coe, hV]; exact ⟨_, pm16_hi x v⟩)
    rw [real_inner_comm, he] at hpos
    rw [inner_neg_left, real_inner_comm, he] at hneg
    exact abs_le.2 ⟨by linarith, hpos⟩

/-- In particular, no model vertex is lost when returning to the original polar. -/
theorem polarModel_extreme_image {e : E5 ≃ₗ[ℝ] E5}
    (he : ∀ p v, ⟪e p, x v⟫ = C.value p v) :
    e '' C.polarModel.extremePoints ℝ =
      (polarSet (convexHull ℝ (range (pm16 x)))).extremePoints ℝ := by
  rw [image_extremePoints, C.polarModel_image he]

/-- A finite injective family of model vertices gives a lower bound for actual facets. -/
theorem model_vertices_le_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ)
    {ι : Type*} [Fintype ι] (f : ι → E5) (hf : Function.Injective f)
    (hmem : ∀ i, f i ∈ C.polarModel.extremePoints ℝ) : Fintype.card ι ≤ fvec P 4 := by
  classical
  obtain ⟨e, he⟩ := C.exists_polar_equiv
  obtain ⟨V, hV⟩ := hP.polytope
  have hconv : convexHull ℝ (range (pm16 x)) = P := by
    rw [hrange, hV]
    exact convexHull_extremePoints_eq V
  have hext : ∀ i, e (f i) ∈ (polarSet P).extremePoints ℝ := by
    intro i
    rw [← hconv, ← C.polarModel_extreme_image he]
    exact ⟨f i, hmem i, rfl⟩
  let S : Finset E5 := Finset.univ.image (fun i => e (f i))
  have hcard : S.card = Fintype.card ι := by
    dsimp [S]
    have hi : Function.Injective (fun i : ι => e (f i)) := fun _ _ h => hf (e.injective h)
    rw [Finset.card_image_of_injective _ hi, Finset.card_univ]
  obtain ⟨W, hW⟩ := hP.polar.polytope
  have hsub : (S : Set E5) ⊆ (polarSet P).extremePoints ℝ := by
    rintro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hz
    exact hext i
  have hfin : ((polarSet P).extremePoints ℝ).Finite := by
    rw [hW]; exact extremePoints_finite W
  have hle := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, hcard] at hle
  have hn : ((polarSet P).extremePoints ℝ).ncard = fvec P 4 := by
    have hp := hP.fvec_polar 4 (by norm_num)
    norm_num at hp
    rw [← hp, hW, fvec_zero_eq]
  rwa [hn] at hle

end Config
end Kalai5.Cube3
