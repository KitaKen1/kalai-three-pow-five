import Kalai5.Cube5.Cube
import Kalai5.LemmaA.Geom

/-!
# Cube polytopes: from the polytope to eight points

`IsCSPolytope5.cube_of_five_full`: a centrally symmetric 5-polytope with sixteen vertices and five
linearly independent full normals `u_i` (`⟪u_i, x⟫ = ±1` at every vertex) has at least `243`
nonempty faces.

Proof: pick one vertex `x_v` from each antipodal pair and use the coordinates
`x ↦ (⟪u_i, x⟫)_i`; the images lie in `{±1}⁵`, the sixteen points `±y_v` are distinct, and they
span because `0` is an interior point (`Cube5.cube_faces`).
-/

namespace Kalai5

open Set Module FullPrism

local notation "⟪" x ", " y "⟫" => inner ℝ x y

lemma pm16_injective_iff {y : Fin 8 → E5} :
    Function.Injective (pm16 y) ↔ Function.Injective y ∧ ∀ u v, y u ≠ -y v := by
  constructor
  · intro h
    refine ⟨fun u v huv => ?_, fun u v huv => ?_⟩
    · have := h (show pm16 y ⟨u, by omega⟩ = pm16 y ⟨v, by omega⟩ by rw [pm16_lo, pm16_lo, huv])
      exact Fin.ext (by simpa using this)
    · have := h (show pm16 y ⟨u, by omega⟩ = pm16 y ⟨v + 8, by omega⟩ by
        rw [pm16_lo, pm16_hi, huv])
      simp [Fin.ext_iff] at this
      omega
  · rintro ⟨hy, hneg⟩ i j hij
    unfold pm16 at hij
    split_ifs at hij with hi hj hj
    · exact Fin.ext (by simpa using hy hij)
    · exact absurd hij (hneg _ _)
    · exact absurd hij.symm (hneg _ _)
    · have := hy (neg_injective hij)
      simp [Fin.ext_iff] at this
      exact Fin.ext (by omega)

/-- **Eight representatives** of a symmetric set of sixteen nonzero points. -/
lemma exists_reps16 {X : Finset E5} (hX : X.card = 16) (hsymm : ∀ x ∈ X, -x ∈ X)
    (h0 : (0 : E5) ∉ X) : ∃ x : Fin 8 → E5, Function.Injective (pm16 x) ∧ range (pm16 x) = X := by
  classical
  obtain ⟨R, hRX, hcov, hcard⟩ := exists_half _ X rfl hsymm h0
  have hsub : X ⊆ R ∪ R.image (fun x => -x) := by
    intro x hx
    rcases hcov x hx with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨-x, h, neg_neg x⟩)
  have himg : (R.image fun x => -x).card = R.card := Finset.card_image_of_injective _ neg_injective
  have hle := Finset.card_le_card hsub
  have hun := Finset.card_union_add_card_inter R (R.image fun x => -x)
  have hR : R.card = 8 := by omega
  have hdisj : ∀ x ∈ R, -x ∉ R := by
    intro x hx hnx
    have : x ∈ R ∩ R.image (fun x => -x) :=
      Finset.mem_inter.2 ⟨hx, Finset.mem_image.2 ⟨-x, hnx, neg_neg x⟩⟩
    have hpos : 0 < (R ∩ R.image fun x => -x).card := Finset.card_pos.2 ⟨x, this⟩
    omega
  set e := Finset.equivFinOfCardEq hR
  refine ⟨fun v => (e.symm v : E5), ?_, ?_⟩
  · rw [pm16_injective_iff]
    refine ⟨fun u v h => e.symm.injective (Subtype.ext h), fun u v h => ?_⟩
    have hu := (e.symm u).2
    have hv := (e.symm v).2
    exact hdisj _ hv (by rw [← neg_eq_iff_eq_neg.2 h, neg_neg]; exact hu)
  · ext z
    rw [mem_range_pm16, Finset.mem_coe]
    constructor
    · rintro ⟨v, rfl | rfl⟩
      · exact hRX (e.symm v).2
      · exact hsymm _ (hRX (e.symm v).2)
    · intro hz
      rcases hcov z hz with h | h
      · exact ⟨e ⟨z, h⟩, Or.inl (by simp)⟩
      · exact ⟨e ⟨-z, h⟩, Or.inr (by simp)⟩

/-- **Cube polytopes**: sixteen vertices and five independent full normals give `243` faces. -/
theorem IsCSPolytope5.cube_of_five_full {P : Set E5} (hP : IsCSPolytope5 P)
    (h16 : fvec P 0 = 16) {u : Fin 5 → E5} (hu : LinearIndependent ℝ u)
    (hfull : ∀ i, ∀ x ∈ P.extremePoints ℝ, ⟪u i, x⟫ = 1 ∨ ⟪u i, x⟫ = -1) :
    243 ≤ (faces P).ncard := by
  classical
  obtain ⟨V, hV⟩ := hP.polytope
  -- the vertex set
  set X := (extremePoints_finite V).toFinset with hXdef
  have hXcoe : (X : Set E5) = P.extremePoints ℝ := by rw [hXdef, Set.Finite.coe_toFinset, hV]
  have hPX : P = convexHull ℝ (X : Set E5) := by
    rw [hXcoe, hV, convexHull_extremePoints_eq]
  have hXcard : X.card = 16 := by
    have h1 := fvec_zero_eq V
    rw [Set.ncard_eq_toFinset_card _ (extremePoints_finite V)] at h1
    rw [hV] at h16
    rw [hXdef, ← h1]
    exact h16
  have hXsymm : ∀ x ∈ X, -x ∈ X := by
    intro x hx
    rw [← Finset.mem_coe, hXcoe] at hx ⊢
    exact neg_mem_extremePoints hP.symm hx
  have hX0 : (0 : E5) ∉ X := by
    rw [← Finset.mem_coe, hXcoe]
    exact hP.zero_not_mem_extremePoints
  obtain ⟨x, hxinj, hxrange⟩ := exists_reps16 hXcard hXsymm hX0
  -- coordinates
  have hT : Function.Injective (coordMapOf u) := coordMapOf_injective hu
  set T := coordMapOf u with hTdef
  have hpm : pm16 (fun v => T (x v)) = T ∘ pm16 x := by
    funext i
    simp only [pm16, Function.comp_apply]
    split_ifs <;> simp [map_neg]
  have hrange : range (pm16 fun v => T (x v)) = T '' (X : Set E5) := by
    rw [hpm, range_comp, hxrange]
  have hfaces : (faces P).ncard =
      (faces (convexHull ℝ (range (pm16 fun v => T (x v))))).ncard := by
    rw [hrange, ← LinearMap.image_convexHull, ← hPX, ncard_faces_image_of_injective T hT]
  rw [hfaces]
  refine Cube5.cube_faces (fun v j => ?_) (by rw [hpm]; exact hT.comp hxinj) ?_
  · -- coordinates `±1`
    rw [hTdef, coordMapOf_apply]
    exact hfull j (x v) (by rw [← hXcoe, ← hxrange]; exact ⟨⟨v, by omega⟩, pm16_lo x v⟩)
  · -- spanning: `0` is an interior point
    intro φ hφ
    have h1 : φ.comp T = 0 := by
      apply linMap_eq_zero_of_interior hP.zero_mem_interior
      intro z hz
      have hsub : P ⊆ (LinearMap.ker (φ.comp T) : Set E5) := by
        rw [hPX]
        refine convexHull_min (fun a ha => ?_) (Submodule.convex _)
        rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply]
        exact hφ _ (by rw [hrange]; exact ⟨a, ha, rfl⟩)
      exact hsub hz
    have hsurj : Function.Surjective T := LinearMap.injective_iff_surjective.1 hT
    ext v
    obtain ⟨a, rfl⟩ := hsurj v
    have := congrArg (fun f : E5 →ₗ[ℝ] ℝ => f a) h1
    simpa using this

end Kalai5
