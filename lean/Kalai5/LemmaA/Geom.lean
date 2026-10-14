import Kalai5.LemmaA.ReduceSound
import Kalai5.Full.Coords
import Kalai5.Full.Rank

/-!
# Lemma A: from the polytope to seven points

`IsCSPolytope5.lemmaA_of_core`: a centrally symmetric 5-polytope with fourteen vertices and four
linearly independent full normals `u_i` (`⟪u_i, x⟫ = ±1` at every vertex) has at least 243 faces,
given the combinatorial core (`LemmaA.lemmaA_core`, passed as a hypothesis to keep this file
independent of the certificate data).

Proof: pick one vertex `x_v` from each antipodal pair, complete the normals to a basis, and use
the coordinates `x ↦ (⟪u_i, x⟫, ⟪w, x⟫)`.  The images `y_v` have first four coordinates `±1`; no
three of the `±y_v` agree in those coordinates (the middle one would not be extreme); and they span
because `0` is an interior point.
-/

namespace Kalai5

open Set Module LemmaA

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- **Seven representatives** of a symmetric set of fourteen nonzero points. -/
lemma exists_reps {X : Finset E5} (hX : X.card = 14) (hsymm : ∀ x ∈ X, -x ∈ X)
    (h0 : (0 : E5) ∉ X) : ∃ x : Fin 7 → E5, Function.Injective (pm x) ∧ range (pm x) = X := by
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
  have hR : R.card = 7 := by omega
  have hdisj : ∀ x ∈ R, -x ∉ R := by
    intro x hx hnx
    have : x ∈ R ∩ R.image (fun x => -x) :=
      Finset.mem_inter.2 ⟨hx, Finset.mem_image.2 ⟨-x, hnx, neg_neg x⟩⟩
    have hpos : 0 < (R ∩ R.image fun x => -x).card := Finset.card_pos.2 ⟨x, this⟩
    omega
  set e := Finset.equivFinOfCardEq hR
  refine ⟨fun v => (e.symm v : E5), ?_, ?_⟩
  · rw [pm_injective_iff]
    refine ⟨fun u v h => e.symm.injective (Subtype.ext h), fun u v h => ?_⟩
    have hu := (e.symm u).2
    have hv := (e.symm v).2
    exact hdisj _ hv (by rw [← neg_eq_iff_eq_neg.2 h, neg_neg]; exact hu)
  · ext z
    rw [mem_range_pm, Finset.mem_coe]
    constructor
    · rintro ⟨v, rfl | rfl⟩
      · exact hRX (e.symm v).2
      · exact hsymm _ (hRX (e.symm v).2)
    · intro hz
      rcases hcov z hz with h | h
      · exact ⟨e ⟨z, h⟩, Or.inl (by simp)⟩
      · exact ⟨e ⟨-z, h⟩, Or.inr (by simp)⟩

/-- **Lemma A** (from the combinatorial core). -/
theorem IsCSPolytope5.lemmaA_of_core {P : Set E5} (hP : IsCSPolytope5 P)
    (hcore : ∀ y : Fin 7 → E5, (∀ v (j : Fin 4), y v j.castSucc = 1 ∨ y v j.castSucc = -1) →
      Function.Injective (pm y) →
      (∀ x₁ ∈ range (pm y), ∀ x₂ ∈ range (pm y), ∀ x₃ ∈ range (pm y), x₁ ≠ x₂ → x₁ ≠ x₃ →
        x₂ ≠ x₃ → (∀ j : Fin 4, x₁ j.castSucc = x₂ j.castSucc ∧ x₁ j.castSucc = x₃ j.castSucc) →
          False) →
      (∀ φ : E5 →ₗ[ℝ] ℝ, (∀ x ∈ range (pm y), φ x = 0) → φ = 0) →
      243 ≤ (faces (convexHull ℝ (range (pm y)))).ncard)
    (h14 : fvec P 0 = 14) {u : Fin 4 → E5} (hu : LinearIndependent ℝ u)
    (hfull : ∀ i, ∀ x ∈ P.extremePoints ℝ, ⟪u i, x⟫ = 1 ∨ ⟪u i, x⟫ = -1) :
    243 ≤ (faces P).ncard := by
  classical
  obtain ⟨V, hV⟩ := hP.polytope
  -- the vertex set
  set X := (extremePoints_finite V).toFinset with hXdef
  have hXcoe : (X : Set E5) = P.extremePoints ℝ := by rw [hXdef, Set.Finite.coe_toFinset, hV]
  have hPX : P = convexHull ℝ (X : Set E5) := by
    rw [hXcoe, hV, convexHull_extremePoints_eq]
  have hXcard : X.card = 14 := by
    have h1 := fvec_zero_eq V
    rw [Set.ncard_eq_toFinset_card _ (extremePoints_finite V)] at h1
    rw [hV] at h14
    rw [hXdef, ← h1]
    exact h14
  have hXsymm : ∀ x ∈ X, -x ∈ X := by
    intro x hx
    rw [← Finset.mem_coe, hXcoe] at hx ⊢
    exact neg_mem_extremePoints hP.symm hx
  have hX0 : (0 : E5) ∉ X := by
    rw [← Finset.mem_coe, hXcoe]
    exact hP.zero_not_mem_extremePoints
  obtain ⟨x, hxinj, hxrange⟩ := exists_reps hXcard hXsymm hX0
  -- coordinates
  obtain ⟨w, hw, hwu⟩ := exists_completion hu
  have hT : Function.Injective (coordMapOf w) := coordMapOf_injective hw
  set T := coordMapOf w with hTdef
  have hpm : pm (fun v => T (x v)) = T ∘ pm x := by
    funext i
    simp only [pm, Function.comp_apply]
    split_ifs <;> simp [map_neg]
  have hrange : range (pm fun v => T (x v)) = T '' (X : Set E5) := by
    rw [hpm, range_comp, hxrange]
  have hfaces : (faces P).ncard = (faces (convexHull ℝ (range (pm fun v => T (x v))))).ncard := by
    rw [hrange, ← LinearMap.image_convexHull, ← hPX, ncard_faces_image_of_injective T hT]
  rw [hfaces]
  refine hcore _ (fun v j => ?_) (by rw [hpm]; exact hT.comp hxinj) ?_ ?_
  · -- first four coordinates `±1`
    have : T (x v) j.castSucc = ⟪u j, x v⟫ := by rw [hTdef, coordMapOf_apply, hwu]
    rw [this]
    exact hfull j (x v) (by rw [← hXcoe, ← hxrange]; exact ⟨_, pm_lo x v⟩)
  · -- fibres: the middle of three points on a vertical line is not extreme
    intro x₁ h₁ x₂ h₂ x₃ h₃ h12 h13 h23 hq
    set e := LinearEquiv.ofInjectiveEndo T hT
    have hext : ∀ z ∈ range (pm fun v => T (x v)), z ∈ (T '' P).extremePoints ℝ := by
      intro z hz
      rw [hrange, hXcoe] at hz
      have h := image_extremePoints (𝕜 := ℝ) e P
      have he : ∀ s : Set E5, (e : E5 → E5) '' s = T '' s := fun s => rfl
      rw [he, he] at h
      rw [← h]
      exact hz
    have hoff : ∀ {a b : E5}, (∀ j : Fin 4, a j.castSucc = b j.castSucc) →
        ∀ i : Fin 5, i ≠ 4 → a i = b i := by
      intro a b hab i hi
      obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 (show i ≠ Fin.last 4 from hi)
      exact hab j
    exact not_three_on_line (hext x₁ h₁) (hext x₂ h₂) (hext x₃ h₃) h12 h13 h23 4
      (hoff fun j => (hq j).1) (hoff fun j => (hq j).2)
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
