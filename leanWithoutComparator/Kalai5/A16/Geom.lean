import Kalai5.A16.ReduceSound
import Kalai5.Cube5.Geom
import Kalai5.LemmaA.Geom

/-!
# A16: from the polytope to eight points

`IsCSPolytope5.a16_of_core`: a centrally symmetric 5-polytope with sixteen vertices, four linearly
independent full normals `u_i` and fewer than `N` facets has at least `243` nonempty faces, given
the combinatorial core (`GoalN N` for every admissible configuration).

Proof: pick representatives and the coordinates `x ↦ (⟪u_i, x⟫, ⟪w, x⟫)`; the core gives either
`N` polar points with spanning tight sets (they pull back to `N` vertices of the polar of `P`, more
than `f₄`), or a fifth full normal, which with the `u_i` gives a cube polytope
(`cube_of_five_full`), or `242` distinct nonempty tight sets of polar families, which are the
vertex sets of `242` distinct proper faces (`faces_of_tight`).
-/

namespace Kalai5

open Set Module FullPrism A16

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- **At most `f₄` vertices of the polar.** -/
lemma IsCSPolytope5.card_le_fvec4 {P : Set E5} (hP : IsCSPolytope5 P) (S : Finset E5)
    (hS : ∀ w ∈ S, w ∈ (polarSet P).extremePoints ℝ) : S.card ≤ fvec P 4 := by
  obtain ⟨V, hV⟩ := hP.polar.polytope
  have h1 : fvec (polarSet P) 0 = fvec P 4 := by
    have := hP.fvec_polar 4 (by norm_num)
    rw [Nat.sub_self] at this
    exact this
  rw [hV, fvec_zero_eq] at h1
  have hsub : (S : Set E5) ⊆ (convexHull ℝ (V : Set E5)).extremePoints ℝ := by
    intro w hw; rw [← hV]; exact hS w hw
  have := Set.ncard_le_ncard hsub (extremePoints_finite V)
  rwa [Set.ncard_coe_finset, h1] at this

/-- **Faces from tight sets**: distinct nonempty tight sets of finite polar families of the vertex
set are the vertex sets of distinct proper faces (exposed by the sum of the family); with `P` itself
there are at least `M.card + 1` faces. -/
lemma IsCSPolytope5.faces_of_tight {P : Set E5} (hP : IsCSPolytope5 P) {X : Finset E5}
    (hPX : P = convexHull ℝ (X : Set E5)) (M : Finset (Set E5))
    (hM : ∀ m ∈ M, m.Nonempty ∧ ∃ Z : Finset E5, Z.Nonempty ∧
      (∀ y ∈ Z, ∀ x ∈ (X : Set E5), ⟪x, y⟫ ≤ 1) ∧ m = {x ∈ (X : Set E5) | ∀ y ∈ Z, ⟪x, y⟫ = 1}) :
    M.card + 1 ≤ (faces P).ncard := by
  classical
  have hM' : ∀ m ∈ M, ∃ Z : Finset E5, Z.Nonempty ∧
      (∀ y ∈ Z, ∀ x ∈ (X : Set E5), ⟪x, y⟫ ≤ 1) ∧ m = {x ∈ (X : Set E5) | ∀ y ∈ Z, ⟪x, y⟫ = 1} :=
    fun m hm => (hM m hm).2
  choose! Z hZ using hM'
  -- the functional `x ↦ ⟪Σ Z, x⟫` and its maximizers on `P`
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Set E5 → E5, ℓ = fun m => ∑ y ∈ Z m, y := ⟨_, rfl⟩
  obtain ⟨Fm, hFm⟩ : ∃ Fm : Set E5 → Set E5,
      Fm = fun m => {x ∈ P | ∀ x' ∈ P, innerSL ℝ (ℓ m) x' ≤ innerSL ℝ (ℓ m) x} := ⟨_, rfl⟩
  have hsum : ∀ m x, innerSL ℝ (ℓ m) x = ∑ y ∈ Z m, ⟪x, y⟫ := by
    intro m x
    rw [innerSL_apply_apply, hℓ, sum_inner]
    exact Finset.sum_congr rfl fun y _ => real_inner_comm _ _
  have hXP : (X : Set E5) ⊆ P := by rw [hPX]; exact subset_convexHull ℝ _
  have hmX : ∀ m ∈ M, m ⊆ X := by
    intro m hm x hx
    rw [(hZ m hm).2.2, Set.mem_sep_iff] at hx
    exact hx.1
  -- the bound on `P` and the value on `m`
  have hle : ∀ m ∈ M, ∀ x ∈ P, innerSL ℝ (ℓ m) x ≤ (Z m).card := by
    intro m hm x hx
    rw [hPX] at hx
    have hconv : Convex ℝ {x : E5 | innerSL ℝ (ℓ m) x ≤ (Z m).card} :=
      convex_halfSpace_le (innerSL ℝ (ℓ m) : E5 →ₗ[ℝ] ℝ).isLinear _
    refine convexHull_min (fun x hx => ?_) hconv hx
    show innerSL ℝ (ℓ m) x ≤ _
    rw [hsum]
    calc ∑ y ∈ Z m, ⟪x, y⟫ ≤ ∑ y ∈ Z m, (1 : ℝ) :=
          Finset.sum_le_sum fun y hy => (hZ m hm).2.1 y hy x hx
      _ = (Z m).card := by simp
  have heq : ∀ m ∈ M, ∀ x ∈ m, innerSL ℝ (ℓ m) x = (Z m).card := by
    intro m hm x hx
    have hx' := hx
    rw [(hZ m hm).2.2, Set.mem_sep_iff] at hx'
    rw [hsum, Finset.sum_congr rfl fun y hy => hx'.2 y hy]
    simp
  have hsubF : ∀ m ∈ M, m ⊆ Fm m := by
    intro m hm x hx
    rw [hFm]
    refine ⟨hXP (hmX m hm hx), fun x' hx' => ?_⟩
    rw [heq m hm x hx]
    exact hle m hm x' hx'
  -- the vertices of `Fm m` are `m`
  have htrace : ∀ m ∈ M, ∀ x ∈ (X : Set E5), x ∈ Fm m → x ∈ m := by
    intro m hm x hxX hxF
    rw [hFm] at hxF
    obtain ⟨x0, hx0⟩ := (hM m hm).1
    have h1 : ((Z m).card : ℝ) ≤ innerSL ℝ (ℓ m) x := by
      rw [← heq m hm x0 hx0]; exact hxF.2 x0 (hXP (hmX m hm hx0))
    rw [hsum] at h1
    have hall : ∀ y ∈ Z m, ⟪x, y⟫ ≤ 1 := fun y hy => (hZ m hm).2.1 y hy x hxX
    have hsumeq : ∑ y ∈ Z m, ⟪x, y⟫ = ∑ y ∈ Z m, (1 : ℝ) := by
      apply le_antisymm (Finset.sum_le_sum hall)
      simpa using h1
    have := (Finset.sum_eq_sum_iff_of_le hall).1 hsumeq
    rw [(hZ m hm).2.2, Set.mem_sep_iff]
    exact ⟨hxX, this⟩
  have hface : ∀ m ∈ M, Fm m ∈ faces P := by
    intro m hm
    obtain ⟨x0, hx0⟩ := (hM m hm).1
    exact ⟨⟨x0, hsubF m hm hx0⟩, fun _ => ⟨innerSL ℝ (ℓ m), by rw [hFm]⟩⟩
  have hinj : Set.InjOn Fm (M : Set (Set E5)) := by
    intro m hm m' hm' he
    ext x
    constructor
    · intro hx
      exact htrace m' hm' x (hmX m hm hx) (he ▸ hsubF m hm hx)
    · intro hx
      exact htrace m hm x (hmX m' hm' hx) (he.symm ▸ hsubF m' hm' hx)
  -- `0 ∈ P` is not in a proper face
  have hne : ∀ m ∈ M, Fm m ≠ P := by
    intro m hm he
    have h0 : (0 : E5) ∈ Fm m := by rw [he]; exact interior_subset hP.zero_mem_interior
    rw [hFm] at h0
    obtain ⟨x0, hx0⟩ := (hM m hm).1
    have h2 := h0.2 x0 (hXP (hmX m hm hx0))
    rw [heq m hm x0 hx0, map_zero] at h2
    have hc : (0 : ℝ) < (Z m).card := by exact_mod_cast Finset.card_pos.2 (hZ m hm).1
    linarith
  -- count
  have hsub : ((insert P (M.image Fm) : Finset (Set E5)) : Set (Set E5)) ⊆ faces P := by
    intro F hF
    rw [Finset.coe_insert, Set.mem_insert_iff] at hF
    rcases hF with rfl | hF
    · exact self_mem_faces hP.nonempty
    · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hF)
      exact hface m hm
  have hcard : (insert P (M.image Fm)).card = M.card + 1 := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injOn hinj]
    intro hPm
    obtain ⟨m, hm, he⟩ := Finset.mem_image.1 hPm
    exact hne m hm he
  have := Set.ncard_le_ncard hsub hP.faces_finite
  rw [Set.ncard_coe_finset, hcard] at this
  exact this

/-- The adjoint of the coordinate map: `T† y = Σ_j y_j w_j`. -/
lemma adjoint_coordMapOf (w : Fin 5 → E5) (y : E5) :
    LinearMap.adjoint (coordMapOf w) y = ∑ j, y j • w j := by
  apply ext_inner_left ℝ
  intro x
  rw [LinearMap.adjoint_inner_right, inner_eq_sum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordMapOf_apply, real_inner_smul_right, real_inner_comm]
  ring

/-- **A16, from the combinatorial core.** -/
theorem IsCSPolytope5.a16_of_core {P : Set E5} (hP : IsCSPolytope5 P) {N : ℕ}
    (hcore : ∀ y : Fin 8 → E5, (∀ v (j : Fin 4), y v j.castSucc = 1 ∨ y v j.castSucc = -1) →
      Function.Injective (pm16 y) →
      (∀ x₁ ∈ range (pm16 y), ∀ x₂ ∈ range (pm16 y), ∀ x₃ ∈ range (pm16 y), x₁ ≠ x₂ → x₁ ≠ x₃ →
        x₂ ≠ x₃ → (∀ j : Fin 4, x₁ j.castSucc = x₂ j.castSucc ∧ x₁ j.castSucc = x₃ j.castSucc) →
          False) →
      (∀ φ : E5 →ₗ[ℝ] ℝ, (∀ x ∈ range (pm16 y), φ x = 0) → φ = 0) →
      GoalN N (range (pm16 y)))
    (h16 : fvec P 0 = 16) {u : Fin 4 → E5} (hu : LinearIndependent ℝ u)
    (hfull : ∀ i, ∀ x ∈ P.extremePoints ℝ, ⟪u i, x⟫ = 1 ∨ ⟪u i, x⟫ = -1)
    (hh : fvec P 4 < N) : 243 ≤ (faces P).ncard := by
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
    exact hP.neg_mem_extremePoints hx
  have hX0 : (0 : E5) ∉ X := by
    rw [← Finset.mem_coe, hXcoe]
    exact hP.zero_not_mem_extremePoints
  obtain ⟨x, hxinj, hxrange⟩ := exists_reps16 hXcard hXsymm hX0
  -- coordinates
  obtain ⟨w, hw, hwu⟩ := exists_completion hu
  have hT : Function.Injective (coordMapOf w) := coordMapOf_injective hw
  set T := coordMapOf w with hTdef
  have hpm : pm16 (fun v => T (x v)) = T ∘ pm16 x := by
    funext i
    simp only [pm16, Function.comp_apply]
    split_ifs <;> simp [map_neg]
  have hrange : range (pm16 fun v => T (x v)) = T '' (X : Set E5) := by
    rw [hpm, range_comp, hxrange]
  have hgoal := hcore (fun v => T (x v)) (fun v j => ?_) (by rw [hpm]; exact hT.comp hxinj) ?_ ?_
  rotate_left
  · -- first four coordinates `±1`
    have : T (x v) j.castSucc = ⟪u j, x v⟫ := by rw [hTdef, coordMapOf_apply, hwu]
    rw [this]
    exact hfull j (x v) (by rw [← hXcoe, ← hxrange]; exact ⟨⟨v, by omega⟩, pm16_lo x v⟩)
  · -- fibres: the middle of three points on a vertical line is not extreme
    intro x₁ h₁ x₂ h₂ x₃ h₃ h12 h13 h23 hq
    set e := LinearEquiv.ofInjectiveEndo T hT
    have hext : ∀ z ∈ range (pm16 fun v => T (x v)), z ∈ (T '' P).extremePoints ℝ := by
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
  rw [hrange] at hgoal
  rcases hgoal with ⟨S, hS, hSpv⟩ | ⟨y, hy, hy4⟩ | hcount
  · -- `N` vertices of the polar of `P`: too many
    exfalso
    have hcard := hP.card_le_fvec4 (S.image (LinearMap.adjoint T)) fun y' hy' => by
      obtain ⟨y, hyS, rfl⟩ := Finset.mem_image.1 hy'
      exact ((hSpv y hyS).adjoint hT).mem_extremePoints hPX
    rw [Finset.card_image_of_injective _ (adjoint_injective hT)] at hcard
    omega
  · -- a fifth full normal: a cube polytope
    set y' := LinearMap.adjoint T y with hy'def
    have hy'full : ∀ x ∈ P.extremePoints ℝ, ⟪y', x⟫ = 1 ∨ ⟪y', x⟫ = -1 := by
      intro x hx
      rw [real_inner_comm, hy'def, LinearMap.adjoint_inner_right]
      exact hy (T x) ⟨x, by rw [hXcoe]; exact hx, rfl⟩
    have hy'sum : y' = ∑ j, y j • w j := by rw [hy'def, hTdef, adjoint_coordMapOf]
    -- the five normals `u_0, …, u_3, y'` are independent
    have hind : LinearIndependent ℝ (Fin.snoc u y' : Fin 5 → E5) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hw' := Fintype.linearIndependent_iff.1 hw
      -- rewrite the relation in the basis `w`
      set dd : Fin 5 → ℝ := Fin.lastCases (c (Fin.last 4) * y (Fin.last 4))
        (fun i => c i.castSucc + c (Fin.last 4) * y i.castSucc) with hdd
      have e1 : ∑ j, c j • (Fin.snoc u y' : Fin 5 → E5) j =
          ∑ i : Fin 4, c i.castSucc • w i.castSucc + c (Fin.last 4) • y' := by
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, hwu]
      have e2 : y' = ∑ i : Fin 4, y i.castSucc • w i.castSucc + y (Fin.last 4) • w (Fin.last 4) := by
        rw [hy'sum, Fin.sum_univ_castSucc]
      have hrel : ∑ j, dd j • w j = 0 := by
        rw [← hc, e1, e2, Fin.sum_univ_castSucc]
        simp only [hdd, Fin.lastCases_castSucc, Fin.lastCases_last, add_smul, smul_add,
          Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
        abel
      have hcoef := hw' _ hrel
      have h4 : c (Fin.last 4) * y (Fin.last 4) = 0 := by
        have := hcoef (Fin.last 4)
        change Fin.lastCases (motive := fun _ => ℝ) (c (Fin.last 4) * y (Fin.last 4))
          (fun i => c i.castSucc + c (Fin.last 4) * y i.castSucc) (Fin.last 4) = 0 at this
        rw [Fin.lastCases_last] at this
        exact this
      have hy4' : y (Fin.last 4) ≠ 0 := hy4
      have hc4 : c (Fin.last 4) = 0 := (mul_eq_zero.1 h4).resolve_right hy4'
      intro i
      refine Fin.lastCases hc4 (fun i => ?_) i
      have := hcoef i.castSucc
      change Fin.lastCases (motive := fun _ => ℝ) (c (Fin.last 4) * y (Fin.last 4))
        (fun i => c i.castSucc + c (Fin.last 4) * y i.castSucc) i.castSucc = 0 at this
      rw [Fin.lastCases_castSucc, hc4, zero_mul, add_zero] at this
      exact this
    have hfull5 : ∀ i, ∀ x ∈ P.extremePoints ℝ,
        ⟪(Fin.snoc u y' : Fin 5 → E5) i, x⟫ = 1 ∨ ⟪(Fin.snoc u y' : Fin 5 → E5) i, x⟫ = -1 := by
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]; exact hy'full
      · simp only [Fin.snoc_castSucc]; exact hfull i
    exact hP.cube_of_five_full h16 hind hfull5
  · -- `242` tight sets: `242` proper faces
    obtain ⟨M, hM, hMm⟩ := hcount.of_image
    have := hP.faces_of_tight hPX M hMm
    omega

end Kalai5
