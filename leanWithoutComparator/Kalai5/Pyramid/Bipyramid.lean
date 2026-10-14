import Kalai5.Pyramid.Prism

/-!
# Bipyramids: `s(bipyramid over R) = 3 s(R)`

The bipyramid over `R = conv V ⊆ E n` (with `0` in its interior) is
`conv (V × {0} ∪ {(0, 1), (0, -1)}) ⊆ E (n+1)`.  Its polar is the prism `R° × [-1,1]`
(`polarSet_bipyr`), so `s(bipyramid) = s(prism) = 3 s(R°) = 3 s(R)` (`ncard_faces_bipyr`).
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

/-- `y ↦ (y, 0)`. -/
noncomputable def embZero (n : ℕ) : E n →ₗ[ℝ] E (n + 1) where
  toFun y := mkPt y 0
  map_add' y y' := by
    refine PiLp.ext fun j => ?_
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
  map_smul' c y := by
    refine PiLp.ext fun j => ?_
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp

@[simp] lemma embZero_apply (y : E n) : embZero n y = mkPt y 0 := rfl

/-- The vertices of the bipyramid over `conv V`. -/
noncomputable def bipyrV (V : Finset (E n)) : Finset (E (n + 1)) :=
  V.image (fun y => mkPt y 0) ∪ {mkPt 0 1, mkPt 0 (-1)}

lemma inner_mkPt (y : E n) (t : ℝ) (z : E (n + 1)) :
    ⟪mkPt y t, z⟫ = ⟪y, fstPart z⟫ + t * z (Fin.last n) := by
  rw [inner_split]; simp

/-- **The polar of a bipyramid is a prism.** -/
lemma polarSet_bipyr (V : Finset (E n)) :
    polarSet (convexHull ℝ ((bipyrV V : Finset (E (n + 1))) : Set (E (n + 1)))) =
      prism (polarSet (convexHull ℝ (V : Set (E n)))) := by
  classical
  ext z
  rw [mem_polarSet_convexHull]
  simp only [prism, Set.mem_ofPred_eq, mem_polarSet_convexHull]
  constructor
  · intro h
    refine ⟨fun y hy => ?_, ?_, ?_⟩
    · have := h (mkPt y 0)
        (Finset.mem_union_left _ (Finset.mem_image_of_mem (fun y => mkPt y 0) hy))
      rw [inner_mkPt] at this
      simpa using this
    · have := h (mkPt 0 (-1))
        (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      rw [inner_mkPt] at this
      simp at this
      linarith
    · have := h (mkPt 0 1) (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
      rw [inner_mkPt] at this
      simpa using this
  · rintro ⟨h1, h2, h3⟩ x hx
    simp only [bipyrV, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with ⟨y, hy, rfl⟩ | rfl | rfl
    · rw [inner_mkPt]; simpa using h1 y hy
    · rw [inner_mkPt]; simpa using h3
    · rw [inner_mkPt]; simp; linarith

lemma norm_fstPart_le (z : E (n + 1)) : ‖fstPart z‖ ≤ ‖z‖ ∧ |z (Fin.last n)| ≤ ‖z‖ := by
  have h := inner_split z z
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have hz := norm_nonneg z
  have hy := norm_nonneg (fstPart z)
  constructor
  · nlinarith [sq_nonneg (z (Fin.last n))]
  · have ht2 : z (Fin.last n) * z (Fin.last n) ≤ ‖z‖ ^ 2 := by
      nlinarith [sq_nonneg ‖fstPart z‖]
    have habs : |z (Fin.last n)| ^ 2 = z (Fin.last n) * z (Fin.last n) := by
      rw [sq_abs]; ring
    nlinarith [abs_nonneg (z (Fin.last n))]

/-- The bipyramid over a polytope with `0` inside has `0` inside. -/
lemma zero_mem_interior_bipyr {V : Finset (E n)}
    (h0 : (0 : E n) ∈ interior (convexHull ℝ (V : Set (E n)))) :
    (0 : E (n + 1)) ∈ interior (convexHull ℝ ((bipyrV V : Finset (E (n + 1))) : Set (E (n + 1)))) := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 h0)
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨min r 1 / 2, by positivity, fun z hz => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hz
  obtain ⟨hy, ht⟩ := norm_fstPart_le z
  have hmin1 : min r 1 ≤ 1 := min_le_right _ _
  have hminr : min r 1 ≤ r := min_le_left _ _
  set t := z (Fin.last n) with htdef
  have ht2 : |t| < 1 / 2 := by linarith
  set s := 1 - |t| with hsdef
  have hs : 1 / 2 < s := by linarith
  have hs0 : 0 < s := by linarith
  set y' := s⁻¹ • fstPart z with hy'def
  have hy'mem : y' ∈ convexHull ℝ (V : Set (E n)) := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, hy'def, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hs0)]
    rw [inv_mul_lt_iff₀ hs0]
    nlinarith
  set σ : ℝ := if 0 ≤ t then 1 else -1 with hσ
  have hσt : |t| * σ = t := by
    rw [hσ]
    split_ifs with h
    · rw [abs_of_nonneg h, mul_one]
    · rw [abs_of_neg (not_le.1 h)]; ring
  have hdecomp : s • mkPt y' 0 + |t| • mkPt 0 σ = z := by
    refine PiLp.ext fun j => ?_
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, mkPt_last, mkPt_last, smul_eq_mul,
        smul_eq_mul, mul_zero, zero_add, hσt]
    · simp only [PiLp.add_apply, PiLp.smul_apply, mkPt_castSucc, PiLp.zero_apply, smul_eq_mul,
        mul_zero, add_zero, hy'def, fstPart_apply, ← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul]
  have hA : mkPt y' 0 ∈ convexHull ℝ ((bipyrV V : Finset (E (n + 1))) : Set (E (n + 1))) := by
    have h1 : embZero n y' ∈ embZero n '' convexHull ℝ (V : Set (E n)) := ⟨y', hy'mem, rfl⟩
    rw [LinearMap.image_convexHull] at h1
    refine convexHull_mono ?_ h1
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem (fun y => mkPt y 0) hy))
  have hB : mkPt 0 σ ∈ convexHull ℝ ((bipyrV V : Finset (E (n + 1))) : Set (E (n + 1))) := by
    apply subset_convexHull
    rw [hσ]
    split_ifs <;> simp [bipyrV]
  rw [← hdecomp]
  exact convex_convexHull ℝ _ hA hB hs0.le (abs_nonneg t) (by rw [hsdef]; ring)

/-- **A bipyramid has three times as many nonempty faces as its base.** -/
theorem ncard_faces_bipyr {V : Finset (E n)}
    (h0 : (0 : E n) ∈ interior (convexHull ℝ (V : Set (E n)))) :
    (faces (convexHull ℝ ((bipyrV V : Finset (E (n + 1))) : Set (E (n + 1))))).ncard =
      3 * (faces (convexHull ℝ (V : Set (E n)))).ncard := by
  rw [← ncard_faces_polarSet (zero_mem_interior_bipyr h0), polarSet_bipyr, ncard_faces_prism,
    ncard_faces_polarSet h0]

end Kalai5
