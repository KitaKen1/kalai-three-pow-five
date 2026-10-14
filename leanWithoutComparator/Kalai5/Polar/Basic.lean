import Kalai5.Faces.Transitive

/-!
# Polar sets of polytopes

For `K = conv V` with `0` in its interior:
* `polarSet K = {y | ∀ x ∈ K, ⟪x, y⟫ ≤ 1}` has the H-description `∀ v ∈ V, ⟪v, y⟫ ≤ 1`;
* it is convex, closed, bounded, contains `0` in its interior;
* it has finitely many extreme points (at an extreme point the tight normals span), hence by
  Krein–Milman it is the convex hull of a finite set;
* bipolar theorem `polarSet (polarSet K) = K` (closed convex `K ∋ 0`, by separation).
-/

namespace Kalai5

open Set Metric

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {d : ℕ}

/-- Finitely many strict inequalities `a i < 1` survive small perturbations. -/
lemma exists_eps_pert {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha : ∀ i ∈ s, a i < 1) :
    ∃ ε > 0, ∀ i ∈ s, a i + ε * |b i| ≤ 1 := by
  set N : ℝ := 1 + ∑ i ∈ s, (|b i| + 1) / (1 - a i)
  have hterm : ∀ i ∈ s, 0 ≤ (|b i| + 1) / (1 - a i) := fun i hi => by
    have := ha i hi; positivity
  have hN : 0 < N := by have := Finset.sum_nonneg hterm; positivity
  refine ⟨1 / N, by positivity, fun i hi => ?_⟩
  have hpos : 0 < 1 - a i := by linarith [ha i hi]
  have hle : (|b i| + 1) / (1 - a i) ≤ N := by
    have := Finset.single_le_sum hterm hi; linarith
  rw [div_le_iff₀ hpos] at hle
  have : 1 / N * (|b i| + 1) ≤ 1 - a i := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hN]; linarith
  nlinarith [abs_nonneg (b i)]

/-- The polar of a set. -/
def polarSet (K : Set (E d)) : Set (E d) := {y | ∀ x ∈ K, ⟪x, y⟫ ≤ 1}

/-- The functional `x ↦ ⟪x, y⟫`. -/
noncomputable def ip (y : E d) : StrongDual ℝ (E d) := innerSL ℝ y

@[simp] lemma ip_apply (y x : E d) : ip y x = ⟪x, y⟫ := by
  simp only [ip, innerSL_apply_apply, real_inner_comm]

lemma polarSet_convex (K : Set (E d)) : Convex ℝ (polarSet K) := by
  intro y hy z hz a b ha hb hab x hx
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have h1 := hy x hx; have h2 := hz x hx
  nlinarith

lemma polarSet_isClosed (K : Set (E d)) : IsClosed (polarSet K) := by
  have : polarSet K = ⋂ x ∈ K, {y | ⟪x, y⟫ ≤ 1} := by ext y; simp [polarSet]
  rw [this]
  exact isClosed_biInter fun x _ =>
    isClosed_le (continuous_const.inner continuous_id) continuous_const

lemma zero_mem_polarSet (K : Set (E d)) : (0 : E d) ∈ polarSet K := fun x _ => by simp

lemma neg_mem_polarSet {K : Set (E d)} (hsymm : ∀ x ∈ K, -x ∈ K) {y : E d}
    (hy : y ∈ polarSet K) : -y ∈ polarSet K := fun x hx => by
  have := hy (-x) (hsymm x hx); rwa [inner_neg_left, ← inner_neg_right] at this

/-- H-description of the polar of a polytope. -/
lemma mem_polarSet_convexHull {V : Finset (E d)} {y : E d} :
    y ∈ polarSet (convexHull ℝ (V : Set (E d))) ↔ ∀ v ∈ V, ⟪v, y⟫ ≤ 1 := by
  classical
  refine ⟨fun h v hv => h v (subset_convexHull ℝ _ hv), fun h x hx => ?_⟩
  have := (le_on_convexHull (ip y) (c := 1) (fun v hv => by rw [ip_apply]; exact h v hv) hx).1
  rwa [ip_apply] at this

lemma norm_le_of_mem_convexHull {V : Finset (E d)} {x : E d}
    (hx : x ∈ convexHull ℝ (V : Set (E d))) : ‖x‖ ≤ ∑ v ∈ V, ‖v‖ := by
  have hsub : (V : Set (E d)) ⊆ closedBall 0 (∑ v ∈ V, ‖v‖) := fun v hv => by
    rw [mem_closedBall, dist_zero_right]
    exact Finset.single_le_sum (fun v _ => norm_nonneg v) hv
  have := convexHull_min hsub (convex_closedBall 0 _) hx
  rwa [mem_closedBall, dist_zero_right] at this

/-- The polar of a polytope contains a ball around `0`. -/
lemma zero_mem_interior_polarSet (V : Finset (E d)) :
    (0 : E d) ∈ interior (polarSet (convexHull ℝ (V : Set (E d)))) := by
  set R := ∑ v ∈ V, ‖v‖ + 1
  have hR : 0 < R := by positivity
  rw [mem_interior]
  refine ⟨ball 0 R⁻¹, fun y hy x hx => ?_, isOpen_ball, mem_ball_self (inv_pos.2 hR)⟩
  rw [mem_ball, dist_zero_right] at hy
  have hxn := norm_le_of_mem_convexHull hx
  calc ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
    _ ≤ R * R⁻¹ := mul_le_mul (by linarith) hy.le (norm_nonneg _) hR.le
    _ = 1 := mul_inv_cancel₀ hR.ne'

/-- If `0` is an interior point of `K`, the polar is bounded. -/
lemma polarSet_isBounded {K : Set (E d)} (h0 : (0 : E d) ∈ interior K) :
    Bornology.IsBounded (polarSet K) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 h0)
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨2 / r, fun y hy => ?_⟩
  rw [mem_closedBall, dist_zero_right]
  rcases eq_or_ne y 0 with hy0 | hy0
  · rw [hy0, norm_zero]; positivity
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hx : (r / 2 / ‖y‖) • y ∈ K := hball (by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      div_mul_cancel₀ _ hyn.ne']
    linarith)
  have h1 := hy _ hx
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at h1
  have h2 : r / 2 / ‖y‖ * ‖y‖ ^ 2 = r / 2 * ‖y‖ := by field_simp
  rw [h2] at h1
  rw [le_div_iff₀ hr]; nlinarith

lemma polarSet_isCompact {K : Set (E d)} (h0 : (0 : E d) ∈ interior K) :
    IsCompact (polarSet K) :=
  Metric.isCompact_of_isClosed_isBounded (polarSet_isClosed K) (polarSet_isBounded h0)

/-- **The polar of a polytope has finitely many extreme points.** -/
lemma extremePoints_polarSet_finite (V : Finset (E d)) :
    ((polarSet (convexHull ℝ (V : Set (E d)))).extremePoints ℝ).Finite := by
  classical
  set Q := polarSet (convexHull ℝ (V : Set (E d)))
  set T : E d → Finset (E d) := fun y => V.filter fun v => ⟪v, y⟫ = 1
  -- at an extreme point the tight normals span
  have hspan : ∀ y ∈ Q.extremePoints ℝ, (Submodule.span ℝ (T y : Set (E d)))ᗮ = ⊥ := by
    intro y hy
    rw [Submodule.eq_bot_iff]
    intro w hw
    by_contra hw0
    have hyQ : ∀ v ∈ V, ⟪v, y⟫ ≤ 1 := mem_polarSet_convexHull.1 hy.1
    obtain ⟨ε, hε, hεle⟩ := exists_eps_pert (V.filter fun v => ⟪v, y⟫ ≠ 1)
      (fun v => ⟪v, y⟫) (fun v => ⟪v, w⟫) (fun v hv => by
        rw [Finset.mem_filter] at hv; exact lt_of_le_of_ne (hyQ v hv.1) hv.2)
    have hmem : ∀ s : ℝ, |s| ≤ ε → y + s • w ∈ Q := by
      intro s hs
      refine mem_polarSet_convexHull.2 fun v hv => ?_
      rw [inner_add_right, real_inner_smul_right]
      by_cases h1 : ⟪v, y⟫ = 1
      · have : ⟪v, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal
          (Submodule.subset_span (by simp [T, hv, h1])) hw
        rw [this, h1]; simp
      · have := hεle v (Finset.mem_filter.2 ⟨hv, h1⟩)
        have hb : s * ⟪v, w⟫ ≤ ε * |⟪v, w⟫| := by
          calc s * ⟪v, w⟫ ≤ |s * ⟪v, w⟫| := le_abs_self _
            _ = |s| * |⟪v, w⟫| := abs_mul _ _
            _ ≤ ε * |⟪v, w⟫| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
        linarith
    have hplus := hmem ε (by rw [abs_of_pos hε])
    have hminus := hmem (-ε) (by rw [abs_neg, abs_of_pos hε])
    have hseg : y ∈ openSegment ℝ (y + (-ε) • w) (y + ε • w) :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
    have := ((mem_extremePoints.1 hy).2 _ hminus _ hplus hseg).1
    have hεw : ε • w = 0 := by
      have h' : y + (-ε) • w - y = 0 := by rw [this, sub_self]
      simpa [neg_smul] using h'
    exact hw0 ((smul_eq_zero.1 hεw).resolve_left hε.ne')
  -- the tight set determines an extreme point
  refine Set.Finite.of_finite_image (f := T) ?_ ?_
  · refine (V.powerset.finite_toSet.image (fun S : Finset (E d) => S)).subset ?_
    rintro _ ⟨y, -, rfl⟩
    exact ⟨T y, Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _)), rfl⟩
  · intro y hy y' _ hT
    have hmem : y - y' ∈ (Submodule.span ℝ (T y : Set (E d)))ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      induction hu using Submodule.span_induction with
      | mem v hv =>
        have hv' : v ∈ T y' := hT ▸ hv
        simp only [T, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter] at hv hv'
        rw [inner_sub_right, hv.2, hv'.2, sub_self]
      | zero => simp
      | add u₁ u₂ _ _ h₁ h₂ => rw [inner_add_left, h₁, h₂, add_zero]
      | smul r u _ h => rw [real_inner_smul_left, h, mul_zero]
    rw [hspan y hy] at hmem
    exact sub_eq_zero.1 ((Submodule.mem_bot ℝ).1 hmem)

/-- **The polar of a polytope with `0` in its interior is a polytope** (Krein–Milman). -/
lemma polarSet_eq_convexHull_extremePoints {V : Finset (E d)}
    (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d)))) :
    convexHull ℝ ((polarSet (convexHull ℝ (V : Set (E d)))).extremePoints ℝ) =
      polarSet (convexHull ℝ (V : Set (E d))) := by
  have hfin := extremePoints_polarSet_finite V
  have hc : IsClosed (convexHull ℝ
      ((polarSet (convexHull ℝ (V : Set (E d)))).extremePoints ℝ)) :=
    Set.Finite.isClosed_convexHull ℝ hfin
  have := closure_convexHull_extremePoints (polarSet_isCompact h0) (polarSet_convex _)
  rwa [hc.closure_eq] at this

lemma exists_polarSet_eq_convexHull {V : Finset (E d)}
    (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d)))) :
    ∃ W : Finset (E d), polarSet (convexHull ℝ (V : Set (E d))) = convexHull ℝ (W : Set (E d)) :=
  ⟨(extremePoints_polarSet_finite V).toFinset, by
    rw [Set.Finite.coe_toFinset, polarSet_eq_convexHull_extremePoints h0]⟩

/-- **Bipolar theorem** for closed convex sets containing `0`. -/
lemma polarSet_polarSet {K : Set (E d)} (hconv : Convex ℝ K) (hclosed : IsClosed K)
    (h0 : (0 : E d) ∈ K) : polarSet (polarSet K) = K := by
  ext x; constructor
  · intro hx
    by_contra hxK
    obtain ⟨f, u, hfK, hfx⟩ := geometric_hahn_banach_closed_point hconv hclosed hxK
    have hu : 0 < u := by have := hfK 0 h0; simpa using this
    set a := (InnerProductSpace.toDual ℝ (E d)).symm f
    have ha : ∀ z, ⟪a, z⟫ = f z := fun z => InnerProductSpace.toDual_symm_apply
    have hy : u⁻¹ • a ∈ polarSet K := fun z hz => by
      rw [real_inner_smul_right, real_inner_comm, ha, inv_mul_le_iff₀ hu, mul_one]
      exact (hfK z hz).le
    have := hx _ hy
    rw [real_inner_smul_left, ha, inv_mul_le_iff₀ hu, mul_one] at this
    linarith
  · intro hx y hy
    rw [real_inner_comm]; exact hy x hx

end Kalai5
