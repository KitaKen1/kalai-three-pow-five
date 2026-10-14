import Kalai5.Foundations

/-!
# Basic facts about faces of polytopes

* a face is the set of maximizers of a continuous linear functional;
* faces of `conv V` are `conv (V ∩ F)`, hence a polytope has finitely many faces;
* a face containing an interior point is the whole set;
* proper faces have dimension at most `d - 1`, the polytope has dimension `d`;
* for centrally symmetric polytopes, `F ↦ -F` permutes the faces, preserving dimension, and has no
  fixed points among proper faces.
-/

namespace Kalai5

open Set Pointwise

variable {d : ℕ}

/-- A finite set with an involution without fixed points has even cardinality. -/
lemma even_card_of_involution {α : Type*} (S : Finset α) (σ : α → α)
    (hmaps : ∀ x ∈ S, σ x ∈ S) (hinv : ∀ x ∈ S, σ (σ x) = x) (hne : ∀ x ∈ S, σ x ≠ x) :
    Even S.card := by
  have h : ∑ x ∈ S, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun x _ => σ x) (fun _ _ => by decide) (fun a ha _ => hne a ha)
      hmaps hinv
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact (ZMod.natCast_eq_zero_iff_even).1 h

section general

variable {P F : Set (E d)}

lemma exists_functional (hF : F ∈ faces P) :
    ∃ l : StrongDual ℝ (E d), F = {x ∈ P | ∀ y ∈ P, l y ≤ l x} := hF.2 hF.1

lemma face_subset (hF : F ∈ faces P) : F ⊆ P := by
  obtain ⟨l, hl⟩ := exists_functional hF
  intro x hx; rw [hl] at hx; exact hx.1

lemma face_convex (hP : Convex ℝ P) (hF : F ∈ faces P) : Convex ℝ F := hF.2.convex hP

/-- A face containing an interior point is everything. -/
lemma face_eq_of_mem_interior (hF : F ∈ faces P) {z : E d} (hzF : z ∈ F)
    (hz : z ∈ interior P) : F = P := by
  obtain ⟨l, hl⟩ := exists_functional hF
  have hzmax : ∀ y ∈ P, l y ≤ l z := by rw [hl] at hzF; exact hzF.2
  have key : ∀ w : E d, l w ≤ 0 := by
    intro w
    have hnhds : P ∈ nhds z := mem_interior_iff_mem_nhds.1 hz
    have hcont : Continuous fun t : ℝ => z + t • w := by fun_prop
    have hpre : (fun t : ℝ => z + t • w) ⁻¹' P ∈ nhds (0 : ℝ) :=
      hcont.continuousAt.preimage_mem_nhds (by simpa using hnhds)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hpre
    have hmem : z + (δ / 2) • w ∈ P := by
      apply hball
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    have := hzmax _ hmem
    rw [map_add, map_smul, smul_eq_mul] at this
    nlinarith
  have hl0 : ∀ w : E d, l w = 0 := fun w => by
    have h1 := key w; have h2 := key (-w); rw [map_neg] at h2; linarith
  rw [hl]; ext x
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, fun y _ => by rw [hl0 y, hl0 x]⟩⟩

/-- Faces of `conv V` are `conv (V ∩ F)`. -/
lemma face_eq_convexHull_filter [DecidablePred (· ∈ F)] {V : Finset (E d)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E d)))) :
    F = convexHull ℝ ((V.filter (· ∈ F) : Finset (E d)) : Set (E d)) := by
  obtain ⟨l, hl⟩ := exists_functional hF
  apply Subset.antisymm
  · intro x hx
    have hxP : x ∈ convexHull ℝ (V : Set (E d)) := face_subset hF hx
    obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.1 hxP
    have hxF := hx
    rw [hl] at hx
    have hmax : ∀ y ∈ V, l y ≤ l x := fun y hy => hx.2 y (subset_convexHull ℝ _ hy)
    have hlx : l x = ∑ y ∈ V, w y * l y := by
      conv_lhs => rw [← hwx]
      simp [map_sum, map_smul]
    have hsum : ∑ y ∈ V, w y * (l x - l y) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, ← hlx, sub_self]
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun y hy =>
      mul_nonneg (hw0 y hy) (sub_nonneg.2 (hmax y hy))).1 hsum
    have hyF : ∀ y ∈ V, w y ≠ 0 → y ∈ F := by
      intro y hy hwy
      have hly : l y = l x := by
        have := hzero y hy
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hwy
        · linarith
      rw [hl]
      exact ⟨subset_convexHull ℝ _ hy, fun z hz => by rw [hly]; exact hx.2 z hz⟩
    refine Finset.mem_convexHull'.2 ⟨w, fun y hy => hw0 y (Finset.mem_filter.1 hy).1, ?_, ?_⟩
    · rw [Finset.sum_filter_of_ne fun y hy hwy => hyF y hy hwy]; exact hw1
    · rw [Finset.sum_filter_of_ne fun y hy hwy => hyF y hy fun h => hwy (by simp [h])]
      exact hwx
  · apply convexHull_min _ (hF.2.convex (convex_convexHull ℝ _))
    intro y hy; exact (Finset.mem_filter.1 hy).2

/-- A polytope has finitely many faces. -/
lemma faces_finite (hP : IsPolytope P) : (faces P).Finite := by
  classical
  obtain ⟨V, rfl⟩ := hP.polytope
  apply ((V.powerset.image fun S : Finset (E d) => convexHull ℝ (S : Set (E d))).finite_toSet).subset
  intro F hF
  exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨V.filter (· ∈ F),
    Finset.mem_powerset.2 (Finset.filter_subset _ _), (face_eq_convexHull_filter hF).symm⟩)

lemma dim_le (F : Set (E d)) : dim F ≤ d := by
  unfold dim
  have := Submodule.finrank_le (vectorSpan ℝ F)
  rwa [finrank_euclideanSpace_fin] at this

/-- A convex set with nonempty interior has full dimension. -/
lemma dim_eq_of_interior (hconv : Convex ℝ P) (hint : (interior P).Nonempty) : dim P = d := by
  unfold dim
  rw [AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top
    (h := (hconv.interior_nonempty_iff_affineSpan_eq_top).1 hint), finrank_top,
    finrank_euclideanSpace_fin]

/-- Proper faces have dimension at most `d - 1`. -/
lemma dim_add_one_le_of_ne (hF : F ∈ faces P) (hne : F ≠ P) : dim F + 1 ≤ d := by
  obtain ⟨l, hl⟩ := exists_functional hF
  have hl0 : l ≠ 0 := by
    rintro rfl; apply hne; rw [hl]; ext x; simp
  have hle : vectorSpan ℝ F ≤ LinearMap.ker (l : E d →ₗ[ℝ] ℝ) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro v ⟨a, ha, b, hb, rfl⟩
    have ha' := ha; have hb' := hb
    rw [hl] at ha' hb'
    simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, map_sub,
      ContinuousLinearMap.coe_coe]
    have h1 := ha'.2 b hb'.1; have h2 := hb'.2 a ha'.1; linarith
  have hrange : Module.finrank ℝ (LinearMap.range (l : E d →ₗ[ℝ] ℝ)) = 1 := by
    have hle1 := Submodule.finrank_le (LinearMap.range (l : E d →ₗ[ℝ] ℝ))
    rw [Module.finrank_self] at hle1
    have hne0 : Module.finrank ℝ (LinearMap.range (l : E d →ₗ[ℝ] ℝ)) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
      intro h; apply hl0; ext x; simpa using congrArg (fun f => f x) h
    omega
  have hrk := LinearMap.finrank_range_add_finrank_ker (l : E d →ₗ[ℝ] ℝ)
  rw [finrank_euclideanSpace_fin, hrange] at hrk
  have := Submodule.finrank_mono hle
  unfold dim; omega

lemma vsub_neg_eq (F : Set (E d)) : (-F) -ᵥ (-F) = F -ᵥ F := by
  ext v; simp only [Set.mem_vsub, Set.mem_neg, vsub_eq_sub]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨-y, hy, -x, hx, by abel⟩
  · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨-y, by simpa using hy, -x, by simpa using hx, by abel⟩

lemma dim_neg (F : Set (E d)) : dim (-F) = dim F := by
  unfold dim; rw [vectorSpan_def, vectorSpan_def, vsub_neg_eq]

/-- For a symmetric `P`, the negative of a face is a face. -/
lemma neg_mem_faces (hsymm : ∀ x ∈ P, -x ∈ P) (hF : F ∈ faces P) : -F ∈ faces P := by
  obtain ⟨l, hl⟩ := exists_functional hF
  refine ⟨hF.1.neg, fun _ => ⟨-l, ?_⟩⟩
  ext x
  rw [Set.mem_neg, hl]
  constructor
  · rintro ⟨hxP, hmax⟩
    refine ⟨by simpa using hsymm _ hxP, fun y hy => ?_⟩
    have := hmax (-y) (hsymm y hy)
    simp only [map_neg, ContinuousLinearMap.neg_apply] at this ⊢
    linarith
  · rintro ⟨hxP, hmax⟩
    refine ⟨hsymm x hxP, fun y hy => ?_⟩
    have := hmax (-y) (hsymm y hy)
    simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg] at this ⊢
    linarith

end general

/-! ### Centrally symmetric 5-polytopes -/

section cs

variable {P F : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.convex : Convex ℝ P := by
  obtain ⟨V, rfl⟩ := hP.polytope; exact convex_convexHull ℝ _

lemma IsCSPolytope5.zero_mem_interior : (0 : E5) ∈ interior P := by
  obtain ⟨z, hz⟩ := hP.full
  have hneg : -z ∈ interior P := by
    have hsub : (fun x : E5 => -x) ⁻¹' interior P ⊆ P := fun x hx => by
      simpa using hP.symm _ (interior_subset hx)
    have hopen : IsOpen ((fun x : E5 => -x) ⁻¹' interior P) :=
      isOpen_interior.preimage continuous_neg
    exact interior_maximal hsub hopen (by simpa using hz)
  have := hP.convex.interior hz hneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simpa [← smul_add] using this

lemma IsCSPolytope5.nonempty : P.Nonempty := by
  obtain ⟨z, hz⟩ := hP.full; exact ⟨z, interior_subset hz⟩

lemma IsCSPolytope5.dim_self : dim P = 5 := dim_eq_of_interior hP.convex hP.full

lemma IsCSPolytope5.faces_finite : (faces P).Finite := Kalai5.faces_finite hP.toIsPolytope

/-- A face containing a pair `x, -x` is the whole polytope. -/
lemma IsCSPolytope5.eq_of_mem_of_neg_mem (hF : F ∈ faces P) {x : E5} (hx : x ∈ F)
    (hnx : -x ∈ F) : F = P := by
  have h0 : (0 : E5) ∈ F := by
    have := face_convex hP.convex hF hx hnx (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa [← smul_add] using this
  exact face_eq_of_mem_interior hF h0 hP.zero_mem_interior

/-- A face equal to its negative is the whole polytope. -/
lemma IsCSPolytope5.eq_of_neg_eq (hF : F ∈ faces P) (hneg : -F = F) : F = P := by
  obtain ⟨x, hx⟩ := hF.1
  have hnx : -x ∈ F := by
    have : x ∈ -F := by rw [hneg]; exact hx
    simpa using this
  exact hP.eq_of_mem_of_neg_mem hF hx hnx

omit hP in
lemma dim_le_four (hF : F ∈ faces P) (hne : F ≠ P) : dim F ≤ 4 := by
  have := dim_add_one_le_of_ne hF hne; omega

lemma IsCSPolytope5.eq_of_dim (hF : F ∈ faces P) (h5 : dim F = 5) : F = P := by
  by_contra hne; have := dim_le_four hF hne; omega

/-- **Proper faces come in antipodal pairs.** -/
theorem IsCSPolytope5.even_fvec (k : ℕ) (hk : k ≤ 4) : Even (fvec P k) := by
  classical
  have hfin : {F | F ∈ faces P ∧ dim F = k}.Finite :=
    hP.faces_finite.subset fun F hF => hF.1
  rw [fvec, Set.ncard_eq_toFinset_card _ hfin]
  refine even_card_of_involution _ (fun F => -F) ?_ (fun F _ => neg_neg F) ?_
  · intro F hF
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hF ⊢
    exact ⟨neg_mem_faces hP.symm hF.1, by rw [dim_neg]; exact hF.2⟩
  · intro F hF hFF
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hF
    have := hP.eq_of_neg_eq hF.1 hFF
    have h5 := hP.dim_self
    rw [← this] at h5; omega

/-- **Flags of proper faces come in antipodal pairs.** -/
theorem IsCSPolytope5.even_flag2 (i j : ℕ) (hj : j ≤ 4) : Even (flag2 P i j) := by
  classical
  have hfin : {FG : Set E5 × Set E5 | FG.1 ∈ faces P ∧ FG.2 ∈ faces P ∧ FG.1 ⊆ FG.2 ∧
      dim FG.1 = i ∧ dim FG.2 = j}.Finite :=
    (hP.faces_finite.prod hP.faces_finite).subset fun FG h => ⟨h.1, h.2.1⟩
  rw [flag2, Set.ncard_eq_toFinset_card _ hfin]
  refine even_card_of_involution _ (fun FG => (-FG.1, -FG.2)) ?_
    (fun FG _ => by simp) ?_
  · intro FG hFG
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hFG ⊢
    exact ⟨neg_mem_faces hP.symm hFG.1, neg_mem_faces hP.symm hFG.2.1,
      Set.neg_subset_neg.2 hFG.2.2.1, by rw [dim_neg]; exact hFG.2.2.2.1,
      by rw [dim_neg]; exact hFG.2.2.2.2⟩
  · intro FG hFG hfix
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hFG
    have h2 : -FG.2 = FG.2 := congrArg Prod.snd hfix
    have := hP.eq_of_neg_eq hFG.2.1 h2
    have h5 := hP.dim_self
    rw [← this] at h5; omega

/-- **The number of nonempty faces is `f₀ + … + f₄ + 1`.** -/
theorem IsCSPolytope5.faces_ncard :
    (faces P).ncard = fvec P 0 + fvec P 1 + fvec P 2 + fvec P 3 + fvec P 4 + 1 := by
  classical
  have hfin := hP.faces_finite
  have hfiber : ∀ k, fvec P k = (hfin.toFinset.filter fun F => dim F = k).card := by
    intro k
    have hk : {F | F ∈ faces P ∧ dim F = k}.Finite := hfin.subset fun F hF => hF.1
    rw [fvec, Set.ncard_eq_toFinset_card _ hk]
    congr 1; ext F; simp
  have h5 : fvec P 5 = 1 := by
    rw [fvec, Set.ncard_eq_one]
    refine ⟨P, ?_⟩
    ext F; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hF, hd⟩; exact hP.eq_of_dim hF hd
    · rintro rfl; exact ⟨self_mem_faces hP.nonempty, hP.dim_self⟩
  rw [Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_card_fiberwise (f := dim) (t := Finset.range 6) (fun F _ => by
      simp only [Finset.coe_range, Set.mem_Iio]; have := dim_le (d := 5) F; omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hfiber, h5]
  ring

end cs

end Kalai5
