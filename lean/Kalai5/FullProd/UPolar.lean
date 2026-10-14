import Kalai5.FullProd.ULines
import Kalai5.FullProd.SideEdges
import Kalai5.Euler.Relations
import Kalai5.Alexandrov.Inactive
import Kalai5.Rigidity.Toric

/-!
# Tools for excluding the facet `U`: vertices of the polar, planes, witnesses

* `mem_extremePoints_polarSet_of_tight` (**L2**): a point `w` of the polar of `conv X` such that
  only `0` is orthogonal to all tight `x ∈ X` (`⟪x, w⟫ = 1`) is a vertex of the polar;
* `eq_zero_of_tight_of_extreme` (**L1**): at a vertex `y` of `polarSet (conv W)`, a vector
  orthogonal to all tight `w ∈ W` is `0`;
* `IsCSPolytope5.card_le_of_polar_vertices`: with eighteen facets the polar has at most eighteen
  vertices;
* `IsCSPolytope5.vertices_pm`: with eighteen vertices and a facet with nine vertices `x i`, the
  vertices of `P` are exactly the `±x i`;
* `finrank_inter_le_two`: a 3-face meets another face, not containing it, in at most a plane;
* `IsCSPolytope5.exists_witness`: a functional vanishing on a face `G` and positive on the rest of
  a facet `U`;
* `line_normal`: normal form of two points on a line through a point where a witness vanishes;
* `exists_dual5`, `eq_zero5`, `indep5`: linear algebra with five independent vectors of `ℝ⁵`.
-/

namespace Kalai5

open Set Module Submodule

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {d : ℕ}

/-! ### Vertices of the polar from tight vectors -/

/-- **L2.** If only `0` is orthogonal to the tight vectors, `w` is a vertex of the polar. -/
lemma mem_extremePoints_polarSet_of_tight {X : Finset (E d)} {w : E d}
    (hw : ∀ x ∈ X, ⟪x, w⟫ ≤ 1)
    (ht : ∀ v : E d, (∀ x ∈ X, ⟪x, w⟫ = 1 → ⟪x, v⟫ = 0) → v = 0) :
    w ∈ (polarSet (convexHull ℝ (X : Set (E d)))).extremePoints ℝ := by
  refine mem_extremePoints.2 ⟨mem_polarSet_convexHull.2 hw, fun w1 hw1 w2 hw2 hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  have h1 := mem_polarSet_convexHull.1 hw1
  have h2 := mem_polarSet_convexHull.1 hw2
  have key : ∀ x ∈ X, ⟪x, a • w1 + b • w2⟫ = 1 → ⟪x, w1⟫ = 1 ∧ ⟪x, w2⟫ = 1 := by
    intro x hx he
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right] at he
    have e1 := h1 x hx
    have e2 := h2 x hx
    have f1 : 0 ≤ a * (1 - ⟪x, w1⟫) := mul_nonneg ha.le (by linarith)
    have f2 : 0 ≤ b * (1 - ⟪x, w2⟫) := mul_nonneg hb.le (by linarith)
    have f3 : a * (1 - ⟪x, w1⟫) + b * (1 - ⟪x, w2⟫) = 0 := by linear_combination hab - he
    have g1 : a * (1 - ⟪x, w1⟫) = 0 := by linarith
    have g2 : b * (1 - ⟪x, w2⟫) = 0 := by linarith
    constructor
    · have := (mul_eq_zero.1 g1).resolve_left ha.ne'; linarith
    · have := (mul_eq_zero.1 g2).resolve_left hb.ne'; linarith
  have e1 : w1 - (a • w1 + b • w2) = 0 := ht _ fun x hx he => by
    rw [inner_sub_right, (key x hx he).1, he, sub_self]
  have e2 : w2 - (a • w1 + b • w2) = 0 := ht _ fun x hx he => by
    rw [inner_sub_right, (key x hx he).2, he, sub_self]
  exact ⟨sub_eq_zero.1 e1, sub_eq_zero.1 e2⟩

/-- **L1.** At a vertex of `polarSet (conv W)`, the tight `w ∈ W` leave no nonzero orthogonal
vector. -/
lemma eq_zero_of_tight_of_extreme {W : Finset (E d)} {y : E d}
    (hy : y ∈ (polarSet (convexHull ℝ (W : Set (E d)))).extremePoints ℝ) {v : E d}
    (hv : ∀ w ∈ W, ⟪w, y⟫ = 1 → ⟪w, v⟫ = 0) : v = 0 := by
  classical
  by_contra hv0
  have hyQ : ∀ w ∈ W, ⟪w, y⟫ ≤ 1 := mem_polarSet_convexHull.1 hy.1
  obtain ⟨ε, hε, hεle⟩ := exists_eps_pert (W.filter fun w => ⟪w, y⟫ ≠ 1)
    (fun w => ⟪w, y⟫) (fun w => ⟪w, v⟫) (fun w hw => by
      rw [Finset.mem_filter] at hw; exact lt_of_le_of_ne (hyQ w hw.1) hw.2)
  have hmem : ∀ s : ℝ, |s| ≤ ε → y + s • v ∈ polarSet (convexHull ℝ (W : Set (E d))) := by
    intro s hs
    refine mem_polarSet_convexHull.2 fun w hw => ?_
    rw [inner_add_right, real_inner_smul_right]
    by_cases h1 : ⟪w, y⟫ = 1
    · rw [hv w hw h1, h1]; simp
    · have := hεle w (Finset.mem_filter.2 ⟨hw, h1⟩)
      have hb : s * ⟪w, v⟫ ≤ ε * |⟪w, v⟫| := by
        calc s * ⟪w, v⟫ ≤ |s * ⟪w, v⟫| := le_abs_self _
          _ = |s| * |⟪w, v⟫| := abs_mul _ _
          _ ≤ ε * |⟪w, v⟫| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
      linarith
  have hplus := hmem ε (by rw [abs_of_pos hε])
  have hminus := hmem (-ε) (by rw [abs_neg, abs_of_pos hε])
  have hseg : y ∈ openSegment ℝ (y + (-ε) • v) (y + ε • v) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
  have := ((mem_extremePoints.1 hy).2 _ hminus _ hplus hseg).1
  have hεv : ε • v = 0 := by
    have h' : y + (-ε) • v - y = 0 := by rw [this, sub_self]
    simpa [neg_smul] using h'
  exact hv0 ((smul_eq_zero.1 hεv).resolve_left hε.ne')

/-! ### Spans of faces -/

lemma vectorSpan_le_of_sub {s : Set (E d)} {p : E d} {S : Submodule ℝ (E d)}
    (h : ∀ v ∈ s, v - p ∈ S) : vectorSpan ℝ s ≤ S := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  have := S.sub_mem (h a ha) (h b hb)
  rw [sub_sub_sub_cancel_right] at this
  exact this

/-- The span of a face of `conv X` is spanned by the differences of the points of `X` in it. -/
lemma vectorSpan_face_le {X : Finset (E d)} {G : Set (E d)}
    (hG : G ∈ faces (convexHull ℝ (X : Set (E d)))) {p : E d} {S : Submodule ℝ (E d)}
    (hS : ∀ v ∈ X, v ∈ G → v - p ∈ S) : vectorSpan ℝ G ≤ S := by
  classical
  rw [face_eq_convexHull_filter hG, ← direction_affineSpan, affineSpan_convexHull,
    direction_affineSpan]
  refine vectorSpan_le_of_sub (p := p) fun v hv => ?_
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hv
  exact hS v hv.1 hv.2

/-- A 3-face `G1` meets a face `G2` not containing it in a face of dimension at most two. -/
lemma finrank_inter_le_two {P G1 G2 : Set (E d)} (h1 : G1 ∈ faces P) (h1d : dim G1 = 3)
    (h2 : G2 ∈ faces P) {a b : E d} (ha : a ∈ G1) (ha2 : a ∈ G2) (hb : b ∈ G1) (hb2 : b ∉ G2) :
    finrank ℝ (vectorSpan ℝ (G1 ∩ G2)) ≤ 2 := by
  have hface : G1 ∩ G2 ∈ faces P := ⟨⟨a, ha, ha2⟩, h1.2.inter h2.2⟩
  have hF : G1 ∩ G2 ∈ faces G1 :=
    mem_faces_of_subset (face_subset h1) hface Set.inter_subset_left
  have hne : G1 ∩ G2 ≠ G1 := by
    intro he
    have : b ∈ G1 ∩ G2 := by rw [he]; exact hb
    exact hb2 this.2
  have := dim_lt_of_mem_faces_ne hF hne
  unfold dim at this h1d
  omega

/-! ### Normal form on a line -/

/-- **Normal form on a line**: if `p = a + s • (b - a)` and a functional vanishes at `p` and is
positive at `a` and `b`, then `b - p` is a positive multiple `τ ≠ 1` of `a - p`. -/
lemma line_normal {p a b ψ : E d} {s : ℝ} (hp : p = a + s • (b - a)) (ha : 0 < ⟪a, ψ⟫)
    (hb : 0 < ⟪b, ψ⟫) (hp0 : ⟪p, ψ⟫ = 0) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≠ 1 ∧ b = p + τ • (a - p) := by
  have hlin : ⟪a, ψ⟫ + s * (⟪b, ψ⟫ - ⟪a, ψ⟫) = 0 := by
    rw [hp, inner_add_left, real_inner_smul_left, inner_sub_left] at hp0; exact hp0
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [zero_mul, add_zero] at hlin; linarith
  have key : s * (s - 1) * ⟪a, ψ⟫ = s ^ 2 * ⟪b, ψ⟫ := by linear_combination (-s) * hlin
  have hs2 : 0 < s ^ 2 := by positivity
  have hprod : 0 < s * (s - 1) := by
    have : 0 < s * (s - 1) * ⟪a, ψ⟫ := by rw [key]; positivity
    exact (mul_pos_iff_of_pos_right ha).1 this
  refine ⟨(s - 1) / s, ?_, ?_, ?_⟩
  · rcases lt_or_gt_of_ne hs0 with hneg | hpos
    · exact div_pos_of_neg_of_neg (by linarith) hneg
    · have : 0 < s - 1 := by
        by_contra hc; push_neg at hc; nlinarith
      exact div_pos this hpos
  · intro h
    rw [div_eq_one_iff_eq hs0] at h
    linarith
  · have e1 : a - p = (-s) • (b - a) := by rw [hp]; module
    have e2 : (s - 1) / s * (-s) = 1 - s := by field_simp; ring
    rw [e1, smul_smul, e2, hp]
    module

/-- A functional vanishing at two points vanishes on their line. -/
lemma inner_line_eq_zero {p a b ψ : E d} {s : ℝ} (hp : p = a + s • (b - a)) (ha : ⟪a, ψ⟫ = 0)
    (hb : ⟪b, ψ⟫ = 0) : ⟪p, ψ⟫ = 0 := by
  rw [hp, inner_add_left, real_inner_smul_left, inner_sub_left, ha, hb]; ring

/-! ### Five independent vectors of `ℝ⁵` -/

lemma indep5 {b0 b1 b2 b3 b4 : E5}
    (h : ∀ S : Submodule ℝ E5, b0 ∈ S → b1 ∈ S → b2 ∈ S → b3 ∈ S → b4 ∈ S → S = ⊤) :
    LinearIndependent ℝ ![b0, b1, b2, b3, b4] := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [h (span ℝ (Set.range ![b0, b1, b2, b3, b4])) (subset_span ⟨0, rfl⟩) (subset_span ⟨1, rfl⟩)
      (subset_span ⟨2, rfl⟩) (subset_span ⟨3, rfl⟩) (subset_span ⟨4, rfl⟩)]
  · simp

/-- A vector with prescribed inner products against five independent vectors. -/
lemma exists_dual5 {b0 b1 b2 b3 b4 : E5} (hb : LinearIndependent ℝ ![b0, b1, b2, b3, b4])
    (f0 f1 f2 f3 f4 : ℝ) :
    ∃ w : E5, ⟪b0, w⟫ = f0 ∧ ⟪b1, w⟫ = f1 ∧ ⟪b2, w⟫ = f2 ∧ ⟪b3, w⟫ = f3 ∧ ⟪b4, w⟫ = f4 := by
  set B := basisOfLinearIndependentOfCardEqFinrank hb (by simp)
  have hB : ∀ k, B k = ![b0, b1, b2, b3, b4] k := fun k => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  set φ := B.constr ℝ ![f0, f1, f2, f3, f4]
  set w := (InnerProductSpace.toDual ℝ E5).symm (LinearMap.toContinuousLinearMap φ)
  have hw : ∀ k, ⟪![b0, b1, b2, b3, b4] k, w⟫ = ![f0, f1, f2, f3, f4] k := by
    intro k
    rw [← hB, real_inner_comm, InnerProductSpace.toDual_symm_apply]
    simp [φ, Basis.constr_basis]
  exact ⟨w, hw 0, hw 1, hw 2, hw 3, hw 4⟩

/-- A vector orthogonal to five independent vectors vanishes. -/
lemma eq_zero5 {b0 b1 b2 b3 b4 : E5} (hb : LinearIndependent ℝ ![b0, b1, b2, b3, b4]) {v : E5}
    (h0 : ⟪b0, v⟫ = 0) (h1 : ⟪b1, v⟫ = 0) (h2 : ⟪b2, v⟫ = 0) (h3 : ⟪b3, v⟫ = 0)
    (h4 : ⟪b4, v⟫ = 0) : v = 0 := by
  set B := basisOfLinearIndependentOfCardEqFinrank hb (by simp)
  have hB : ∀ k, ⟪B k, v⟫ = 0 := by
    intro k
    simp only [B, coe_basisOfLinearIndependentOfCardEqFinrank]
    fin_cases k <;> simpa
  have hall : ∀ y, ⟪y, v⟫ = 0 := fun y => by
    rw [← B.sum_repr y, sum_inner]
    simp [real_inner_smul_left, hB]
  exact inner_self_eq_zero.1 (hall v)

/-- Membership in the span of four vectors through an explicit combination. -/
lemma mem_span4 {v g1 g2 g3 g4 : E5} (c1 c2 c3 c4 : ℝ)
    (h : v = c1 • g1 + c2 • g2 + c3 • g3 + c4 • g4) :
    v ∈ span ℝ ({g1, g2, g3, g4} : Set E5) := by
  rw [h]
  refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;> refine smul_mem _ _ (subset_span ?_) <;>
    simp

/-! ### The centrally symmetric polytope -/

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- At most eighteen facets bound every set of polar vertices by eighteen. -/
lemma IsCSPolytope5.card_le_of_polar_vertices_of_le (hh : fvec P 4 ≤ 18) (S : Finset E5)
    (hS : ∀ w ∈ S, w ∈ (polarSet P).extremePoints ℝ) : S.card ≤ 18 := by
  obtain ⟨V, hV⟩ := hP.polar.polytope
  have h1 : fvec (polarSet P) 0 ≤ 18 := by
    have := hP.fvec_polar 4 (by norm_num)
    rw [Nat.sub_self] at this
    rw [this]
    exact hh
  rw [hV, fvec_zero_eq] at h1
  have hsub : (S : Set E5) ⊆ (convexHull ℝ (V : Set E5)).extremePoints ℝ := by
    intro w hw; rw [← hV]; exact hS w hw
  have := Set.ncard_le_ncard hsub (extremePoints_finite V)
  rw [Set.ncard_coe_finset] at this
  exact this.trans h1

/-- The original equality interface is retained for existing clients. -/
lemma IsCSPolytope5.card_le_of_polar_vertices (hh : fvec P 4 = 18) (S : Finset E5)
    (hS : ∀ w ∈ S, w ∈ (polarSet P).extremePoints ℝ) : S.card ≤ 18 :=
  hP.card_le_of_polar_vertices_of_le hh.le S hS

/-- The vertices of the polar as a finite set, and the bipolar. -/
lemma IsCSPolytope5.exists_polar_finset :
    ∃ W : Finset E5, (W : Set E5) = (polarSet P).extremePoints ℝ ∧
      P = polarSet (convexHull ℝ (W : Set E5)) := by
  obtain ⟨V, hV⟩ := hP.polytope
  have h0 : (0 : E5) ∈ interior (convexHull ℝ (V : Set E5)) := hV ▸ hP.zero_mem_interior
  have hfin := extremePoints_polarSet_finite V
  refine ⟨hfin.toFinset, by rw [Set.Finite.coe_toFinset, hV], ?_⟩
  rw [Set.Finite.coe_toFinset, polarSet_eq_convexHull_extremePoints h0, ← hV,
    hP.polarSet_polarSet]

/-- **The vertices of `P` are the `±x i`** when `P` has eighteen vertices and a facet `U` with the
nine vertices `x i`. -/
lemma IsCSPolytope5.vertices_pm (hv : fvec P 0 = 18) {U : Set E5} (hU : U ∈ faces P)
    (h4 : dim U = 4) {x : Fin 9 → E5} (hinj : Function.Injective x)
    (hx : ∀ i, x i ∈ U.extremePoints ℝ) :
    ∃ X : Finset E5, P = convexHull ℝ (X : Set E5) ∧ (X : Set E5) = P.extremePoints ℝ ∧
      (∀ v ∈ X, ∃ i, v = x i ∨ v = -x i) ∧ (∀ i, x i ∈ X ∧ -x i ∈ X) := by
  classical
  have hUP : U ≠ P := hP.ne_of_dim_ne (by rw [h4]; norm_num)
  have hdisj : ∀ z ∈ U, -z ∉ U := fun z hz hnz => hUP (hP.eq_of_mem_of_neg_mem hU hz hnz)
  have hxU : ∀ i, x i ∈ U := fun i => (hx i).1
  have hxP : ∀ i, x i ∈ P.extremePoints ℝ := fun i => by
    have := hx i
    rw [hU.2.isExtreme.extremePoints_eq] at this
    exact this.2
  let vtx : Bool × Fin 9 → E5 := fun s => cond s.1 (x s.2) (-x s.2)
  have hvtx_inj : Function.Injective vtx := by
    rintro ⟨s, i⟩ ⟨s', i'⟩ he
    cases s <;> cases s' <;> simp only [vtx, cond_true, cond_false] at he
    · rw [hinj (neg_injective he)]
    · exact absurd (by rw [he]; exact hxU i' : -x i ∈ U) (hdisj _ (hxU i))
    · exact absurd (by rw [← he]; exact hxU i : -x i' ∈ U) (hdisj _ (hxU i'))
    · rw [hinj he]
  set X : Finset E5 := Finset.univ.image vtx with hX
  have hXext : (X : Set E5) ⊆ P.extremePoints ℝ := by
    intro v hv
    obtain ⟨⟨s, i⟩, -, rfl⟩ := Finset.mem_image.1 hv
    cases s
    · exact hP.neg_mem_extremePoints (hxP i)
    · exact hxP i
  have hXcard : X.card = 18 := by
    rw [hX, Finset.card_image_of_injective _ hvtx_inj]; rfl
  obtain ⟨V, hV⟩ := hP.polytope
  have hextfin : (P.extremePoints ℝ).Finite := by rw [hV]; exact extremePoints_finite V
  have hextcard : (P.extremePoints ℝ).ncard = 18 := by rw [← hv, hV, fvec_zero_eq]
  have hextX : (X : Set E5) = P.extremePoints ℝ :=
    Set.eq_of_subset_of_ncard_le hXext (by rw [hextcard, Set.ncard_coe_finset, hXcard]) hextfin
  have hPX : P = convexHull ℝ (X : Set E5) := by
    rw [hextX, hV]; exact (convexHull_extremePoints_eq V).symm
  refine ⟨X, hPX, hextX, fun v hv => ?_, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨⟨s, i⟩, -, rfl⟩ := Finset.mem_image.1 hv
    cases s
    · exact ⟨i, Or.inr rfl⟩
    · exact ⟨i, Or.inl rfl⟩
  · exact Finset.mem_image.2 ⟨(true, i), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.2 ⟨(false, i), Finset.mem_univ _, rfl⟩

/-- **Witness**: a functional vanishing on a face `G` and positive on the rest of a facet `U`. -/
lemma IsCSPolytope5.exists_witness {U G : Set E5} (hU : U ∈ faces P) (hUP : U ≠ P)
    (hG : G ∈ faces P) (hGP : G ≠ P) :
    ∃ ψ : E5, ∀ x ∈ U, (x ∈ G → ⟪x, ψ⟫ = 0) ∧ (x ∉ G → 0 < ⟪x, ψ⟫) := by
  obtain ⟨cU, -, hcU⟩ := hP.exists_dual hU hUP
  obtain ⟨cG, hcGle, hcG⟩ := hP.exists_dual hG hGP
  refine ⟨cU - cG, fun x hx => ⟨fun hxG => ?_, fun hxG => ?_⟩⟩
  · have hxP := face_subset hU hx
    rw [inner_sub_right, (hcU x hxP).1 hx, (hcG x hxP).1 hxG, sub_self]
  · have hxP := face_subset hU hx
    have h1 := hcGle x hxP
    have h2 : ⟪x, cG⟫ ≠ 1 := fun he => hxG ((hcG x hxP).2 he)
    rw [inner_sub_right, (hcU x hxP).1 hx]
    have := lt_of_le_of_ne h1 h2
    linarith

end cs

end Kalai5
