import Kalai5.FullProd.Facet
import Kalai5.FullProd.Repr
import Kalai5.Faces.Symmetry

/-!
# A `Δ2 × Δ2` facet forces many edges

**Theorem** (`IsCSPolytope5.edges_ge_72`): if a centrally symmetric 5-polytope `P` with 18
vertices has a facet `F` with the row `qRow` of `Δ2 × Δ2`, then `P` has at least 72 edges.

The vertices of `P` are the 9 vertices `x a b` of `F` and their negatives.  Besides the 18 edges
of `F` and the 18 edges of `-F` there are 36 *side edges* `[x i j, -x i' j']` (`i ≠ i'`,
`j ≠ j'`).  To expose a side edge write the facet functional as `c_F = Σ γ i • h i + Σ δ j • g j`
with `γ, δ > 0` (`exists_pos_repr`, where `h i`, `g j` are the differences with the functionals
of the 3-faces `R i`, `C j`), and take `L = Σ (u k * γ k) • h k + Σ (v l * δ l) • g l` with
potentials `u, v ∈ {1, -1, 0}`: its value at `x a b` is a convex combination of `u a` and `v b`
with positive weights, so `x i j` is the unique maximum and `x i' j'` the unique minimum on `F`.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-! ### Potentials and convex combinations -/

/-- The potential `1` at `i`, `-1` at `i'` and `0` elsewhere. -/
def pot (i i' k : Fin 3) : ℝ := if k = i then 1 else if k = i' then -1 else 0

lemma pot_le_one (i i' k : Fin 3) : pot i i' k ≤ 1 := by
  unfold pot; split_ifs <;> norm_num

lemma neg_pot_le_one (i i' k : Fin 3) : -pot i i' k ≤ 1 := by
  unfold pot; split_ifs <;> norm_num

lemma eq_of_pot_eq_one {i i' k : Fin 3} (h : pot i i' k = 1) : k = i := by
  unfold pot at h; split_ifs at h with h1 h2 <;> first | exact h1 | norm_num at h

lemma eq_of_neg_pot_eq_one {i i' k : Fin 3} (h : -pot i i' k = 1) : k = i' := by
  unfold pot at h; split_ifs at h with h1 h2 <;> first | exact h2 | norm_num at h

lemma pot_self (i i' : Fin 3) : pot i i' i = 1 := by simp [pot]

lemma pot_self' {i i' : Fin 3} (h : i ≠ i') : pot i i' i' = -1 := by simp [pot, Ne.symm h]

/-- A convex combination with positive weights of numbers `≤ 1` is `≤ 1`, with equality only if
both numbers are `1`. -/
lemma conv_le_one {p q w₁ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) (hp : p ≤ 1)
    (hq : q ≤ 1) : p * w₁ + q * w₂ ≤ 1 ∧ (p * w₁ + q * w₂ = 1 → p = 1 ∧ q = 1) := by
  have h1 : 0 ≤ (1 - p) * w₁ := mul_nonneg (by linarith) hw₁.le
  have h2 : 0 ≤ (1 - q) * w₂ := mul_nonneg (by linarith) hw₂.le
  have hsum : (1 - p) * w₁ + (1 - q) * w₂ = 1 - (p * w₁ + q * w₂) := by
    linear_combination hw
  refine ⟨by linarith, fun he => ?_⟩
  have h0 : (1 - p) * w₁ + (1 - q) * w₂ = 0 := by linarith
  have hp0 : (1 - p) * w₁ = 0 := by linarith
  have hq0 : (1 - q) * w₂ = 0 := by linarith
  have := (mul_eq_zero.1 hp0).resolve_right hw₁.ne'
  have := (mul_eq_zero.1 hq0).resolve_right hw₂.ne'
  constructor <;> linarith

/-! ### Segments cut out by a functional -/

section seg

variable {d : ℕ}

/-- If `⟪·, L⟫ ≤ 1` on a finite set `X` with equality only at `p ≠ q`, then the segment `[p, q]`
is an edge of `conv X`. -/
lemma segment_mem_faces_of_functional {P : Set (E d)} {X : Finset (E d)}
    (hPX : P = convexHull ℝ (X : Set (E d))) (L : E d) {p q : E d} (hp : p ∈ X) (hq : q ∈ X)
    (hpq : p ≠ q) (hle : ∀ v ∈ X, ⟪v, L⟫ ≤ 1) (hp1 : ⟪p, L⟫ = 1) (hq1 : ⟪q, L⟫ = 1)
    (heq : ∀ v ∈ X, ⟪v, L⟫ = 1 → v = p ∨ v = q) :
    segment ℝ p q ∈ faces P ∧ dim (segment ℝ p q) = 1 ∧ ∀ z ∈ segment ℝ p q, ⟪z, L⟫ = 1 := by
  classical
  have hseg1 : ∀ z ∈ segment ℝ p q, ⟪z, L⟫ = 1 := by
    rintro z ⟨a, b, -, -, hab, rfl⟩
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hp1, hq1]
    linarith
  have hsegP : segment ℝ p q ⊆ P := by
    rw [hPX]
    exact (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ hp)
      (subset_convexHull ℝ _ hq)
  set l : StrongDual ℝ (E d) := innerSL ℝ L with hl
  have hlv : ∀ z, l z = ⟪z, L⟫ := fun z => by rw [hl, innerSL_apply_apply, real_inner_comm]
  have hP1 : ∀ z ∈ P, ⟪z, L⟫ ≤ 1 ∧ (⟪z, L⟫ = 1 → z ∈ segment ℝ p q) := by
    intro z hz
    rw [hPX] at hz
    have h := le_on_convexHull l (c := 1) (fun v hv => by rw [hlv]; exact hle v hv) hz
    rw [hlv] at h
    refine ⟨h.1, fun he => ?_⟩
    have hz' := h.2 he
    rw [← convexHull_pair]
    refine convexHull_mono ?_ hz'
    intro v hv
    rw [Finset.coe_filter] at hv
    obtain ⟨hvX, hv1⟩ := hv
    rw [hlv] at hv1
    rcases heq v hvX hv1 with rfl | rfl
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  refine ⟨⟨⟨p, left_mem_segment ℝ p q⟩, fun _ => ⟨l, ?_⟩⟩, ?_, hseg1⟩
  · ext z
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hz
      refine ⟨hsegP hz, fun y hy => ?_⟩
      rw [hlv, hlv, hseg1 z hz]
      exact (hP1 y hy).1
    · rintro ⟨hzP, hmax⟩
      have h1 := hmax p (hsegP (left_mem_segment ℝ p q))
      rw [hlv, hlv, hp1] at h1
      exact (hP1 z hzP).2 (le_antisymm (hP1 z hzP).1 h1)
  · unfold dim
    rw [← convexHull_pair, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan,
      vectorSpan_pair, finrank_span_singleton]
    rw [vsub_eq_sub]
    exact sub_ne_zero.2 hpq

end seg

/-- The 36 index quadruples `(i, j, i', j')` with `i ≠ i'` and `j ≠ j'`. -/
lemma card_sideIdx : (Finset.univ.filter fun q : Fin 3 × Fin 3 × Fin 3 × Fin 3 =>
    q.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2).card = 36 := by
  decide

/-! ### The centrally symmetric polytope -/

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.exists_dual {G : Set E5} (hG : G ∈ faces P) (hne : G ≠ P) :
    ∃ c : E5, (∀ x ∈ P, ⟪x, c⟫ ≤ 1) ∧ ∀ x ∈ P, (x ∈ G ↔ ⟪x, c⟫ = 1) := by
  obtain ⟨V, hV⟩ := hP.polytope
  have h0 : (0 : E5) ∈ interior (convexHull ℝ (V : Set E5)) := hV ▸ hP.zero_mem_interior
  rw [hV] at hG hne ⊢
  exact exists_dual_vector h0 hG hne

lemma IsCSPolytope5.ne_of_dim_ne {G : Set E5} (hG : dim G ≠ 5) : G ≠ P := by
  rintro rfl
  exact hG hP.dim_self

lemma IsCSPolytope5.neg_mem_extremePoints {z : E5} (hz : z ∈ P.extremePoints ℝ) :
    -z ∈ P.extremePoints ℝ := by
  obtain ⟨V, hV⟩ := hP.polytope
  have hz' := hz
  rw [hV] at hz'
  have h1 := singleton_mem_faces_of_extreme hz'
  rw [← hV] at h1
  have h2 := neg_mem_faces hP.symm h1
  rw [Set.neg_singleton] at h2
  exact mem_extremePoints_of_singleton_face h2

/-- **A `Δ2 × Δ2` facet in an 18-vertex cs 5-polytope forces 72 edges.** -/
theorem IsCSPolytope5.edges_ge_72 (hv : fvec P 0 = 18) {F : Set E5} (hF : F ∈ faces P)
    (h4 : dim F = 4) (hrow : faceRow P F = qRow) : 72 ≤ fvec P 1 := by
  classical
  obtain ⟨x, R, C, hinj, hx, -, hR, hC, hxR, hxC⟩ := hP.prodTri_facet hF h4 hrow
  have hFP : F ≠ P := hP.ne_of_dim_ne (by rw [h4]; norm_num)
  have hdisj : ∀ z ∈ F, -z ∉ F := fun z hz hnz => hFP (hP.eq_of_mem_of_neg_mem hF hz hnz)
  have hxP : ∀ a b, x a b ∈ P := fun a b => (hx a b).1.1
  -- the 18 vertices
  let vtx : Bool × Fin 3 × Fin 3 → E5 := fun s => cond s.1 (x s.2.1 s.2.2) (-x s.2.1 s.2.2)
  have hvtx_inj : Function.Injective vtx := by
    rintro ⟨s, a, b⟩ ⟨s', a', b'⟩ he
    cases s <;> cases s' <;> simp only [vtx, cond_true, cond_false] at he
    · obtain ⟨rfl, rfl⟩ := hinj a b a' b' (neg_injective he); rfl
    · exact absurd (by rw [he]; exact (hx a' b').2 : -x a b ∈ F) (hdisj _ (hx a b).2)
    · exact absurd (by rw [← he]; exact (hx a b).2 : -x a' b' ∈ F) (hdisj _ (hx a' b').2)
    · obtain ⟨rfl, rfl⟩ := hinj a b a' b' he; rfl
  set X : Finset E5 := Finset.univ.image vtx with hX
  have hXext : (X : Set E5) ⊆ P.extremePoints ℝ := by
    intro v hv
    obtain ⟨⟨s, a, b⟩, -, rfl⟩ := Finset.mem_image.1 hv
    cases s
    · exact hP.neg_mem_extremePoints (hx a b).1
    · exact (hx a b).1
  have hXcard : X.card = 18 := by
    rw [hX, Finset.card_image_of_injective _ hvtx_inj]
    rfl
  obtain ⟨V, hV⟩ := hP.polytope
  have hextfin : (P.extremePoints ℝ).Finite := by rw [hV]; exact extremePoints_finite V
  have hextcard : (P.extremePoints ℝ).ncard = 18 := by rw [← hv, hV, fvec_zero_eq]
  have hextX : (X : Set E5) = P.extremePoints ℝ :=
    Set.eq_of_subset_of_ncard_le hXext (by rw [hextcard, Set.ncard_coe_finset, hXcard]) hextfin
  have hPX : P = convexHull ℝ (X : Set E5) := by
    rw [hextX, hV]
    exact (convexHull_extremePoints_eq V).symm
  have hxX : ∀ a b, x a b ∈ X := fun a b => Finset.mem_image.2 ⟨(true, a, b), Finset.mem_univ _, rfl⟩
  have hnxX : ∀ a b, -x a b ∈ X :=
    fun a b => Finset.mem_image.2 ⟨(false, a, b), Finset.mem_univ _, rfl⟩
  -- the functionals
  obtain ⟨cF, -, hcF⟩ := hP.exists_dual hF hFP
  choose cR hcRle hcR using fun i =>
    hP.exists_dual (hR i).1 (hP.ne_of_dim_ne (by rw [(hR i).2.2]; norm_num))
  choose cC hcCle hcC using fun j =>
    hP.exists_dual (hC j).1 (hP.ne_of_dim_ne (by rw [(hC j).2.2]; norm_num))
  set h : Fin 3 → E5 := fun i => cF - cR i with hh
  set g : Fin 3 → E5 := fun j => cF - cC j with hg
  have hcFx : ∀ a b, ⟪x a b, cF⟫ = 1 := fun a b => (hcF _ (hxP a b)).1 (hx a b).2
  have hh0 : ∀ a b i, i ≠ a → ⟪x a b, h i⟫ = 0 := by
    intro a b i hi
    rw [hh, inner_sub_right, hcFx, (hcR i _ (hxP a b)).1 ((hxR a b i).2 (Ne.symm hi)), sub_self]
  have hhpos : ∀ a b, 0 < ⟪x a b, h a⟫ := by
    intro a b
    have h1 := hcRle a _ (hxP a b)
    have h2 : ⟪x a b, cR a⟫ ≠ 1 := fun he => (hxR a b a).1 ((hcR a _ (hxP a b)).2 he) rfl
    rw [hh, inner_sub_right, hcFx]
    have := lt_of_le_of_ne h1 h2
    linarith
  have hg0 : ∀ a b j, j ≠ b → ⟪x a b, g j⟫ = 0 := by
    intro a b j hj
    rw [hg, inner_sub_right, hcFx, (hcC j _ (hxP a b)).1 ((hxC a b j).2 (Ne.symm hj)), sub_self]
  have hgpos : ∀ a b, 0 < ⟪x a b, g b⟫ := by
    intro a b
    have h1 := hcCle b _ (hxP a b)
    have h2 : ⟪x a b, cC b⟫ ≠ 1 := fun he => (hxC a b b).1 ((hcC b _ (hxP a b)).2 he) rfl
    rw [hg, inner_sub_right, hcFx]
    have := lt_of_le_of_ne h1 h2
    linarith
  obtain ⟨γ, δ, hγ, hδ, hrep⟩ := exists_pos_repr h g x cF hh0 hhpos hg0 hgpos hcFx
  have hw : ∀ a b, γ a * ⟪x a b, h a⟫ + δ b * ⟪x a b, g b⟫ = 1 := by
    intro a b
    rw [← inner_eval h g x hh0 hg0 γ δ a b, ← hrep, hcFx]
  have hw₁ : ∀ a b, 0 < γ a * ⟪x a b, h a⟫ := fun a b => mul_pos (hγ a) (hhpos a b)
  have hw₂ : ∀ a b, 0 < δ b * ⟪x a b, g b⟫ := fun a b => mul_pos (hδ b) (hgpos a b)
  -- the side-edge functionals
  let Lv : Fin 3 × Fin 3 × Fin 3 × Fin 3 → E5 := fun q =>
    ∑ k, (pot q.1 q.2.2.1 k * γ k) • h k + ∑ l, (pot q.2.1 q.2.2.2 l * δ l) • g l
  have hval : ∀ q a b, ⟪x a b, Lv q⟫ =
      pot q.1 q.2.2.1 a * (γ a * ⟪x a b, h a⟫) + pot q.2.1 q.2.2.2 b * (δ b * ⟪x a b, g b⟫) := by
    intro q a b
    rw [inner_eval h g x hh0 hg0 _ _ a b]
    ring
  set T : Finset (Fin 3 × Fin 3 × Fin 3 × Fin 3) :=
    Finset.univ.filter fun q => q.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2 with hT
  have hmax : ∀ q a b, ⟪x a b, Lv q⟫ ≤ 1 ∧ (⟪x a b, Lv q⟫ = 1 → a = q.1 ∧ b = q.2.1) := by
    intro q a b
    rw [hval]
    obtain ⟨h1, h2⟩ := conv_le_one (hw₁ a b) (hw₂ a b) (hw a b) (pot_le_one _ _ a)
      (pot_le_one _ _ b)
    exact ⟨h1, fun he => ⟨eq_of_pot_eq_one (h2 he).1, eq_of_pot_eq_one (h2 he).2⟩⟩
  have hmin : ∀ q a b, ⟪-x a b, Lv q⟫ ≤ 1 ∧
      (⟪-x a b, Lv q⟫ = 1 → a = q.2.2.1 ∧ b = q.2.2.2) := by
    intro q a b
    rw [inner_neg_left, hval]
    obtain ⟨h1, h2⟩ := conv_le_one (hw₁ a b) (hw₂ a b) (hw a b) (neg_pot_le_one _ _ a)
      (neg_pot_le_one _ _ b)
    refine ⟨by linarith, fun he => ?_⟩
    have h3 := h2 (by linarith)
    exact ⟨eq_of_neg_pot_eq_one h3.1, eq_of_neg_pot_eq_one h3.2⟩
  have hside : ∀ q ∈ T, segment ℝ (x q.1 q.2.1) (-x q.2.2.1 q.2.2.2) ∈ faces P ∧
      dim (segment ℝ (x q.1 q.2.1) (-x q.2.2.1 q.2.2.2)) = 1 ∧
      ∀ z ∈ segment ℝ (x q.1 q.2.1) (-x q.2.2.1 q.2.2.2), ⟪z, Lv q⟫ = 1 := by
    rintro ⟨i, j, i', j'⟩ hq
    rw [hT, Finset.mem_filter] at hq
    obtain ⟨-, hii, hjj⟩ := hq
    have hne : x i j ≠ -x i' j' := fun he =>
      hdisj _ (hx i' j').2 (by rw [← he]; exact (hx i j).2)
    refine segment_mem_faces_of_functional hPX (Lv (i, j, i', j')) (hxX i j) (hnxX i' j') hne
      ?_ ?_ ?_ ?_
    · intro v hv
      obtain ⟨⟨s, a, b⟩, -, rfl⟩ := Finset.mem_image.1 hv
      cases s
      · exact (hmin _ a b).1
      · exact (hmax _ a b).1
    · rw [hval]
      simp only [pot_self]
      linarith [hw i j]
    · rw [inner_neg_left, hval]
      simp only [pot_self' hii, pot_self' hjj]
      linarith [hw i' j']
    · intro v hv hv1
      obtain ⟨⟨s, a, b⟩, -, rfl⟩ := Finset.mem_image.1 hv
      cases s
      · obtain ⟨rfl, rfl⟩ := (hmin _ a b).2 hv1
        exact Or.inr rfl
      · obtain ⟨rfl, rfl⟩ := (hmax _ a b).2 hv1
        exact Or.inl rfl
  -- counting
  set seg : Fin 3 × Fin 3 × Fin 3 × Fin 3 → Set E5 :=
    fun q => segment ℝ (x q.1 q.2.1) (-x q.2.2.1 q.2.2.2) with hseg
  set E1 := {G : Set E5 | G ∈ faces P ∧ dim G = 1} with hE1
  set EF := {G : Set E5 | G ∈ faces P ∧ G ⊆ F ∧ dim G = 1} with hEF
  set EnF := {G : Set E5 | G ∈ faces P ∧ G ⊆ -F ∧ dim G = 1} with hEnF
  set ES := seg '' (T : Set (Fin 3 × Fin 3 × Fin 3 × Fin 3)) with hES
  have hfin : ∀ S : Set (Set E5), (∀ G ∈ S, G ∈ faces P) → S.Finite :=
    fun S hS => hP.faces_finite.subset hS
  have hEFc : EF.ncard = 18 := congrArg Row.e hrow
  have hEnFc : EnF.ncard = 18 := by
    have h1 : EnF.ncard = cnt P (-F) 1 := rfl
    rw [h1, hP.cnt_neg]
    exact hEFc
  have hinjOn : Set.InjOn seg (T : Set (Fin 3 × Fin 3 × Fin 3 × Fin 3)) := by
    rintro ⟨i, j, i', j'⟩ hq ⟨k, l, k', l'⟩ hq' he
    have h1 : x i j ∈ seg (k, l, k', l') := by rw [← he]; exact left_mem_segment ℝ _ _
    have h2 : -x i' j' ∈ seg (k, l, k', l') := by rw [← he]; exact right_mem_segment ℝ _ _
    have e1 := (hmax (k, l, k', l') i j).2 ((hside _ hq').2.2 _ h1)
    have e2 := (hmin (k, l, k', l') i' j').2 ((hside _ hq').2.2 _ h2)
    obtain ⟨rfl, rfl⟩ := e1
    obtain ⟨rfl, rfl⟩ := e2
    rfl
  have hESc : ES.ncard = 36 := by
    rw [hES, hinjOn.ncard_image, Set.ncard_coe_finset, hT]
    exact card_sideIdx
  have hd1 : Disjoint EF EnF := by
    rw [Set.disjoint_left]
    rintro G ⟨hG, hGF, -⟩ ⟨-, hGnF, -⟩
    obtain ⟨z, hz⟩ := hG.1
    exact hdisj z (hGF hz) (Set.mem_neg.1 (hGnF hz))
  have hd2 : Disjoint (EF ∪ EnF) ES := by
    rw [Set.disjoint_left]
    rintro G hG ⟨⟨i, j, i', j'⟩, -, rfl⟩
    rcases hG with ⟨-, hGF, -⟩ | ⟨-, hGnF, -⟩
    · exact hdisj _ (hx i' j').2 (by simpa using hGF (right_mem_segment ℝ _ _))
    · exact hdisj _ (hx i j).2 (Set.mem_neg.1 (hGnF (left_mem_segment ℝ _ _)))
  have hsub : EF ∪ EnF ∪ ES ⊆ E1 := by
    rintro G ((⟨hG, -, hd⟩ | ⟨hG, -, hd⟩) | ⟨q, hq, rfl⟩)
    · exact ⟨hG, hd⟩
    · exact ⟨hG, hd⟩
    · exact ⟨(hside q hq).1, (hside q hq).2.1⟩
  have hEFfin : EF.Finite := hfin _ fun G hG => hG.1
  have hEnFfin : EnF.Finite := hfin _ fun G hG => hG.1
  have hESfin : ES.Finite := (Finset.finite_toSet T).image _
  have hE1fin : E1.Finite := hfin _ fun G hG => hG.1
  have hcount : (EF ∪ EnF ∪ ES).ncard = 72 := by
    rw [Set.ncard_union_eq hd2 (hEFfin.union hEnFfin) hESfin, Set.ncard_union_eq hd1 hEFfin hEnFfin,
      hEFc, hEnFc, hESc]
  have := Set.ncard_le_ncard hsub hE1fin
  rw [hcount] at this
  exact this

end cs

end Kalai5
