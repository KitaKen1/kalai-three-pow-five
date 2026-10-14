import Kalai5.LemmaB.Faces
import Kalai5.Euler.Relations
import Kalai5.Faces.LowDim

/-!
# Lemma B: planar facts

For a finite set `A ⊂ ℝ²` and a direction `b`, `amax A b` is the set of points of `A` maximizing
`⟪b, ·⟫`; `amaxSets A` is the (finite) set of all of them.

* `ncard_faces_le_amaxSets`: faces `F` of `conv A` inject into argmax sets (`F ↦ A ∩ F`).
* `ncard_faces_polygon`: a 2-dimensional polygon has `s = 2 f₁ + 1` faces (Euler: `f₀ = f₁`).
* Edge normals (`IsEdgeNormal A n`: `‖n‖ = 1` and at least two points maximize `⟪n, ·⟫`): distinct
  ones give distinct edges, so `card_amaxSets_ge`: `#argmax sets ≥ 2 #N + 1` for any set `N` of
  at least three edge normals.
* Minkowski sums: `amax (A + B) b = amax A b + amax B b`; edge normals pass to sums.
* Convex position: a 2-dimensional set in convex position has at least `|A|` edge normals
  (`exists_edgeNormals`), and `≥ 3` points in convex position span the plane.
* Triangles: no two antiparallel edge normals, and the directions `±n` give distinct argmax sets.
-/

namespace Kalai5.LemmaB

open Set Module
open scoped Pointwise

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-! ### Argmax sets -/

/-- Points of `A` maximizing `⟪b, ·⟫`. -/
noncomputable def amax (A : Finset (E 2)) (b : E 2) : Finset (E 2) :=
  A.filter fun p => ∀ q ∈ A, ⟪b, q⟫ ≤ ⟪b, p⟫

lemma mem_amax {A : Finset (E 2)} {b p : E 2} :
    p ∈ amax A b ↔ p ∈ A ∧ ∀ q ∈ A, ⟪b, q⟫ ≤ ⟪b, p⟫ := Finset.mem_filter

lemma amax_subset (A : Finset (E 2)) (b : E 2) : amax A b ⊆ A := Finset.filter_subset _ _

lemma amax_nonempty {A : Finset (E 2)} (hA : A.Nonempty) (b : E 2) : (amax A b).Nonempty := by
  obtain ⟨p, hp, hmax⟩ := A.exists_max_image (fun q => ⟪b, q⟫) hA
  exact ⟨p, mem_amax.2 ⟨hp, hmax⟩⟩

lemma amax_zero (A : Finset (E 2)) : amax A 0 = A := by
  ext p; simp [mem_amax]

lemma inner_eq_of_mem_amax {A : Finset (E 2)} {b p q : E 2} (hp : p ∈ amax A b)
    (hq : q ∈ amax A b) : ⟪b, p⟫ = ⟪b, q⟫ :=
  le_antisymm ((mem_amax.1 hq).2 p (mem_amax.1 hp).1) ((mem_amax.1 hp).2 q (mem_amax.1 hq).1)

open Classical in
/-- The argmax sets of `A`. -/
noncomputable def amaxSets (A : Finset (E 2)) : Finset (Finset (E 2)) :=
  A.powerset.filter fun T => ∃ b, amax A b = T

lemma mem_amaxSets {A T : Finset (E 2)} : T ∈ amaxSets A ↔ ∃ b, amax A b = T := by
  classical
  simp only [amaxSets, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact fun h => h.2
  · rintro ⟨b, rfl⟩; exact ⟨amax_subset A b, b, rfl⟩

lemma amax_mem_amaxSets (A : Finset (E 2)) (b : E 2) : amax A b ∈ amaxSets A :=
  mem_amaxSets.2 ⟨b, rfl⟩

/-! ### Faces and argmax sets -/

lemma mem_argmaxFace_of_mem_amax {A : Finset (E 2)} {b p : E 2} (hp : p ∈ amax A b) :
    p ∈ argmaxFace A b := by
  classical
  obtain ⟨hpA, hmax⟩ := mem_amax.1 hp
  refine ⟨subset_convexHull ℝ _ hpA, fun y hy => ?_⟩
  have hle : ∀ u ∈ A, ip b u ≤ ⟪p, b⟫ := fun u hu => by
    rw [ip_apply]; linarith [real_inner_comm b u, real_inner_comm b p, hmax u hu]
  have := (le_on_convexHull (ip b) hle hy).1
  rwa [ip_apply] at this

lemma mem_amax_iff_mem_argmaxFace {A : Finset (E 2)} {b p : E 2} (hp : p ∈ A) :
    p ∈ amax A b ↔ p ∈ argmaxFace A b := by
  refine ⟨mem_argmaxFace_of_mem_amax, fun hpF => mem_amax.2 ⟨hp, fun q hq => ?_⟩⟩
  have := hpF.2 q (subset_convexHull ℝ _ hq)
  linarith [real_inner_comm b q, real_inner_comm b p]

lemma argmaxFace_eq_convexHull_amax {A : Finset (E 2)} (hA : A.Nonempty) (b : E 2) :
    argmaxFace A b = convexHull ℝ (amax A b : Set (E 2)) := by
  classical
  have h := face_eq_convexHull_filter (argmaxFace_mem_faces hA b)
  have hf : A.filter (· ∈ argmaxFace A b) = amax A b := by
    ext p
    rw [Finset.mem_filter]
    exact ⟨fun h => (mem_amax_iff_mem_argmaxFace h.1).2 h.2,
      fun h => ⟨amax_subset A b h, mem_argmaxFace_of_mem_amax h⟩⟩
  rw [h, hf]

/-- **Faces inject into argmax sets.** -/
theorem ncard_faces_le_amaxSets (A : Finset (E 2)) :
    (faces (convexHull ℝ (A : Set (E 2)))).ncard ≤ (amaxSets A).card := by
  classical
  rw [← Set.ncard_coe_finset (amaxSets A)]
  refine Set.ncard_le_ncard_of_injOn (fun F => A.filter (· ∈ F)) ?_ ?_ (Finset.finite_toSet _)
  · intro F hF
    obtain ⟨c, rfl⟩ := exists_argmaxFace_eq hF
    show A.filter (· ∈ argmaxFace A c) ∈ (amaxSets A : Set (Finset (E 2)))
    rw [Finset.mem_coe, mem_amaxSets]
    refine ⟨c, ?_⟩
    ext p
    rw [Finset.mem_filter]
    exact ⟨fun h => ⟨amax_subset A c h, mem_argmaxFace_of_mem_amax h⟩,
      fun h => (mem_amax_iff_mem_argmaxFace h.1).2 h.2⟩
  · intro F hF G hG h
    simp only at h
    rw [face_eq_convexHull_filter hF, face_eq_convexHull_filter hG, h]

/-! ### Polygons: Euler -/

lemma nonempty_of_dim_pos {A : Finset (E 2)} (h : 0 < dim (convexHull ℝ (A : Set (E 2)))) :
    A.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  have h0 : vectorSpan ℝ (convexHull ℝ ((∅ : Finset (E 2)) : Set (E 2))) = ⊥ := by
    rw [Finset.coe_empty, convexHull_empty, vectorSpan_empty]
  rw [dim, h0, finrank_bot] at h
  exact lt_irrefl 0 h

lemma ncard_faces_eq_sum (A : Finset (E 2)) :
    (faces (convexHull ℝ (A : Set (E 2)))).ncard =
      fvec (convexHull ℝ (A : Set (E 2))) 0 + fvec (convexHull ℝ (A : Set (E 2))) 1 +
        fvec (convexHull ℝ (A : Set (E 2))) 2 := by
  classical
  have hfin := faces_finite_convexHull A
  rw [Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_card_fiberwise (f := dim) (t := Finset.range 3) (fun F _ => by
      have := dim_le F; simp only [Finset.coe_range, Set.mem_Iio]; omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have key : ∀ k, (hfin.toFinset.filter fun F => dim F = k).card =
      fvec (convexHull ℝ (A : Set (E 2))) k := by
    intro k
    rw [fvec, Set.ncard_eq_toFinset_card _ (hfin.subset fun F hF => hF.1)]
    congr 1; ext F; simp
  rw [key 0, key 1, key 2]

lemma fvec_two_eq_one {A : Finset (E 2)} (h2 : dim (convexHull ℝ (A : Set (E 2))) = 2) :
    fvec (convexHull ℝ (A : Set (E 2))) 2 = 1 := by
  have hA := nonempty_of_dim_pos (A := A) (by omega)
  rw [fvec, Set.ncard_eq_one]
  refine ⟨convexHull ℝ (A : Set (E 2)), ?_⟩
  ext G
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hG, hd⟩
    by_contra hne
    have := dim_lt_of_mem_faces_ne hG hne
    omega
  · rintro rfl
    exact ⟨⟨(Finset.coe_nonempty.2 hA).convexHull, IsExposed.refl _⟩, h2⟩

/-- **Euler for polygons**: `f₀ = f₁`. -/
lemma fvec_zero_eq_fvec_one {A : Finset (E 2)} (h2 : dim (convexHull ℝ (A : Set (E 2))) = 2) :
    fvec (convexHull ℝ (A : Set (E 2))) 0 = fvec (convexHull ℝ (A : Set (E 2))) 1 := by
  have hA := nonempty_of_dim_pos (A := A) (by omega)
  have he := euler_fvec hA 2 (fun G _ => dim_le G)
  have hf2 := fvec_two_eq_one h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul,
    pow_one, neg_one_mul, even_two, Even.neg_pow, one_pow, hf2, Nat.cast_one] at he
  omega

/-- **A 2-dimensional polygon has `2 f₁ + 1` faces.** -/
theorem ncard_faces_polygon {A : Finset (E 2)} (h2 : dim (convexHull ℝ (A : Set (E 2))) = 2) :
    (faces (convexHull ℝ (A : Set (E 2)))).ncard =
      2 * fvec (convexHull ℝ (A : Set (E 2))) 1 + 1 := by
  rw [ncard_faces_eq_sum, fvec_zero_eq_fvec_one h2, fvec_two_eq_one h2]
  ring

/-! ### Edge normals -/

/-- `n` is a unit outer normal of an edge of `conv A`. -/
def IsEdgeNormal (A : Finset (E 2)) (n : E 2) : Prop := ‖n‖ = 1 ∧ 1 < (amax A n).card

lemma IsEdgeNormal.ne_zero {A : Finset (E 2)} {n : E 2} (h : IsEdgeNormal A n) : n ≠ 0 := by
  rintro rfl
  have := h.1
  rw [norm_zero] at this
  exact zero_ne_one this

lemma finrank_orth_eq_one {n : E 2} (hn : n ≠ 0) : finrank ℝ (ℝ ∙ n)ᗮ = 1 := by
  haveI : Fact (finrank ℝ (E 2) = 1 + 1) := ⟨by simp⟩
  exact Submodule.finrank_orthogonal_span_singleton hn

/-- If `⟪·, n⟫` is constant on `S` (`n ≠ 0`), then `dim S ≤ 1`. -/
lemma dim_le_one_of_const {S : Set (E 2)} {n : E 2} (hn : n ≠ 0) {κ : ℝ}
    (h : ∀ x ∈ S, ⟪x, n⟫ = κ) : dim S ≤ 1 := by
  have hle : vectorSpan ℝ S ≤ (ℝ ∙ n)ᗮ := by
    intro u hu
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    exact inner_vectorSpan_eq_zero_of_const h u hu
  calc dim S = finrank ℝ (vectorSpan ℝ S) := rfl
    _ ≤ finrank ℝ (ℝ ∙ n)ᗮ := Submodule.finrank_mono hle
    _ = 1 := finrank_orth_eq_one hn

lemma one_le_dim_of_ne {S : Set (E 2)} {p q : E 2} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    1 ≤ dim S := by
  by_contra h
  have h0 : dim S = 0 := by omega
  have hbot : vectorSpan ℝ S = ⊥ := Submodule.finrank_eq_zero.1 h0
  have hmem : p -ᵥ q ∈ vectorSpan ℝ S := vsub_mem_vectorSpan ℝ hp hq
  rw [hbot, Submodule.mem_bot, vsub_eq_sub, sub_eq_zero] at hmem
  exact hpq hmem

lemma dim_argmaxFace_of_edgeNormal {A : Finset (E 2)} {n : E 2} (hn : IsEdgeNormal A n) :
    dim (argmaxFace A n) = 1 := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 hn.2
  have hA : A.Nonempty := ⟨p, amax_subset A n hp⟩
  obtain ⟨x0, -, hconst⟩ := argmaxFace_value hA n
  exact le_antisymm (dim_le_one_of_const hn.ne_zero hconst)
    (one_le_dim_of_ne (mem_argmaxFace_of_mem_amax hp) (mem_argmaxFace_of_mem_amax hq) hpq)

/-- In the plane, two unit vectors orthogonal to the same nonzero vector agree up to sign. -/
lemma eq_or_eq_neg_of_inner {v n n' : E 2} (hv : v ≠ 0) (hn : ‖n‖ = 1) (hn' : ‖n'‖ = 1)
    (h : ⟪v, n⟫ = 0) (h' : ⟪v, n'⟫ = 0) : n' = n ∨ n' = -n := by
  have hn0 : n ≠ 0 := by rintro rfl; rw [norm_zero] at hn; exact zero_ne_one hn
  have hmem : n ∈ (ℝ ∙ v)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_right.2 h
  have hmem' : n' ∈ (ℝ ∙ v)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_right.2 h'
  have hne : (⟨n, hmem⟩ : (ℝ ∙ v)ᗮ) ≠ 0 := by
    intro h0; apply hn0; simpa using congrArg Subtype.val h0
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 (finrank_orth_eq_one hv) ⟨n', hmem'⟩
  have ht' : n' = t • n := by
    have := congrArg Subtype.val ht
    simpa using this.symm
  have habs : |t| = 1 := by
    have := congrArg norm ht'
    rw [norm_smul, hn, hn', Real.norm_eq_abs, mul_one] at this
    exact this.symm
  rcases (abs_eq zero_le_one).1 habs with h1 | h1
  · left; rw [ht', h1, one_smul]
  · right; rw [ht', h1, neg_one_smul]

/-- Distinct edge normals give distinct edges (in a 2-dimensional polygon). -/
lemma eq_of_argmaxFace_eq {A : Finset (E 2)} (h2 : dim (convexHull ℝ (A : Set (E 2))) = 2)
    {n n' : E 2} (hn : IsEdgeNormal A n) (hn' : IsEdgeNormal A n')
    (h : argmaxFace A n = argmaxFace A n') : n = n' := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 hn.2
  have hpF := mem_argmaxFace_of_mem_amax hp
  have hqF := mem_argmaxFace_of_mem_amax hq
  have hpF0 := hpF
  rw [h] at hpF hqF
  have e1 : ⟪p - q, n⟫ = 0 := by
    have := inner_eq_of_mem_amax hp hq
    rw [inner_sub_left]; linarith [real_inner_comm n p, real_inner_comm n q]
  have e2 : ⟪p - q, n'⟫ = 0 := by
    have h1 := hpF.2 q hqF.1
    have h2 := hqF.2 p hpF.1
    rw [inner_sub_left]; linarith
  rcases eq_or_eq_neg_of_inner (sub_ne_zero.2 hpq) hn.1 hn'.1 e1 e2 with h' | h'
  · exact h'.symm
  · exfalso
    have hconst : ∀ y ∈ convexHull ℝ (A : Set (E 2)), ⟪y, n⟫ = ⟪p, n⟫ := by
      intro y hy
      have h1 := hpF0.2 y hy
      have h2 := hpF.2 y hy
      rw [h', inner_neg_right, inner_neg_right] at h2
      linarith
    have := dim_le_one_of_const hn.ne_zero hconst
    omega

/-- **Edges are at least as many as edge normals** (2-dimensional polygon). -/
theorem card_le_fvec_one {A : Finset (E 2)} (h2 : dim (convexHull ℝ (A : Set (E 2))) = 2)
    {N : Finset (E 2)} (hN : ∀ n ∈ N, IsEdgeNormal A n) :
    N.card ≤ fvec (convexHull ℝ (A : Set (E 2))) 1 := by
  have hA := nonempty_of_dim_pos (A := A) (by omega)
  rw [fvec, ← Set.ncard_coe_finset N]
  refine Set.ncard_le_ncard_of_injOn (fun n => argmaxFace A n) ?_ ?_
    ((faces_finite_convexHull A).subset fun F hF => hF.1)
  · intro n hn
    exact ⟨argmaxFace_mem_faces hA n, dim_argmaxFace_of_edgeNormal (hN n hn)⟩
  · intro n hn n' hn' h
    exact eq_of_argmaxFace_eq h2 (hN n hn) (hN n' hn') h

/-- Two non-parallel edge normals force dimension two. -/
lemma dim_eq_two {A : Finset (E 2)} {n n' : E 2} (hn : IsEdgeNormal A n)
    (hn' : IsEdgeNormal A n') (h1 : n' ≠ n) (h2 : n' ≠ -n) :
    dim (convexHull ℝ (A : Set (E 2))) = 2 := by
  refine le_antisymm (dim_le _) ?_
  by_contra hlt
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 hn.2
  obtain ⟨p', hp', q', hq', hpq'⟩ := Finset.one_lt_card.1 hn'.2
  have hmem : ∀ {a b : E 2}, a ∈ A → b ∈ A →
      a - b ∈ vectorSpan ℝ (convexHull ℝ (A : Set (E 2))) := fun ha hb =>
    vsub_mem_vectorSpan ℝ (subset_convexHull ℝ _ ha) (subset_convexHull ℝ _ hb)
  have hpqV := hmem (amax_subset A n hp) (amax_subset A n hq)
  have hpqV' := hmem (amax_subset A n' hp') (amax_subset A n' hq')
  have hge := one_le_dim_of_ne (subset_convexHull ℝ _ (amax_subset A n hp))
    (subset_convexHull ℝ _ (amax_subset A n hq)) hpq
  have hV1 : finrank ℝ (vectorSpan ℝ (convexHull ℝ (A : Set (E 2)))) = 1 := by
    change dim _ = 1; omega
  have hne : (⟨p - q, hpqV⟩ : vectorSpan ℝ (convexHull ℝ (A : Set (E 2)))) ≠ 0 := by
    intro h0
    have := congrArg Subtype.val h0
    simp only [ZeroMemClass.coe_zero, sub_eq_zero] at this
    exact hpq this
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 hV1 ⟨p' - q', hpqV'⟩
  have ht' : p' - q' = t • (p - q) := by
    have := congrArg Subtype.val ht
    simpa using this.symm
  have e1 : ⟪p - q, n⟫ = 0 := by
    have := inner_eq_of_mem_amax hp hq
    rw [inner_sub_left]; linarith [real_inner_comm n p, real_inner_comm n q]
  have e2' : ⟪p' - q', n'⟫ = 0 := by
    have := inner_eq_of_mem_amax hp' hq'
    rw [inner_sub_left]; linarith [real_inner_comm n' p', real_inner_comm n' q']
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul, sub_eq_zero] at ht'
    exact hpq' ht'
  have e2 : ⟪p - q, n'⟫ = 0 := by
    rw [ht', real_inner_smul_left] at e2'
    rcases mul_eq_zero.1 e2' with h | h
    · exact absurd h ht0
    · exact h
  rcases eq_or_eq_neg_of_inner (sub_ne_zero.2 hpq) hn.1 hn'.1 e1 e2 with h | h
  · exact h1 h
  · exact h2 h

/-- **Planar bound**: at least three edge normals `N` give `2 #N + 1` argmax sets. -/
theorem card_amaxSets_ge {M N : Finset (E 2)} (hN : ∀ n ∈ N, IsEdgeNormal M n)
    (h3 : 3 ≤ N.card) : 2 * N.card + 1 ≤ (amaxSets M).card := by
  obtain ⟨n, hn⟩ : N.Nonempty := Finset.card_pos.1 (by omega)
  have hc : 1 ≤ ((N.erase n).erase (-n)).card := by
    have h1 := Finset.pred_card_le_card_erase (s := N) (a := n)
    have h2 := Finset.pred_card_le_card_erase (s := N.erase n) (a := -n)
    omega
  obtain ⟨n', hn'⟩ := Finset.card_pos.1 (by omega : 0 < ((N.erase n).erase (-n)).card)
  simp only [Finset.mem_erase] at hn'
  have h2 := dim_eq_two (hN n hn) (hN n' hn'.2.2) hn'.2.1 hn'.1
  have h1 := ncard_faces_le_amaxSets M
  rw [ncard_faces_polygon h2] at h1
  have h3 := card_le_fvec_one h2 hN
  omega

/-- Two distinct points give at least three argmax sets (the whole set and two ends). -/
theorem three_le_card_amaxSets {A : Finset (E 2)} {p q : E 2} (hp : p ∈ A) (hq : q ∈ A)
    (hpq : p ≠ q) : 3 ≤ (amaxSets A).card := by
  have hpos : 0 < ⟪p - q, p - q⟫ := real_inner_self_pos.2 (sub_ne_zero.2 hpq)
  simp only [inner_sub_left, inner_sub_right] at hpos
  have hc := real_inner_comm p q
  set X := amax A (q - p)
  set Y := amax A (p - q)
  have hpX : p ∉ X := fun h => by
    have := (mem_amax.1 h).2 q hq
    simp only [inner_sub_left] at this; linarith
  have hqY : q ∉ Y := fun h => by
    have := (mem_amax.1 h).2 p hp
    simp only [inner_sub_left] at this; linarith
  have hXA : X ≠ A := fun h => hpX (h ▸ hp)
  have hYA : Y ≠ A := fun h => hqY (h ▸ hq)
  have hXY : X ≠ Y := by
    intro h
    obtain ⟨r, hr⟩ := amax_nonempty ⟨p, hp⟩ (q - p)
    have hrY : r ∈ Y := h ▸ hr
    have h3 := (mem_amax.1 hrY).2 p hp
    have h4 := (mem_amax.1 hr).2 q hq
    simp only [inner_sub_left] at h3 h4
    linarith [real_inner_comm p r, real_inner_comm q r]
  have hsub : ({A, X, Y} : Finset (Finset (E 2))) ⊆ amaxSets A := by
    intro T hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl
    · exact mem_amaxSets.2 ⟨0, amax_zero _⟩
    · exact amax_mem_amaxSets _ _
    · exact amax_mem_amaxSets _ _
  have hcard : ({A, X, Y} : Finset (Finset (E 2))).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hXY
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hXA.symm, hYA.symm⟩
  calc 3 = _ := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

lemma one_le_card_amaxSets {A : Finset (E 2)} (hA : A.Nonempty) : 1 ≤ (amaxSets A).card :=
  Finset.card_pos.2 ⟨_, amax_mem_amaxSets A 0⟩

/-! ### Minkowski sums and negation -/

lemma amax_add (A B : Finset (E 2)) (b : E 2) : amax (A + B) b = amax A b + amax B b := by
  ext p
  simp only [mem_amax, Finset.mem_add]
  constructor
  · rintro ⟨⟨a, ha, c, hc, rfl⟩, hmax⟩
    refine ⟨a, ⟨ha, fun q hq => ?_⟩, c, ⟨hc, fun q hq => ?_⟩, rfl⟩
    · have := hmax (q + c) ⟨q, hq, c, hc, rfl⟩
      rw [inner_add_right, inner_add_right] at this; linarith
    · have := hmax (a + q) ⟨a, ha, q, hq, rfl⟩
      rw [inner_add_right, inner_add_right] at this; linarith
  · rintro ⟨a, ⟨ha, hma⟩, c, ⟨hc, hmc⟩, rfl⟩
    refine ⟨⟨a, ha, c, hc, rfl⟩, ?_⟩
    rintro _ ⟨a', ha', c', hc', rfl⟩
    rw [inner_add_right, inner_add_right]
    linarith [hma a' ha', hmc c' hc']

lemma amax_neg (A : Finset (E 2)) (b : E 2) : amax (-A) b = -amax A (-b) := by
  ext p
  rw [Finset.mem_neg', mem_amax, mem_amax, Finset.mem_neg']
  constructor
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, fun q hq => ?_⟩
    have := hmax (-q) (by rwa [Finset.mem_neg', neg_neg])
    rw [inner_neg_right] at this
    rw [inner_neg_left, inner_neg_left, inner_neg_right]
    linarith
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, fun q hq => ?_⟩
    have := hmax (-q) (by rwa [Finset.mem_neg'] at hq)
    rw [inner_neg_left, inner_neg_left, inner_neg_right, inner_neg_right] at this
    linarith

lemma IsEdgeNormal.add_right {A B : Finset (E 2)} {n : E 2} (h : IsEdgeNormal A n)
    (hB : B.Nonempty) : IsEdgeNormal (A + B) n := by
  refine ⟨h.1, ?_⟩
  rw [amax_add]
  exact lt_of_lt_of_le h.2 (Finset.card_le_card_add_right (amax_nonempty hB n))

lemma IsEdgeNormal.add_left {A B : Finset (E 2)} {n : E 2} (h : IsEdgeNormal B n)
    (hA : A.Nonempty) : IsEdgeNormal (A + B) n := by
  refine ⟨h.1, ?_⟩
  rw [amax_add]
  exact lt_of_lt_of_le h.2 (Finset.card_le_card_add_left (amax_nonempty hA n))

lemma IsEdgeNormal.neg {A : Finset (E 2)} {n : E 2} (h : IsEdgeNormal A n) :
    IsEdgeNormal (-A) (-n) := by
  refine ⟨by rw [norm_neg]; exact h.1, ?_⟩
  rw [amax_neg, neg_neg, Finset.card_neg]
  exact h.2

/-! ### Convex position -/

/-- **`≥ 3` points in convex position span the plane.** -/
theorem dim_eq_two_of_convpos {A : Finset (E 2)}
    (hA : ∀ p ∈ A, p ∈ (convexHull ℝ (A : Set (E 2))).extremePoints ℝ) (h3 : 3 ≤ A.card) :
    dim (convexHull ℝ (A : Set (E 2))) = 2 := by
  have hext : (convexHull ℝ (A : Set (E 2))).extremePoints ℝ = (A : Set (E 2)) :=
    Subset.antisymm extremePoints_convexHull_subset (fun p hp => hA p hp)
  have hle := dim_le (convexHull ℝ (A : Set (E 2)))
  by_contra hne
  obtain h0 | h1 : dim (convexHull ℝ (A : Set (E 2))) = 0 ∨
      dim (convexHull ℝ (A : Set (E 2))) = 1 := by omega
  · have hAne : A.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨g, hg⟩ := eq_singleton_of_dim_eq_zero
      ((Finset.coe_nonempty.2 hAne).convexHull (𝕜 := ℝ)) h0
    have : A.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have ha' : a ∈ convexHull ℝ (A : Set (E 2)) := subset_convexHull ℝ _ ha
      have hb' : b ∈ convexHull ℝ (A : Set (E 2)) := subset_convexHull ℝ _ hb
      rw [hg] at ha' hb'
      exact ha'.trans hb'.symm
    omega
  · have := ncard_extremePoints_of_dim_one A h1
    rw [hext, Set.ncard_coe_finset] at this
    omega

/-- **A 2-dimensional set in convex position has at least `|A|` edge normals.** -/
theorem exists_edgeNormals {A : Finset (E 2)}
    (hA : ∀ p ∈ A, p ∈ (convexHull ℝ (A : Set (E 2))).extremePoints ℝ)
    (h2 : dim (convexHull ℝ (A : Set (E 2))) = 2) :
    ∃ N : Finset (E 2), (∀ n ∈ N, IsEdgeNormal A n) ∧ A.card ≤ N.card := by
  classical
  have hAne := nonempty_of_dim_pos (A := A) (by omega)
  have hf0 : fvec (convexHull ℝ (A : Set (E 2))) 0 = A.card := by
    rw [fvec_zero_eq]
    have : (convexHull ℝ (A : Set (E 2))).extremePoints ℝ = (A : Set (E 2)) :=
      Subset.antisymm extremePoints_convexHull_subset (fun p hp => hA p hp)
    rw [this, Set.ncard_coe_finset]
  have hf01 := fvec_zero_eq_fvec_one h2
  have hedge : ∀ F ∈ {F | F ∈ faces (convexHull ℝ (A : Set (E 2))) ∧ dim F = 1},
      ∃ n, IsEdgeNormal A n ∧ argmaxFace A n = F := by
    rintro F ⟨hF, hd⟩
    obtain ⟨c, rfl⟩ := exists_argmaxFace_eq hF
    have hc0 : c ≠ 0 := by
      rintro rfl
      have : argmaxFace A 0 = convexHull ℝ (A : Set (E 2)) := by
        ext x; simp [argmaxFace]
      rw [this] at hd; omega
    have hpos : 0 < ‖c‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hc0)
    have hn1 : ‖‖c‖⁻¹ • c‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, inv_mul_cancel₀ (norm_ne_zero_iff.2 hc0)]
    have hFn : argmaxFace A (‖c‖⁻¹ • c) = argmaxFace A c := by
      ext x
      simp only [argmaxFace, Set.mem_setOf_eq, real_inner_smul_right]
      constructor <;> rintro ⟨hx, h⟩ <;> refine ⟨hx, fun y hy => ?_⟩
      · exact le_of_mul_le_mul_left (h y hy) hpos
      · exact mul_le_mul_of_nonneg_left (h y hy) hpos.le
    refine ⟨‖c‖⁻¹ • c, ⟨hn1, ?_⟩, hFn⟩
    by_contra hle
    push_neg at hle
    obtain ⟨p, hp⟩ := Finset.card_eq_one.1
      (le_antisymm hle (Finset.card_pos.2 (amax_nonempty hAne _)))
    have := argmaxFace_eq_convexHull_amax hAne (‖c‖⁻¹ • c)
    rw [hp, Finset.coe_singleton, convexHull_singleton, hFn] at this
    rw [this, dim_singleton] at hd
    omega
  choose! f hf using hedge
  have hfinE : {F | F ∈ faces (convexHull ℝ (A : Set (E 2))) ∧ dim F = 1}.Finite :=
    (faces_finite_convexHull A).subset fun F hF => hF.1
  refine ⟨hfinE.toFinset.image f, ?_, ?_⟩
  · intro n hn
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hn
    exact (hf F ((Set.Finite.mem_toFinset _).1 hF)).1
  · rw [Finset.card_image_of_injOn]
    · rw [← Set.ncard_eq_toFinset_card _ hfinE, ← fvec, ← hf01, hf0]
    · intro F hF G hG h
      have h1 := (hf F ((Set.Finite.mem_toFinset _).1 hF)).2
      have h2 := (hf G ((Set.Finite.mem_toFinset _).1 hG)).2
      rw [← h1, ← h2, h]

/-! ### Antiparallel normals, triangles -/

lemma amax_disjoint_neg {A : Finset (E 2)} (h2 : dim (convexHull ℝ (A : Set (E 2))) = 2)
    {n : E 2} (hn : n ≠ 0) : Disjoint (amax A n) (amax A (-n)) := by
  rw [Finset.disjoint_left]
  intro r hr hr'
  have hconst : ∀ y ∈ convexHull ℝ (A : Set (E 2)), ⟪y, n⟫ = ⟪r, n⟫ := by
    intro y hy
    have h1 := (mem_argmaxFace_of_mem_amax hr).2 y hy
    have h2 := (mem_argmaxFace_of_mem_amax hr').2 y hy
    rw [inner_neg_right, inner_neg_right] at h2
    linarith
  have := dim_le_one_of_const hn hconst
  omega

lemma card_amax_add_card_amax_neg_le {A : Finset (E 2)}
    (h2 : dim (convexHull ℝ (A : Set (E 2))) = 2) {n : E 2} (hn : n ≠ 0) :
    (amax A n).card + (amax A (-n)).card ≤ A.card := by
  rw [← Finset.card_union_of_disjoint (amax_disjoint_neg h2 hn)]
  exact Finset.card_le_card (Finset.union_subset (amax_subset _ _) (amax_subset _ _))

/-- **A triangle has no antiparallel edge normals.** -/
lemma not_edgeNormal_neg {T : Finset (E 2)} (hT : T.card = 3)
    (h2 : dim (convexHull ℝ (T : Set (E 2))) = 2) {n : E 2} (hn : IsEdgeNormal T n) :
    ¬ IsEdgeNormal T (-n) := by
  intro hn'
  have := card_amax_add_card_amax_neg_le h2 hn.ne_zero
  have := hn.2; have := hn'.2
  omega

/-- For a triangle, the argmax set at an edge normal or its negative determines the direction. -/
theorem eq_of_amax_eq_triangle {T : Finset (E 2)} (hT : T.card = 3)
    (h2 : dim (convexHull ℝ (T : Set (E 2))) = 2) {b b' : E 2}
    (hb : IsEdgeNormal T b ∨ IsEdgeNormal T (-b)) (hb' : IsEdgeNormal T b' ∨ IsEdgeNormal T (-b'))
    (h : amax T b = amax T b') : b = b' := by
  have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
  -- two edge normals with the same argmax set agree
  have key : ∀ {c c' : E 2}, IsEdgeNormal T c → IsEdgeNormal T c' → amax T c = amax T c' →
      c = c' := fun hc hc' hcc => eq_of_argmaxFace_eq h2 hc hc'
        (by rw [argmaxFace_eq_convexHull_amax hTne, argmaxFace_eq_convexHull_amax hTne, hcc])
  have hb0 : b ≠ 0 := by
    rcases hb with hb | hb
    · exact hb.ne_zero
    · exact fun h0 => hb.ne_zero (by rw [h0, neg_zero])
  have hb0' : b' ≠ 0 := by
    rcases hb' with hb' | hb'
    · exact hb'.ne_zero
    · exact fun h0 => hb'.ne_zero (by rw [h0, neg_zero])
  have hs := card_amax_add_card_amax_neg_le h2 hb0
  have hs' := card_amax_add_card_amax_neg_le h2 hb0'
  rcases hb with hb | hb
  · rcases hb' with hb' | hb'
    · exact key hb hb' h
    · exfalso
      have h1 := hb.2; have h3 := hb'.2
      rw [h] at h1
      omega
  · rcases hb' with hb' | hb'
    · exfalso
      have := hb.2; have := hb'.2
      rw [← h] at this
      omega
    · -- the complements of the singletons `amax T b = amax T b'` coincide
      have hc : ∀ {c : E 2}, c ≠ 0 → IsEdgeNormal T (-c) → amax T (-c) = T \ amax T c := by
        intro c hc0 hc
        have hdisj := amax_disjoint_neg h2 hc0
        have hsub : amax T (-c) ⊆ T \ amax T c := by
          intro p hp
          exact Finset.mem_sdiff.2 ⟨amax_subset _ _ hp, Finset.disjoint_right.1 hdisj hp⟩
        refine Finset.eq_of_subset_of_card_le hsub ?_
        have h1 := Finset.card_sdiff_of_subset (amax_subset T c)
        have hpos := Finset.card_pos.2 (amax_nonempty hTne c)
        have h3 := card_amax_add_card_amax_neg_le h2 hc0
        have := hc.2
        omega
      have := key hb hb' (by rw [hc hb0 hb, hc hb0' hb', h])
      exact neg_injective this

/-! ### Perturbations -/

/-- For large `t`, the maximizers of `t α + d` are among the maximizers of `α`. -/
lemma eventually_amax_subset (A : Finset (E 2)) (α d : E 2) :
    ∀ᶠ t : ℝ in Filter.atTop, amax A (t • α + d) ⊆ amax A α := by
  have key : ∀ p ∈ A, ∀ᶠ t : ℝ in Filter.atTop, p ∈ amax A (t • α + d) → p ∈ amax A α := by
    intro p hp
    by_cases hpm : p ∈ amax A α
    · exact Filter.Eventually.of_forall fun _ _ => hpm
    · obtain ⟨q, hq, hlt⟩ : ∃ q ∈ A, ⟪α, p⟫ < ⟪α, q⟫ := by
        by_contra hcon
        push_neg at hcon
        exact hpm (mem_amax.2 ⟨hp, hcon⟩)
      have hδ : 0 < ⟪α, q⟫ - ⟪α, p⟫ := by linarith
      filter_upwards [Filter.eventually_gt_atTop (|⟪d, q⟫ - ⟪d, p⟫| / (⟪α, q⟫ - ⟪α, p⟫))]
        with t ht
      intro hpt
      exfalso
      have h1 := (mem_amax.1 hpt).2 q hq
      rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left] at h1
      rw [div_lt_iff₀ hδ] at ht
      have habs := neg_abs_le (⟪d, q⟫ - ⟪d, p⟫)
      have hexp : t * (⟪α, q⟫ - ⟪α, p⟫) = t * ⟪α, q⟫ - t * ⟪α, p⟫ := by ring
      linarith
  filter_upwards [(Filter.eventually_all_finset A).2 key] with t ht p hp
  exact ht p (amax_subset _ _ hp) hp

end Kalai5.LemmaB
