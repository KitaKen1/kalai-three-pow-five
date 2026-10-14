import Kalai5.Euler.Euler
import Kalai5.Polar.Intervals

/-!
# Euler relations for centrally symmetric 5-polytopes and their faces

From `euler_poincare`:
* `f₀ - f₁ + f₂ - f₃ + f₄ = 2`;
* every face `G` satisfies `Σ_{j ≤ dim G} (-1)^j #(j-faces in G) = 1`;
* summed over vertices (through polarity, the faces containing a vertex are the faces of a facet
  of `P°`): `f₀₃ = f₀₄ + f₀₂ - 2f₁`;
* summed over 3-faces, with `#3-faces ⊇ Q = #facets ⊇ Q` for 2-faces `Q` (a polygon has as many
  edges as vertices): `f₁₃ = f₀₄ + f₀₂ + f₂₄ - 2(f₁ + f₃)`.
-/

namespace Kalai5

open Set

variable {d : ℕ}

/-- A proper face of a face has smaller dimension. -/
lemma dim_lt_of_mem_faces_ne {F G : Set (E d)} (hG : G ∈ faces F) (hne : G ≠ F) :
    dim G < dim F := by
  obtain ⟨l, hl⟩ := exists_functional hG
  obtain ⟨g, hg⟩ := hG.1
  have hGF : G ⊆ F := face_subset hG
  have hgmax : ∀ y ∈ F, l y ≤ l g := by have := hg; rw [hl] at this; exact this.2
  obtain ⟨x, hxF, hxG⟩ : ∃ x ∈ F, x ∉ G := by
    by_contra h; push_neg at h; exact hne (Set.Subset.antisymm hGF h)
  have hlt : l x < l g := by
    rcases lt_or_eq_of_le (hgmax x hxF) with h | h
    · exact h
    · exfalso; apply hxG; rw [hl]; exact ⟨hxF, fun y hy => h ▸ hgmax y hy⟩
  have hker : vectorSpan ℝ G ≤ LinearMap.ker (l : E d →ₗ[ℝ] ℝ) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro v ⟨a, ha, b, hb, rfl⟩
    have ha' := ha; have hb' := hb
    rw [hl] at ha' hb'
    simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, map_sub,
      ContinuousLinearMap.coe_coe]
    have h1 := ha'.2 b hb'.1; have h2 := hb'.2 a ha'.1; linarith
  have hlt' : vectorSpan ℝ G < vectorSpan ℝ F := by
    refine lt_of_le_of_ne (vectorSpan_mono ℝ hGF) fun h => ?_
    have hmem : x -ᵥ g ∈ vectorSpan ℝ F := vsub_mem_vectorSpan ℝ hxF (hGF hg)
    rw [← h] at hmem
    have := hker hmem
    simp only [LinearMap.mem_ker, vsub_eq_sub, map_sub, ContinuousLinearMap.coe_coe] at this
    linarith
  exact Submodule.finrank_lt_finrank_of_lt hlt'

open Classical in
/-- Euler–Poincaré in terms of face numbers. -/
lemma euler_fvec {V : Finset (E d)} (hV : V.Nonempty) (n : ℕ)
    (hn : ∀ G ∈ faces (convexHull ℝ (V : Set (E d))), dim G ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * fvec (convexHull ℝ (V : Set (E d))) k = 1 := by
  refine Eq.trans ?_ (euler_poincare hV)
  set FS := (faces_finite_convexHull V).toFinset
  symm
  rw [← Finset.sum_fiberwise_of_maps_to (s := FS) (t := Finset.range (n + 1)) (g := dim)
    (fun F hF => by
      rw [Set.Finite.mem_toFinset] at hF
      rw [Finset.mem_range]; have := hn F hF; omega)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc : ∑ F ∈ FS with dim F = k, (-1 : ℤ) ^ dim F = ∑ F ∈ FS with dim F = k, (-1 : ℤ) ^ k :=
    Finset.sum_congr rfl fun F hF => by rw [(Finset.mem_filter.1 hF).2]
  have hcard : (FS.filter fun F => dim F = k).card = fvec (convexHull ℝ (V : Set (E d))) k := by
    rw [fvec, Set.ncard_eq_toFinset_card _ ((faces_finite_convexHull V).subset fun F hF => hF.1)]
    congr 1
    ext F; simp [FS]
  rw [hc, Finset.sum_const, nsmul_eq_mul, hcard, mul_comm]

/-! ### Centrally symmetric 5-polytopes -/

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- `#{faces of P containing G of dimension j}`. -/
noncomputable def up (P G : Set E5) (j : ℕ) : ℕ := {F | F ∈ faces P ∧ G ⊆ F ∧ dim F = j}.ncard

lemma IsCSPolytope5.cnt_self {G : Set E5} (hG : G ∈ faces P) : cnt P G (dim G) = 1 := by
  obtain ⟨V, hV⟩ := hP.polytope
  have hG' : G ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hG
  rw [cnt, Set.ncard_eq_one]
  refine ⟨G, ?_⟩
  ext H
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hH, hHG, hd⟩
    by_contra hne
    have hH' : H ∈ faces G := (mem_faces_face_iff hG').2 ⟨hV ▸ hH, hHG⟩
    have := dim_lt_of_mem_faces_ne hH' hne
    omega
  · rintro rfl; exact ⟨hG, le_rfl, rfl⟩

/-- **Euler relation for a face**. -/
lemma IsCSPolytope5.euler_face {G : Set E5} (hG : G ∈ faces P) :
    ∑ j ∈ Finset.range (dim G + 1), (-1 : ℤ) ^ j * cnt P G j = 1 := by
  classical
  obtain ⟨V, hV⟩ := hP.polytope
  have hG' : G ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hG
  set S := V.filter (· ∈ G)
  have hGS : G = convexHull ℝ (S : Set E5) := face_eq_convexHull_filter hG'
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    obtain ⟨x, hx⟩ := hG.1
    rw [hGS, h, Finset.coe_empty, convexHull_empty] at hx; exact hx
  have hdims : ∀ H ∈ faces (convexHull ℝ (S : Set E5)), dim H ≤ dim G := by
    intro H hH
    rw [← hGS] at hH
    exact Submodule.finrank_mono (vectorSpan_mono ℝ (face_subset hH))
  have h := euler_fvec hS (dim G) hdims
  rw [← hGS] at h
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
  rw [fvec_face_eq_cnt hG', ← hV]

/-- Faces containing a proper face `G` ↔ faces of `P°` inside `G♦`, with the dual face data. -/
lemma IsCSPolytope5.up_eq_cnt_dual {G : Set E5} (hG : G ∈ faces P) (hne : G ≠ P) (j : ℕ)
    (hj : j ≤ 4) : up P G j = cnt (polarSet P) (dualFace P G) (4 - j) :=
  hP.ncard_up hG hne j hj

lemma IsCSPolytope5.dualFace_mem {G : Set E5} (hG : G ∈ faces P) (hne : G ≠ P) :
    dualFace P G ∈ faces (polarSet P) ∧ dim (dualFace P G) + dim G = 4 := by
  obtain ⟨W, hW, hmem, hdim⟩ := hP.dualFace_facts hG hne
  exact ⟨hW ▸ hmem, hdim⟩

/-- Around a vertex: `#facets - #3-faces + #2-faces - #edges = 0`. -/
lemma IsCSPolytope5.vertex_identity {G : Set E5} (hG : G ∈ faces P) (h0 : dim G = 0) :
    (up P G 4 : ℤ) - up P G 3 + up P G 2 - up P G 1 = 0 := by
  have hne : G ≠ P := fun h => by have := hP.dim_self; rw [← h, h0] at this; omega
  obtain ⟨hmem, hdim⟩ := hP.dualFace_mem hG hne
  have hd4 : dim (dualFace P G) = 4 := by omega
  have he := hP.polar.euler_face hmem
  have hc4 := hP.polar.cnt_self hmem
  rw [hd4] at he hc4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at he
  rw [hc4] at he
  rw [hP.up_eq_cnt_dual hG hne 4 le_rfl, hP.up_eq_cnt_dual hG hne 3 (by norm_num),
    hP.up_eq_cnt_dual hG hne 2 (by norm_num), hP.up_eq_cnt_dual hG hne 1 (by norm_num)]
  norm_num at he ⊢
  linarith

/-- Around a 2-face: as many 3-faces as facets contain it. -/
lemma IsCSPolytope5.twoface_identity {Q : Set E5} (hQ : Q ∈ faces P) (h2 : dim Q = 2) :
    up P Q 3 = up P Q 4 := by
  have hne : Q ≠ P := fun h => by have := hP.dim_self; rw [← h, h2] at this; omega
  obtain ⟨hmem, hdim⟩ := hP.dualFace_mem hQ hne
  have hd2 : dim (dualFace P Q) = 2 := by omega
  have he := hP.polar.euler_face hmem
  have hc2 := hP.polar.cnt_self hmem
  rw [hd2] at he hc2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at he
  rw [hc2] at he
  rw [hP.up_eq_cnt_dual hQ hne 3 (by norm_num), hP.up_eq_cnt_dual hQ hne 4 le_rfl]
  norm_num at he ⊢
  omega

/-- A 3-face satisfies `f₀ - f₁ + f₂ = 2`. -/
lemma IsCSPolytope5.threeface_identity {T : Set E5} (hT : T ∈ faces P) (h3 : dim T = 3) :
    (cnt P T 0 : ℤ) - cnt P T 1 + cnt P T 2 = 2 := by
  have he := hP.euler_face hT
  have hc3 := hP.cnt_self hT
  rw [h3] at he hc3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at he
  rw [hc3] at he
  norm_num at he
  linarith

/-- **Euler's relation** for centrally symmetric 5-polytopes. -/
theorem IsCSPolytope5.euler_relation :
    (fvec P 0 : ℤ) - fvec P 1 + fvec P 2 - fvec P 3 + fvec P 4 = 2 := by
  obtain ⟨V, hV⟩ := hP.polytope
  have hVne : V.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    obtain ⟨x, hx⟩ := hP.nonempty
    rw [hV, h, Finset.coe_empty, convexHull_empty] at hx; exact hx
  have h := euler_fvec hVne 5 fun G _ => dim_le G
  rw [← hV] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have h5 : fvec P 5 = 1 := by
    have := hP.cnt_self (self_mem_faces hP.nonempty)
    rw [hP.dim_self] at this
    rw [← this, fvec, cnt]
    congr 1; ext F
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => ⟨h.1, face_subset h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [h5] at h
  push_cast at h
  linarith

/-- **Summed Euler relation over vertices**: `f₀₃ = f₀₄ + f₀₂ - 2 f₁`. -/
theorem IsCSPolytope5.flag03_identity :
    (flag2 P 0 3 : ℤ) = flag2 P 0 4 + flag2 P 0 2 - 2 * fvec P 1 := by
  have hsum : ∀ j, (flag2 P 0 j : ℤ) = ∑ G ∈ (hP.kfaces_finite 0).toFinset, (up P G j : ℤ) := by
    intro j; rw [hP.flag2_eq_sum_up 0 j]; push_cast; rfl
  have h01 : (flag2 P 0 1 : ℤ) = 2 * fvec P 1 := by
    rw [hP.flag2_eq_sum 0 1]
    have hconst : ∀ E ∈ (hP.kfaces_finite 1).toFinset, cnt P E 0 = 2 := by
      intro E hE
      rw [Set.Finite.mem_toFinset] at hE
      obtain ⟨V, hV⟩ := hP.polytope
      have hE' : E ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hE.1
      have := cnt_zero_of_dim_one hE' hE.2
      rwa [← hV] at this
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, fvec,
      Set.ncard_eq_toFinset_card _ (hP.kfaces_finite 1)]
    push_cast; ring
  have hv : ∑ G ∈ (hP.kfaces_finite 0).toFinset,
      ((up P G 4 : ℤ) - up P G 3 + up P G 2 - up P G 1) = 0 := by
    refine Finset.sum_eq_zero fun G hG => ?_
    rw [Set.Finite.mem_toFinset] at hG
    exact hP.vertex_identity hG.1 hG.2
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hv
  rw [← hsum 4, ← hsum 3, ← hsum 2, ← hsum 1, h01] at hv
  linarith

/-- **Summed Euler relation over 3-faces**: `f₁₃ = f₀₄ + f₀₂ + f₂₄ - 2 (f₁ + f₃)`. -/
theorem IsCSPolytope5.flag13_identity :
    (flag2 P 1 3 : ℤ) = flag2 P 0 4 + flag2 P 0 2 + flag2 P 2 4 - 2 * (fvec P 1 + fvec P 3) := by
  have h03 := hP.flag03_identity
  have hdown : ∀ i, (flag2 P i 3 : ℤ) = ∑ T ∈ (hP.kfaces_finite 3).toFinset, (cnt P T i : ℤ) := by
    intro i; rw [hP.flag2_eq_sum i 3]; push_cast; rfl
  have h23 : flag2 P 2 3 = flag2 P 2 4 := by
    rw [hP.flag2_eq_sum_up 2 3, hP.flag2_eq_sum_up 2 4]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [Set.Finite.mem_toFinset] at hQ
    exact hP.twoface_identity hQ.1 hQ.2
  have ht : ∑ T ∈ (hP.kfaces_finite 3).toFinset,
      ((cnt P T 0 : ℤ) - cnt P T 1 + cnt P T 2) =
        ∑ _T ∈ (hP.kfaces_finite 3).toFinset, (2 : ℤ) := by
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Set.Finite.mem_toFinset] at hT
    exact hP.threeface_identity hT.1 hT.2
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at ht
  rw [← hdown 0, ← hdown 1, ← hdown 2, h23] at ht
  have hcard : ((hP.kfaces_finite 3).toFinset.card : ℤ) = fvec P 3 := by
    rw [fvec, Set.ncard_eq_toFinset_card _ (hP.kfaces_finite 3)]
  rw [hcard] at ht
  linarith

end cs

end Kalai5
