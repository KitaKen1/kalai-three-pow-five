import Kalai5.Polar.Flags
import Kalai5.Faces.LowDim

/-!
# Upper intervals through polarity, and the remaining facet-row and `A ≥ 0` obligations

* double dual `(F♦)♦ = F`;
* the faces of `P` containing a proper face `G` correspond to the faces of `P°` inside `G♦`
  (`ncard_up`), so a 3-face lies in exactly two facets and a 2-face in at least three;
* edges have two vertices and 2-faces at least three (`Kalai5.Faces.LowDim`);
* double counting of 3-flags; consequences `Σ r = 2 f₃`, `Σ J = 2 f₀₃` and `A ≥ 0`.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {d : ℕ}

/-- **Double dual**: `(F♦)♦ = F` for a proper face of a polytope with `0` inside. -/
lemma dualFace_dualFace {V : Finset (E d)} {F : Set (E d)}
    (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d))))
    (hF : F ∈ faces (convexHull ℝ (V : Set (E d)))) (hne : F ≠ convexHull ℝ (V : Set (E d))) :
    dualFace (polarSet (convexHull ℝ (V : Set (E d))))
      (dualFace (convexHull ℝ (V : Set (E d))) F) = F := by
  set K := convexHull ℝ (V : Set (E d))
  have hbip : polarSet (polarSet K) = K := polarSet_polarSet (convex_convexHull ℝ _)
    (Set.Finite.isClosed_convexHull ℝ V.finite_toSet) (interior_subset h0)
  have hF' := eq_of_dualFace h0 hF hne
  ext x
  constructor
  · rintro ⟨hx, hall⟩
    rw [hbip] at hx
    rw [hF']
    exact ⟨hx, fun y hy => by rw [real_inner_comm]; exact hall y hy⟩
  · intro hx
    rw [hF'] at hx
    refine ⟨by rw [hbip]; exact hx.1, fun y hy => ?_⟩
    rw [real_inner_comm]; exact hx.2 y hy

/-- The number of vertices of a face is the number of its extreme points. -/
lemma cnt_zero_eq {V : Finset (E d)} {F : Set (E d)} [DecidablePred (· ∈ F)]
    (hF : F ∈ faces (convexHull ℝ (V : Set (E d)))) :
    cnt (convexHull ℝ (V : Set (E d))) F 0 =
      ((convexHull ℝ ((V.filter (· ∈ F) : Finset (E d)) : Set (E d))).extremePoints ℝ).ncard := by
  rw [← fvec_face_eq_cnt hF, ← fvec_zero_eq]
  conv_lhs => rw [face_eq_convexHull_filter hF]

/-- **An edge has exactly two vertices.** -/
lemma cnt_zero_of_dim_one {V : Finset (E d)} {F : Set (E d)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E d)))) (h1 : dim F = 1) :
    cnt (convexHull ℝ (V : Set (E d))) F 0 = 2 := by
  classical
  rw [cnt_zero_eq hF]
  apply ncard_extremePoints_of_dim_one
  rw [← face_eq_convexHull_filter hF]; exact h1

/-- **A 2-face has at least three vertices.** -/
lemma three_le_cnt_zero_of_dim_two {V : Finset (E d)} {F : Set (E d)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E d)))) (h2 : dim F = 2) :
    3 ≤ cnt (convexHull ℝ (V : Set (E d))) F 0 := by
  classical
  rw [cnt_zero_eq hF]
  have hS : (V.filter (· ∈ F)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := face_eq_convexHull_filter hF
    rw [h, Finset.coe_empty, convexHull_empty] at this
    obtain ⟨x, hx⟩ := hF.1; rw [this] at hx; exact hx
  have := dim_add_one_le_ncard_extremePoints _ hS
  rw [← face_eq_convexHull_filter hF] at this ⊢
  rw [h2] at this
  omega

/-! ### Centrally symmetric 5-polytopes -/

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **Upper intervals**: faces of `P` containing a proper face `G` ↔ faces of `P°` inside `G♦`. -/
theorem IsCSPolytope5.ncard_up {G : Set E5} (hG : G ∈ faces P) (hne : G ≠ P) (j : ℕ)
    (hj : j ≤ 4) :
    {F | F ∈ faces P ∧ G ⊆ F ∧ dim F = j}.ncard = cnt (polarSet P) (dualFace P G) (4 - j) := by
  have hPol := hP.polar
  have hbip := hP.polarSet_polarSet
  obtain ⟨V, hV⟩ := hP.polytope
  obtain ⟨W, hW⟩ := hPol.polytope
  have h0V : (0 : E5) ∈ interior (convexHull ℝ (V : Set E5)) := hV ▸ hP.zero_mem_interior
  have h0W : (0 : E5) ∈ interior (convexHull ℝ (W : Set E5)) := hW ▸ hPol.zero_mem_interior
  have hdimP := hP.dim_self
  have hdimQ := hPol.dim_self
  have hfinP := hP.faces_finite
  have hfinQ := hPol.faces_finite
  apply le_antisymm
  · -- `F ↦ F♦`
    refine Set.ncard_le_ncard_of_injOn (dualFace P) ?_ ?_ (hfinQ.subset fun H hH => hH.1)
    · rintro F ⟨hF, hGF, hd⟩
      have hneF : F ≠ P := fun h => by rw [h] at hd; omega
      rw [hV] at hF hneF
      have e := dim_dualFace h0V hF hneF
      have hmem := dualFace_mem_faces h0V hF hneF
      rw [← hV] at e hmem
      exact ⟨hmem, dualFace_antitone hGF, by omega⟩
    · rintro F ⟨hF, -, hd⟩ F' ⟨hF', -, hd'⟩ heq
      have hneF : F ≠ P := fun h => by rw [h] at hd; omega
      have hneF' : F' ≠ P := fun h => by rw [h] at hd'; omega
      rw [hV] at hF hF' hneF hneF'
      have e1 := eq_of_dualFace h0V hF hneF
      have e2 := eq_of_dualFace h0V hF' hneF'
      rw [← hV] at e1 e2
      rw [heq] at e1
      exact e1.trans e2.symm
  · -- `H ↦ H♦` (in the polar)
    have hGdd : dualFace (polarSet P) (dualFace P G) = G := by
      have hG' : G ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hG
      have hne' : G ≠ convexHull ℝ (V : Set E5) := hV ▸ hne
      have := dualFace_dualFace h0V hG' hne'
      rwa [← hV] at this
    refine Set.ncard_le_ncard_of_injOn (dualFace (polarSet P)) ?_ ?_
      (hfinP.subset fun F hF => hF.1)
    · rintro H ⟨hH, hHG, hd⟩
      have hneH : H ≠ polarSet P := fun h => by rw [h] at hd; omega
      rw [hW] at hH hneH
      have e := dim_dualFace h0W hH hneH
      have hmem := dualFace_mem_faces h0W hH hneH
      rw [← hW, hbip] at hmem
      rw [← hW] at e
      refine ⟨hmem, ?_, by omega⟩
      calc G = dualFace (polarSet P) (dualFace P G) := hGdd.symm
        _ ⊆ dualFace (polarSet P) H := dualFace_antitone hHG
    · rintro H ⟨hH, -, hd⟩ H' ⟨hH', -, hd'⟩ heq
      have hneH : H ≠ polarSet P := fun h => by rw [h] at hd; omega
      have hneH' : H' ≠ polarSet P := fun h => by rw [h] at hd'; omega
      rw [hW] at hH hH' hneH hneH'
      have e1 := eq_of_dualFace h0W hH hneH
      have e2 := eq_of_dualFace h0W hH' hneH'
      rw [← hW] at e1 e2
      rw [heq] at e1
      exact e1.trans e2.symm

lemma IsCSPolytope5.dualFace_facts {G : Set E5} (hG : G ∈ faces P) (hne : G ≠ P) :
    ∃ W : Finset E5, polarSet P = convexHull ℝ (W : Set E5) ∧
      dualFace P G ∈ faces (convexHull ℝ (W : Set E5)) ∧ dim (dualFace P G) + dim G = 4 := by
  obtain ⟨V, hV⟩ := hP.polytope
  obtain ⟨W, hW⟩ := hP.polar.polytope
  have h0V : (0 : E5) ∈ interior (convexHull ℝ (V : Set E5)) := hV ▸ hP.zero_mem_interior
  have hG' : G ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hG
  have hne' : G ≠ convexHull ℝ (V : Set E5) := hV ▸ hne
  have e := dim_dualFace h0V hG' hne'
  have hmem := dualFace_mem_faces h0V hG' hne'
  rw [← hV] at e hmem
  rw [hW] at hmem
  exact ⟨W, hW, hmem, by omega⟩

/-- **A 3-face lies in exactly two facets.** -/
theorem IsCSPolytope5.ridge_two {T : Set E5} (hT : T ∈ faces P) (h3 : dim T = 3) :
    {F | F ∈ faces P ∧ T ⊆ F ∧ dim F = 4}.ncard = 2 := by
  have hne : T ≠ P := fun h => by have := hP.dim_self; rw [← h, h3] at this; omega
  rw [hP.ncard_up hT hne 4 le_rfl]
  obtain ⟨W, hW, hmem, hdim⟩ := hP.dualFace_facts hT hne
  rw [hW]
  exact cnt_zero_of_dim_one hmem (by omega)

/-- **A 2-face lies in at least three facets.** -/
theorem IsCSPolytope5.three_le_up {Q : Set E5} (hQ : Q ∈ faces P) (h2 : dim Q = 2) :
    3 ≤ {F | F ∈ faces P ∧ Q ⊆ F ∧ dim F = 4}.ncard := by
  have hne : Q ≠ P := fun h => by have := hP.dim_self; rw [← h, h2] at this; omega
  rw [hP.ncard_up hQ hne 4 le_rfl]
  obtain ⟨W, hW, hmem, hdim⟩ := hP.dualFace_facts hQ hne
  rw [hW]
  exact three_le_cnt_zero_of_dim_two hmem (by omega)

theorem IsCSPolytope5.three_le_cnt {Q : Set E5} (hQ : Q ∈ faces P) (h2 : dim Q = 2) :
    3 ≤ cnt P Q 0 := by
  obtain ⟨V, hV⟩ := hP.polytope
  have hQ' : Q ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hQ
  have := three_le_cnt_zero_of_dim_two hQ' h2
  rwa [← hV] at this

/-! ### Double counting of flags -/

lemma IsCSPolytope5.up_finite (G : Set E5) (k : ℕ) :
    {H | H ∈ faces P ∧ G ⊆ H ∧ dim H = k}.Finite :=
  hP.faces_finite.subset fun H hH => hH.1

/-- `flag2 P i j = Σ_{i-faces G} #{j-faces above G}`. -/
lemma IsCSPolytope5.flag2_eq_sum_up (i j : ℕ) :
    flag2 P i j = ∑ G ∈ (hP.kfaces_finite i).toFinset,
      {H | H ∈ faces P ∧ G ⊆ H ∧ dim H = j}.ncard := by
  classical
  have hS : {FG : Set E5 × Set E5 | FG.1 ∈ faces P ∧ FG.2 ∈ faces P ∧ FG.1 ⊆ FG.2 ∧
      dim FG.1 = i ∧ dim FG.2 = j}.Finite :=
    (hP.faces_finite.prod hP.faces_finite).subset fun FG h => ⟨h.1, h.2.1⟩
  rw [flag2, Set.ncard_eq_toFinset_card _ hS,
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := (hP.kfaces_finite i).toFinset)
      (fun FG hFG => by
        rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hFG
        rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        exact ⟨hFG.1, hFG.2.2.2.1⟩)]
  refine Finset.sum_congr rfl fun G hG => ?_
  rw [Set.Finite.mem_toFinset] at hG
  rw [Set.ncard_eq_toFinset_card _ (hP.up_finite G j)]
  refine Finset.card_nbij' Prod.snd (fun H => (G, H)) ?_ ?_ ?_ ?_
  · intro FG hFG
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset] at hFG
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    obtain ⟨⟨-, h2, h3, -, h5⟩, h⟩ := hFG
    exact ⟨h2, h ▸ h3, h5⟩
  · intro H hH
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hH
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hG.1, hH.1, hH.2.1, hG.2, hH.2.2⟩, rfl⟩
  · intro FG hFG
    rw [Finset.mem_coe, Finset.mem_filter] at hFG
    obtain ⟨-, h⟩ := hFG
    ext <;> simp [h]
  · intro H _; rfl

lemma IsCSPolytope5.flag3_finite (i j k : ℕ) :
    {FGH : Set E5 × Set E5 × Set E5 | FGH.1 ∈ faces P ∧ FGH.2.1 ∈ faces P ∧
      FGH.2.2 ∈ faces P ∧ FGH.1 ⊆ FGH.2.1 ∧ FGH.2.1 ⊆ FGH.2.2 ∧
      dim FGH.1 = i ∧ dim FGH.2.1 = j ∧ dim FGH.2.2 = k}.Finite :=
  (hP.faces_finite.prod (hP.faces_finite.prod hP.faces_finite)).subset
    fun FGH h => ⟨h.1, h.2.1, h.2.2.1⟩

/-- `flag3 P i j k = Σ_{k-faces H} #{(F, G) : F ⊆ G ⊆ H}`. -/
lemma IsCSPolytope5.flag3_eq_sum_last (i j k : ℕ) :
    flag3 P i j k = ∑ H ∈ (hP.kfaces_finite k).toFinset, incid P H i j := by
  classical
  rw [flag3, Set.ncard_eq_toFinset_card _ (hP.flag3_finite i j k),
    Finset.card_eq_sum_card_fiberwise (f := fun FGH => FGH.2.2)
      (t := (hP.kfaces_finite k).toFinset)
      (fun FGH hFGH => by
        rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hFGH
        rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        exact ⟨hFGH.2.2.1, hFGH.2.2.2.2.2.2.2⟩)]
  refine Finset.sum_congr rfl fun H hH => ?_
  rw [Set.Finite.mem_toFinset] at hH
  have hfin : {GH : Set E5 × Set E5 | GH.1 ∈ faces P ∧ GH.2 ∈ faces P ∧ GH.1 ⊆ GH.2 ∧
      GH.2 ⊆ H ∧ dim GH.1 = i ∧ dim GH.2 = j}.Finite :=
    (hP.faces_finite.prod hP.faces_finite).subset fun GH h => ⟨h.1, h.2.1⟩
  rw [incid, Set.ncard_eq_toFinset_card _ hfin]
  refine Finset.card_nbij' (fun FGH => (FGH.1, FGH.2.1)) (fun FG => (FG.1, FG.2, H))
    ?_ ?_ ?_ ?_
  · intro FGH hFGH
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset] at hFGH
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    obtain ⟨⟨h1, h2, -, h4, h5, h6, h7, -⟩, h⟩ := hFGH
    exact ⟨h1, h2, h4, h ▸ h5, h6, h7⟩
  · intro FG hFG
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hFG
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hFG.1, hFG.2.1, hH.1, hFG.2.2.1, hFG.2.2.2.1, hFG.2.2.2.2.1, hFG.2.2.2.2.2,
      hH.2⟩, rfl⟩
  · intro FGH hFGH
    rw [Finset.mem_coe, Finset.mem_filter] at hFGH
    obtain ⟨-, h⟩ := hFGH
    ext <;> simp [h]
  · intro FG _; rfl

/-- `flag3 P i j k = Σ_{j-faces G} #{i-faces in G} · #{k-faces above G}`. -/
lemma IsCSPolytope5.flag3_eq_sum_mid (i j k : ℕ) :
    flag3 P i j k = ∑ G ∈ (hP.kfaces_finite j).toFinset,
      cnt P G i * {H | H ∈ faces P ∧ G ⊆ H ∧ dim H = k}.ncard := by
  classical
  rw [flag3, Set.ncard_eq_toFinset_card _ (hP.flag3_finite i j k),
    Finset.card_eq_sum_card_fiberwise (f := fun FGH => FGH.2.1)
      (t := (hP.kfaces_finite j).toFinset)
      (fun FGH hFGH => by
        rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hFGH
        rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        exact ⟨hFGH.2.1, hFGH.2.2.2.2.2.2.1⟩)]
  refine Finset.sum_congr rfl fun G hG => ?_
  rw [Set.Finite.mem_toFinset] at hG
  rw [cnt, Set.ncard_eq_toFinset_card _ (hP.below_finite G i),
    Set.ncard_eq_toFinset_card _ (hP.up_finite G k), ← Finset.card_product]
  refine Finset.card_nbij' (fun FGH => (FGH.1, FGH.2.2)) (fun FH => (FH.1, G, FH.2))
    ?_ ?_ ?_ ?_
  · intro FGH hFGH
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset] at hFGH
    rw [Finset.mem_coe, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    obtain ⟨⟨h1, -, h3, h4, h5, h6, -, h8⟩, h⟩ := hFGH
    exact ⟨⟨h1, h ▸ h4, h6⟩, h3, h ▸ h5, h8⟩
  · intro FH hFH
    rw [Finset.mem_coe, Finset.mem_product, Set.Finite.mem_toFinset,
      Set.Finite.mem_toFinset] at hFH
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hFH.1.1, hG.1, hFH.2.1, hFH.1.2.1, hFH.2.2.1, hFH.1.2.2, hG.2, hFH.2.2.2⟩, rfl⟩
  · intro FGH hFGH
    rw [Finset.mem_coe, Finset.mem_filter] at hFGH
    obtain ⟨-, h⟩ := hFGH
    ext <;> simp [h]
  · intro FH _; rfl

/-! ### The obligations -/

/-- **Every 3-face lies in exactly two facets**: `Σ r = 2 f₃`. -/
theorem IsCSPolytope5.facetRows_sum_r : ((facetRows P).map Row.r).sum = 2 * fvec P 3 := by
  rw [hP.facetRows_sum Row.r]
  change ∑ F ∈ (hP.kfaces_finite 4).toFinset, cnt P F 3 = _
  rw [← hP.flag2_eq_sum 3 4, hP.flag2_eq_sum_up 3 4]
  have hconst : ∀ T ∈ (hP.kfaces_finite 3).toFinset,
      {H | H ∈ faces P ∧ T ⊆ H ∧ dim H = 4}.ncard = 2 := by
    intro T hT
    rw [Set.Finite.mem_toFinset] at hT
    exact hP.ridge_two hT.1 hT.2
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, fvec,
    Set.ncard_eq_toFinset_card _ (hP.kfaces_finite 3)]
  ring

/-- `Σ J = 2 f₀₃`. -/
theorem IsCSPolytope5.facetRows_sum_J : ((facetRows P).map Row.J).sum = 2 * flag2 P 0 3 := by
  rw [hP.facetRows_sum Row.J]
  change ∑ F ∈ (hP.kfaces_finite 4).toFinset, incid P F 0 3 = _
  rw [← hP.flag3_eq_sum_last 0 3 4, hP.flag3_eq_sum_mid 0 3 4, hP.flag2_eq_sum 0 3,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Set.Finite.mem_toFinset] at hT
  rw [hP.ridge_two hT.1 hT.2]; ring

/-- **`A ≥ 0`**: `A = Σ_Q (f₀(Q) - 3)(#facets ⊇ Q - 3)`. -/
theorem IsCSPolytope5.A_nonneg : 0 ≤ (flagDataOf P).A := by
  have hA : (flagDataOf P).A = ∑ Q ∈ (hP.kfaces_finite 2).toFinset,
      ((cnt P Q 0 : ℤ) - 3) * (({F | F ∈ faces P ∧ Q ⊆ F ∧ dim F = 4}.ncard : ℤ) - 3) := by
    simp only [FlagData.A, flagDataOf]
    rw [hP.flag3_eq_sum_mid 0 2 4, hP.flag2_eq_sum 0 2, hP.flag2_eq_sum_up 2 4, fvec,
      Set.ncard_eq_toFinset_card _ (hP.kfaces_finite 2)]
    push_cast
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Q _ => ?_
    push_cast; ring
  rw [hA]
  refine Finset.sum_nonneg fun Q hQ => ?_
  rw [Set.Finite.mem_toFinset] at hQ
  have h1 := hP.three_le_cnt hQ.1 hQ.2
  have h2 := hP.three_le_up hQ.1 hQ.2
  exact mul_nonneg (by omega) (by omega)

end Kalai5
