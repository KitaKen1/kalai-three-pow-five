import Kalai5.Endpoints.Fake8Parity

/-!
# The 3-faces of a facet with at most seven 3-faces

The polar of a facet `F` with at most seven 3-faces is a 4-polytope with at most seven vertices, so
its extended row is in the catalogue `smallRowsX`.  The vertices of the polar with face numbers
`(e, p, r)` above are the duals of the 3-faces of `F` with face numbers `(r, p, e)` below
(`vertCnt_polar`), so the vertex profile of the catalogued polar counts the 3-faces of `F` by type
(`IsCSPolytope5.facet_types_r7`).
-/

namespace Kalai5

open Set

open scoped Classical

variable {d : ℕ}

/-- **Polarity of profiles**: the vertices of the polar with face numbers `t` above correspond to the
3-faces with the reversed face numbers below. -/
lemma vertCnt_polar {n : ℕ} (hn : n = 4) {V : Finset (E n)}
    (h0 : (0 : E n) ∈ interior (convexHull ℝ (V : Set (E n)))) (t : ℕ × ℕ × ℕ) :
    vertCnt (polarSet (convexHull ℝ (V : Set (E n)))) t =
      facetCnt (convexHull ℝ (V : Set (E n))) (t.2.2, t.2.1, t.1) := by
  subst hn
  obtain ⟨t1, t2, t3⟩ := t
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have h0W : (0 : E 4) ∈ interior (convexHull ℝ (W : Set (E 4))) :=
    hW ▸ zero_mem_interior_polarSet V
  have hbip : polarSet (convexHull ℝ (W : Set (E 4))) = convexHull ℝ (V : Set (E 4)) := by
    rw [← hW]
    exact polarSet_polarSet (convex_convexHull ℝ _)
      (Set.Finite.isClosed_convexHull ℝ V.finite_toSet) (interior_subset h0)
  have hdimK : dim (convexHull ℝ (V : Set (E 4))) = 4 :=
    dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0⟩
  have hdimW : dim (convexHull ℝ (W : Set (E 4))) = 4 :=
    dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0W⟩
  unfold vertCnt facetCnt
  rw [hW]
  symm
  refine Set.ncard_congr (fun G _ => dualFace (convexHull ℝ (V : Set (E 4))) G) ?_ ?_ ?_
  · rintro G ⟨hG, hd, hk⟩
    have hne : G ≠ convexHull ℝ (V : Set (E 4)) := fun h => by rw [h, hdimK] at hd; omega
    have hmem := dualFace_mem_faces h0 hG hne
    have hdd := dim_dualFace h0 hG hne
    rw [hW] at hmem
    have hd0 : dim (dualFace (convexHull ℝ (V : Set (E 4))) G) = 0 := by omega
    have hneH : dualFace (convexHull ℝ (V : Set (E 4))) G ≠ convexHull ℝ (W : Set (E 4)) :=
      fun h => by rw [h, hdimW] at hd0; omega
    refine ⟨hmem, hd0, ?_⟩
    have hGG := dualFace_dualFace h0 hG hne
    rw [hW] at hGG
    have hup : ∀ j, j ≤ 3 → upIn (convexHull ℝ (W : Set (E 4)))
        (dualFace (convexHull ℝ (V : Set (E 4))) G) j =
        cnt (convexHull ℝ (V : Set (E 4))) G (3 - j) := by
      intro j hj
      rw [upIn_eq_cnt_dualFace h0W hmem hneH j (by omega), hbip, hGG]
    simp only [triAbove, triBelow, Prod.mk.injEq] at hk ⊢
    rw [hup 1 (by norm_num), hup 2 (by norm_num), hup 3 (by norm_num),
      show (3 : ℕ) - 1 = 2 from rfl, show (3 : ℕ) - 2 = 1 from rfl, show (3 : ℕ) - 3 = 0 from rfl]
    exact ⟨hk.2.2, hk.2.1, hk.1⟩
  · intro G G' hGm hG'm heq
    obtain ⟨hG, hd, -⟩ := hGm
    obtain ⟨hG', hd', -⟩ := hG'm
    have hne : G ≠ convexHull ℝ (V : Set (E 4)) := fun h => by rw [h, hdimK] at hd; omega
    have hne' : G' ≠ convexHull ℝ (V : Set (E 4)) := fun h => by rw [h, hdimK] at hd'; omega
    have e1 := dualFace_dualFace h0 hG hne
    have e2 := dualFace_dualFace h0 hG' hne'
    have heq' : dualFace (convexHull ℝ (V : Set (E 4))) G =
        dualFace (convexHull ℝ (V : Set (E 4))) G' := heq
    rw [heq'] at e1
    exact e1.symm.trans e2
  · rintro H ⟨hH, hd, hk⟩
    have hneH : H ≠ convexHull ℝ (W : Set (E 4)) := fun h => by rw [h, hdimW] at hd; omega
    have hmem := dualFace_mem_faces h0W hH hneH
    have hdd := dim_dualFace h0W hH hneH
    rw [hbip] at hmem
    have hd3 : dim (dualFace (convexHull ℝ (W : Set (E 4))) H) = 3 := by omega
    have hHH := dualFace_dualFace h0W hH hneH
    rw [hbip] at hHH
    refine ⟨dualFace (convexHull ℝ (W : Set (E 4))) H, ⟨hmem, hd3, ?_⟩, hHH⟩
    have hup : ∀ j, j ≤ 3 → upIn (convexHull ℝ (W : Set (E 4))) H j =
        cnt (convexHull ℝ (V : Set (E 4))) (dualFace (convexHull ℝ (W : Set (E 4))) H) (3 - j) := by
      intro j hj
      rw [upIn_eq_cnt_dualFace h0W hH hneH j (by omega), hbip]
    simp only [triAbove, triBelow, Prod.mk.injEq] at hk ⊢
    rw [hup 1 (by norm_num), hup 2 (by norm_num), hup 3 (by norm_num),
      show (3 : ℕ) - 1 = 2 from rfl, show (3 : ℕ) - 2 = 1 from rfl,
      show (3 : ℕ) - 3 = 0 from rfl] at hk
    exact ⟨hk.2.2, hk.2.1, hk.1⟩

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **Types of the 3-faces of a facet with at most seven 3-faces**: its polar is catalogued, with the
dual row, and the vertex profile of the polar counts the 3-faces by reversed face numbers. -/
theorem IsCSPolytope5.facet_types_r7 {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hr : cnt P F 3 ≤ 7) :
    ∃ X ∈ smallRowsX, X.1 = ⟨cnt P F 3, cnt P F 2, cnt P F 1, cnt P F 0, incid P F 0 3⟩ ∧
      X.2.2 = fv7.map (fun t => tcnt P F (t.2.2, t.2.1, t.1)) := by
  obtain ⟨V, hV⟩ := hP.polytope
  have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
  have hFS : F = convexHull ℝ ((V.filter (· ∈ F) : Finset E5) : Set E5) :=
    face_eq_convexHull_filter hF'
  have hrowF : rowOf F = faceRow P F := by rw [rowOf_face hF', ← hV]
  obtain ⟨p, hp, V', hV', h0⟩ := exists_good_affEmb hFS hF.1
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have h0W : (0 : E (dim F)) ∈ interior (convexHull ℝ (W : Set (E (dim F)))) :=
    hW ▸ zero_mem_interior_polarSet V'
  have hdimW : dim (convexHull ℝ (W : Set (E (dim F)))) = 4 := by
    rw [dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0W⟩, h4]
  have hfv : ∀ j, fvec (convexHull ℝ (V' : Set (E (dim F)))) j = fvec F j := fun j => by
    rw [← hV', ← fvec_affEmb hp]
  have hfl : flag2 (convexHull ℝ (V' : Set (E (dim F)))) 0 3 = flag2 F 0 3 := by
    rw [← hV', ← flag2_affEmb hp]
  have hrowW : rowOf (convexHull ℝ (W : Set (E (dim F)))) =
      ⟨cnt P F 3, cnt P F 2, cnt P F 1, cnt P F 0, incid P F 0 3⟩ := by
    have e0 := fvec_polarSet_eq h0 3 (by omega)
    have e1 := fvec_polarSet_eq h0 2 (by omega)
    have e2 := fvec_polarSet_eq h0 1 (by omega)
    have e3 := fvec_polarSet_eq h0 0 (by omega)
    have eJ := flag2_polarSet_eq h0 0 3 (by omega) (by omega)
    rw [hW] at e0 e1 e2 e3 eJ
    rw [show dim F - 1 - 3 = 0 by omega] at e0 eJ
    rw [show dim F - 1 - 2 = 1 by omega] at e1
    rw [show dim F - 1 - 1 = 2 by omega] at e2
    rw [show dim F - 1 - 0 = 3 by omega] at e3 eJ
    have hz := hrowF
    simp only [rowOf, faceRow, Row.mk.injEq] at hz
    simp only [rowOf, e0, e1, e2, e3, eJ, hfv, hfl, hz]
  have hreal : IsRealRowX (rowXOf (convexHull ℝ (W : Set (E (dim F))))) :=
    ⟨dim F, _, ⟨W, rfl⟩, hdimW, rfl⟩
  have hmem := smallX_classification _ hreal (by
    show (rowOf (convexHull ℝ (W : Set (E (dim F))))).n ≤ 7
    rw [hrowW]
    exact hr)
  refine ⟨_, hmem, hrowW, ?_⟩
  show fv7.map (vertCnt (convexHull ℝ (W : Set (E (dim F))))) = _
  refine List.map_congr_left fun t _ => ?_
  rw [← hW, vertCnt_polar h4 h0 t, ← hV', ← facetCnt_affEmb hp, hP.facetCnt_eq_card hF,
    hP.tcnt_eq_card]

end cs

end Kalai5
