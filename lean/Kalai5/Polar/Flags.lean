import Kalai5.Polar.Faces

/-!
# Flags under polarity

`(G, H) ↦ (H♦, G♦)` reverses flags, so `flag2 P° (4 - j) (4 - i) = flag2 P i j` for a centrally
symmetric 5-polytope.  Consequences: `G*(P) = G(P°)`, `C(P) = B(P°)`, and the `f₁₄` identity of
`P` is the `f₀₃` identity of `P°`.
-/

namespace Kalai5

open Set

variable {d : ℕ}

lemma dualFace_antitone {K F G : Set (E d)} (h : F ⊆ G) : dualFace K G ⊆ dualFace K F :=
  fun _ hy => ⟨hy.1, fun x hx => hy.2 x (h hx)⟩

lemma flag2_le_flag2_polarSet {V : Finset (E d)}
    (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d)))) (i j : ℕ) (hj : j + 1 ≤ d) :
    flag2 (convexHull ℝ (V : Set (E d))) i j ≤
      flag2 (polarSet (convexHull ℝ (V : Set (E d)))) (d - 1 - j) (d - 1 - i) := by
  set K := convexHull ℝ (V : Set (E d))
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have hpoly : IsPolytope (polarSet K) := ⟨⟨W, hW⟩, ⟨0, zero_mem_interior_polarSet V⟩⟩
  have hdimK : dim K = d := dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0⟩
  have hfin := faces_finite hpoly
  refine Set.ncard_le_ncard_of_injOn (fun GH : Set (E d) × Set (E d) =>
      (dualFace K GH.2, dualFace K GH.1)) ?_ ?_
    ((hfin.prod hfin).subset fun GH h => ⟨h.1, h.2.1⟩)
  · rintro ⟨G, H⟩ hGH₀
    obtain ⟨hG, hH, hGH, hi, hjH⟩ := hGH₀
    dsimp only at hG hH hGH hi hjH ⊢
    have hneH : H ≠ K := fun h => by rw [h] at hjH; omega
    have hneG : G ≠ K := fun h => by
      rw [h] at hGH
      exact hneH (Set.Subset.antisymm (face_subset hH) hGH)
    have e1 := dim_dualFace h0 hH hneH
    have e2 := dim_dualFace h0 hG hneG
    change dim (dualFace K H) + dim H + 1 = d at e1
    change dim (dualFace K G) + dim G + 1 = d at e2
    exact ⟨dualFace_mem_faces h0 hH hneH, dualFace_mem_faces h0 hG hneG,
      dualFace_antitone hGH, by dsimp only; omega, by dsimp only; omega⟩
  · rintro ⟨G, H⟩ hGH₀ ⟨G', H'⟩ hGH₀' heq
    obtain ⟨hG, hH, hGH, hi, hjH⟩ := hGH₀
    obtain ⟨hG', hH', hGH', hi', hjH'⟩ := hGH₀'
    dsimp only at hG hH hGH hi hjH hG' hH' hGH' hi' hjH' heq
    simp only [Prod.mk.injEq] at heq
    have hneH : ∀ {H}, H ∈ faces K → dim H = j → H ≠ K := fun _ hd h => by
      rw [h] at hd; omega
    have hneG : ∀ {G H}, G ∈ faces K → H ∈ faces K → G ⊆ H → dim H = j → G ≠ K :=
      fun hG hH hGH hd h => by
        rw [h] at hGH
        exact hneH hH hd (Set.Subset.antisymm (face_subset hH) hGH)
    have eH : H = H' := by
      have e1 := eq_of_dualFace h0 hH (hneH hH hjH)
      have e2 := eq_of_dualFace h0 hH' (hneH hH' hjH')
      rw [heq.1] at e1
      exact e1.trans e2.symm
    have eG : G = G' := by
      have e1 := eq_of_dualFace h0 hG (hneG hG hH hGH hjH)
      have e2 := eq_of_dualFace h0 hG' (hneG hG' hH' hGH' hjH')
      rw [heq.2] at e1
      exact e1.trans e2.symm
    rw [eG, eH]

/-! ### Centrally symmetric 5-polytopes -/

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.flag2_le_flag2_polar (i j : ℕ) (hj : j ≤ 4) :
    flag2 P i j ≤ flag2 (polarSet P) (4 - j) (4 - i) := by
  obtain ⟨V, hV⟩ := hP.polytope
  have h0 : (0 : E5) ∈ interior (convexHull ℝ (V : Set E5)) := hV ▸ hP.zero_mem_interior
  have := flag2_le_flag2_polarSet h0 i j (by omega)
  rw [← hV] at this
  simpa using this

/-- **Polarity reverses flags**: `f_{4-j, 4-i}(P°) = f_{i,j}(P)` (`i ≤ 4`, `j ≤ 4`). -/
theorem IsCSPolytope5.flag2_polar (i j : ℕ) (hi : i ≤ 4) (hj : j ≤ 4) :
    flag2 (polarSet P) (4 - j) (4 - i) = flag2 P i j := by
  have h1 := hP.flag2_le_flag2_polar i j hj
  have h2 := hP.polar.flag2_le_flag2_polar (4 - j) (4 - i) (by omega)
  rw [hP.polarSet_polarSet, show 4 - (4 - i) = i by omega, show 4 - (4 - j) = j by omega] at h2
  omega

lemma IsCSPolytope5.G_polar : (flagDataOf (polarSet P)).G = (flagDataOf P).Gs := by
  have e1 := hP.fvec_polar 3 (by norm_num)
  have e2 := hP.fvec_polar 2 (by norm_num)
  have e4 := hP.fvec_polar 4 (by norm_num)
  have f24 := hP.flag2_polar 2 4 (by norm_num) le_rfl
  norm_num at e1 e2 e4 f24
  simp only [FlagData.G, FlagData.Gs, flagDataOf, e1, e2, e4, f24]

lemma IsCSPolytope5.B_polar : (flagDataOf (polarSet P)).B = (flagDataOf P).C := by
  have f13 := hP.flag2_polar 1 3 (by norm_num) (by norm_num)
  have f14 := hP.flag2_polar 1 4 (by norm_num) le_rfl
  norm_num at f13 f14
  simp only [FlagData.B, FlagData.C, flagDataOf, f13, f14]

/-- The `f₁₄` identity of `P` is the `f₀₃` identity of `P°`. -/
lemma IsCSPolytope5.flag14_of_polar
    (h03 : (flag2 (polarSet P) 0 3 : ℤ) =
      flag2 (polarSet P) 0 4 + flag2 (polarSet P) 0 2 - 2 * fvec (polarSet P) 1) :
    (flag2 P 1 4 : ℤ) = flag2 P 0 4 + flag2 P 2 4 - 2 * fvec P 3 := by
  have f03 := hP.flag2_polar 1 4 (by norm_num) le_rfl
  have f04 := hP.flag2_polar 0 4 (by norm_num) le_rfl
  have f02 := hP.flag2_polar 2 4 (by norm_num) le_rfl
  have e1 := hP.fvec_polar 3 (by norm_num)
  norm_num at f03 f04 f02 e1
  rw [f03, f04, f02, e1] at h03
  exact h03

end Kalai5
