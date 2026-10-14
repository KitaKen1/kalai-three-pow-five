import Kalai5.Rows.Degree

/-!
# Upper intervals in 4-polytopes

For a 4-polytope `K` (not necessarily full-dimensional in its ambient space):

* `vertex_four_le_r`: a vertex lies in at least four facets (the dual face is a 3-polytope, which
  has at least four vertices);
* `two_face_up_two`: a 2-face lies in exactly two facets (the dual face is a segment);
* `edge_three_le_up`: an edge lies in at least three facets (the upper interval is a polygon).
-/

namespace Kalai5

open Set

variable {d : ℕ}

/-- At a face of codimension four, at least four facets. -/
theorem upIn_codim_four_ge {V : Finset (E d)}
    (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d))))
    {G : Set (E d)} (hG : G ∈ faces (convexHull ℝ (V : Set (E d)))) (hcod : dim G + 4 = d) :
    4 ≤ upIn (convexHull ℝ (V : Set (E d))) G (dim G + 3) := by
  classical
  have hdimK : dim (convexHull ℝ (V : Set (E d))) = d :=
    dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0⟩
  have hne : G ≠ convexHull ℝ (V : Set (E d)) := fun h => by
    rw [h, hdimK] at hcod; omega
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have hmem := dualFace_mem_faces h0 hG hne
  have hdim := dim_dualFace h0 hG hne
  rw [hW] at hmem
  set X := dualFace (convexHull ℝ (V : Set (E d))) G with hXdef
  have hX3 : dim X = 3 := by omega
  rw [upIn_eq_cnt_dualFace h0 hG hne _ (by omega), show d - 1 - (dim G + 3) = 0 by omega, hW,
    ← fvec_face_eq_cnt hmem]
  have hX := face_eq_convexHull_filter hmem
  have hne' : (W.filter (· ∈ X)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hXne : X.Nonempty := hmem.1
    have h' := hX
    rw [h, Finset.coe_empty, convexHull_empty] at h'
    rw [h'] at hXne
    exact Set.not_nonempty_empty hXne
  rw [hX] at hX3 ⊢
  rw [fvec_zero_eq]
  have := dim_add_one_le_ncard_extremePoints _ hne'
  omega

/-- At a face of codimension two, exactly two facets. -/
theorem upIn_codim_two_eq {V : Finset (E d)}
    (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d))))
    {G : Set (E d)} (hG : G ∈ faces (convexHull ℝ (V : Set (E d)))) (hcod : dim G + 2 = d) :
    upIn (convexHull ℝ (V : Set (E d))) G (dim G + 1) = 2 := by
  classical
  have hdimK : dim (convexHull ℝ (V : Set (E d))) = d :=
    dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0⟩
  have hne : G ≠ convexHull ℝ (V : Set (E d)) := fun h => by
    rw [h, hdimK] at hcod; omega
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have hmem := dualFace_mem_faces h0 hG hne
  have hdim := dim_dualFace h0 hG hne
  rw [hW] at hmem
  rw [upIn_eq_cnt_dualFace h0 hG hne _ (by omega), show d - 1 - (dim G + 1) = 0 by omega, hW]
  exact cnt_zero_of_dim_one hmem (by omega)

/-- **A vertex of a 4-polytope lies in at least four facets.** -/
theorem vertex_four_le_r {K : Set (E d)} {V : Finset (E d)}
    (hK : K = convexHull ℝ (V : Set (E d))) (h4 : dim K = 4) {v : Set (E d)} (hv : v ∈ faces K)
    (hv0 : dim v = 0) : 4 ≤ upIn K v 3 := by
  obtain ⟨p, hp, V', hV', h0⟩ := exists_good_affEmb hK (hv.1.mono (face_subset hv))
  have hvr := subset_range_affEmb hp (face_subset hv)
  have hvv : affEmb K p '' (affEmb K p ⁻¹' v) = v := Set.image_preimage_eq_of_subset hvr
  have hv' : affEmb K p ⁻¹' v ∈ faces (convexHull ℝ (V' : Set (E (dim K)))) :=
    hV' ▸ preimage_mem_faces hp hv
  have hdv : dim (affEmb K p ⁻¹' v) = 0 := by
    have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' v)
    rw [hvv, hv0] at this
    omega
  have key := upIn_codim_four_ge h0 hv' (by omega)
  simp only [hdv, zero_add] at key
  rw [← hvv, upIn_affEmb hp, hV']
  exact key

/-- **A 2-face of a 4-polytope lies in exactly two facets.** -/
theorem two_face_up_two {K : Set (E d)} {V : Finset (E d)}
    (hK : K = convexHull ℝ (V : Set (E d))) (h4 : dim K = 4) {Q : Set (E d)} (hQ : Q ∈ faces K)
    (hQ2 : dim Q = 2) : upIn K Q 3 = 2 := by
  obtain ⟨p, hp, V', hV', h0⟩ := exists_good_affEmb hK (hQ.1.mono (face_subset hQ))
  have hQr := subset_range_affEmb hp (face_subset hQ)
  have hQQ : affEmb K p '' (affEmb K p ⁻¹' Q) = Q := Set.image_preimage_eq_of_subset hQr
  have hQ' : affEmb K p ⁻¹' Q ∈ faces (convexHull ℝ (V' : Set (E (dim K)))) :=
    hV' ▸ preimage_mem_faces hp hQ
  have hdQ : dim (affEmb K p ⁻¹' Q) = 2 := by
    have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' Q)
    rw [hQQ, hQ2] at this
    omega
  have key := upIn_codim_two_eq h0 hQ' (by omega)
  rw [hdQ] at key
  rw [← hQQ, upIn_affEmb hp, hV']
  exact key

/-- **An edge of a 4-polytope lies in at least three facets.** -/
theorem edge_three_le_up {K : Set (E d)} {V : Finset (E d)}
    (hK : K = convexHull ℝ (V : Set (E d))) (h4 : dim K = 4) {L : Set (E d)} (hL : L ∈ faces K)
    (hL1 : dim L = 1) : 3 ≤ upIn K L 3 := by
  obtain ⟨p, hp, V', hV', h0⟩ := exists_good_affEmb hK (hL.1.mono (face_subset hL))
  have hLr := subset_range_affEmb hp (face_subset hL)
  have hLL : affEmb K p '' (affEmb K p ⁻¹' L) = L := Set.image_preimage_eq_of_subset hLr
  have hL' : affEmb K p ⁻¹' L ∈ faces (convexHull ℝ (V' : Set (E (dim K)))) :=
    hV' ▸ preimage_mem_faces hp hL
  have hdL : dim (affEmb K p ⁻¹' L) = 1 := by
    have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' L)
    rw [hLL, hL1] at this
    omega
  have key := upIn_codim_three h0 hL' (by omega)
  rw [hdL] at key
  simp only [Nat.reduceAdd] at key
  rw [← hLL, upIn_affEmb hp, hV']
  omega

end Kalai5
