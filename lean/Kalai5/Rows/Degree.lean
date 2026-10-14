import Kalai5.Rows.Basic
import Kalai5.Polar.Facet4
import Kalai5.Pyramid.Recognition

/-!
# Vertex degrees and the bound `J + 4n ≤ 4e`

* `flag2_eq_sum_cnt_conv`: flags counted from the top face.
* `flag2_zero_one`: the handshake identity `f₀₁ = 2 f₁`.
* `three_fvec_zero_le`: in a 3-polytope every vertex has degree `≥ 3`, so `3 f₀ ≤ 2 f₁`.
* `vertex_three_r_le`: at a vertex of a 4-polytope, `3 r_v ≤ 2 t_v` (facets and 2-faces through
  `v`), by relative polarity: they are the vertices and edges of the dual 3-polytope `v♦`.
* `realRow_B4`: `J + 4n ≤ 4e` for every row of a 4-polytope (vertex figures are 3-polytopes:
  `r_v ≤ 2 e_v - 4`).
-/

namespace Kalai5

open Set

variable {d : ℕ}

/-- `flag2 K i j = Σ_{j-faces H} #{i-faces below H}` for any polytope. -/
lemma flag2_eq_sum_cnt_conv (V : Finset (E d)) (i j : ℕ) :
    flag2 (convexHull ℝ (V : Set (E d))) i j =
      ∑ H ∈ (kfaces_finite_conv V j).toFinset, cnt (convexHull ℝ (V : Set (E d))) H i := by
  classical
  have hfin := faces_finite_convexHull V
  have hS : {FG : Set (E d) × Set (E d) | FG.1 ∈ faces (convexHull ℝ (V : Set (E d))) ∧
      FG.2 ∈ faces (convexHull ℝ (V : Set (E d))) ∧ FG.1 ⊆ FG.2 ∧
      dim FG.1 = i ∧ dim FG.2 = j}.Finite :=
    (hfin.prod hfin).subset fun FG h => ⟨h.1, h.2.1⟩
  rw [flag2, Set.ncard_eq_toFinset_card _ hS,
    Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := (kfaces_finite_conv V j).toFinset)
      (fun FG hFG => by
        rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hFG
        rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        exact ⟨hFG.2.1, hFG.2.2.2.2⟩)]
  refine Finset.sum_congr rfl fun H hH => ?_
  rw [Set.Finite.mem_toFinset] at hH
  have hfinH : {G | G ∈ faces (convexHull ℝ (V : Set (E d))) ∧ G ⊆ H ∧ dim G = i}.Finite :=
    hfin.subset fun G hG => hG.1
  rw [cnt, Set.ncard_eq_toFinset_card _ hfinH]
  refine Finset.card_nbij' Prod.fst (fun G => (G, H)) ?_ ?_ ?_ ?_
  · intro FG hFG
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset] at hFG
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    obtain ⟨⟨h1, -, h3, h4, -⟩, h⟩ := hFG
    exact ⟨h1, h ▸ h3, h4⟩
  · intro G hG
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hG
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hG.1, hH.1, hG.2.1, hG.2.2, hH.2⟩, rfl⟩
  · intro FG hFG
    rw [Finset.mem_coe, Finset.mem_filter] at hFG
    obtain ⟨-, h⟩ := hFG
    ext <;> simp [h]
  · intro G _; rfl

lemma card_kfaces_eq_fvec (V : Finset (E d)) (k : ℕ) :
    (kfaces_finite_conv V k).toFinset.card = fvec (convexHull ℝ (V : Set (E d))) k := by
  rw [fvec, Set.ncard_eq_toFinset_card _ (kfaces_finite_conv V k)]

/-- **Handshake**: every edge has two vertices. -/
lemma flag2_zero_one (V : Finset (E d)) :
    flag2 (convexHull ℝ (V : Set (E d))) 0 1 = 2 * fvec (convexHull ℝ (V : Set (E d))) 1 := by
  rw [flag2_eq_sum_cnt_conv, Finset.sum_congr rfl fun H hH =>
    cnt_zero_of_dim_one ((Set.Finite.mem_toFinset _).1 hH).1 ((Set.Finite.mem_toFinset _).1 hH).2,
    Finset.sum_const, smul_eq_mul, card_kfaces_eq_fvec, mul_comm]

/-- **In a 3-polytope, `3 f₀ ≤ 2 f₁`.** -/
lemma three_fvec_zero_le (V : Finset (E d)) (h3 : dim (convexHull ℝ (V : Set (E d))) = 3) :
    3 * fvec (convexHull ℝ (V : Set (E d))) 0 ≤ 2 * fvec (convexHull ℝ (V : Set (E d))) 1 := by
  rw [← flag2_zero_one, flag2_eq_sum_upIn_conv, ← card_kfaces_eq_fvec, mul_comm,
    ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  exact (vertex_up_dim_three rfl h3 hw.1 hw.2).2

/-- At a face of codimension four, `3 #facets ≤ 2 #ridges` through it (polarity: they are the
vertices and edges of the dual 3-polytope). -/
theorem upIn_codim_four_le {V : Finset (E d)}
    (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d))))
    {G : Set (E d)} (hG : G ∈ faces (convexHull ℝ (V : Set (E d)))) (hcod : dim G + 4 = d) :
    3 * upIn (convexHull ℝ (V : Set (E d))) G (dim G + 3) ≤
      2 * upIn (convexHull ℝ (V : Set (E d))) G (dim G + 2) := by
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
  rw [upIn_eq_cnt_dualFace h0 hG hne _ (by omega), upIn_eq_cnt_dualFace h0 hG hne _ (by omega),
    show d - 1 - (dim G + 3) = 0 by omega, show d - 1 - (dim G + 2) = 1 by omega, hW,
    ← fvec_face_eq_cnt hmem, ← fvec_face_eq_cnt hmem]
  have hX := face_eq_convexHull_filter hmem
  rw [hX] at hX3 ⊢
  exact three_fvec_zero_le _ hX3

/-- **At a vertex of a 4-polytope, `3 r_v ≤ 2 t_v`.** -/
theorem vertex_three_r_le {K : Set (E d)} {V : Finset (E d)}
    (hK : K = convexHull ℝ (V : Set (E d))) (h4 : dim K = 4) {v : Set (E d)} (hv : v ∈ faces K)
    (hv0 : dim v = 0) :
    3 * upIn K v 3 ≤ 2 * upIn K v 2 := by
  obtain ⟨p, hp, V', hV', h0⟩ := exists_good_affEmb hK (hv.1.mono (face_subset hv))
  have hvr := subset_range_affEmb hp (face_subset hv)
  have hvv : affEmb K p '' (affEmb K p ⁻¹' v) = v := Set.image_preimage_eq_of_subset hvr
  have hv' : affEmb K p ⁻¹' v ∈ faces (convexHull ℝ (V' : Set (E (dim K)))) :=
    hV' ▸ preimage_mem_faces hp hv
  have hdv : dim (affEmb K p ⁻¹' v) = 0 := by
    have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' v)
    rw [hvv, hv0] at this
    omega
  have key := upIn_codim_four_le h0 hv' (by omega)
  simp only [hdv, zero_add] at key
  rw [← hvv, upIn_affEmb hp, upIn_affEmb hp, hV']
  exact key

/-- **`J + 4n ≤ 4e` for rows of 4-polytopes** (each vertex figure is a 3-polytope, so a vertex in
`e_v` edges lies in at most `2 e_v - 4` facets). -/
theorem realRow_B4 {R : Row} (hR : IsRealRow R) : R.J + 4 * R.n ≤ 4 * R.e := by
  obtain ⟨d, Q, ⟨V, rfl⟩, hdim, rfl⟩ := hR
  simp only [rowOf]
  have hper : ∀ v ∈ (kfaces_finite_conv V 0).toFinset,
      upIn (convexHull ℝ (V : Set (E d))) v 3 + 4 ≤ 2 * upIn (convexHull ℝ (V : Set (E d))) v 1 := by
    intro v hv
    rw [Set.Finite.mem_toFinset] at hv
    have h1 := vertex_up_dim_four rfl hdim hv.1 hv.2
    have h2 := vertex_three_r_le rfl hdim hv.1 hv.2
    omega
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum,
    ← flag2_eq_sum_upIn_conv, ← flag2_eq_sum_upIn_conv, flag2_zero_one, card_kfaces_eq_fvec] at hsum
  omega

end Kalai5
