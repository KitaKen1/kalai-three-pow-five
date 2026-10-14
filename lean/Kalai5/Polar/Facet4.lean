import Kalai5.Polar.Relative

/-!
# Vertex figures of 4-polytopes and the local toric `g` of a facet

* `upIn_codim_four`: through polarity, the faces containing a face of codimension four form the
  face lattice of a 3-polytope, so `#(dim G + 1) - #(dim G + 2) + #(dim G + 3) = 2`;
* `vertex_up_dim_four`: in a 4-dimensional polytope every vertex lies in `e_v` edges, `t_v`
  2-faces and `r_v` 3-faces with `e_v - t_v + r_v = 2` (relative polarity);
* for a facet `F` of a centrally symmetric 5-polytope: Euler `f₀ - f₁ + f₂ - f₃ = 0`, the
  summed vertex-figure relation `f₀₁ - f₀₂ + f₀₃ = 2 f₀`, and hence (`IsCSPolytope5.facet_g_eq`)

  `g(F) = J - 3n - 3r + 10 = f₁(F) + f₀₂(F) - 3 f₂(F) - 4 f₀(F) + 10`,

  the toric `g₂` written through the number `f₁ + f₀₂ - 3f₂` of bars of a triangulated
  2-skeleton.
-/

namespace Kalai5

open Set

variable {d : ℕ}

/-- At a face of codimension four the upper interval is the face lattice of a 3-polytope. -/
theorem upIn_codim_four {V : Finset (E d)}
    (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d))))
    {G : Set (E d)} (hG : G ∈ faces (convexHull ℝ (V : Set (E d)))) (hcod : dim G + 4 = d) :
    (upIn (convexHull ℝ (V : Set (E d))) G (dim G + 1) : ℤ)
      - upIn (convexHull ℝ (V : Set (E d))) G (dim G + 2)
      + upIn (convexHull ℝ (V : Set (E d))) G (dim G + 3) = 2 := by
  have hdimK : dim (convexHull ℝ (V : Set (E d))) = d :=
    dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0⟩
  have hne : G ≠ convexHull ℝ (V : Set (E d)) := fun h => by
    rw [h, hdimK] at hcod; omega
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have hmem := dualFace_mem_faces h0 hG hne
  have hdim := dim_dualFace h0 hG hne
  rw [hW] at hmem
  have hX3 : dim (dualFace (convexHull ℝ (V : Set (E d))) G) = 3 := by omega
  rw [upIn_eq_cnt_dualFace h0 hG hne _ (by omega), upIn_eq_cnt_dualFace h0 hG hne _ (by omega),
    upIn_eq_cnt_dualFace h0 hG hne _ (by omega),
    show d - 1 - (dim G + 1) = 2 by omega, show d - 1 - (dim G + 2) = 1 by omega,
    show d - 1 - (dim G + 3) = 0 by omega, hW]
  have he := euler_face_conv hmem
  have hc := cnt_self_conv hmem
  rw [hX3] at he hc
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at he
  rw [hc] at he
  norm_num at he
  linarith

/-- **Vertex figures of 4-polytopes**: `e_v - t_v + r_v = 2`. -/
theorem vertex_up_dim_four {K : Set (E d)} {V : Finset (E d)}
    (hK : K = convexHull ℝ (V : Set (E d))) (h4 : dim K = 4) {v : Set (E d)} (hv : v ∈ faces K)
    (hv0 : dim v = 0) :
    (upIn K v 1 : ℤ) - upIn K v 2 + upIn K v 3 = 2 := by
  obtain ⟨p, hp, V', hV', h0⟩ := exists_good_affEmb hK (hv.1.mono (face_subset hv))
  have hvr := subset_range_affEmb hp (face_subset hv)
  have hvv : affEmb K p '' (affEmb K p ⁻¹' v) = v := Set.image_preimage_eq_of_subset hvr
  have hv' : affEmb K p ⁻¹' v ∈ faces (convexHull ℝ (V' : Set (E (dim K)))) :=
    hV' ▸ preimage_mem_faces hp hv
  have hdv : dim (affEmb K p ⁻¹' v) = 0 := by
    have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' v)
    rw [hvv, hv0] at this
    omega
  have key := upIn_codim_four h0 hv' (by omega)
  simp only [hdv, zero_add] at key
  rw [← hvv, upIn_affEmb hp, upIn_affEmb hp, upIn_affEmb hp, hV']
  exact key

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Euler's relation for a facet: `f₀ - f₁ + f₂ - f₃ = 0`. -/
lemma IsCSPolytope5.facet_euler {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    (cnt P F 0 : ℤ) - cnt P F 1 + cnt P F 2 - cnt P F 3 = 0 := by
  have he := hP.euler_face hF
  have hc := hP.cnt_self hF
  rw [h4] at he hc
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at he
  rw [hc] at he
  norm_num at he
  linarith

/-- Vertex figures inside a facet: `e_v - t_v + r_v = 2` for `v ⊆ F`. -/
lemma IsCSPolytope5.vertex_in_facet {F v : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hv : v ∈ faces P) (hvF : v ⊆ F) (hv0 : dim v = 0) :
    ({E | E ∈ faces P ∧ v ⊆ E ∧ E ⊆ F ∧ dim E = 1}.ncard : ℤ)
      - {E | E ∈ faces P ∧ v ⊆ E ∧ E ⊆ F ∧ dim E = 2}.ncard
      + {E | E ∈ faces P ∧ v ⊆ E ∧ E ⊆ F ∧ dim E = 3}.ncard = 2 := by
  classical
  obtain ⟨V, hV⟩ := hP.polytope
  have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
  have hFV : F = convexHull ℝ ((V.filter (· ∈ F) : Finset E5) : Set E5) :=
    face_eq_convexHull_filter hF'
  have hvF' : v ∈ faces F := (mem_faces_face_iff hF').2 ⟨hV ▸ hv, hvF⟩
  have key := vertex_up_dim_four hFV h4 hvF' hv0
  have hup : ∀ j, upIn F v j = {E | E ∈ faces P ∧ v ⊆ E ∧ E ⊆ F ∧ dim E = j}.ncard := by
    intro j
    unfold upIn
    congr 1
    ext E
    simp only [Set.mem_ofPred_eq, mem_faces_face_iff hF', ← hV]
    tauto
  rw [hup, hup, hup] at key
  exact key

/-- Summed vertex figures of a facet: `f₀₁ - f₀₂ + f₀₃ = 2 f₀`. -/
lemma IsCSPolytope5.facet_vertex_sum {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    (incid P F 0 1 : ℤ) - incid P F 0 2 + incid P F 0 3 = 2 * cnt P F 0 := by
  rw [hP.incid_eq_sum_first F 0 1, hP.incid_eq_sum_first F 0 2, hP.incid_eq_sum_first F 0 3,
    cnt, Set.ncard_eq_toFinset_card _ (hP.below_finite F 0)]
  push_cast
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones,
    Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Set.Finite.mem_toFinset] at hv
  rw [hP.vertex_in_facet hF h4 hv.1 hv.2.1 hv.2.2]
  norm_num

/-- **The local toric `g` of a facet** through bar counts of a triangulated 2-skeleton:
`g(F) = f₁ + f₀₂ - 3 f₂ - 4 f₀ + 10`. -/
theorem IsCSPolytope5.facet_g_eq {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    (faceRow P F).g = (cnt P F 1 : ℤ) + incid P F 0 2 - 3 * cnt P F 2 - 4 * cnt P F 0 + 10 := by
  have h1 := hP.facet_euler hF h4
  have h2 := hP.facet_vertex_sum hF h4
  have h3 : (incid P F 0 1 : ℤ) = 2 * cnt P F 1 := by exact_mod_cast hP.incid_zero_one F
  simp only [Row.g, faceRow]
  linarith

end cs

end Kalai5
