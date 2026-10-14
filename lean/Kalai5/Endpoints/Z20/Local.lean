import Kalai5.Rows.SixCount

/-!
# Local facts for the quadrilateral-link inequality

* `upIn_codim_two`, `face_up_codim_two`: in a polytope, a face of codimension two lies in exactly
  two faces of one dimension more (relative polarity: its dual face is an edge).
* `IsCSPolytope5.twoface_in_facet`: a 2-face `Q` of a facet `F` of `P` lies in exactly two
  3-faces `Q ⊆ T ⊆ F`.
* `exc P F = f₀₂(F) - 3 f₂(F) = Σ_{2-faces Q ⊆ F} (f₀(Q) - 3)`, the polygon excess of `F`:
  for a 3-face `T`, `exc P T = 2 f₁(T) - 3 f₂(T)`; for a facet `F`,
  `2 exc P F = Σ_{3-faces T ⊆ F} exc P T`.
-/

namespace Kalai5

open Set

variable {d : ℕ}

section polar

variable {V : Finset (E d)} (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d))))
include h0

/-- At a face of codimension two there are exactly two faces of one dimension more (the dual face
is an edge). -/
theorem upIn_codim_two {G : Set (E d)} (hG : G ∈ faces (convexHull ℝ (V : Set (E d))))
    (hcod : dim G + 2 = d) :
    upIn (convexHull ℝ (V : Set (E d))) G (dim G + 1) = 2 := by
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

end polar

/-- **Faces of codimension two.**  In a polytope (in any `E d`) a face of codimension two lies in
exactly two faces of one dimension more. -/
theorem face_up_codim_two {K : Set (E d)} {V : Finset (E d)}
    (hK : K = convexHull ℝ (V : Set (E d))) {G : Set (E d)} (hG : G ∈ faces K)
    (hcod : dim G + 2 = dim K) : upIn K G (dim G + 1) = 2 := by
  obtain ⟨p, hp, V', hV', h0⟩ := exists_good_affEmb hK (hG.1.mono (face_subset hG))
  have hGr := subset_range_affEmb hp (face_subset hG)
  have hGG : affEmb K p '' (affEmb K p ⁻¹' G) = G := Set.image_preimage_eq_of_subset hGr
  have hG' : affEmb K p ⁻¹' G ∈ faces (convexHull ℝ (V' : Set (E (dim K)))) :=
    hV' ▸ preimage_mem_faces hp hG
  have hdG : dim (affEmb K p ⁻¹' G) = dim G := by
    have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' G)
    rw [hGG] at this
    exact this.symm
  have key := upIn_codim_two h0 hG' (by rw [hdG]; omega)
  rw [hdG] at key
  have htr := upIn_affEmb hp (affEmb K p ⁻¹' G) (dim G + 1)
  rw [hGG, hV'] at htr
  rw [htr]
  exact key

/-- The polygon excess `f₀₂(F) - 3 f₂(F)` of a face `F` of `P`. -/
noncomputable def exc (P F : Set E5) : ℤ := (incid P F 0 2 : ℤ) - 3 * cnt P F 2

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **A 2-face of a facet lies in exactly two of its 3-faces.** -/
theorem IsCSPolytope5.twoface_in_facet {F Q : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hQ : Q ∈ faces P) (hQF : Q ⊆ F) (h2 : dim Q = 2) :
    {T | T ∈ faces P ∧ Q ⊆ T ∧ T ⊆ F ∧ dim T = 3}.ncard = 2 := by
  classical
  obtain ⟨V, hV⟩ := hP.polytope
  have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
  have hFV : F = convexHull ℝ ((V.filter (· ∈ F) : Finset E5) : Set E5) :=
    face_eq_convexHull_filter hF'
  have hQF' : Q ∈ faces F := (mem_faces_face_iff hF').2 ⟨hV ▸ hQ, hQF⟩
  have key := face_up_codim_two hFV hQF' (by rw [h2, h4])
  rw [h2] at key
  rw [← key]
  unfold upIn
  congr 1
  ext T
  simp only [Set.mem_ofPred_eq, mem_faces_face_iff hF', ← hV]
  constructor
  · rintro ⟨h1, h2', h3, h4'⟩; exact ⟨⟨h1, h3⟩, h2', by omega⟩
  · rintro ⟨⟨h1, h3⟩, h2', h4'⟩; exact ⟨h1, h2', h3, by omega⟩

/-- **Double counting below a face**: `Σ_{j-faces T ⊆ F} Σ_{i-faces Q ⊆ T} f Q =
Σ_{i-faces Q ⊆ F} f Q · #{j-faces T : Q ⊆ T ⊆ F}`. -/
lemma IsCSPolytope5.sum_below_comm (F : Set E5) (i j : ℕ) (f : Set E5 → ℤ) :
    ∑ T ∈ (hP.below_finite F j).toFinset, ∑ Q ∈ (hP.below_finite T i).toFinset, f Q =
      ∑ Q ∈ (hP.below_finite F i).toFinset,
        f Q * ({T | T ∈ faces P ∧ Q ⊆ T ∧ T ⊆ F ∧ dim T = j}.ncard : ℤ) := by
  classical
  have hsub : ∀ T ∈ (hP.below_finite F j).toFinset, (hP.below_finite T i).toFinset =
      (hP.below_finite F i).toFinset.filter (fun Q => Q ⊆ T) := by
    intro T hT
    rw [Set.Finite.mem_toFinset] at hT
    ext Q
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2.trans hT.2.1, h3⟩, h2⟩
    · rintro ⟨⟨h1, -, h3⟩, h2⟩; exact ⟨h1, h2, h3⟩
  rw [Finset.sum_congr rfl fun T hT => by rw [hsub T hT]]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  have hfin : {T | T ∈ faces P ∧ Q ⊆ T ∧ T ⊆ F ∧ dim T = j}.Finite :=
    hP.faces_finite.subset fun T hT => hT.1
  rw [Set.ncard_eq_toFinset_card _ hfin]
  congr 1
  ext T
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  tauto

/-- The excess as a sum over the 2-faces. -/
lemma IsCSPolytope5.exc_eq_sum (G : Set E5) :
    exc P G = ∑ Q ∈ (hP.below_finite G 2).toFinset, ((cnt P Q 0 : ℤ) - 3) := by
  unfold exc
  rw [hP.incid_eq_sum_second G 0 2, cnt, Set.ncard_eq_toFinset_card _ (hP.below_finite G 2)]
  push_cast
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Excess of a 3-face**: `exc P T = 2 f₁(T) - 3 f₂(T)`. -/
lemma IsCSPolytope5.exc_threeface {T : Set E5} (hT : T ∈ faces P) (h3 : dim T = 3) :
    exc P T = 2 * (cnt P T 1 : ℤ) - 3 * cnt P T 2 := by
  have h := hP.threeface_vertex_sums hT h3
  have h01 := hP.incid_zero_one T
  unfold exc
  rw [h.1, h01]
  push_cast
  ring

/-- **Excess of a facet**: `2 exc P F = Σ_{3-faces T ⊆ F} exc P T`. -/
lemma IsCSPolytope5.two_exc_facet {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    2 * exc P F = ∑ T ∈ (hP.below_finite F 3).toFinset, exc P T := by
  rw [Finset.sum_congr rfl fun T _ => hP.exc_eq_sum T, hP.sum_below_comm F 2 3, hP.exc_eq_sum F,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [Set.Finite.mem_toFinset] at hQ
  rw [hP.twoface_in_facet hF h4 hQ.1 hQ.2.1 hQ.2.2]
  push_cast
  ring

end cs

end Kalai5
