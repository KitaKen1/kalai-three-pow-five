import Kalai5.Endpoints.WeightR0

/-!
# Edges of a facet

In a 4-polytope every edge lies in as many 2-faces as 3-faces, and in at least three of each (the
upper interval of an edge is a polygon, `upIn_codim_three`).  For a facet `F` of `P` this is
`IsCSPolytope5.edge_in_facet`; summing, `Σ_{3-faces T ⊆ F} f₁(T) ≥ 3 f₁(F)`, with equality iff every
edge lies in exactly three 3-faces of `F` (`IsCSPolytope5.edge_three_of_sum`).
-/

namespace Kalai5

open Set

open scoped Classical

variable {d : ℕ}

/-- **Edges of 4-polytopes.**  In a 4-dimensional polytope (in any `E d`) every edge lies in as many
2-faces as 3-faces, and in at least three 2-faces. -/
theorem edge_up_dim_four {K : Set (E d)} {V : Finset (E d)} (hK : K = convexHull ℝ (V : Set (E d)))
    (h4 : dim K = 4) {e : Set (E d)} (he : e ∈ faces K) (he1 : dim e = 1) :
    upIn K e 2 = upIn K e 3 ∧ 3 ≤ upIn K e 2 := by
  obtain ⟨p, hp, V', hV', h0⟩ := exists_good_affEmb hK (he.1.mono (face_subset he))
  have her := subset_range_affEmb hp (face_subset he)
  have hee : affEmb K p '' (affEmb K p ⁻¹' e) = e := Set.image_preimage_eq_of_subset her
  have he' : affEmb K p ⁻¹' e ∈ faces (convexHull ℝ (V' : Set (E (dim K)))) :=
    hV' ▸ preimage_mem_faces hp he
  have hde : dim (affEmb K p ⁻¹' e) = 1 := by
    have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' e)
    rw [hee, he1] at this
    omega
  have key := upIn_codim_three h0 he' (by omega)
  simp only [hde] at key
  rw [← hee, upIn_affEmb hp, upIn_affEmb hp, hV']
  exact key

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **An edge of a facet lies in as many of its 2-faces as of its 3-faces, at least three.** -/
theorem IsCSPolytope5.edge_in_facet {F e : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (he : e ∈ faces P) (heF : e ⊆ F) (h1 : dim e = 1) :
    {Q | Q ∈ faces P ∧ e ⊆ Q ∧ Q ⊆ F ∧ dim Q = 2}.ncard =
        {T | T ∈ faces P ∧ e ⊆ T ∧ T ⊆ F ∧ dim T = 3}.ncard ∧
      3 ≤ {T | T ∈ faces P ∧ e ⊆ T ∧ T ⊆ F ∧ dim T = 3}.ncard := by
  obtain ⟨V, hV⟩ := hP.polytope
  have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
  have hFV : F = convexHull ℝ ((V.filter (· ∈ F) : Finset E5) : Set E5) :=
    face_eq_convexHull_filter hF'
  have heF' : e ∈ faces F := (mem_faces_face_iff hF').2 ⟨hV ▸ he, heF⟩
  have key := edge_up_dim_four hFV h4 heF' h1
  have hup : ∀ j, upIn F e j = {T | T ∈ faces P ∧ e ⊆ T ∧ T ⊆ F ∧ dim T = j}.ncard := by
    intro j
    unfold upIn
    congr 1
    ext T
    simp only [Set.mem_ofPred_eq, mem_faces_face_iff hF', ← hV]
    constructor
    · rintro ⟨⟨h1', h3'⟩, h2', h4'⟩; exact ⟨h1', h2', h3', h4'⟩
    · rintro ⟨h1', h2', h3', h4'⟩; exact ⟨⟨h1', h3'⟩, h2', h4'⟩
  rw [hup 2, hup 3] at key
  exact ⟨key.1, key.1 ▸ key.2⟩

/-- `Σ_{3-faces T ⊆ F} f₁(T) = Σ_{edges e ⊆ F} #{3-faces of F through e}`. -/
lemma IsCSPolytope5.sum_edges_threefaces (F : Set E5) :
    ∑ T ∈ (hP.below_finite F 3).toFinset, (cnt P T 1 : ℤ) =
      ∑ e ∈ (hP.below_finite F 1).toFinset,
        ({T | T ∈ faces P ∧ e ⊆ T ∧ T ⊆ F ∧ dim T = 3}.ncard : ℤ) := by
  have h1 := hP.incid_eq_sum_second F 1 3
  have h2 := hP.incid_eq_sum_first F 1 3
  rw [h1] at h2
  exact_mod_cast h2

/-- **Edges in exactly three 3-faces**: if `Σ_{T ⊆ F} f₁(T) = 3 f₁(F)`, every edge of the facet lies
in exactly three of its 3-faces. -/
theorem IsCSPolytope5.edge_three_of_sum {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hsum : ∑ T ∈ (hP.below_finite F 3).toFinset, (cnt P T 1 : ℤ) = 3 * cnt P F 1)
    {e : Set E5} (he : e ∈ faces P) (heF : e ⊆ F) (h1 : dim e = 1) :
    {T | T ∈ faces P ∧ e ⊆ T ∧ T ⊆ F ∧ dim T = 3}.ncard = 3 := by
  rw [hP.sum_edges_threefaces F] at hsum
  have hge : ∀ e' ∈ (hP.below_finite F 1).toFinset,
      (3 : ℤ) ≤ ({T | T ∈ faces P ∧ e' ⊆ T ∧ T ⊆ F ∧ dim T = 3}.ncard : ℤ) := by
    intro e' he'
    rw [Set.Finite.mem_toFinset] at he'
    exact_mod_cast (hP.edge_in_facet hF h4 he'.1 he'.2.1 he'.2.2).2
  have hmem : e ∈ (hP.below_finite F 1).toFinset := by
    rw [Set.Finite.mem_toFinset]; exact ⟨he, heF, h1⟩
  have hcard : ((hP.below_finite F 1).toFinset.card : ℤ) = cnt P F 1 := by
    rw [cnt, Set.ncard_eq_toFinset_card _ (hP.below_finite F 1)]
  have hnn : ∀ e' ∈ (hP.below_finite F 1).toFinset,
      (0 : ℤ) ≤ ({T | T ∈ faces P ∧ e' ⊆ T ∧ T ⊆ F ∧ dim T = 3}.ncard : ℤ) - 3 :=
    fun e' he' => by have := hge e' he'; linarith
  have hsingle := Finset.single_le_sum hnn hmem
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard, hsum] at hsingle
  have hlow := hge e hmem
  have : ({T | T ∈ faces P ∧ e ⊆ T ∧ T ⊆ F ∧ dim T = 3}.ncard : ℤ) = 3 := by linarith
  exact_mod_cast this

end cs

end Kalai5
