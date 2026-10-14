import Kalai5.Endpoints.Fake8Count

/-!
# Vertex-figure parity in a facet

For a vertex `v` of a facet `H`, the vertex figure of `H` at `v` is a 3-polytope whose faces are the
3-faces `R ∋ v` of `H`, a face having as many sides as `v` has edges in `R`.  Counting the
face–edge incidences of the vertex figure twice gives
`Σ_{R ∋ v} deg_R(v) = 2 #{2-faces of H through v}` (`IsCSPolytope5.vertex_parity`).

With the degrees in the small 3-faces (a tetrahedron or a triangular prism: all degrees three) this
is the parity used to exclude 3-face compositions of eight-vertex facets.
-/

namespace Kalai5

open Set

open scoped Classical

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The degree of `v` in `R`: the edges of `P` through `v` inside `R`. -/
noncomputable def vdeg (P R v : Set E5) : ℕ :=
  {e | e ∈ faces P ∧ v ⊆ e ∧ e ⊆ R ∧ dim e = 1}.ncard

/-- **Vertex-figure parity**: the degrees of a vertex `v` of a facet `H` in the 3-faces of `H`
through `v` add up to twice the number of 2-faces of `H` through `v`. -/
theorem IsCSPolytope5.vertex_parity {H v : Set E5} (hH : H ∈ faces P) (h4 : dim H = 4)
    (hv : v ∈ faces P) (h0 : dim v = 0) :
    ∑ R ∈ (hP.below_finite H 3).toFinset.filter (fun R => v ⊆ R), (vdeg P R v : ℤ) =
      2 * (((hP.below_finite H 2).toFinset.filter (fun Q => v ⊆ Q)).card : ℤ) := by
  have h1 : ∀ R ∈ (hP.below_finite H 3).toFinset.filter (fun R => v ⊆ R),
      (vdeg P R v : ℤ) =
        ∑ Q ∈ (hP.below_finite H 2).toFinset, if v ⊆ Q ∧ Q ⊆ R then (1 : ℤ) else 0 := by
    intro R hR
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hR
    unfold vdeg
    rw [(hP.vertex_in_threeface hR.1.1 hR.1.2.2 hv hR.2 h0).1, Finset.sum_boole]
    congr 1
    rw [← Set.ncard_coe_finset]
    congr 1
    ext Q
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hQ, hvQ, hQR, hQ2⟩
      exact ⟨⟨hQ, hQR.trans hR.1.2.1, hQ2⟩, hvQ, hQR⟩
    · rintro ⟨⟨hQ, -, hQ2⟩, hvQ, hQR⟩
      exact ⟨hQ, hvQ, hQR, hQ2⟩
  have h2 : ∀ Q ∈ (hP.below_finite H 2).toFinset,
      (∑ R ∈ (hP.below_finite H 3).toFinset.filter (fun R => v ⊆ R),
        if v ⊆ Q ∧ Q ⊆ R then (1 : ℤ) else 0) = if v ⊆ Q then 2 else 0 := by
    intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ
    by_cases hvQ : v ⊆ Q
    · rw [if_pos hvQ, Finset.sum_boole]
      have htwo := hP.twoface_in_facet hH h4 hQ.1 hQ.2.1 hQ.2.2
      have hfinT : {T | T ∈ faces P ∧ Q ⊆ T ∧ T ⊆ H ∧ dim T = 3}.Finite :=
        hP.faces_finite.subset fun T hT => hT.1
      have hc : (((hP.below_finite H 3).toFinset.filter (fun R => v ⊆ R)).filter
          (fun R => v ⊆ Q ∧ Q ⊆ R)) = hfinT.toFinset := by
        ext T
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨⟨⟨hT, hTH, hT3⟩, -⟩, -, hQT⟩
          exact ⟨hT, hQT, hTH, hT3⟩
        · rintro ⟨hT, hQT, hTH, hT3⟩
          exact ⟨⟨⟨hT, hTH, hT3⟩, hvQ.trans hQT⟩, hvQ, hQT⟩
      rw [hc, ← Set.ncard_eq_toFinset_card _ hfinT, htwo]
      norm_num
    · rw [if_neg hvQ]
      exact Finset.sum_eq_zero fun R _ => if_neg fun h => hvQ h.1
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_congr rfl h2, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- All degrees in a 3-face with `2 f₁ = 3 f₀` (a tetrahedron, a triangular prism) are three. -/
lemma IsCSPolytope5.vdeg_eq_three {R v : Set E5} (hR : R ∈ faces P) (h3 : dim R = 3)
    (hf : 2 * cnt P R 1 = 3 * cnt P R 0) (hv : v ∈ faces P) (hvR : v ⊆ R) (h0 : dim v = 0) :
    vdeg P R v = 3 := by
  have hdeg : ∀ w ∈ (hP.below_finite R 0).toFinset, 3 ≤ vdeg P R w := by
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    exact (hP.vertex_in_threeface hR h3 hw.1 hw.2.1 hw.2.2).2
  have hinc : incid P R 0 1 = ∑ w ∈ (hP.below_finite R 0).toFinset, vdeg P R w := by
    rw [hP.incid_eq_sum_first R 0 1]
    rfl
  rw [hP.incid_zero_one] at hinc
  have hmem : v ∈ (hP.below_finite R 0).toFinset := by
    rw [Set.Finite.mem_toFinset]; exact ⟨hv, hvR, h0⟩
  have hcard : (hP.below_finite R 0).toFinset.card = cnt P R 0 := by
    rw [cnt, Set.ncard_eq_toFinset_card _ (hP.below_finite R 0)]
  by_contra hne
  have hv4 : 4 ≤ vdeg P R v := by have := hdeg v hmem; omega
  have hnn : ∀ w ∈ (hP.below_finite R 0).toFinset, (0 : ℤ) ≤ (vdeg P R w : ℤ) - 3 := by
    intro w hw
    have := hdeg w hw
    omega
  have h1 := Finset.single_le_sum hnn hmem
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard] at h1
  have hinc' : (2 * cnt P R 1 : ℤ) = ∑ w ∈ (hP.below_finite R 0).toFinset, (vdeg P R w : ℤ) := by
    exact_mod_cast hinc
  have hf' : (2 * cnt P R 1 : ℤ) = 3 * cnt P R 0 := by exact_mod_cast hf
  have hv4' : (4 : ℤ) ≤ vdeg P R v := by exact_mod_cast hv4
  linarith

end cs

end Kalai5
