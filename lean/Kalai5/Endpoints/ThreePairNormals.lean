import Kalai5.Endpoints.SixteenRank
import Kalai5.Cert.Engine3

/-!
# The geometric branch with three full pairs

A putative counterexample with at least six full facets has three independent
full normals. Every antipodal class of the cube occurs: a missing class is
the already proved octahedral case. No full normal lies outside their span,
because that would invoke the four-normal theorem.
-/

namespace Kalai5

open Set Module LemmaA LemmaB

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.no_four_full_of_faces_lt
    (hv : fvec P 0 = 16) (hh : fvec P 4 ≤ 18) (hlt : (faces P).ncard < 243)
    {u : Fin 4 → E5} (hu : LinearIndependent ℝ u)
    (hpm : ∀ i, ∀ y ∈ P.extremePoints ℝ, ⟪u i, y⟫ = 1 ∨ ⟪u i, y⟫ = -1) : False :=
  (not_le_of_gt hlt) (hP.a16 hv hu hpm hh)

/-- Six full normals cannot span only two dimensions. -/
theorem IsCSPolytope5.three_indep_full_normals
    (hv : fvec P 0 = 16) (hc : 6 ≤ cnt8 (facetRows P)) :
    ∃ u : Fin 3 → E5, LinearIndependent ℝ u ∧
      ∀ i, ∀ y ∈ P.extremePoints ℝ, ⟪u i, y⟫ = 1 ∨ ⟪u i, y⟫ = -1 := by
  classical
  obtain ⟨N, hNcard, hNpm⟩ := hP.full_normal_finset16 hv
  obtain ⟨V, hV⟩ := hP.polytope
  set X := (extremePoints_finite V).toFinset with hXdef
  have hXcoe : (X : Set E5) = P.extremePoints ℝ := by
    rw [hXdef, Set.Finite.coe_toFinset, hV]
  have hsep : ∀ u : E5, (∀ x ∈ X, ⟪u, x⟫ = 0) → u = 0 := fun u hu =>
    hP.eq_zero_of_inner_vertices fun x hx => hu x (by rw [← Finset.mem_coe, hXcoe]; exact hx)
  have hNX : ∀ n ∈ N, ∀ x ∈ X, ⟪n, x⟫ = 1 ∨ ⟪n, x⟫ = -1 := fun n hn x hx =>
    hNpm n hn x (by rw [← hXcoe]; exact hx)
  obtain ⟨b, hbN, hspan, hb⟩ := exists_linearIndependent ℝ (N : Set E5)
  have hbfin : b.Finite := N.finite_toSet.subset hbN
  haveI : Fintype b := hbfin.fintype
  have hdim : finrank ℝ (Submodule.span ℝ (N : Set E5)) = Fintype.card b := by
    rw [← hspan, finrank_span_set_eq_card hb, Set.toFinset_card]
  have h3 : 3 ≤ Fintype.card b := by
    have hle := card_le_two_pow_finrank hsep hNX
    rw [hdim] at hle
    change N.card = cnt8 (facetRows P) at hNcard
    by_contra hlt
    have : 2 ^ Fintype.card b ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨f⟩ : Nonempty (Fin 3 ↪ b) := Function.Embedding.nonempty_of_card_le (by simpa using h3)
  exact ⟨fun i => (f i : E5), hb.comp f f.injective,
    fun i y hy => hNpm _ (hbN (f i).2) y hy⟩

/-- A missing cube class would be the proved octahedral branch. -/
theorem IsCSPolytope5.all_cube_classes_of_faces_lt
    (hv : fvec P 0 = 16) (hh : fvec P 4 ≤ 18) (hlt : (faces P).ncard < 243)
    {u : Fin 3 → E5} (hu : LinearIndependent ℝ u)
    (hpm : ∀ i, ∀ y ∈ P.extremePoints ℝ, ⟪u i, y⟫ = 1 ∨ ⟪u i, y⟫ = -1) :
    ∀ j : Fin 4, ∃ y ∈ P.extremePoints ℝ,
      (fun i => ⟪u i, y⟫) = clsRep j ∨ (fun i => ⟪u i, y⟫) = -clsRep j := by
  intro j
  by_contra hno
  have hmiss : ∀ y ∈ P.extremePoints ℝ,
      (fun i => ⟪u i, y⟫) ≠ clsRep j ∧ (fun i => ⟪u i, y⟫) ≠ -clsRep j := by
    intro y hy
    exact ⟨fun h => hno ⟨y, hy, Or.inl h⟩, fun h => hno ⟨y, hy, Or.inr h⟩⟩
  rcases LemmaB.Eight.IsCSPolytope5.rank3_oct16 hP hv hu hpm hmiss with ⟨w, hw, hwpm⟩ | h
  · exact hP.no_four_full_of_faces_lt hv hh hlt hw hwpm
  · exact (not_le_of_gt hlt) h

theorem IsCSPolytope5.full_normal_mem_span_three_of_faces_lt
    (hv : fvec P 0 = 16) (hh : fvec P 4 ≤ 18) (hlt : (faces P).ncard < 243)
    {u : Fin 3 → E5} (hu : LinearIndependent ℝ u)
    (hpm : ∀ i, ∀ y ∈ P.extremePoints ℝ, ⟪u i, y⟫ = 1 ∨ ⟪u i, y⟫ = -1)
    {z : E5} (hz : ∀ y ∈ P.extremePoints ℝ, ⟪z, y⟫ = 1 ∨ ⟪z, y⟫ = -1) :
    z ∈ Submodule.span ℝ (range u) := by
  by_contra hspan
  apply hP.no_four_full_of_faces_lt hv hh hlt
    ((linearIndependent_fin_snoc).2 ⟨hu, hspan⟩)
  intro i y hy
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using hz y hy
  · simpa only [Fin.snoc_castSucc] using hpm j y hy

end Kalai5
