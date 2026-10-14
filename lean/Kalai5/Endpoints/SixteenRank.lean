import Kalai5.Endpoints.SixteenLowRank
import Kalai5.LemmaB.Eight.Core

/-!
# Sixteen vertices: the rank of the full normals

The full normals at sixteen vertices are the normals of the facets with eight vertices
(`full_normal_finset16`, one per facet).  If there are at least eight of them (four full pairs)
and they span at most three dimensions, their positions in `{±1}³` avoid one of the four classes
(otherwise every full normal is `±u_i`), so the rank-three octahedral case applies
(`LemmaB.Eight.IsCSPolytope5.rank3_oct16`, the eight-point Lemma B): four independent full
normals, or `243` faces.  Hence `LowRank16` reduces to `FewFull16`: one to three full pairs.
-/

namespace Kalai5

open Set Module LemmaA LemmaB

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {P : Set E5}

/-- **Full normals at `f₀ = 16`**: a finset of distinct `±1`-functionals, one for each facet with
eight vertices. -/
theorem IsCSPolytope5.full_normal_finset16 (hP : IsCSPolytope5 P) (h16 : fvec P 0 = 16) :
    ∃ N : Finset E5, N.card = ((facetRows P).filter fun R => R.n = 8).length ∧
      ∀ n ∈ N, ∀ y ∈ P.extremePoints ℝ, ⟪n, y⟫ = 1 ∨ ⟪n, y⟫ = -1 := by
  classical
  set FS := (hP.kfaces_finite 4).toFinset.filter fun F => cnt P F 0 = 8 with hFSdef
  have hFS : FS.card = ((facetRows P).filter fun R => R.n = 8).length := by
    rw [length_filter_eq_sum, hP.facetRows_sum (fun R => if R.n = 8 then 1 else 0), hFSdef,
      Finset.card_filter]
    rfl
  have hnormal : ∀ F ∈ FS, ∃ v : E5, F = {x ∈ P | ⟪v, x⟫ = 1} ∧
      ∀ x ∈ P.extremePoints ℝ, ⟪v, x⟫ = 1 ∨ ⟪v, x⟫ = -1 := by
    intro F hF
    simp only [hFSdef, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hF
    obtain ⟨⟨hFf, hFd⟩, hF8⟩ := hF
    have hne : F ≠ P := fun h => by have := hP.dim_self; rw [← h, hFd] at this; omega
    obtain ⟨u, -, hFu, hpm⟩ := hP.exists_full_normal hFf hne (by rw [hF8, h16])
    refine ⟨(InnerProductSpace.toDual ℝ E5).symm u, ?_, fun x hx => ?_⟩
    · rw [hFu]; simp only [InnerProductSpace.toDual_symm_apply]
    · rw [InnerProductSpace.toDual_symm_apply]; exact hpm x hx
  choose! nv hnvF hnvpm using hnormal
  have hinj : Set.InjOn nv FS := fun F hF G hG h => by rw [hnvF F hF, hnvF G hG, h]
  refine ⟨FS.image nv, by rw [Finset.card_image_of_injOn hinj, hFS], fun n hn y hy => ?_⟩
  obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hn
  exact hnvpm F hF y hy

/-- **One to three full pairs**: with `h` facets and between one and three pairs of
facets with eight vertices, at least `243` faces.  (The full normals then span at
most three dimensions: ranks one and two, and rank three with all four classes of `{±1}³`, the
cube type.) -/
def FewFull16 (h : ℕ) : Prop :=
  ∀ P : Set E5, IsCSPolytope5 P → fvec P 0 = 16 → fvec P 4 = h →
    1 ≤ ((facetRows P).filter fun R => R.n = 8).length →
    ((facetRows P).filter fun R => R.n = 8).length ≤ 6 → 243 ≤ (faces P).ncard

/-- **`LowRank16` from `FewFull16`** and the rank-three octahedral case. -/
theorem lowRank16_of_fewFull {h : ℕ} (hF : FewFull16 h) : LowRank16 h := by
  classical
  intro P hP h16 hh hrow
  obtain ⟨N, hNcard, hNpm⟩ := hP.full_normal_finset16 h16
  by_cases h6 : N.card ≤ 6
  · right
    obtain ⟨R, hR, hR8⟩ := hrow
    have h1 : 1 ≤ ((facetRows P).filter fun R => R.n = 8).length :=
      List.length_pos_of_mem (List.mem_filter.2 ⟨hR, by simp [hR8]⟩)
    exact hF P hP h16 hh h1 (by omega)
  push Not at h6
  obtain ⟨V, hV⟩ := hP.polytope
  set X := (extremePoints_finite V).toFinset with hXdef
  have hXcoe : (X : Set E5) = P.extremePoints ℝ := by rw [hXdef, Set.Finite.coe_toFinset, hV]
  have hsep : ∀ u : E5, (∀ x ∈ X, ⟪u, x⟫ = 0) → u = 0 := fun u hu =>
    hP.eq_zero_of_inner_vertices fun x hx => hu x (by rw [← Finset.mem_coe, hXcoe]; exact hx)
  have hNX : ∀ n ∈ N, ∀ x ∈ X, ⟪n, x⟫ = 1 ∨ ⟪n, x⟫ = -1 := fun n hn x hx =>
    hNpm n hn x (by rw [← hXcoe]; exact hx)
  obtain ⟨b, hbN, hspan, hb⟩ := exists_linearIndependent ℝ (N : Set E5)
  have hbfin : b.Finite := N.finite_toSet.subset hbN
  haveI : Fintype b := hbfin.fintype
  have hdim : finrank ℝ (Submodule.span ℝ (N : Set E5)) = Fintype.card b := by
    rw [← hspan, finrank_span_set_eq_card hb, Set.toFinset_card]
  by_cases h4 : 4 ≤ Fintype.card b
  · left
    obtain ⟨f⟩ : Nonempty (Fin 4 ↪ b) := Function.Embedding.nonempty_of_card_le (by simpa using h4)
    exact ⟨fun i => (f i : E5), hb.comp f f.injective, fun i y hy => hNpm _ (hbN (f i).2) y hy⟩
  have h3 : Fintype.card b = 3 := by
    have hle := card_le_two_pow_finrank hsep hNX
    rw [hdim] at hle
    have : 3 ≤ Fintype.card b := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ Fintype.card b ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  -- three independent normals spanning all of them
  obtain ⟨e⟩ : Nonempty (Fin 3 ≃ b) := ⟨(Fintype.equivFinOfCardEq h3).symm⟩
  set u : Fin 3 → E5 := fun i => (e i : E5) with hudef
  have hu : LinearIndependent ℝ u := hb.comp e e.injective
  have hupm : ∀ i, ∀ y ∈ P.extremePoints ℝ, ⟪u i, y⟫ = 1 ∨ ⟪u i, y⟫ = -1 :=
    fun i y hy => hNpm _ (hbN (e i).2) y hy
  have hrange : Set.range u = b := by
    ext y; constructor
    · rintro ⟨i, rfl⟩; exact (e i).2
    · intro hy; exact ⟨e.symm ⟨y, hy⟩, by simp [hudef]⟩
  have hcomb : ∀ n ∈ N, ∃ coef : Fin 3 → ℝ, coef 0 • u 0 + coef 1 • u 1 + coef 2 • u 2 = n := by
    intro n hn
    have hmem : n ∈ Submodule.span ℝ (Set.range u) := by
      rw [hrange, hspan]; exact Submodule.subset_span hn
    obtain ⟨coef, hcoef⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
    exact ⟨coef, by rw [← hcoef, Fin.sum_univ_three]⟩
  -- a class is missing (otherwise at most six full normals)
  have hmiss : ∃ m : Fin 4, ∀ y ∈ P.extremePoints ℝ,
      (fun i => ⟪u i, y⟫) ≠ clsRep m ∧ (fun i => ⟪u i, y⟫) ≠ -clsRep m := by
    by_contra hall
    push Not at hall
    have hall' : ∀ m : Fin 4, ∃ y ∈ P.extremePoints ℝ,
        (fun i => ⟪u i, y⟫) = clsRep m ∨ (fun i => ⟪u i, y⟫) = -clsRep m := by
      intro m
      obtain ⟨y, hy, h⟩ := hall m
      by_cases h1 : (fun i => ⟪u i, y⟫) = clsRep m
      · exact ⟨y, hy, Or.inl h1⟩
      · exact ⟨y, hy, Or.inr (h h1)⟩
    have hsub : N ⊆ Finset.univ.image fun p : Fin 3 × Bool => if p.2 then u p.1 else -u p.1 := by
      intro n hn
      obtain ⟨coef, hcoef⟩ := hcomb n hn
      have hval : ∀ y ∈ P.extremePoints ℝ,
          coef 0 * ⟪u 0, y⟫ + coef 1 * ⟪u 1, y⟫ + coef 2 * ⟪u 2, y⟫ = 1 ∨
            coef 0 * ⟪u 0, y⟫ + coef 1 * ⟪u 1, y⟫ + coef 2 * ⟪u 2, y⟫ = -1 := by
        intro y hy
        have := hNpm n hn y hy
        rw [← hcoef] at this
        simpa [inner_add_left, real_inner_smul_left] using this
      rw [Finset.mem_image]
      rcases pm_combination hupm hall' hval with ⟨h0 | h0, h1, h2⟩ | ⟨h0, h1 | h1, h2⟩ |
          ⟨h0, h1, h2 | h2⟩
      · exact ⟨(0, true), Finset.mem_univ _, by simp [← hcoef, h0, h1, h2]⟩
      · exact ⟨(0, false), Finset.mem_univ _, by simp [← hcoef, h0, h1, h2]⟩
      · exact ⟨(1, true), Finset.mem_univ _, by simp [← hcoef, h0, h1, h2]⟩
      · exact ⟨(1, false), Finset.mem_univ _, by simp [← hcoef, h0, h1, h2]⟩
      · exact ⟨(2, true), Finset.mem_univ _, by simp [← hcoef, h0, h1, h2]⟩
      · exact ⟨(2, false), Finset.mem_univ _, by simp [← hcoef, h0, h1, h2]⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin 3 × Bool)))
      (f := fun p : Fin 3 × Bool => if p.2 then u p.1 else -u p.1)
    simp at h2
    omega
  obtain ⟨m, hm⟩ := hmiss
  exact LemmaB.Eight.IsCSPolytope5.rank3_oct16 hP h16 hu hupm hm

end Kalai5
