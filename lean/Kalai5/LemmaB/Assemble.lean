import Kalai5.LemmaB.Normal
import Kalai5.LemmaA.Final

/-!
# Lemma B: assembly of the fourteen-vertex lemma

`fourteen_full_of_core`: at `f₀ = 14`, eight facets with seven vertices give at least 243 faces,
given the counting core for rank-three configurations (`hcore`).

* nine or more such facets: four independent full normals, Lemma A;
* exactly eight, with four independent normals: Lemma A;
* rank three: the positions avoid one of the four classes (otherwise every normal is `±u_i`, at
  most six of them), so `rank3_normal` applies; a fourth `±1`-functional again gives Lemma A, and
  otherwise `hcore`.
-/

namespace Kalai5.LemmaB

open Set Module LemmaA

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {P : Set E5}

/-- **Full normals at `f₀ = 14`**: a finset of distinct `±1`-functionals, one for each facet with
seven vertices. -/
theorem IsCSPolytope5.full_normal_finset (hP : IsCSPolytope5 P) (h14 : fvec P 0 = 14) :
    ∃ N : Finset E5, N.card = ((facetRows P).filter fun R => R.n = 7).length ∧
      ∀ n ∈ N, ∀ y ∈ P.extremePoints ℝ, ⟪n, y⟫ = 1 ∨ ⟪n, y⟫ = -1 := by
  classical
  set FS := (hP.kfaces_finite 4).toFinset.filter fun F => cnt P F 0 = 7 with hFSdef
  have hFS : FS.card = ((facetRows P).filter fun R => R.n = 7).length := by
    rw [length_filter_eq_sum, hP.facetRows_sum (fun R => if R.n = 7 then 1 else 0), hFSdef,
      Finset.card_filter]
    rfl
  have hnormal : ∀ F ∈ FS, ∃ v : E5, F = {x ∈ P | ⟪v, x⟫ = 1} ∧
      ∀ x ∈ P.extremePoints ℝ, ⟪v, x⟫ = 1 ∨ ⟪v, x⟫ = -1 := by
    intro F hF
    simp only [hFSdef, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hF
    obtain ⟨⟨hFf, hFd⟩, hF7⟩ := hF
    have hne : F ≠ P := fun h => by have := hP.dim_self; rw [← h, hFd] at this; omega
    obtain ⟨u, -, hFu, hpm⟩ := hP.exists_full_normal hFf hne (by rw [hF7, h14])
    refine ⟨(InnerProductSpace.toDual ℝ E5).symm u, ?_, fun x hx => ?_⟩
    · rw [hFu]; simp only [InnerProductSpace.toDual_symm_apply]
    · rw [InnerProductSpace.toDual_symm_apply]; exact hpm x hx
  choose! nv hnvF hnvpm using hnormal
  have hinj : Set.InjOn nv FS := fun F hF G hG h => by rw [hnvF F hF, hnvF G hG, h]
  refine ⟨FS.image nv, by rw [Finset.card_image_of_injOn hinj, hFS], fun n hn y hy => ?_⟩
  obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hn
  exact hnvpm F hF y hy

/-- If the positions of the vertices meet all four classes, a `±1`-combination of `u` is `±u_i`. -/
lemma pm_combination {u : Fin 3 → E5} (hpm : ∀ i, ∀ y ∈ P.extremePoints ℝ,
      ⟪u i, y⟫ = 1 ∨ ⟪u i, y⟫ = -1)
    (hall : ∀ m : Fin 4, ∃ y ∈ P.extremePoints ℝ,
      (fun i => ⟪u i, y⟫) = clsRep m ∨ (fun i => ⟪u i, y⟫) = -clsRep m)
    {coef : Fin 3 → ℝ} (hn : ∀ y ∈ P.extremePoints ℝ,
      coef 0 * ⟪u 0, y⟫ + coef 1 * ⟪u 1, y⟫ + coef 2 * ⟪u 2, y⟫ = 1 ∨
        coef 0 * ⟪u 0, y⟫ + coef 1 * ⟪u 1, y⟫ + coef 2 * ⟪u 2, y⟫ = -1) :
    (coef 0 = 1 ∨ coef 0 = -1) ∧ coef 1 = 0 ∧ coef 2 = 0 ∨
      coef 0 = 0 ∧ (coef 1 = 1 ∨ coef 1 = -1) ∧ coef 2 = 0 ∨
      coef 0 = 0 ∧ coef 1 = 0 ∧ (coef 2 = 1 ∨ coef 2 = -1) := by
  have key : ∀ m : Fin 4, coef 0 * clsRep m 0 + coef 1 * clsRep m 1 + coef 2 * clsRep m 2 = 1 ∨
      coef 0 * clsRep m 0 + coef 1 * clsRep m 1 + coef 2 * clsRep m 2 = -1 := by
    intro m
    obtain ⟨y, hy, hq⟩ := hall m
    have h := hn y hy
    rcases hq with hq | hq
    · have e0 := congrFun hq 0; have e1 := congrFun hq 1; have e2 := congrFun hq 2
      rw [e0, e1, e2] at h; exact h
    · have e0 := congrFun hq 0; have e1 := congrFun hq 1; have e2 := congrFun hq 2
      simp only [Pi.neg_apply] at e0 e1 e2
      rw [e0, e1, e2] at h
      rcases h with h | h
      · right; linarith
      · left; linarith
  have k0 := key 0; have k1 := key 1; have k2 := key 2; have k3 := key 3
  simp only [clsRep] at k0 k1 k2 k3
  norm_num at k0 k1 k2 k3
  dsimp at k0 k1 k2 k3
  norm_num at k0 k1 k2 k3
  apply four_classes_c
  · rcases k0 with h | h <;> [left; right] <;> linarith
  · rcases k1 with h | h <;> [left; right] <;> linarith
  · rcases k2 with h | h <;> [left; right] <;> linarith
  · rcases k3 with h | h <;> [left; right] <;> linarith

/-- `±1`-vectors on a separating set: at most `2 ^ dim` of them. -/
theorem card_le_two_pow_finrank {N X : Finset E5}
    (hX : ∀ u : E5, (∀ x ∈ X, ⟪u, x⟫ = 0) → u = 0)
    (hN : ∀ u ∈ N, ∀ x ∈ X, ⟪u, x⟫ = 1 ∨ ⟪u, x⟫ = -1) :
    N.card ≤ 2 ^ finrank ℝ (Submodule.span ℝ (N : Set E5)) := by
  classical
  let ev : E5 →ₗ[ℝ] (X → ℝ) :=
    { toFun := fun u x => ⟪u, (x : E5)⟫
      map_add' := fun u v => by ext x; simp [inner_add_left]
      map_smul' := fun r u => by ext x; simp [real_inner_smul_left] }
  have hev : Function.Injective ev := by
    intro u v huv
    have h0 : u - v = 0 := hX (u - v) fun x hx => by
      have := congrFun huv ⟨x, hx⟩
      simp only [ev, LinearMap.coe_mk, AddHom.coe_mk] at this
      rw [inner_sub_left, this, sub_self]
    exact sub_eq_zero.1 h0
  have hS := card_pm_one_le ((Submodule.span ℝ (N : Set E5)).map ev) (N.image ev) (by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨Submodule.mem_map_of_mem (Submodule.subset_span hu), fun x => hN u hu x x.2⟩)
  rw [Finset.card_image_of_injective _ hev] at hS
  exact le_trans hS (Nat.pow_le_pow_right (by norm_num) (Submodule.finrank_map_le _ _))

/-- The counting core of Lemma B. -/
def CoreClaim : Prop := ∀ (x : Fin 7 → E5) (C : Config x), ¬ C.ExtraPM →
  243 ≤ (faces (convexHull ℝ (range (pm x)))).ncard

/-- **The fourteen-vertex lemma** from the counting core. -/
theorem fourteen_full_of_core (hcore : CoreClaim) (hP : IsCSPolytope5 P) (h14 : fvec P 0 = 14)
    (h8 : 8 ≤ ((facetRows P).filter fun R => R.n = 7).length) : 243 ≤ (faces P).ncard := by
  classical
  by_cases h9 : 9 ≤ ((facetRows P).filter fun R => R.n = 7).length
  · exact hP.three_pow_five_of_nine_full h14 h9
  obtain ⟨N, hNcard, hNpm⟩ := IsCSPolytope5.full_normal_finset hP h14
  have hN8 : N.card = 8 := by omega
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
  · obtain ⟨f⟩ : Nonempty (Fin 4 ↪ b) := Function.Embedding.nonempty_of_card_le (by simpa using h4)
    exact hP.lemmaA h14 (hb.comp f f.injective) (fun i y hy => hNpm _ (hbN (f i).2) y hy)
  have h3 : Fintype.card b = 3 := by
    have hle := card_le_two_pow_finrank hsep hNX
    rw [hN8, hdim] at hle
    have : 3 ≤ Fintype.card b := by
      by_contra hlt
      push_neg at hlt
      have : 2 ^ Fintype.card b ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  -- three independent normals spanning all eight
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
  -- a class is missing
  have hmiss : ∃ m : Fin 4, ∀ y ∈ P.extremePoints ℝ,
      (fun i => ⟪u i, y⟫) ≠ clsRep m ∧ (fun i => ⟪u i, y⟫) ≠ -clsRep m := by
    by_contra hall
    push_neg at hall
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
  obtain ⟨x, -, hxrange, C, hCE⟩ := IsCSPolytope5.rank3_normal hP h14 hu hupm hm
  by_cases hE : C.ExtraPM
  · obtain ⟨u4, hu4, hu4pm⟩ := hCE hE
    exact hP.lemmaA h14 hu4 hu4pm
  · have h := hcore x C hE
    rwa [hxrange, hV, convexHull_extremePoints_eq, ← hV] at h

end Kalai5.LemmaB
