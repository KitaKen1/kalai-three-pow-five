import Kalai5.Endpoints.OnePairProfile
import Kalai5.Rows.FacetTypeParity

/-!
# Local consequences of the unique one-pair facet profile

The global Q55 bound is saturated. Every local weight therefore attains its
lower bound, forcing the two quadrilaterals in a full facet to be of type (5,5).
-/

namespace Kalai5

open Set
open scoped Classical

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The proven row weights exhaust the global budget in the one-pair case. -/
lemma IsCSPolytope5.fewFull18_one_pair_weight_sum
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243) :
    ((facetRows P).map q55StrongRowWeight).sum = 72 := by
  obtain ⟨hall, hY, hJ, hH, -, -⟩ := hP.fewFull18_one_pair_profile hv hh hc hlt
  have hs := sum_three q55StrongRowWeight hall
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [hY, hJ, hH] at hs
  exact hs

/-- Equality in the global budget forces equality in every facet's weight. -/
theorem IsCSPolytope5.fewFull18_one_pair_weight_eq
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    q55w P F + 2 * exc P F = q55StrongRowWeight (faceRow P F) := by
  have hD := hP.fewFull18_one_pair_flagData hv hh hc hlt
  have hs := hP.fewFull18_one_pair_weight_sum hv hh hc hlt
  rw [hP.facetRows_sum q55StrongRowWeight] at hs
  have hsZ : ∑ H ∈ (hP.kfaces_finite 4).toFinset,
      (q55StrongRowWeight (faceRow P H) : ℤ) = 72 := by exact_mod_cast hs
  have hu := hP.q55 hv
  rw [hD] at hu
  norm_num [FlagData.A] at hu
  have hle : ∀ H ∈ (hP.kfaces_finite 4).toFinset,
      (q55StrongRowWeight (faceRow P H) : ℤ) ≤ q55w P H + 2 * exc P H := by
    intro H hH
    rw [Set.Finite.mem_toFinset] at hH
    exact hP.q55_strong_row_weight hH.1 hH.2
  have heq : (∑ H ∈ (hP.kfaces_finite 4).toFinset,
      (q55StrongRowWeight (faceRow P H) : ℤ)) =
      ∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H) := by
    have hl := Finset.sum_le_sum hle
    omega
  exact ((Finset.sum_eq_sum_iff_of_le hle).1 heq F
    (by rw [Set.Finite.mem_toFinset]; exact ⟨hF, h4⟩)).symm

/-- The full facet has two quadrilaterals, and both are bounded by square
pyramids on each side within that facet. -/
theorem IsCSPolytope5.fewFull18_one_pair_full_quads
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = OnePairProfile.fullRow 20) :
    q4 P F = 2 ∧ big2 P F = 0 ∧ (b55set P F).ncard = 2 ∧
      q55w P F = -4 ∧ tcnt P F (5, 8, 5) = 4 := by
  have hw := hP.fewFull18_one_pair_weight_eq hv hh hc hlt hF h4
  rw [hrow] at hw
  have hw0 : q55StrongRowWeight (OnePairProfile.fullRow 20) = 0 := by decide +kernel
  rw [hw0, Nat.cast_zero] at hw
  have hexc := hP.exc_eq_faceRow hF h4
  rw [hrow] at hexc
  norm_num [OnePairProfile.fullRow] at hexc
  have hq := hP.q4_add_big_le_exc F
  have hlo := hP.q55w_ge F
  have hb := hP.q55w_eq_b55 F
  have hpyr := hP.two_b55_le hF h4
  have hn : cnt P F 0 = 8 := congrArg Row.n hrow
  have hl := hP.two_q4_lb hF h4 hn (fun _ => 0)
    (fun _ _ _ _ => by positivity) (fun _ _ _ => rfl)
  simp only [Finset.sum_const_zero, add_zero] at hl
  omega

/-- Before global ridge parity is applied, a full facet has two or three
tetrahedra. The only possible extra tetrahedron replaces two bipyramids by an octahedron. -/
lemma IsCSPolytope5.fewFull18_one_pair_full_tetra_bounds
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = OnePairProfile.fullRow 20) :
    2 ≤ tcnt P F (4, 6, 4) ∧ tcnt P F (4, 6, 4) ≤ 3 := by
  obtain ⟨hq, -, hb, hw, hy⟩ := hP.fewFull18_one_pair_full_quads hv hh hc hlt hF h4 hrow
  have hrow' := hrow
  simp only [faceRow, OnePairProfile.fullRow, Row.mk.injEq] at hrow'
  obtain ⟨hn, -, hp, hr, hJ⟩ := hrow'
  obtain ⟨c1, c2, c3, -⟩ := hP.facet8_arith hF h4 hn
  have h7 := fun e p => hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn (by omega) e p
  have hprism : tcnt P F (6, 9, 5) = 0 := by
    by_contra hne
    have h := hP.b55_add_three_le_of_prism (by omega : 1 ≤ tcnt P F (6, 9, 5))
    omega
  simp only [hy, hprism, h7, hr, hJ, hp] at c1 c2 c3
  omega

/-- The small catalogue fixes the tetrahedron counts of Y and J. -/
lemma IsCSPolytope5.one_pair_small_tetra {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = excRow ∨ faceRow P F = OnePairProfile.jRow) :
    tcnt P F (4, 6, 4) = if faceRow P F = OnePairProfile.jRow then 3 else 2 := by
  have hn : cnt P F 0 ≤ 7 := by
    rcases hrow with h | h <;> have := congrArg Row.n h <;> exact this.le
  obtain ⟨hmem, heq⟩ := hP.facet_rowX hF h4 hn
  have hprof := (hP.facet_profile hF h4 hn).2
  have hcheck : ∀ X ∈ smallRowsX, X.1 = excRow ∨ X.1 = OnePairProfile.jRow →
      X.2.1.headD 0 = if X.1 = OnePairProfile.jRow then 3 else 2 := by decide +kernel
  have h := hcheck (rowXOf F) hmem (by change rowOf F = _ ∨ rowOf F = _; rwa [heq])
  rw [hprof] at h
  change _ = if rowOf F = _ then 3 else 2 at h
  rw [heq] at h
  simpa only [fv7, List.map_cons, List.headD_cons, ← hP.tcnt_eq_card] using h

/-- Ridge parity removes the extra-tetrahedron possibility simultaneously for
both full facets: the total is between 44 and 46 and is divisible by four. -/
theorem IsCSPolytope5.fewFull18_one_pair_full_tetra
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = OnePairProfile.fullRow 20) : tcnt P F (4, 6, 4) = 2 := by
  obtain ⟨hall, hY, hJ, hH, -, -⟩ := hP.fewFull18_one_pair_profile hv hh hc hlt
  let lower : Row → ℕ := fun R => if R = OnePairProfile.jRow then 3 else 2
  let upper : Row → ℕ := fun R => if R = OnePairProfile.fullRow 20 then 3 else lower R
  have hl := sum_three lower hall (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hu := sum_three upper hall (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [hY, hJ, hH] at hl hu
  norm_num [lower, upper, excRow, OnePairProfile.jRow, OnePairProfile.fullRow] at hl hu
  rw [hP.facetRows_sum] at hl hu
  have hsumL : (∑ H ∈ (hP.kfaces_finite 4).toFinset, lower (faceRow P H)) = 44 := hl
  have hsumU : (∑ H ∈ (hP.kfaces_finite 4).toFinset, upper (faceRow P H)) = 46 := hu
  have hpoint : ∀ H ∈ (hP.kfaces_finite 4).toFinset,
      lower (faceRow P H) ≤ tcnt P H (4, 6, 4) ∧
        tcnt P H (4, 6, 4) ≤ upper (faceRow P H) := by
    intro H hH
    have hHP := hH
    rw [Set.Finite.mem_toFinset] at hHP
    have hm : faceRow P H ∈ facetRows P := by
      rw [hP.facetRows_eq]
      exact List.mem_map.2 ⟨H, Finset.mem_toList.2 hH, rfl⟩
    rcases hall _ hm with hY | hJ | hH
    · have ht := hP.one_pair_small_tetra hHP.1 hHP.2 (Or.inl hY)
      norm_num [hY, lower, upper, excRow, OnePairProfile.jRow, OnePairProfile.fullRow] at ht ⊢
      omega
    · have ht := hP.one_pair_small_tetra hHP.1 hHP.2 (Or.inr hJ)
      norm_num [hJ, lower, upper, OnePairProfile.jRow, OnePairProfile.fullRow] at ht ⊢
      omega
    · have ht := hP.fewFull18_one_pair_full_tetra_bounds hv hh hc hlt hHP.1 hHP.2 hH
      simpa only [hH, lower, upper, ite_true,
        show OnePairProfile.fullRow 20 ≠ OnePairProfile.jRow by decide +kernel, ite_false] using ht
  have hlo := Finset.sum_le_sum fun H hH => (hpoint H hH).1
  have hhi := Finset.sum_le_sum fun H hH => (hpoint H hH).2
  have hdvd := hP.four_dvd_sum_tcnt (4, 6, 4)
  have heq : (∑ H ∈ (hP.kfaces_finite 4).toFinset, lower (faceRow P H)) =
      ∑ H ∈ (hP.kfaces_finite 4).toFinset, tcnt P H (4, 6, 4) := by omega
  have ht := (Finset.sum_eq_sum_iff_of_le (fun H hH => (hpoint H hH).1)).1 heq F
    (by rw [Set.Finite.mem_toFinset]; exact ⟨hF, h4⟩)
  simpa [lower, hrow, OnePairProfile.fullRow, OnePairProfile.jRow] using ht.symm

/-- The full facet's complete 3-face profile, obtained from saturation and
global parity without classifying eight-vertex polytopes. -/
theorem IsCSPolytope5.fewFull18_one_pair_full_types
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = OnePairProfile.fullRow 20) :
    tcnt P F (4, 6, 4) = 2 ∧ tcnt P F (5, 8, 5) = 4 ∧ tcnt P F (5, 9, 6) = 2 ∧
      ∀ T ∈ faces P, T ⊆ F → dim T = 3 →
        tri3 P T = (4, 6, 4) ∨ tri3 P T = (5, 8, 5) ∨ tri3 P T = (5, 9, 6) := by
  have ht := hP.fewFull18_one_pair_full_tetra hv hh hc hlt hF h4 hrow
  obtain ⟨-, -, -, -, hy⟩ := hP.fewFull18_one_pair_full_quads hv hh hc hlt hF h4 hrow
  have hrow' := hrow
  simp only [faceRow, OnePairProfile.fullRow, Row.mk.injEq] at hrow'
  obtain ⟨hn, -, -, hr, hJ⟩ := hrow'
  obtain ⟨c1, c2, -, -⟩ := hP.facet8_arith hF h4 hn
  simp only [ht, hy, hr, hJ] at c1 c2
  refine ⟨ht, hy, by omega, ?_⟩
  intro T hT hTF hT3
  have h1 := hP.one_le_tcnt hT hTF hT3
  have hne : T ≠ F := by rintro rfl; omega
  have hltT := hP.cnt_zero_lt hT hF hTF hne
  have hin := hP.tri3_mem_fv8 hT hT3 (by omega)
  simp only [fv8, List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with h | h | h | h | h | h | h | h | h | h | h | h <;>
    rw [h] at h1 ⊢ <;> first | (left; rfl) | (right; left; rfl) | (right; right; rfl) | omega

end Kalai5
