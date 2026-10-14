import Kalai5.Rigidity.Stress4
import Kalai5.Faces.Counting
import Kalai5.Polar.Flags
import Kalai5.Alexandrov.Final

/-!
# The two-facet bound on facet rows

`IsCSPolytope5.cntBig_le_two`: if some facet has `g ≥ j`, then at most two facets (one antipodal
pair) have `2g + 2j > G`.  Three distinct facets cannot all lie in `{H₀, -H₀}`, and for a facet
`H' ≠ ±H₀` the two-facet stress localization gives `2 g(H₀) + 2 g(H') ≤ G`.  The same holds for
the facets of the polar, with `G*` in place of `G`.
-/

namespace Kalai5

open Set

/-- Number of rows with `τ < 2g`. -/
def cntBig (rows : List Row) (τ : ℤ) : ℕ := (rows.filter fun R => decide (τ < 2 * R.g)).length

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **At most one antipodal pair of facets has `2g + 2j > G`** when some facet has `g ≥ j`. -/
theorem IsCSPolytope5.cntBig_le_two (hW : WhiteleyCSLoc P) {j : ℤ}
    (hj : ∃ R ∈ facetRows P, j ≤ R.g) :
    cntBig (facetRows P) ((flagDataOf P).G - 2 * j) ≤ 2 := by
  classical
  obtain ⟨R0, hR0, hjR0⟩ := hj
  obtain ⟨H0, hH0, h40, rfl⟩ := hP.mem_facetRows hR0
  unfold cntBig
  rw [hP.facetRows_eq, List.filter_map, List.length_map]
  set S := (hP.kfaces_finite 4).toFinset with hS
  set L := S.toList.filter ((fun R => decide ((flagDataOf P).G - 2 * j < 2 * R.g)) ∘ faceRow P)
    with hL
  have hnd : L.Nodup := (Finset.nodup_toList S).filter _
  have hmem : ∀ H ∈ L, (H ∈ faces P ∧ dim H = 4) ∧ (flagDataOf P).G - 2 * j < 2 * (faceRow P H).g := by
    intro H hH
    rw [hL, List.mem_filter] at hH
    obtain ⟨h1, h2⟩ := hH
    rw [Finset.mem_toList, hS, Set.Finite.mem_toFinset] at h1
    simp only [Function.comp_apply, decide_eq_true_eq] at h2
    exact ⟨h1, h2⟩
  by_contra hlt
  push_neg at hlt
  -- a facet of `L` other than `±H₀`
  obtain ⟨H', hH'L, hne, hne'⟩ : ∃ H' ∈ L, H' ≠ H0 ∧ H' ≠ -H0 := by
    by_contra hall
    push_neg at hall
    have hsub : L.toFinset ⊆ ({H0, -H0} : Finset (Set E5)) := by
      intro H hH
      rw [List.mem_toFinset] at hH
      rw [Finset.mem_insert, Finset.mem_singleton]
      by_cases h : H = H0
      · exact Or.inl h
      · exact Or.inr (hall H hH h)
    have h1 := Finset.card_le_card hsub
    have h2 : ({H0, -H0} : Finset (Set E5)).card ≤ 2 := Finset.card_le_two
    rw [List.toFinset_card_of_nodup hnd] at h1
    omega
  obtain ⟨⟨hH', h4'⟩, hbig⟩ := hmem H' hH'L
  have hloc := hP.two_facet_localization hW hH0 h40 hH' h4' hne hne'
  linarith

/-- **The polar version**: at most one antipodal pair of facets of `P°` has `2g + 2j > G*`. -/
theorem IsCSPolytope5.cntBig_le_two_polar {j : ℤ} (hj : ∃ R ∈ facetRows (polarSet P), j ≤ R.g) :
    cntBig (facetRows (polarSet P)) ((flagDataOf P).Gs - 2 * j) ≤ 2 := by
  have h := hP.polar.cntBig_le_two (hP.polar.whiteleyCSLoc_of_w3 alexandrov3_proof) hj
  rwa [hP.G_polar] at h

/-- The facet version with the Whiteley data built from Alexandrov's theorem. -/
theorem IsCSPolytope5.cntBig_le_two' {j : ℤ} (hj : ∃ R ∈ facetRows P, j ≤ R.g) :
    cntBig (facetRows P) ((flagDataOf P).G - 2 * j) ≤ 2 :=
  hP.cntBig_le_two (hP.whiteleyCSLoc_of_w3 alexandrov3_proof) hj

end cs

end Kalai5
