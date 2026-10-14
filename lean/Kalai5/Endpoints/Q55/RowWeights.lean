import Kalai5.Endpoints.WeightV

/-!
# Proven row weights for the sixteen-vertex Q55 inequality

This is a deliberately weak table: B has weight 1 and V has weight 4. It uses
neither a classification of all eight-vertex facets nor the stronger conjectural
weights used in the earlier exploratory scripts.
-/

namespace Kalai5

open Set
open scoped Classical

def q55RowWeight (R : Row) : ℕ :=
  if R = excRow then 9
  else if R = eRow then 4
  else if R = r0Row then 15
  else if R = r35Row then 10
  else if R = zRow then 9
  else if R = ⟨8, 19, 19, 8, 38⟩ then 1
  else q55ElementaryWeight R

/-- Stronger table for the remaining eighteen-facet endpoint. -/
def q55StrongRowWeight (R : Row) : ℕ :=
  if R = ⟨8, 19, 19, 8, 38⟩ ∨ R = ⟨8, 20, 20, 8, 39⟩ then 3
  else if R = ⟨8, 19, 19, 8, 39⟩ then 8
  else if R = ⟨8, 19, 19, 8, 40⟩ then 10
  else if R = ⟨8, 19, 20, 9, 41⟩ then 8
  else if R = ⟨8, 19, 19, 8, 41⟩ then 12
  else q55RowWeight R

lemma q55RowWeight_le_strong (R : Row) : q55RowWeight R ≤ q55StrongRowWeight R := by
  unfold q55StrongRowWeight
  split_ifs with h hV h40 h9 h41
  · rcases h with rfl | rfl <;>
      norm_num [q55RowWeight, q55ElementaryWeight, excRow, eRow, r0Row, r35Row, zRow]
  · subst R
    norm_num [q55RowWeight, q55ElementaryWeight, excRow, eRow, r0Row, r35Row, zRow]
  · subst R
    norm_num [q55RowWeight, q55ElementaryWeight, excRow, eRow, r0Row, r35Row, zRow]
  · subst R
    norm_num [q55RowWeight, q55ElementaryWeight, excRow, eRow, r0Row, r35Row, zRow]
  · subst R
    norm_num [q55RowWeight, q55ElementaryWeight, excRow, eRow, r0Row, r35Row, zRow]
  · exact le_rfl

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.q55w_good {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hg : goodRow (faceRow P F)) : q55w P F = q4 P F := by
  have he : b55set P F = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro Q hQ
    have h1 := hP.good_five_one hF h4 hg hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2.1
    have h2 := hP.card_three_through hF h4 hQ.1 hQ.2.1 hQ.2.2.1
    have hfilter : (hP.below_finite F 3).toFinset.filter (fun T => Q ⊆ T ∧ cnt P T 0 = 5) =
        (hP.below_finite F 3).toFinset.filter (fun T => Q ⊆ T) := by
      ext T
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      constructor
      · tauto
      · rintro ⟨⟨hT, hTF, hT3⟩, hQT⟩
        refine ⟨⟨hT, hTF, hT3⟩, hQT, ?_⟩
        by_contra h5
        have hm : T ∈ non5 P F Q := ⟨hT, hTF, hT3, hQT, h5⟩
        rw [hQ.2.2.2.2] at hm
        exact hm
    rw [hfilter, h2] at h1
    omega
  rw [hP.q55w_eq_b55 F, he, Set.ncard_empty]
  simp

lemma IsCSPolytope5.q55_qlWeight {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    (qlWeight (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F := by
  by_cases hg : goodRow (faceRow P F)
  · have hw := hP.weight_ge hF h4
    rw [if_pos hg, one_mul, ← hP.q55w_good hF h4 hg] at hw
    exact hw
  · have hY : faceRow P F ≠ excRow := fun h => hg (Or.inl h)
    have hE : faceRow P F ≠ eRow := fun h => hg (Or.inr h)
    simp only [qlWeight, hY, hE, ite_false, Nat.cast_zero]
    exact hP.q55w_add_exc_nonneg F

theorem IsCSPolytope5.q55_row_weight {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    (q55RowWeight (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F := by
  unfold q55RowWeight
  split_ifs with hY hE hR0 hR35 hZ hB
  · have := hP.q55_qlWeight hF h4
    rwa [hY, qlWeight, if_pos rfl] at this
  · have := hP.q55_qlWeight hF h4
    rw [hE] at this
    norm_num [qlWeight, eRow, excRow] at this
    exact this
  · exact hP.q55_r0 hF h4 hR0
  · exact hP.q55_r35 hF h4 hR35
  · exact hP.q55_r19 hF h4 hZ
  · exact hP.q55_b_pos hF h4 hB
  · exact hP.q55_elementary hF h4

/-- The single row-weight inequality consumed by the new endpoint certificates. -/
theorem IsCSPolytope5.q55_rows (h16 : fvec P 0 = 16) :
    (((facetRows P).map q55RowWeight).sum : ℤ) ≤
      4 * (flagDataOf P).A + 2 * (((flagDataOf P).f024 : ℤ) - 3 * (flagDataOf P).y) := by
  rw [hP.facetRows_sum q55RowWeight, Nat.cast_sum]
  calc ∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55RowWeight (faceRow P F) : ℤ)
      ≤ ∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F) := by
        refine Finset.sum_le_sum fun F hF => ?_
        rw [Set.Finite.mem_toFinset] at hF
        exact hP.q55_row_weight hF.1 hF.2
    _ ≤ _ := hP.q55 h16

theorem IsCSPolytope5.q55_strong_row_weight {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) :
    (q55StrongRowWeight (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F := by
  unfold q55StrongRowWeight
  split_ifs with h hV h40 h9 h41
  · rcases h with hB | hC
    · exact hP.q55_b_three hF h4 hB
    · exact hP.q55_c_three hF h4 hC
  · exact hP.q55_v_eight hF h4 hV
  · exact hP.q55_19_40_ten hF h4 h40
  · exact hP.q55_19_20_9_eight hF h4 h9
  · exact hP.q55_19_41_twelve hF h4 h41
  · exact hP.q55_row_weight hF h4

/-- The strengthened global Q55 budget for the eighteen-facet endpoint. -/
theorem IsCSPolytope5.q55_strong_rows (h16 : fvec P 0 = 16) :
    (((facetRows P).map q55StrongRowWeight).sum : ℤ) ≤
      4 * (flagDataOf P).A + 2 * (((flagDataOf P).f024 : ℤ) - 3 * (flagDataOf P).y) := by
  rw [hP.facetRows_sum q55StrongRowWeight, Nat.cast_sum]
  calc ∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55StrongRowWeight (faceRow P F) : ℤ)
      ≤ ∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F) := by
        refine Finset.sum_le_sum fun F hF => ?_
        rw [Set.Finite.mem_toFinset] at hF
        exact hP.q55_strong_row_weight hF.1 hF.2
    _ ≤ _ := hP.q55 h16

end Kalai5
