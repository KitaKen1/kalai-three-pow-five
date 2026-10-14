import Kalai5.Endpoints.TwoPairPositivePairs

/-! A proved, budget-pruned multiset enumerator for the positive cells. -/
namespace Kalai5.TwoPairPositiveProfile

def fullIndicator (R : Row) : ℕ := if R.n = 8 then 1 else 0

def expandRows (rows : List Row) (m : Row → ℕ) : List Row :=
  rows.flatMap fun R => List.replicate (m R) R

/-- One table row, with a supplied continuation for the remaining rows. -/
def searchStep (R : Row) (next : ℕ → ℕ → ℕ → List (List Row)) (n f b : ℕ) :
    List (List Row) :=
  if n = 0 then (if f = 0 then [[]] else []) else
    (List.range (n + 1)).flatMap fun k =>
      if k * fullIndicator R ≤ f ∧ k * ridgeExcess R ≤ b then
        (next (n - k) (f - k * fullIndicator R) (b - k * ridgeExcess R)).map
          (fun tail => List.replicate k R ++ tail)
      else []

/-- An explicit fold avoids a course-of-values recursion table in kernel reduction. -/
def searchRows (rows : List Row) (n f b : ℕ) : List (List Row) :=
  rows.foldr searchStep (fun n f _ => if n = 0 ∧ f = 0 then [[]] else []) n f b

/-- Completeness is proved for arbitrary multiplicities, independently of computed output. -/
theorem searchRows_complete (rows : List Row) (m : Row → ℕ) (n f b : ℕ)
    (hlen : (expandRows rows m).length = n)
    (hfull : ((expandRows rows m).map fullIndicator).sum = f)
    (hbudget : ((expandRows rows m).map ridgeExcess).sum ≤ b) :
    expandRows rows m ∈ searchRows rows n f b := by
  induction rows generalizing n f b with
  | nil =>
    simp only [expandRows,List.flatMap_nil,List.length_nil,List.map_nil,List.sum_nil] at hlen hfull ⊢
    simp [searchRows,← hlen,← hfull]
  | cons R rs ih =>
    have hl : m R + (expandRows rs m).length = n := by
      simpa [expandRows] using hlen
    have hf : m R * fullIndicator R + ((expandRows rs m).map fullIndicator).sum = f := by
      simpa [expandRows,List.map_append,List.sum_append,List.map_replicate,
        List.sum_replicate,smul_eq_mul] using hfull
    have hb : m R * ridgeExcess R + ((expandRows rs m).map ridgeExcess).sum ≤ b := by
      simpa [expandRows,List.map_append,List.sum_append,List.map_replicate,
        List.sum_replicate,smul_eq_mul] using hbudget
    change expandRows (R :: rs) m ∈ searchStep R (searchRows rs) n f b
    by_cases hz : n = 0
    · have he : expandRows (R :: rs) m = [] := List.eq_nil_of_length_eq_zero (hlen.trans hz)
      have hf0 : f = 0 := by simpa only [he,List.map_nil,List.sum_nil] using hfull.symm
      rw [he]
      simp [searchStep,hz,hf0]
    simp only [searchStep,if_neg hz]
    apply List.mem_flatMap.2
    refine ⟨m R,List.mem_range.2 (by omega),?_⟩
    rw [if_pos (show m R * fullIndicator R ≤ f ∧ m R * ridgeExcess R ≤ b from ⟨by omega,by omega⟩)]
    apply List.mem_map.2
    refine ⟨expandRows rs m,ih (n - m R) (f - m R * fullIndicator R)
      (b - m R * ridgeExcess R) (by omega) (by omega) (by omega),?_⟩
    rfl

def admissible (G S : ℤ) (rows : List Row) : Prop :=
  2 * ((rows.map Row.e).sum : ℤ) = 288 + S ∧
  (rows.map Row.g).sum = G - 1 ∧
  (rows.map ridgeExcess).sum = 4 ∧
  2 * ((rows.map q55BSixRowWeight).sum : ℤ) ≤ 156 - 6 * S

instance (G S : ℤ) (rows : List Row) : Decidable (admissible G S rows) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def profiles (G S : ℤ) : List (List Row) :=
  (searchRows catalogue 9 2 4).filter fun rows => decide (admissible G S rows)

def allProfiles : List (List Row) :=
  TwoPairPositive.remainingCells.flatMap fun cell => profiles cell.1 cell.2

-- Generate the recursion equations above before sealing computation from elaboration.
attribute [irreducible] searchStep searchRows profiles allProfiles

end Kalai5.TwoPairPositiveProfile

namespace Kalai5
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

set_option maxHeartbeats 2000000 in
/-- Every actual counterexample belongs to the computed 151-profile list. -/
theorem IsCSPolytope5.fewFull18_positive_profile_mem
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    positivePairRows P ∈ TwoPairPositiveProfile.allProfiles := by
  obtain ⟨hlen,hfull,_,_,he,hg,hw,hb⟩ := hP.fewFull18_positive_pair_budgets hv hh h1 h6 hlt
  have hfull' : ((positivePairRows P).map TwoPairPositiveProfile.fullIndicator).sum = 2 := by
    change ((positivePairRows P).map (fun R => if R.n = 8 then 1 else 0)).sum = 2
    rw [← length_filter_eq_sum]
    exact hfull
  have hsearch : positivePairRows P ∈ TwoPairPositiveProfile.searchRows
      TwoPairPositiveProfile.catalogue 9 2 4 :=
    TwoPairPositiveProfile.searchRows_complete TwoPairPositiveProfile.catalogue
      (fun R => (facetRows P).count R / 2)
      9 2 4 hlen hfull' hb.le
  have hmem : positivePairRows P ∈ TwoPairPositiveProfile.profiles
      (flagDataOf P).G (flagDataOf P).Gs := by
    unfold TwoPairPositiveProfile.profiles
    exact List.mem_filter.2 ⟨hsearch,decide_eq_true (show TwoPairPositiveProfile.admissible
      (flagDataOf P).G (flagDataOf P).Gs (positivePairRows P) from ⟨he,hg,hb,hw⟩)⟩
  unfold TwoPairPositiveProfile.allProfiles
  exact (List.mem_flatMap (l := TwoPairPositive.remainingCells)
    (f := fun cell => TwoPairPositiveProfile.profiles cell.1 cell.2)
    (b := positivePairRows P)).2 ⟨((flagDataOf P).G,(flagDataOf P).Gs),
    (hP.fewFull18_positive_constraints hv hh h1 h6 hlt).2.1,hmem⟩

end Kalai5
