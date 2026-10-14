import Kalai5.Endpoints.TwoPairZeroB19Obstruction

/-! The saturated B19 shell is impossible; strengthen its weight from four to five. -/
namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.q55_b_five {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F=4)
    (hrow : faceRow P F=⟨8,19,19,8,38⟩) :
    5 ≤ q55w P F+2*exc P F := by
  have hlo := hP.q55_b_four hF h4 hrow
  by_contra hbad
  have hw : q55w P F+2*exc P F=q55RefinedRowWeight (faceRow P F) := by
    rw [hrow]
    have hr : q55RefinedRowWeight ⟨8,19,19,8,38⟩=4 := by decide +kernel
    rw [hr]
    omega
  obtain ⟨s⟩ := hP.b19_shell_of_refined_equality hF h4 hrow hw
  exact s.impossible hP hF h4 (congrArg Row.n hrow) (congrArg Row.r hrow)

omit hP in
def q55BFiveRowWeight (R : Row) : ℕ :=
  if R=⟨8,19,19,8,38⟩ then 5 else q55RefinedRowWeight R

omit hP in
lemma q55RefinedRowWeight_le_bFive (R : Row) : q55RefinedRowWeight R ≤ q55BFiveRowWeight R := by
  unfold q55BFiveRowWeight
  split_ifs with h
  · subst R; decide +kernel
  · exact le_rfl

theorem IsCSPolytope5.q55_bFive_row_weight {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F=4) :
    (q55BFiveRowWeight (faceRow P F) : ℤ) ≤ q55w P F+2*exc P F := by
  unfold q55BFiveRowWeight
  split_ifs with h
  · exact hP.q55_b_five hF h4 h
  · exact hP.q55_refined_row_weight hF h4

theorem IsCSPolytope5.q55_bFive_rows (hv : fvec P 0=16) :
    (((facetRows P).map q55BFiveRowWeight).sum : ℤ) ≤
      4*(flagDataOf P).A+2*((flagDataOf P).f024-3*((flagDataOf P).y : ℤ)) := by
  rw [hP.facetRows_sum q55BFiveRowWeight,Nat.cast_sum]
  exact (Finset.sum_le_sum (fun F hF => by
    rw [Set.Finite.mem_toFinset] at hF
    exact hP.q55_bFive_row_weight hF.1 hF.2)).trans (hP.q55 hv)

theorem IsCSPolytope5.two_pair_zero_profileB
    (hv : fvec P 0=16) (hh : fvec P 4=18) (hc : cnt8 (facetRows P)=4)
    (hG : (flagDataOf P).G=0) (hlt : (faces P).ncard<243) :
    (facetRows P).Perm TwoPairZeroProfile.profileB ∧
      (flagDataOf P).e=58 ∧ (flagDataOf P).r=60 := by
  rcases hP.two_pair_zero_profile hv hh hc hG hlt with ⟨hA,_,_⟩ | hB
  · have hm : (⟨8,19,19,8,38⟩ : Row) ∈ facetRows P :=
      hA.mem_iff.mpr (by decide +kernel)
    obtain ⟨F,hF,h4,hrow⟩ := hP.mem_facetRows hm
    have hlo := hP.q55_b_five hF h4 hrow
    have heq := hP.two_pair_zero_weight_eq hv hh hc hG hlt hF h4
    rw [hrow] at heq
    have hr : q55RefinedRowWeight ⟨8,19,19,8,38⟩=4 := by decide +kernel
    rw [hr] at heq
    omega
  · exact hB

end Kalai5
