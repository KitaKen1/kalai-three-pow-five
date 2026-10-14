import Kalai5.Endpoints.TwoPairZeroProfile

/-! Both remaining profiles saturate every local refined Q55 weight. -/
namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.two_pair_zero_weight_sum
    (hv : fvec P 0=16) (hh : fvec P 4=18) (hc : cnt8 (facetRows P)=4)
    (hG : (flagDataOf P).G=0) (hlt : (faces P).ncard<243) :
    ((facetRows P).map q55RefinedRowWeight).sum+6*(flagDataOf P).e=420 := by
  rcases hP.two_pair_zero_profile hv hh hc hG hlt with ⟨hp,he,_⟩ | ⟨hp,he,_⟩
  all_goals
    rw [(hp.map q55RefinedRowWeight).sum_eq,he]
    decide +kernel

theorem IsCSPolytope5.two_pair_zero_weight_eq
    (hv : fvec P 0=16) (hh : fvec P 4=18) (hc : cnt8 (facetRows P)=4)
    (hG : (flagDataOf P).G=0) (hlt : (faces P).ncard<243)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F=4) :
    q55w P F+2*exc P F=q55RefinedRowWeight (faceRow P F) := by
  have hS := hP.fewFull18_zero_stress_polar_ten hv hh (by omega) (by omega) hlt hG
  have hI := (hP.zero_stress_eighteen_budgets hv hh hG hS).1
  have hA := hP.A_eq_zero_of_G_eq_zero hG
  have hD := hP.flagData_valid
  have hbudget : 4*(flagDataOf P).A+2*((flagDataOf P).f024-3*((flagDataOf P).y : ℤ))+
      6*(flagDataOf P).e=420 := by
    have he := hD.euler
    have h024 := hD.f024_eq
    have hvD : (flagDataOf P).v=16 := hv
    have hhD : (flagDataOf P).h=18 := hh
    simp only [FlagData.G,FlagData.Gs,FlagData.A,hvD,hhD] at hG hS hA he h024 ⊢
    omega
  have hsum := hP.two_pair_zero_weight_sum hv hh hc hG hlt
  rw [hP.facetRows_sum q55RefinedRowWeight] at hsum
  have hsumZ : (∑ H ∈ (hP.kfaces_finite 4).toFinset,
      (q55RefinedRowWeight (faceRow P H) : ℤ))+6*(flagDataOf P).e=420 := by
    exact_mod_cast hsum
  have hlo : ∀ H ∈ (hP.kfaces_finite 4).toFinset,
      (q55RefinedRowWeight (faceRow P H) : ℤ)≤q55w P H+2*exc P H := by
    intro H hH
    rw [Set.Finite.mem_toFinset] at hH
    exact hP.q55_refined_row_weight hH.1 hH.2
  have hl := Finset.sum_le_sum hlo
  have hu := hP.q55 hv
  have heq : (∑ H ∈ (hP.kfaces_finite 4).toFinset,(q55RefinedRowWeight (faceRow P H) : ℤ))=
      ∑ H ∈ (hP.kfaces_finite 4).toFinset,(q55w P H+2*exc P H) := by omega
  exact ((Finset.sum_eq_sum_iff_of_le hlo).1 heq F
    (by rw [Set.Finite.mem_toFinset]; exact ⟨hF,h4⟩)).symm

end Kalai5
