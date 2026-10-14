import Kalai5.Endpoints.TwoPairZeroCounts

/-! Only two actual facet-row profiles remain in the zero-stress two-pair cell. -/
namespace Kalai5
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.two_pair_zero_catalogue
    (hv : fvec P 0=16) (hh : fvec P 4=18) (hc : cnt8 (facetRows P)=4)
    (hG : (flagDataOf P).G=0) (hS : (flagDataOf P).Gs=10)
    (hlt : (faces P).ncard<243) :
    ∀ R ∈ facetRows P,R ∈ TwoPairZeroProfile.catalogue := by
  have hb := hP.two_pair_zero_row_bounds hv hh hc hG hS hlt
  intro R hR
  obtain ⟨hn6,hn8,hg,hr⟩ := hb R hR
  have hreal := hP.facetRows_real R hR
  by_cases hn : R.n=8
  · apply List.mem_append_right
    exact TwoPairZeroProfile.full_classification hn (hr hn).1 (hr hn).2 hg
      (realRow_euler hreal) (realRow_B4 hreal) (realRow_polygon_excess hreal)
      (hP.facetRows_not_fake8 R hR)
  · apply List.mem_append_left
    have hrow := hP.rowOK_P_le (nmax := 8) (fun S hS => (hb S hS).2.1)
      (show ∀ S ∈ facetRows P,S ∉ ([] : List Row) from fun _ _ => List.not_mem_nil) R hR
    exact TwoPairZeroProfile.small_classification R (hrow.small (by omega)) hn6 (by omega) hg

theorem IsCSPolytope5.two_pair_zero_profile
    (hv : fvec P 0=16) (hh : fvec P 4=18) (hc : cnt8 (facetRows P)=4)
    (hG : (flagDataOf P).G=0) (hlt : (faces P).ncard<243) :
    ((facetRows P).Perm TwoPairZeroProfile.profileA ∧
      (flagDataOf P).e=56 ∧ (flagDataOf P).r=62) ∨
    ((facetRows P).Perm TwoPairZeroProfile.profileB ∧
      (flagDataOf P).e=58 ∧ (flagDataOf P).r=60) := by
  have hS := hP.fewFull18_zero_stress_polar_ten hv hh (by omega) (by omega) hlt hG
  obtain ⟨hI,h14,hw⟩ := hP.zero_stress_eighteen_budgets hv hh hG hS
  apply TwoPairZeroProfile.counts_closure (facetRows P) (flagDataOf P).e (flagDataOf P).r
    (hP.two_pair_zero_catalogue hv hh hc hG hS hlt) hP.facetRows_filter_even
    (hP.facetRows_length.trans hh) (hP.facetRows_sum_n.trans hI) hc
    (hP.facetRows_sum_e.trans h14) hP.facetRows_sum_r
    (by exact_mod_cast hP.t_le_of_faces_lt hlt) hw hP.flagData_valid.even_e hP.flagData_valid.even_r

end Kalai5
