import Kalai5.Endpoints.PrismNoB55
import Kalai5.Endpoints.G4S6Closure

namespace Kalai5
open scoped Classical

/-- The V entry incorporates the prism/b55 geometric obstruction. -/
def q55VTwelveRowWeight (R : Row) : ℕ :=
  if R = ⟨8,19,19,8,39⟩ then 12 else q55BSixRowWeight R

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.q55_vTwelve_row_weight {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) :
    (q55VTwelveRowWeight (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F := by
  unfold q55VTwelveRowWeight
  split_ifs with he
  · have hw := (hP.v_weight_twelve hF h4 he).2.2.2
    omega
  · exact hP.q55_bSix_row_weight hF h4

theorem IsCSPolytope5.fewFull18_positive_vTwelve_budget
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (((facetRows P).map q55VTwelveRowWeight).sum : ℤ) ≤ 156 - 6 * (flagDataOf P).Gs := by
  rw [hP.facetRows_sum q55VTwelveRowWeight,Nat.cast_sum]
  apply (Finset.sum_le_sum (fun F hF => ?_)).trans
    (hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt)
  rw [Set.Finite.mem_toFinset] at hF
  exact hP.q55_vTwelve_row_weight hF.1 hF.2

theorem IsCSPolytope5.fewFull18_positive_vTwelve_pair_budget
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (((positivePairRows P).map q55VTwelveRowWeight).sum : ℤ) ≤ 78 - 3 * (flagDataOf P).Gs := by
  have hb := hP.fewFull18_positive_vTwelve_budget hv hh h1 h6 hlt
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  rw [(hp.map q55VTwelveRowWeight).sum_eq,List.map_append,List.sum_append,Nat.cast_add] at hb
  omega

theorem IsCSPolytope5.fewFull18_positive_g4s2_D_ne
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) (hS : (flagDataOf P).Gs = 2) :
    positivePairRows P ≠ TwoPairPositiveProfile.g4s2PairsD := by
  intro he
  have hb := hP.fewFull18_positive_vTwelve_pair_budget hv hh h1 h6 hlt
  rw [he,hS] at hb
  have hw : (TwoPairPositiveProfile.g4s2PairsD.map q55VTwelveRowWeight).sum = 78 := by decide +kernel
  rw [hw] at hb
  omega

theorem IsCSPolytope5.fewFull18_positive_g4s2_two_profiles
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243)
    (hG : (flagDataOf P).G = 4) (hS : (flagDataOf P).Gs = 2) :
    positivePairRows P ∈ [TwoPairPositiveProfile.g4s2PairsA,TwoPairPositiveProfile.g4s2PairsC] := by
  have hm := hP.fewFull18_positive_g4s2_three_profiles hv hh h1 h6 hlt hG hS
  have hn := hP.fewFull18_positive_g4s2_D_ne hv hh h1 h6 hlt hS
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm ⊢
  tauto

end Kalai5
