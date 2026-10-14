import Kalai5.Endpoints.FullNineTetra
import Kalai5.Endpoints.TwoPairPositiveFullPolygon

namespace Kalai5
open Set
open scoped Classical
namespace G2S2
def nineR0Pairs : List Row := [excRow,excRow,excRow,excRow,excRow,excRow,G2S4.dRow,r0Row,⟨8,20,21,9,41⟩]
end G2S2
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The R0 row has one tetrahedral ridge, but the other full pair has
nine ridges and forces two. This excludes original profile 22. -/
theorem IsCSPolytope5.g2s2_nine_r0_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hp : (facetRows P).Perm (G2S2.nineR0Pairs ++ G2S2.nineR0Pairs)) : False := by
  have hm : (⟨8,20,21,9,41⟩ : Row) ∈ facetRows P := hp.mem_iff.2 (List.mem_append_left _ (by decide +kernel))
  obtain ⟨F,hF,hF4,hFR⟩ := hP.mem_facetRows hm
  have hmH : r0Row ∈ facetRows P := hp.mem_iff.2 (List.mem_append_left _ (by decide +kernel))
  obtain ⟨H,hH,hH4,hHR⟩ := hP.mem_facetRows hmH
  have hF8 : cnt P F 0 = 8 := congrArg Row.n hFR
  have hr : cnt P F 3 = 9 := congrArg Row.r hFR
  have hH8 : cnt P H 0 = 8 := congrArg Row.n hHR
  have hH7 : cnt P H 3 = 7 := congrArg Row.r hHR
  have hHF : H ≠ F := by intro he; rw [he,hr] at hH7; omega
  have hHnF : H ≠ -F := by intro he; rw [he,hP.cnt_neg,hr] at hH7; omega
  have hb := hP.full_nine_other_full_two_tetra hv hh hc hF hF4 hF8 hr hH hH4 hH8 hHF hHnF
  have ht := (hP.r0_types hH hH4 hHR).1
  omega

end Kalai5
