import Kalai5.Endpoints.R35ASupply
import Kalai5.Endpoints.TwoPairPositiveNineTetra

namespace Kalai5
open Set
open scoped Classical
namespace G2S2
def d36Row : Row := ⟨7,17,18,8,36⟩
def r35Pairs2 : List Row := [excRow,excRow,excRow,excRow,G2S4.aRow,G2S4.aRow,d36Row,r35Row,r35Row]
def r35Pairs8 : List Row := [excRow,excRow,excRow,excRow,excRow,G2S4.aRow,d36Row,r35Row,G2S4.bRow]
def r35Excluded : List (List Row) := [r35Pairs2,r35Pairs8]
end G2S2
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- In original profiles 2 and 8, every R35 needs two A facets, whereas
each A has only one six-vertex ridge. Their multiplicities violate this bound. -/
theorem IsCSPolytope5.g2s2_r35_profiles_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    {rows : List Row} (hp : (facetRows P).Perm (rows ++ rows))
    (hrows : rows ∈ G2S2.r35Excluded) : False := by
  have hcheck : ∀ rows ∈ G2S2.r35Excluded,
      r35Row ∈ rows ∧
      (∀ R ∈ rows, R = excRow ∨ R = G2S4.aRow ∨ R = G2S2.d36Row ∨ R = r35Row ∨ R = G2S4.bRow) ∧
      ((rows ++ rows).map fun R => if R = G2S4.aRow then 1 else 0).sum <
        2 * ((rows ++ rows).map fun R => if R = r35Row then 1 else 0).sum := by decide +kernel
  obtain ⟨hm,hcases,hbad⟩ := hcheck rows hrows
  have cases : ∀ F ∈ faces P, dim F = 4 →
      faceRow P F = excRow ∨ faceRow P F = G2S4.aRow ∨ faceRow P F = G2S2.d36Row ∨
        faceRow P F = r35Row ∨ faceRow P F = G2S4.bRow := by
    intro F hF h4
    exact hcases _ (hP.faceRow_mem_pair_rows hp hF h4)
  have hsmall : ∀ X ∈ faces P, dim X = 4 → cnt P X 0 ≠ 8 → cnt P X 0 = 7 := by
    intro X hX hX4 hn
    rcases cases X hX hX4 with h | h | h | h | h
    · exact congrArg Row.n h
    · exact congrArg Row.n h
    · exact congrArg Row.n h
    · exact False.elim (hn (congrArg Row.n h))
    · exact False.elim (hn (congrArg Row.n h))
  have hr : ∀ X ∈ faces P, dim X = 4 → cnt P X 0 = 8 → 7 ≤ cnt P X 3 := by
    intro X hX hX4 hn
    rcases cases X hX hX4 with h | h | h | h | h
    all_goals
      have h0 := congrArg Row.n h
      have h3 := congrArg Row.r h
      simp only [excRow,G2S4.aRow,G2S2.d36Row,r35Row,G2S4.bRow,faceRow] at h0 h3
      omega
  have hz : ∀ X, big2 P X = 0 := hP.big2_zero_of_r35_sixteen_mod_four hv (by rw [hh])
    (hp.mem_iff.2 (List.mem_append_left _ hm))
  have hpartner : ∀ F ∈ faces P, dim F = 4 → faceRow P F = r35Row →
      ∀ T ∈ faces P, T ⊆ F → dim T = 3 → tri3 P T = (6,10,6) →
        ∃ A, A ∈ faces P ∧ dim A = 4 ∧ faceRow P A = G2S4.aRow ∧ T ⊆ A := by
    intro F hF hF4 hFR T hT hTF hT3 ht
    obtain ⟨A,hA,hA4,hAF,hTA⟩ := hP.exists_other_facet hT hT3 hTF
    have hn := hP.r35_6106_partner_nonfull hv hh hc hsmall hr hF hF4 hFR hT hTF hT3 ht hA hA4 hAF hTA
    have hpos := hP.one_le_tcnt hT hTA hT3
    rw [ht] at hpos
    rcases cases A hA hA4 with hY | hAR | hD | hR | hB
    · have hzero := (hP.small_special_free_counts hA hA4 (by rw [hY]; decide +kernel)).1
      omega
    · exact ⟨A,hA,hA4,hAR,hTA⟩
    · have hzero := (hP.small_special_free_counts hA hA4 (by rw [hD]; decide +kernel)).1
      omega
    · exact False.elim (hn (congrArg Row.n hR))
    · exact False.elim (hn (congrArg Row.n hB))
  have hb := hP.r35_a_supply_bound hv hh (fun A _ _ _ => hz A) hpartner
  rw [(hp.map _).sum_eq,(hp.map _).sum_eq] at hb
  omega

end Kalai5
