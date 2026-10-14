import Kalai5.Endpoints.RidgeExcess

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- A polygon larger than a quadrilateral already costs at least four units. -/
theorem IsCSPolytope5.big2_zero_of_weight_lt_four {F : Set E5}
    (hw : q55w P F + 2 * exc P F < 4) : big2 P F = 0 := by
  have hq := hP.q4_add_big_le_exc F
  have hl := hP.q55w_ge F
  omega

/-- With no large polygons, each quadrilateral of a non-five-vertex ridge
costs three units of facet weight. -/
theorem IsCSPolytope5.three_ridge_exc_le_weight {F T : Set E5}
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3)
    (hn : cnt P T 0 ≠ 5) (hb : big2 P F = 0) :
    3 * exc P T ≤ q55w P F + 2 * exc P F := by
  have hbt : big2 P T = 0 := by
    have hm := hP.big2_mono_of_subset hTF
    omega
  have hFq := hP.exc_eq_q4_of_big F hb
  have hTq := hP.exc_eq_q4_of_big T hbt
  have hreserve := hP.b55_add_q4_le hT hTF hT3 hn
  have hweight := hP.q55w_eq_b55 F
  omega

/-- A low-weight facet cannot contain a non-five-vertex ridge with more
polygon excess than its weight can pay for. -/
theorem IsCSPolytope5.tcnt_zero_of_small_weight {F : Set E5} {t : ℕ × ℕ × ℕ}
    (hn : t.1 ≠ 5) (hw : q55w P F + 2 * exc P F < 4)
    (he : q55w P F + 2 * exc P F < 3 * (2 * (t.2.1 : ℤ) - 3 * t.2.2)) :
    tcnt P F t = 0 := by
  by_contra hz
  obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F t)
  have htn : cnt P T 0 ≠ 5 := by
    have hh := congrArg Prod.fst ht
    exact hh.trans_ne hn
  have hl := hP.three_ridge_exc_le_weight hT hTF hT3 htn
    (hP.big2_zero_of_weight_lt_four hw)
  have heq := hP.exc_threeface hT hT3
  have hte := congrArg (fun u => u.2.1) ht
  have htp := congrArg (fun u => u.2.2) ht
  change cnt P T 1 = t.2.1 at hte
  change cnt P T 2 = t.2.2 at htp
  rw [hte,htp] at heq
  omega

/-- Equality at zero forces all non-five-vertex ridges to have zero excess. -/
theorem IsCSPolytope5.zero_weight_nonfive_exc_zero {F T : Set E5}
    (hw : q55w P F + 2 * exc P F ≤ 0)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3)
    (hn : cnt P T 0 ≠ 5) : exc P T = 0 := by
  have hl := hP.three_ridge_exc_le_weight hT hTF hT3 hn
    (hP.big2_zero_of_weight_lt_four (by omega : q55w P F + 2 * exc P F < 4))
  have hnonneg := hP.q4_add_big_le_exc T
  omega

end Kalai5
