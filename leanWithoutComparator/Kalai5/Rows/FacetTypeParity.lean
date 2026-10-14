import Kalai5.Rows.SixCount
import Kalai5.Endpoints.Fake8

/-!
# Ridge parity for every three-face type

Every ridge belongs to two facets and every three-face type is invariant under
the fixed-point-free antipodal involution. Hence its total multiplicity in all
facet profiles is divisible by four. This refines parity of the ordinary flags
and the earlier six-vertex ridge count without any eight-vertex catalogue.
-/

namespace Kalai5

open Set

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.tri3_neg (F : Set E5) : tri3 P (-F) = tri3 P F := by
  simp only [tri3, hP.cnt_neg]

/-- Each three-face type contributes a multiple of four across all facets. -/
theorem IsCSPolytope5.four_dvd_sum_tcnt (t : ℕ × ℕ × ℕ) :
    4 ∣ ∑ F ∈ (hP.kfaces_finite 4).toFinset, tcnt P F t := by
  classical
  set T3 := (hP.kfaces_finite 3).toFinset with hT3
  set T4 := (hP.kfaces_finite 4).toFinset with hT4
  have hcnt : ∀ F, tcnt P F t = (T3.filter fun G => G ⊆ F ∧ tri3 P G = t).card := by
    intro F
    unfold tcnt
    rw [← Set.ncard_coe_finset]
    congr 1
    ext G
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, hT3, Set.Finite.mem_toFinset]
    tauto
  have hup : ∀ G ∈ T3, (T4.filter fun F => G ⊆ F).card = 2 := by
    intro G hG
    rw [hT3, Set.Finite.mem_toFinset] at hG
    rw [← hP.ridge_two hG.1 hG.2, ← Set.ncard_coe_finset]
    congr 1
    ext F
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, hT4, Set.Finite.mem_toFinset]
    tauto
  have hsum : ∑ F ∈ T4, tcnt P F t = 2 * (T3.filter fun G => tri3 P G = t).card := by
    simp only [hcnt, Finset.card_filter]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun G hG => ?_
    by_cases hc : tri3 P G = t
    · simp only [hc, and_true, if_true, mul_one]
      rw [← hup G hG, Finset.card_filter]
    · simp [hc]
  have heven : Even (T3.filter fun G => tri3 P G = t).card := by
    refine even_card_of_involution _ (fun G => -G) ?_ (fun G _ => neg_neg G) ?_
    · intro G hG
      rw [Finset.mem_filter, hT3, Set.Finite.mem_toFinset] at hG ⊢
      exact ⟨⟨neg_mem_faces hP.symm hG.1.1, by rw [dim_neg]; exact hG.1.2⟩,
        by rw [hP.tri3_neg]; exact hG.2⟩
    · intro G hG hGG
      rw [Finset.mem_filter, hT3, Set.Finite.mem_toFinset] at hG
      have := hP.eq_of_neg_eq hG.1.1 hGG
      have h5 := hP.dim_self
      rw [← this, hG.1.2] at h5
      omega
  obtain ⟨m, hm⟩ := heven
  rw [hsum, hm]
  exact ⟨m, by ring⟩

end Kalai5
