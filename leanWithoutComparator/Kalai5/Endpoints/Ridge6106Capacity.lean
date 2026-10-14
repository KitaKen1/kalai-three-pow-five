import Kalai5.Endpoints.NegativeGapCapacity
import Kalai5.Endpoints.LowWeightRidgeExcess
import Kalai5.Endpoints.BSupportBudget

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget

def ridge6106FreeAt (s : ℤ) (R : Row) : Prop :=
  bSpecialFree R ∨ (q55QFourRowWeight R : ℤ) + s < 4

instance (s : ℤ) (R : Row) : Decidable (ridge6106FreeAt s R) := by
  unfold ridge6106FreeAt
  infer_instance

def ridge6106Need (R : Row) : ℕ :=
  if R = zRow then 2 else if R = ⟨7,16,16,7,32⟩ then 1 else 0

def ridge6106CapacityOK (S : ℤ) (rows : List Row) : Bool :=
  rows.all fun R => decide (ridge6106Need R = 0 ∨ ridge6106Need R + 1 ≤
    (rows.filter fun U => decide (¬ ridge6106FreeAt (qFourPairSlack S rows) U)).length)

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.ridge6106_free_at_count {F : Set E5} {s : ℤ}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : PrismBudget.ridge6106FreeAt s (faceRow P F))
    (hw : q55w P F + 2 * exc P F ≤ (q55QFourRowWeight (faceRow P F) : ℤ) + s) :
    tcnt P F (6,10,6) = 0 := by
  rcases hR with hb | hl
  · exact (hP.b_special_free_counts hF h4 hb).1
  · exact hP.tcnt_zero_of_small_weight (by decide) (by omega) (by norm_num; omega)

theorem IsCSPolytope5.ridge6106_row_need {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) :
    PrismBudget.ridge6106Need (faceRow P F) ≤ tcnt P F (6,10,6) := by
  unfold PrismBudget.ridge6106Need
  split_ifs with hZ hA
  · exact (hP.r19_types hF h4 hZ).2.2.2.1.ge
  · have hn : cnt P F 0 = 7 := congrArg Row.n hA
    obtain ⟨hm,he⟩ := hP.facet_rowX hF h4 hn.le
    have hcheck : ∀ X ∈ smallRowsX, X.1 = ⟨7,16,16,7,32⟩ →
        1 ≤ X.2.1[4]?.getD 0 := by decide +kernel
    have hz := hcheck _ hm (by change rowOf F = _; rw [he]; exact hA)
    rw [(hP.facet_profile hF h4 hn.le).2] at hz
    simp only [fv7,List.map_cons,List.map_nil,List.getElem?_cons_succ,List.getElem?_cons_zero,
      Option.getD_some] at hz
    rw [hP.tcnt_eq_card]
    exact hz
  · omega

theorem IsCSPolytope5.ridge6106_capacity_necessary {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F)) ≤ 156 - 6 * S) :
    PrismBudget.ridge6106CapacityOK S rows = true := by
  apply List.all_eq_true.2
  intro R hRm
  apply decide_eq_true
  by_cases hz : PrismBudget.ridge6106Need R = 0
  · exact Or.inl hz
  · apply Or.inr
    obtain ⟨F,hF,h4,hR⟩ := hP.mem_facetRows (hp.mem_iff.2 (List.mem_append_left _ hRm))
    have hFR : faceRow P F = zRow ∨ faceRow P F = ⟨7,16,16,7,32⟩ := by
      rw [hR]
      by_contra hh
      push Not at hh
      simp [PrismBudget.ridge6106Need,hh.1,hh.2] at hz
    have ht := hP.ridge6106_row_need hF h4
    rw [hR] at ht
    have hn : cnt P F 0 ≤ 8 := by
      rcases hFR with hz | ha
      · have hh := congrArg Row.n hz; change cnt P F 0 = 8 at hh; omega
      · have hh := congrArg Row.n ha; change cnt P F 0 = 7 at hh; omega
    have hnot : ¬ PrismBudget.ridge6106FreeAt (PrismBudget.qFourPairSlack S rows) (faceRow P F) := by
      intro hf
      have hz' := hP.ridge6106_free_at_count hF h4 hf (hP.facet_weight_le_of_qFour_pair_slack hp hb hF h4)
      omega
    have hc := hP.ridge_type_pair_capacity
      (fun U => ¬ PrismBudget.ridge6106FreeAt (PrismBudget.qFourPairSlack S rows) U)
      [(6,10,6)] (by decide) hp (fun H hH hH4 hfree t ht => ?_)
      hF h4 hnot (by
        intro t ht u hu
        simp only [List.mem_singleton] at ht hu
        subst t
        subst u
        exact hn.trans_lt (by decide : 8 < 12))
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at hc
      omega
    · simp only [List.mem_singleton] at ht
      subst t
      exact hP.ridge6106_free_at_count hH hH4 (not_not.1 hfree)
        (hP.facet_weight_le_of_qFour_pair_slack hp hb hH hH4)

end Kalai5
