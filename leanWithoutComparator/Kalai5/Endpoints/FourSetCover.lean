import Mathlib.Tactic

/-! A four-set incidence bound: equality forces coverage by the two double intersections. -/
namespace Kalai5
open scoped BigOperators

theorem four_set_double_cover {α : Type*} [DecidableEq α]
    (s a b c d : Finset α)
    (ha : a ⊆ s) (hb : b ⊆ s) (hc : c ⊆ s) (hd : d ⊆ s)
    (hs : s.card=8) (hca : a.card=5) (hcb : b.card=5)
    (hcc : c.card=6) (hcd : d.card=6)
    (hac : (a ∩ c).card ≤ 3) (had : (a ∩ d).card ≤ 3)
    (hbc : (b ∩ c).card ≤ 3) (hbd : (b ∩ d).card ≤ 3) :
    (a ∩ b) ∪ (c ∩ d)=s ∧
      (a ∩ c).card=3 ∧ (a ∩ d).card=3 ∧ (b ∩ c).card=3 ∧ (b ∩ d).card=3 := by
  let f : α → ℕ := fun v =>
    ((if v ∈ a then 0 else 1)+(if v ∈ b then 0 else 1)) *
    ((if v ∈ c then 0 else 1)+(if v ∈ d then 0 else 1))
  have point (v : α) :
      f v+2*(if v ∈ a then 1 else 0)+2*(if v ∈ b then 1 else 0)+
        2*(if v ∈ c then 1 else 0)+2*(if v ∈ d then 1 else 0)=
      4+(if v ∈ a ∩ c then 1 else 0)+(if v ∈ a ∩ d then 1 else 0)+
        (if v ∈ b ∩ c then 1 else 0)+(if v ∈ b ∩ d then 1 else 0) := by
    by_cases h1 : v ∈ a <;> by_cases h2 : v ∈ b <;>
      by_cases h3 : v ∈ c <;> by_cases h4 : v ∈ d <;> simp [f,h1,h2,h3,h4]
  have sum_card (t : Finset α) (ht : t ⊆ s) :
      (∑ v ∈ s,if v ∈ t then (1 : ℕ) else 0)=t.card := by
    rw [← Finset.card_filter]
    congr 1
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨ht h,h⟩⟩
  have heq := Finset.sum_congr rfl (fun v (_ : v ∈ s) => point v)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    smul_eq_mul,sum_card a ha,sum_card b hb,sum_card c hc,sum_card d hd,
    sum_card (a ∩ c) (Finset.inter_subset_left.trans ha),
    sum_card (a ∩ d) (Finset.inter_subset_left.trans ha),
    sum_card (b ∩ c) (Finset.inter_subset_left.trans hb),
    sum_card (b ∩ d) (Finset.inter_subset_left.trans hb),hs,hca,hcb,hcc,hcd] at heq
  have hz : ∑ v ∈ s,f v=0 := by omega
  refine ⟨Finset.Subset.antisymm ?_ ?_,by omega,by omega,by omega,by omega⟩
  · exact Finset.union_subset (Finset.inter_subset_left.trans ha) (Finset.inter_subset_left.trans hc)
  · intro v hv
    have hf : f v=0 := Finset.sum_eq_zero_iff.mp hz v hv
    by_cases h1 : v ∈ a <;> by_cases h2 : v ∈ b <;>
      by_cases h3 : v ∈ c <;> by_cases h4 : v ∈ d <;> simp_all [f]

end Kalai5

