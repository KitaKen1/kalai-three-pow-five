import Kalai5.Endpoints.ExactPrismBudget
import Kalai5.Endpoints.CWeightThree

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget

def smallNo6117Rows : List Row :=
  [excRow,⟨7,16,16,7,32⟩,⟨7,17,17,7,32⟩,⟨7,17,18,8,36⟩,
   ⟨7,17,19,9,38⟩,⟨7,18,19,8,35⟩,⟨7,18,20,9,38⟩,⟨7,18,20,9,39⟩]

def no6117Rows : List Row := smallNo6117Rows ++ [r35Row,r0Row,zRow] ++ exactPrismRows

def ridge6117Value (R : Row) : ℕ := if R = ⟨8,20,20,8,39⟩ then 1 else 0

def ridge6117Known (s : ℤ) (R : Row) : Prop :=
  R ∈ no6117Rows ∨ (R = ⟨8,20,20,8,39⟩ ∧ (q55QThreeRowWeight R : ℤ) + s ≤ 3)

instance (s : ℤ) (R : Row) : Decidable (ridge6117Known s R) := by
  unfold ridge6117Known
  infer_instance

def ridge6117ParityOK (S : ℤ) (rows : List Row) : Bool :=
  rowParityOK ridge6117Value (fun R => decide (ridge6117Known (pairSlack S rows) R)) rows

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.small_rows_6117_zero {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F ∈ PrismBudget.smallNo6117Rows) : tcnt P F (6,11,7) = 0 := by
  have hc : ∀ R ∈ PrismBudget.smallNo6117Rows, R.n = 7 := by decide +kernel
  have hn : cnt P F 0 = 7 := hc _ hR
  obtain ⟨hm,he⟩ := hP.facet_rowX hF h4 hn.le
  have hcheck : ∀ X ∈ smallRowsX, X.1 ∈ PrismBudget.smallNo6117Rows →
      X.2.1[5]? = some 0 := by decide +kernel
  have hz := hcheck _ hm (by change rowOf F ∈ _; rw [he]; exact hR)
  have hp := congrArg (fun xs : List ℕ => xs[5]?) (hP.facet_profile hF h4 hn.le).2
  simp only [fv7,List.map_cons,List.map_nil,List.getElem?_cons_succ,List.getElem?_cons_zero] at hp
  rw [hz] at hp
  rw [hP.tcnt_eq_card]
  exact (Option.some.inj hp).symm

theorem IsCSPolytope5.exact_prism_rows_6117_zero {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F ∈ PrismBudget.exactPrismRows) : tcnt P F (6,11,7) = 0 := by
  have hc : ∀ R ∈ PrismBudget.exactPrismRows, R.n = 8 ∧ R.J = 2 * R.p + 1 := by decide +kernel
  obtain ⟨hn,hgap⟩ := hc _ hR
  obtain ⟨_,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  have he := hP.exact_prism_event_count hF h4 hR
  change incid P F 0 3 = 2 * cnt P F 2 + 1 at hgap
  omega

set_option maxHeartbeats 2000000 in
theorem IsCSPolytope5.r7_named_rows_6117_zero {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = r35Row ∨ faceRow P F = r0Row ∨ faceRow P F = zRow) :
    tcnt P F (6,11,7) = 0 := by
  have hn : cnt P F 0 = 8 := hR.elim (congrArg Row.n)
    (fun h => h.elim (congrArg Row.n) (congrArg Row.n))
  have hr : cnt P F 3 = 7 := hR.elim (congrArg Row.r)
    (fun h => h.elim (congrArg Row.r) (congrArg Row.r))
  obtain ⟨c1,_,_,_⟩ := hP.facet8_arith hF h4 hn
  rcases hR with h35 | h0 | hz
  · have hR' := h35
    simp only [faceRow,r35Row,Row.mk.injEq] at hR'
    obtain ⟨h0,h1,h2,h3,hJ⟩ := hR'
    obtain ⟨X,hX,hX1,hX2⟩ := hP.facet_types_r7 hF h4 hr.le
    rw [h0,h1,h2,h3,hJ] at hX1
    rcases smallRowsX_r35dual X hX hX1 with hp | hp | hp <;>
      rw [hp] at hX2 <;>
      simp only [fv7,List.map_cons,List.map_nil,List.cons.injEq] at hX2 <;> omega
  · obtain ⟨a,b,c,d,e,f⟩ := hP.r0_types hF h4 h0
    omega
  · obtain ⟨a,b,c,d,e,f⟩ := hP.r19_types hF h4 hz
    omega

theorem IsCSPolytope5.no6117_rows_count_zero {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F ∈ PrismBudget.no6117Rows) : tcnt P F (6,11,7) = 0 := by
  simp only [PrismBudget.no6117Rows,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hR
  rcases hR with (hs | hr) | he
  · exact hP.small_rows_6117_zero hF h4 hs
  · exact hP.r7_named_rows_6117_zero hF h4 hr
  · exact hP.exact_prism_rows_6117_zero hF h4 he

theorem IsCSPolytope5.ridge6117_count_of_budget {F : Set E5} {s : ℤ}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hknown : PrismBudget.ridge6117Known s (faceRow P F))
    (hw : q55w P F + 2 * exc P F ≤ (q55QThreeRowWeight (faceRow P F) : ℤ) + s) :
    tcnt P F (6,11,7) = PrismBudget.ridge6117Value (faceRow P F) := by
  rcases hknown with hz | ⟨hC,hle⟩
  · have hc : ∀ R ∈ PrismBudget.no6117Rows, R ≠ ⟨8,20,20,8,39⟩ := by decide +kernel
    rw [hP.no6117_rows_count_zero hF h4 hz]
    simp [PrismBudget.ridge6117Value,hc _ hz]
  · obtain ⟨_,_,_,_,_,_,_,_,hc,_,_⟩ := hP.c_weight_three_profile hF h4 hC (hw.trans hle)
    rw [hc]
    simp [PrismBudget.ridge6117Value,hC]

theorem IsCSPolytope5.ridge6117_pair_budget_parity {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F)) ≤ 156 - 6 * S) :
    PrismBudget.ridge6117ParityOK S rows = true := by
  apply hP.facet_count_pair_row_parity (fun F => tcnt P F (6,11,7))
    PrismBudget.ridge6117Value _ hp
  · intro F hF h4 hk
    exact hP.ridge6117_count_of_budget hF h4 (of_decide_eq_true hk)
      (hP.facet_weight_le_of_pair_slack hp hb hF h4)
  · exact hP.four_dvd_sum_tcnt (6,11,7)

end Kalai5
