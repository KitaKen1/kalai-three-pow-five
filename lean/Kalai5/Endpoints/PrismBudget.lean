import Kalai5.Endpoints.WeightQThree

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget

def smallFreeRows : List Row :=
  [⟨7,16,16,7,32⟩,⟨7,17,17,7,32⟩,⟨7,17,18,8,35⟩,⟨7,17,18,8,36⟩,
   ⟨7,17,19,9,38⟩,⟨7,18,19,8,35⟩,⟨7,18,20,9,38⟩,⟨7,18,20,9,39⟩]

def rowExcess (R : Row) : ℤ := (R.J : ℤ) + R.n - 3 * R.r - R.e

def prismLower (R : Row) : ℤ :=
  if rowExcess R ≤ 4 then 3 * rowExcess R else 3 + 2 * rowExcess R

/-- A sufficient, decidable condition for a row to have no prism at this slack. -/
def freeAt (slack : ℤ) (R : Row) : Prop :=
  R ∈ smallFreeRows ∨ R = zRow ∨
    (R.n = 8 ∧ (rowExcess R < 3 ∨ (q55QThreeRowWeight R : ℤ) + slack < prismLower R))

instance (slack : ℤ) (R : Row) : Decidable (freeAt slack R) := by
  unfold freeAt
  infer_instance

def yCount (rows : List Row) : ℕ := (rows.map fun R => if R = excRow then 1 else 0).sum

def slack (S : ℤ) (rows : List Row) : ℤ :=
  156 - 6 * S - 2 * (rows.map q55QThreeRowWeight).sum

/-- If every other row is prism-free, the number of Y pairs must be even. -/
def parityOK (S : ℤ) (rows : List Row) : Bool :=
  decide (2 ∣ yCount rows) || !(rows.all fun R => decide (R = excRow ∨ freeAt (slack S rows) R))

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.small_rows_prism_free {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F ∈ PrismBudget.smallFreeRows) : tcnt P F (6,9,5) = 0 := by
  have hn : cnt P F 0 ≤ 7 := by
    have hc : ∀ R ∈ PrismBudget.smallFreeRows, R.n = 7 := by decide +kernel
    have := hc _ hR
    change cnt P F 0 = 7 at this
    omega
  obtain ⟨hm,he⟩ := hP.facet_rowX hF h4 hn
  have hc : ∀ X ∈ smallRowsX, X.1 ∈ PrismBudget.smallFreeRows → X.2.1[3]? = some 0 := by
    decide +kernel
  have hz := hc _ hm (by change rowOf F ∈ _; rw [he]; exact hR)
  have hp := (hP.facet_profile hF h4 hn).2
  have ht := congrArg (fun xs : List ℕ => xs[3]?) hp
  simp only [fv7,List.map_cons,List.map_nil,List.getElem?_cons_succ,List.getElem?_cons_zero] at ht
  rw [hz] at ht
  have hzero := Option.some.inj ht
  rw [hP.tcnt_eq_card]
  exact hzero.symm

/-- A prism supplies three quadrilaterals. In eight vertices it also
excludes b55; at excess at most four this fixes the whole weight. -/
theorem IsCSPolytope5.prism_weight_lower {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (h8 : cnt P F 0 = 8)
    (ht : 1 ≤ tcnt P F (6,9,5)) :
    3 ≤ PrismBudget.rowExcess (faceRow P F) ∧
      PrismBudget.prismLower (faceRow P F) ≤ q55w P F + 2 * exc P F := by
  obtain ⟨T,hT,hTF,hT3,htri⟩ := hP.exists_of_tcnt ht
  have hb := hP.prism_b55_zero_of_eight hF h4 h8.le hT hTF hT3 htri
  have hq := hP.b55_add_three_le_of_prism ht
  have hbound := hP.q4_add_big_le_exc F
  have he : exc P F = PrismBudget.rowExcess (faceRow P F) := hP.exc_eq_faceRow hF h4
  have hw := hP.q55w_eq_b55 F
  refine ⟨by omega,?_⟩
  unfold PrismBudget.prismLower
  split_ifs with hl
  · have hz : big2 P F = 0 := by omega
    have hqe := hP.exc_eq_q4_of_big F hz
    omega
  · omega

/-- The sum of nonnegative deficits bounds the deficit at each facet. -/
theorem IsCSPolytope5.facet_weight_le_of_lower_bound
    (w : Row → ℕ)
    (hw : ∀ F ∈ faces P, dim F = 4 → (w (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F)
    (B : ℤ)
    (hbudget : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ B)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    q55w P F + 2 * exc P F ≤ (w (faceRow P F) : ℤ) +
      (B - ((facetRows P).map w).sum) := by
  have hnonneg : ∀ H ∈ (hP.kfaces_finite 4).toFinset,
      0 ≤ q55w P H + 2 * exc P H - (w (faceRow P H) : ℤ) := by
    intro H hH
    rw [Set.Finite.mem_toFinset] at hH
    exact sub_nonneg.2 (hw H hH.1 hH.2)
  have hm : F ∈ (hP.kfaces_finite 4).toFinset := by
    rw [Set.Finite.mem_toFinset]; exact ⟨hF,h4⟩
  have ht := Finset.single_le_sum hnonneg hm
  rw [Finset.sum_sub_distrib] at ht
  rw [hP.facetRows_sum w,Nat.cast_sum]
  omega

theorem IsCSPolytope5.prism_free_of_budget {F : Set E5} {s : ℤ}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : PrismBudget.freeAt s (faceRow P F))
    (hw : q55w P F + 2 * exc P F ≤ (q55QThreeRowWeight (faceRow P F) : ℤ) + s) :
    tcnt P F (6,9,5) = 0 := by
  rcases hR with hs | hz | ⟨hn,he⟩
  · exact hP.small_rows_prism_free hF h4 hs
  · exact (hP.r19_types hF h4 hz).2.2.2.2.1
  · by_contra hne
    obtain ⟨hmin,hl⟩ := hP.prism_weight_lower hF h4 hn (by omega)
    rcases he with he | he <;> omega

/-- The Boolean parity filter is necessary for every geometric pair profile.
Its single parity bit is justified by the four-divisibility of ridge incidences. -/
theorem IsCSPolytope5.prism_budget_parity {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F)) ≤ 156 - 6 * S) :
    PrismBudget.parityOK S rows = true := by
  by_cases heven : 2 ∣ PrismBudget.yCount rows
  · simp [PrismBudget.parityOK,heven]
  by_cases hall : ∀ R ∈ rows, R = excRow ∨ PrismBudget.freeAt (PrismBudget.slack S rows) R
  · have hcount : ∀ F ∈ (hP.kfaces_finite 4).toFinset,
        tcnt P F (6,9,5) = if faceRow P F = excRow then 1 else 0 := by
      intro F hF
      have hFm := hF
      rw [Set.Finite.mem_toFinset] at hFm
      have hm : faceRow P F ∈ rows := by
        have hf : faceRow P F ∈ facetRows P := by
          rw [hP.facetRows_eq]
          exact List.mem_map.2 ⟨F,Finset.mem_toList.2 hF,rfl⟩
        simpa only [List.mem_append,or_self] using hp.mem_iff.1 hf
      by_cases hY : faceRow P F = excRow
      · simp only [hY,ite_true]
        exact hP.Y_prism_count hFm.1 hFm.2 hY
      · rw [if_neg hY]
        apply hP.prism_free_of_budget hFm.1 hFm.2 ((hall _ hm).resolve_left hY)
        have hu := hP.facet_weight_le_of_lower_bound q55QThreeRowWeight
          (fun _ => hP.q55_qThree_row_weight) (156 - 6 * S) hb hFm.1 hFm.2
        rw [(hp.map q55QThreeRowWeight).sum_eq,List.map_append,List.sum_append,Nat.cast_add] at hu
        unfold PrismBudget.slack
        omega
    have hs : (∑ F ∈ (hP.kfaces_finite 4).toFinset, tcnt P F (6,9,5)) =
        2 * PrismBudget.yCount rows := by
      rw [Finset.sum_congr rfl hcount,← hP.facetRows_sum (fun R => if R = excRow then 1 else 0),(hp.map _).sum_eq,
        List.map_append,List.sum_append]
      unfold PrismBudget.yCount
      omega
    have hd := hP.four_dvd_sum_tcnt (6,9,5)
    rw [hs] at hd
    omega
  · have hf : (rows.all fun R => decide (R = excRow ∨
        PrismBudget.freeAt (PrismBudget.slack S rows) R)) = false := by
      apply Bool.eq_false_iff.2
      intro hh
      apply hall
      intro R hR
      exact of_decide_eq_true ((List.all_eq_true.1 hh) R hR)
    simp only [PrismBudget.parityOK,hf,Bool.not_false,Bool.or_true]

end Kalai5
