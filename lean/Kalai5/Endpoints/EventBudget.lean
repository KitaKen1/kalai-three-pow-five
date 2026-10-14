import Kalai5.Endpoints.PrismBudget

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget

def rowEvent (R : Row) : ℕ :=
  if R = excRow ∨ R = r35Row then 1 else if R = r0Row then 2 else 0

def eventKnown (s : ℤ) (R : Row) : Prop :=
  R = excRow ∨ R = r35Row ∨ R = r0Row ∨ R ∈ smallFreeRows ∨ R = zRow ∨
    (R.n = 8 ∧ 8 ≤ R.r ∧ freeAt s R)

instance (s : ℤ) (R : Row) : Decidable (eventKnown s R) := by
  unfold eventKnown
  infer_instance

def eventParityOK (S : ℤ) (rows : List Row) : Bool :=
  decide (2 ∣ (rows.map rowEvent).sum) ||
    !(rows.all fun R => decide (eventKnown (slack S rows) R))

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- An eight-vertex facet with at least eight ridges has no (7,11,6) ridge. -/
theorem IsCSPolytope5.eight_ridges_no_7116 {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hn : cnt P F 0 = 8)
    (hr : 8 ≤ cnt P F 3) : tcnt P F (7,11,6) = 0 := by
  by_contra hz
  obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (7,11,6))
  have hT7 : cnt P T 0 = 7 := congrArg Prod.fst ht
  have hT6 : cnt P T 2 = 6 := congrArg (fun t => t.2.2) ht
  have hb := hP.near_pyramid_ridge_count hF h4 hT hTF hT3 (by omega)
  omega

/-- The sum of the two exceptional ridge counts is one for R35. -/
theorem IsCSPolytope5.r35_event_one {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = r35Row) :
    tcnt P F (6,9,5) + tcnt P F (7,11,6) = 1 := by
  have hR' := hR
  simp only [faceRow,r35Row,Row.mk.injEq] at hR'
  obtain ⟨h0,h1,h2,h3,hJ⟩ := hR'
  obtain ⟨X,hX,hX1,hX2⟩ := hP.facet_types_r7 hF h4 (by omega)
  rw [h0,h1,h2,h3,hJ] at hX1
  rcases smallRowsX_r35dual X hX hX1 with hp | hp | hp <;>
    rw [hp] at hX2 <;>
    simp only [fv7,List.map_cons,List.map_nil,List.cons.injEq] at hX2 <;> omega

theorem IsCSPolytope5.event_count_of_budget {F : Set E5} {s : ℤ}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hknown : PrismBudget.eventKnown s (faceRow P F))
    (hw : q55w P F + 2 * exc P F ≤ (q55QThreeRowWeight (faceRow P F) : ℤ) + s) :
    tcnt P F (6,9,5) + tcnt P F (7,11,6) = PrismBudget.rowEvent (faceRow P F) := by
  rcases hknown with hY | h35 | h0 | hs | hz | ⟨hn,hr,hfree⟩
  · have hp := hP.Y_prism_count hF h4 hY
    have hn : cnt P F 0 = 7 := congrArg Row.n hY
    have ht := hP.small_facet_seven_ridge_zero hF h4 hn.le 11 6
    simp only [PrismBudget.rowEvent,hY,eq_self,true_or,ite_true]
    omega
  · rw [hP.r35_event_one hF h4 h35]
    simp [PrismBudget.rowEvent,h35]
  · obtain ⟨_,_,hp,_,_,ht⟩ := hP.r0_types hF h4 h0
    rw [hp,ht,h0]
    decide +kernel
  · have hn : cnt P F 0 ≤ 7 := by
      have hc : ∀ R ∈ PrismBudget.smallFreeRows, R.n = 7 := by decide +kernel
      have := hc _ hs
      change cnt P F 0 = 7 at this
      omega
    have hp := hP.small_rows_prism_free hF h4 hs
    have ht := hP.small_facet_seven_ridge_zero hF h4 hn 11 6
    have hc : ∀ R ∈ PrismBudget.smallFreeRows, PrismBudget.rowEvent R = 0 := by decide +kernel
    rw [hp,ht,hc _ hs]
  · obtain ⟨_,_,_,_,hp,ht⟩ := hP.r19_types hF h4 hz
    rw [hp,ht,hz]
    decide +kernel
  · have hp := hP.prism_free_of_budget hF h4 hfree hw
    have ht := hP.eight_ridges_no_7116 hF h4 hn hr
    have hneY : faceRow P F ≠ excRow := by
      intro he
      have := congrArg Row.n he
      change (faceRow P F).n = 7 at this
      omega
    have hne35 : faceRow P F ≠ r35Row := by
      intro he
      have := congrArg Row.r he
      change (faceRow P F).r = 7 at this
      omega
    have hne0 : faceRow P F ≠ r0Row := by
      intro he
      have := congrArg Row.r he
      change (faceRow P F).r = 7 at this
      omega
    simp [PrismBudget.rowEvent,hneY,hne35,hne0,hp,ht]

/-- A second parity check adds the (7,11,6) count to the prism count. -/
theorem IsCSPolytope5.event_budget_parity {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F)) ≤ 156 - 6 * S) :
    PrismBudget.eventParityOK S rows = true := by
  by_cases heven : 2 ∣ (rows.map PrismBudget.rowEvent).sum
  · simp [PrismBudget.eventParityOK,heven]
  by_cases hall : ∀ R ∈ rows, PrismBudget.eventKnown (PrismBudget.slack S rows) R
  · have hcount : ∀ F ∈ (hP.kfaces_finite 4).toFinset,
        tcnt P F (6,9,5) + tcnt P F (7,11,6) = PrismBudget.rowEvent (faceRow P F) := by
      intro F hF
      have hFm := hF
      rw [Set.Finite.mem_toFinset] at hFm
      have hm : faceRow P F ∈ rows := by
        have hf : faceRow P F ∈ facetRows P := by
          rw [hP.facetRows_eq]
          exact List.mem_map.2 ⟨F,Finset.mem_toList.2 hF,rfl⟩
        simpa only [List.mem_append,or_self] using hp.mem_iff.1 hf
      apply hP.event_count_of_budget hFm.1 hFm.2 (hall _ hm)
      have hu := hP.facet_weight_le_of_lower_bound q55QThreeRowWeight
        (fun _ => hP.q55_qThree_row_weight) (156 - 6 * S) hb hFm.1 hFm.2
      rw [(hp.map q55QThreeRowWeight).sum_eq,List.map_append,List.sum_append,Nat.cast_add] at hu
      unfold PrismBudget.slack
      omega
    have hs : (∑ F ∈ (hP.kfaces_finite 4).toFinset,
        (tcnt P F (6,9,5) + tcnt P F (7,11,6))) = 2 * (rows.map PrismBudget.rowEvent).sum := by
      rw [Finset.sum_congr rfl hcount,← hP.facetRows_sum PrismBudget.rowEvent,(hp.map _).sum_eq,
        List.map_append,List.sum_append]
      omega
    have hd := dvd_add (hP.four_dvd_sum_tcnt (6,9,5)) (hP.four_dvd_sum_tcnt (7,11,6))
    rw [← Finset.sum_add_distrib,hs] at hd
    omega
  · have hf : (rows.all fun R => decide (PrismBudget.eventKnown (PrismBudget.slack S rows) R)) = false := by
      apply Bool.eq_false_iff.2
      intro hh
      apply hall
      intro R hR
      exact of_decide_eq_true ((List.all_eq_true.1 hh) R hR)
    simp only [PrismBudget.eventParityOK,hf,Bool.not_false,Bool.or_true]

end Kalai5
