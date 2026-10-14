import Kalai5.Endpoints.ContextWeight
import Kalai5.Endpoints.Ridge6106Capacity
import Kalai5.Endpoints.CWeightThree

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget

def sevenFreeAt (s : ℤ) (R : Row) : Prop :=
  R.n ≤ 7 ∨ (R.n = 8 ∧ (q55QFourRowWeight R : ℤ) + s < 2 * rowExcess R)

instance (s : ℤ) (R : Row) : Decidable (sevenFreeAt s R) := by
  unfold sevenFreeAt
  infer_instance

def cSupportFree (S : ℤ) (rows : List Row) : Prop :=
  pairRowCount ⟨8,20,20,8,39⟩ rows = 1 ∧
  contextUpper S rows ⟨8,20,20,8,39⟩ < 9 ∧
  (rows.all fun R => decide (R = ⟨8,20,20,8,39⟩ ∨
    (ridge6106FreeAt (qFourPairSlack S rows) R ∧ sevenFreeAt (qFourPairSlack S rows) R))) = true

instance (S : ℤ) (rows : List Row) : Decidable (cSupportFree S rows) := by
  unfold cSupportFree
  infer_instance

def contextBipyrFree (S : ℤ) (rows : List Row) (R : Row) : Prop :=
  R ∈ bipyrFreeRows ∨
  (R = ⟨8,20,20,8,39⟩ ∧ (contextUpper S rows R ≤ 3 ∨ cSupportFree S rows))

instance (S : ℤ) (rows : List Row) (R : Row) : Decidable (contextBipyrFree S rows R) := by
  unfold contextBipyrFree
  infer_instance

def contextBipyrCapacityOK (S : ℤ) (rows : List Row) : Bool :=
  rows.all fun R => decide (R ≠ jRow ∨
    3 ≤ (rows.filter fun U => decide (¬ contextBipyrFree S rows U)).length)

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.seven_free_at_counts {F : Set E5} {s : ℤ}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : PrismBudget.sevenFreeAt s (faceRow P F))
    (hw : q55w P F + 2 * exc P F ≤ (q55QFourRowWeight (faceRow P F) : ℤ) + s) :
    ∀ e p, tcnt P F (7,e,p) = 0 := by
  rcases hR with hn | ⟨hn,hl⟩
  · exact hP.small_facet_seven_ridge_zero hF h4 hn
  · have he : exc P F = PrismBudget.rowExcess (faceRow P F) := hP.exc_eq_faceRow hF h4
    exact hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn (by omega)

/-- After the possible exceptional ridge types have been removed, a
bipyramid in C would leave exactly one tetrahedron, which is impossible. -/
theorem IsCSPolytope5.c_bipyr_zero_of_restricted {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8,20,20,8,39⟩)
    (hpr : tcnt P F (6,9,5) = 0) (h610 : tcnt P F (6,10,6) = 0)
    (h7 : ∀ e p, tcnt P F (7,e,p) = 0) : tcnt P F (5,9,6) = 0 := by
  have hR' := hR
  simp only [faceRow,Row.mk.injEq] at hR'
  obtain ⟨hn,_,hp,hr,hJ⟩ := hR'
  obtain ⟨c1,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  simp only [hr,hJ,hp] at c1 c2 c3
  have h7a := h7 11 6
  have h7b := h7 12 7
  have h7c := h7 13 8
  have h7d := h7 14 9
  have h7e := h7 15 10
  by_contra hz
  have ht : tcnt P F (4,6,4) = 1 := by omega
  have hb : tcnt P F (5,9,6) = 1 := by omega
  apply hP.not_one_tetrahedron_bipyramid_pyramids hF h4 ht hb
  intro T hT hTF hT3
  have h1 := hP.one_le_tcnt hT hTF hT3
  have hne : T ≠ F := by rintro rfl; omega
  have hlt := hP.cnt_zero_lt hT hF hTF hne
  have hin := hP.tri3_mem_fv8 hT hT3 (by omega)
  simp only [fv8,List.mem_cons,List.not_mem_nil,or_false] at hin
  rcases hin with h | h | h | h | h | h | h | h | h | h | h | h <;>
    rw [h] at h1 ⊢ <;>
    first | (left; rfl) | (right; left; rfl) | (right; right; rfl) | omega

theorem IsCSPolytope5.c_support_bipyr_zero {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 156 - 6 * S)
    (hs : PrismBudget.cSupportFree S rows)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = ⟨8,20,20,8,39⟩) : tcnt P F (5,9,6) = 0 := by
  have hother : ∀ H ∈ faces P, dim H = 4 → faceRow P H ≠ ⟨8,20,20,8,39⟩ →
      tcnt P H (6,10,6) = 0 ∧ ∀ e p, tcnt P H (7,e,p) = 0 := by
    intro H hH hH4 hne
    have hm := hP.faceRow_mem_pair_rows hp hH hH4
    have hk := of_decide_eq_true ((List.all_eq_true.1 hs.2.2) _ hm)
    have hf := hk.resolve_left hne
    have hw := hP.facet_weight_le_of_qFour_pair_slack hp hb hH hH4
    exact ⟨hP.ridge6106_free_at_count hH hH4 hf.1 hw,
      hP.seven_free_at_counts hH hH4 hf.2 hw⟩
  have h610 := hP.tcnt_zero_of_unique_pair_row hp hs.1 (6,10,6)
    (fun H hH hH4 hne => (hother H hH hH4 hne).1) hF h4
  have h7 : ∀ e p, tcnt P F (7,e,p) = 0 := by
    intro e p
    exact hP.tcnt_zero_of_unique_pair_row hp hs.1 (7,e,p)
      (fun H hH hH4 hne => (hother H hH hH4 hne).2 e p) hF h4
  have hpr : tcnt P F (6,9,5) = 0 := by
    by_contra hz
    have hn : cnt P F 0 = 8 := congrArg Row.n hR
    have hl := (hP.prism_weight_lower hF h4 hn (by omega)).2
    have hu := hP.facet_weight_le_context_upper hp hb hF h4
    rw [hR] at hl hu
    norm_num [PrismBudget.prismLower,PrismBudget.rowExcess] at hl
    have hh := hs.2.1
    omega
  exact hP.c_bipyr_zero_of_restricted hF h4 hR hpr h610 h7

theorem IsCSPolytope5.context_bipyr_free_count {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 156 - 6 * S)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hf : PrismBudget.contextBipyrFree S rows (faceRow P F)) : tcnt P F (5,9,6) = 0 := by
  rcases hf with hfree | ⟨hR,hl | hs⟩
  · exact hP.bipyr_free_rows_count_zero hF h4 hfree
  · have hu := hP.facet_weight_le_context_upper hp hb hF h4
    exact (hP.c_weight_three_profile hF h4 hR (by omega)).2.2.2.2.2.1
  · exact hP.c_support_bipyr_zero hp hb hs hF h4 hR

theorem IsCSPolytope5.context_bipyr_capacity_necessary {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 156 - 6 * S) :
    PrismBudget.contextBipyrCapacityOK S rows = true := by
  apply List.all_eq_true.2
  intro R hRm
  apply decide_eq_true
  by_cases hRJ : R = PrismBudget.jRow
  · apply Or.inr
    obtain ⟨F,hF,h4,hR⟩ := hP.mem_facetRows (hp.mem_iff.2 (List.mem_append_left _ hRm))
    have hJ : faceRow P F = PrismBudget.jRow := hR.trans hRJ
    have ht := hP.small_bipyr_marked_count hF h4 (Or.inl hJ)
    rw [if_pos hJ] at ht
    have hn : cnt P F 0 = 7 := congrArg Row.n hJ
    have hnot : ¬ PrismBudget.contextBipyrFree S rows (faceRow P F) := by
      intro hf
      have hz := hP.context_bipyr_free_count hp hb hF h4 hf
      omega
    have hc := hP.ridge_type_pair_capacity
      (fun U => ¬ PrismBudget.contextBipyrFree S rows U)
      [(5,9,6)] (by decide) hp (fun H hH hH4 hfree t ht => ?_)
      hF h4 hnot (by
        intro t ht u hu
        simp only [List.mem_singleton] at ht hu
        subst t
        subst u
        omega)
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at hc
      omega
    · simp only [List.mem_singleton] at ht
      subst t
      exact hP.context_bipyr_free_count hp hb hH hH4 (not_not.1 hfree)
  · exact Or.inl hRJ

end Kalai5
