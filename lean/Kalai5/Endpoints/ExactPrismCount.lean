import Kalai5.Endpoints.AntipodalWeightBudget
import Kalai5.Endpoints.WeightForcedPrism

namespace Kalai5
open scoped Classical

namespace PrismBudget

def exactPrismRows : List Row :=
  [⟨8,19,19,8,39⟩,⟨8,19,20,9,41⟩,⟨8,20,22,10,45⟩]

def exactPrismValue (R : Row) : ℕ :=
  if R ∈ exactPrismRows ∨ R = excRow then 1 else 0

def exactPrismKnown (s : ℤ) (R : Row) : Prop :=
  R ∈ exactPrismRows ∨ R = excRow ∨ freeAt s R

def exactRowEvent (R : Row) : ℕ :=
  if R ∈ exactPrismRows then 1 else rowEvent R

def exactEventKnown (s : ℤ) (R : Row) : Prop :=
  R ∈ exactPrismRows ∨ eventKnown s R

instance (s : ℤ) (R : Row) : Decidable (exactPrismKnown s R) := by
  unfold exactPrismKnown
  infer_instance

instance (s : ℤ) (R : Row) : Decidable (exactEventKnown s R) := by
  unfold exactEventKnown
  infer_instance

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Two distinct prisms need at least five quadrilaterals. -/
theorem IsCSPolytope5.prism_count_le_one_of_exc_le_four {F : Set E5}
    (he : exc P F ≤ 4) : tcnt P F (6,9,5) ≤ 1 := by
  by_contra hn
  have hq := hP.b55_add_five_le_of_two_prisms (by omega : 2 ≤ tcnt P F (6,9,5))
  have hb := hP.q4_add_big_le_exc F
  omega

theorem IsCSPolytope5.v_prism_count_one {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8,19,19,8,39⟩) :
    tcnt P F (6,9,5) = 1 := by
  have hp := hP.v_prism_positive hF h4 hR
  have he := hP.exc_eq_faceRow hF h4
  rw [hR] at he
  norm_num at he
  have hu := hP.prism_count_le_one_of_exc_le_four (by omega : exc P F ≤ 4)
  omega

theorem IsCSPolytope5.forced_prism_count_one {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = ⟨8,19,20,9,41⟩ ∨ faceRow P F = ⟨8,20,22,10,45⟩) :
    tcnt P F (6,9,5) = 1 := by
  rcases hR with hR | hR
  all_goals
    have hn : cnt P F 0 = 8 := congrArg Row.n hR
    have hr := congrArg Row.r hR
    have hp := congrArg Row.p hR
    have hj := congrArg Row.J hR
    simp only [faceRow] at hr hp hj
    have hl := hP.prism_positive_of_flag_gap hF h4 hn (by omega) (by omega)
    have he := hP.exc_eq_faceRow hF h4
    rw [hR] at he
    norm_num at he
    have hu := hP.prism_count_le_one_of_exc_le_four (by omega : exc P F ≤ 4)
    omega

theorem IsCSPolytope5.exact_prism_row_count {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F ∈ PrismBudget.exactPrismRows) :
    tcnt P F (6,9,5) = 1 := by
  simp only [PrismBudget.exactPrismRows,List.mem_cons,List.not_mem_nil,or_false] at hR
  rcases hR with hV | hother
  · exact hP.v_prism_count_one hF h4 hV
  · exact hP.forced_prism_count_one hF h4 hother

theorem IsCSPolytope5.exact_prism_event_count {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F ∈ PrismBudget.exactPrismRows) :
    tcnt P F (6,9,5) + tcnt P F (7,11,6) = 1 := by
  have hc : ∀ R ∈ PrismBudget.exactPrismRows, R.n = 8 ∧ 8 ≤ R.r := by decide +kernel
  obtain ⟨hn,hr⟩ := hc _ hR
  have hz := hP.eight_ridges_no_7116 hF h4 hn hr
  rw [hP.exact_prism_row_count hF h4 hR,hz]

theorem IsCSPolytope5.exact_prism_count_of_budget {F : Set E5} {s : ℤ}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hknown : PrismBudget.exactPrismKnown s (faceRow P F))
    (hw : q55w P F + 2 * exc P F ≤ (q55QThreeRowWeight (faceRow P F) : ℤ) + s) :
    tcnt P F (6,9,5) = PrismBudget.exactPrismValue (faceRow P F) := by
  by_cases he : faceRow P F ∈ PrismBudget.exactPrismRows
  · rw [hP.exact_prism_row_count hF h4 he]
    simp [PrismBudget.exactPrismValue,he]
  by_cases hy : faceRow P F = excRow
  · rw [hP.Y_prism_count hF h4 hy]
    simp [PrismBudget.exactPrismValue,hy]
  · have hf : PrismBudget.freeAt s (faceRow P F) := (hknown.resolve_left he).resolve_left hy
    rw [hP.prism_free_of_budget hF h4 hf hw]
    simp [PrismBudget.exactPrismValue,he,hy]

theorem IsCSPolytope5.exact_event_count_of_budget {F : Set E5} {s : ℤ}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hknown : PrismBudget.exactEventKnown s (faceRow P F))
    (hw : q55w P F + 2 * exc P F ≤ (q55QThreeRowWeight (faceRow P F) : ℤ) + s) :
    tcnt P F (6,9,5) + tcnt P F (7,11,6) = PrismBudget.exactRowEvent (faceRow P F) := by
  by_cases he : faceRow P F ∈ PrismBudget.exactPrismRows
  · rw [hP.exact_prism_event_count hF h4 he]
    simp [PrismBudget.exactRowEvent,he]
  · rw [hP.event_count_of_budget hF h4 (hknown.resolve_left he) hw]
    simp [PrismBudget.exactRowEvent,he]

end Kalai5
