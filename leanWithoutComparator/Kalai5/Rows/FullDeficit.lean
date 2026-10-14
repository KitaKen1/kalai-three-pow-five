import Kalai5.Endpoints.FullRidge

/-!
# Incidence saturation for rows with at most eight vertices

A non-full row has at most seven vertices. Summing its shortfall from seven
turns equality in the incidence bound into a pointwise statement, avoiding
any classification of eight-vertex facets.
-/

namespace Kalai5

def sevenDeficit (R : Row) : ℕ := if R.n = 8 then 0 else 7 - R.n

lemma cnt8_cons (R : Row) (rows : List Row) :
    cnt8 (R :: rows) = cnt8 rows + if R.n = 8 then 1 else 0 := by
  by_cases h : R.n = 8 <;> simp [cnt8, List.filter_cons, h, Nat.add_comm]

lemma sum_n_add_sevenDeficit (rows : List Row) (hn : ∀ R ∈ rows, R.n ≤ 8) :
    (rows.map Row.n).sum + (rows.map sevenDeficit).sum = 7 * rows.length + cnt8 rows := by
  induction rows with
  | nil => simp [cnt8]
  | cons R rows ih =>
    have hnR := hn R (List.mem_cons_self ..)
    have ih := ih (fun S hS => hn S (List.mem_cons_of_mem R hS))
    simp only [List.map_cons, List.sum_cons, List.length_cons, cnt8_cons]
    by_cases h : R.n = 8
    · simp only [sevenDeficit, h, if_true]
      omega
    · simp only [sevenDeficit, h, if_false]
      omega

lemma sum_n_le_seven_length_add_cnt8 (rows : List Row) (hn : ∀ R ∈ rows, R.n ≤ 8) :
    (rows.map Row.n).sum ≤ 7 * rows.length + cnt8 rows := by
  have := sum_n_add_sevenDeficit rows hn
  omega

/-- Equality in the incidence bound forces every non-full row to have seven vertices. -/
theorem seven_le_n_of_incidence_saturated (rows : List Row)
    (hn : ∀ R ∈ rows, R.n ≤ 8)
    (heq : (rows.map Row.n).sum = 7 * rows.length + cnt8 rows) :
    ∀ R ∈ rows, 7 ≤ R.n := by
  have hzero : (rows.map sevenDeficit).sum = 0 := by
    have := sum_n_add_sevenDeficit rows hn
    omega
  have hz : ∀ R ∈ rows, sevenDeficit R = 0 := by
    clear hn heq
    induction rows with
    | nil => simp
    | cons S rows ih =>
      simp only [List.map_cons, List.sum_cons] at hzero
      intro R hR
      rcases List.mem_cons.1 hR with rfl | hR
      · omega
      · exact ih (by omega) R hR
  intro R hR
  have := hz R hR
  unfold sevenDeficit at this
  split_ifs at this <;> omega

/-- A lower bound on each term gives the corresponding bound on the sum. -/
lemma eight_length_le_sum_r (rows : List Row) (h : ∀ R ∈ rows, 8 ≤ R.r) :
    8 * rows.length ≤ (rows.map Row.r).sum := by
  induction rows with
  | nil => simp
  | cons R rows ih =>
    have hR := h R (List.mem_cons_self ..)
    have ht := ih (fun S hS => h S (List.mem_cons_of_mem R hS))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem r_eq_eight_of_sum_le (rows : List Row) (h : ∀ R ∈ rows, 8 ≤ R.r)
    (hs : (rows.map Row.r).sum ≤ 8 * rows.length) : ∀ R ∈ rows, R.r = 8 := by
  induction rows with
  | nil => simp
  | cons S rows ih =>
    have hS := h S (List.mem_cons_self ..)
    have ht : ∀ R ∈ rows, 8 ≤ R.r := fun R hR => h R (List.mem_cons_of_mem S hR)
    have hl := eight_length_le_sum_r rows ht
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hs
    have heq : S.r = 8 := by omega
    intro R hR
    rcases List.mem_cons.1 hR with rfl | hR
    · exact heq
    · exact ih ht (by omega) R hR

end Kalai5
