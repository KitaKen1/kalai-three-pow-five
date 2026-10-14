import Kalai5.Endpoints.TwoPairPositiveSearch

namespace Kalai5.TwoPairPositiveProfile


/-- If every remaining nonfull row costs at least one ridge unit,
the nonfull slots cannot outnumber the remaining ridge budget. -/
theorem searchRows_nil_of_nonfull_budget (rows : List Row) (n f b : ℕ)
    (hcost : ∀ R ∈ rows, 1 ≤ fullIndicator R + ridgeExcess R)
    (hbad : f + b < n) : searchRows rows n f b = [] := by
  induction rows generalizing n f b with
  | nil =>
    simp [searchRows,show ¬ (n = 0 ∧ f = 0) by omega]
  | cons R rs ih =>
    have hn : n ≠ 0 := by omega
    rw [show searchRows (R :: rs) = searchStep R (searchRows rs) by
      unfold searchRows; rfl]
    simp only [searchStep,if_neg hn]
    apply List.flatMap_eq_nil_iff.2
    intro k hk
    have hkn : k ≤ n := by have := List.mem_range.1 hk; omega
    split_ifs with hc
    · have hkcost : k ≤ k * fullIndicator R + k * ridgeExcess R := by
        have h := Nat.mul_le_mul_left k (hcost R (List.mem_cons_self ..))
        simpa only [Nat.mul_one,Nat.mul_add] using h
      rw [ih (n-k) (f-k*fullIndicator R) (b-k*ridgeExcess R)
        (fun S hS => hcost S (List.mem_cons_of_mem R hS)) (by omega)]
      rfl
    · rfl

/-- The same enumeration with a necessary lower-bound check on each suffix.
An explicit list recursor prevents course-of-values tables during reduction. -/
def guardedRows (rows : List Row) : ℕ → ℕ → ℕ → List (List Row) :=
  List.rec (fun n f _ => if n = 0 ∧ f = 0 then [[]] else [])
    (fun R rs next n f b =>
      if (R :: rs).all (fun S => decide (1 ≤ fullIndicator S + ridgeExcess S)) = true ∧
          f + b < n then [] else searchStep R next n f b) rows

theorem guardedRows_eq_searchRows (rows : List Row) :
    guardedRows rows = searchRows rows := by
  induction rows with
  | nil => unfold guardedRows searchRows; rfl
  | cons R rs ih =>
    funext n f b
    change (if (R :: rs).all (fun S => decide (1 ≤ fullIndicator S + ridgeExcess S)) = true ∧
        f + b < n then [] else searchStep R (guardedRows rs) n f b) =
      searchRows (R :: rs) n f b
    rw [ih]
    split_ifs with hc
    · symm
      apply searchRows_nil_of_nonfull_budget _ _ _ _ _ hc.2
      intro S hS
      exact of_decide_eq_true (List.all_eq_true.1 hc.1 S hS)
    · unfold searchRows; rfl

theorem profiles_guarded (G S : ℤ) : profiles G S =
    (guardedRows catalogue 9 2 4).filter (fun rows => decide (admissible G S rows)) := by
  rw [profiles,guardedRows_eq_searchRows]

end Kalai5.TwoPairPositiveProfile
