import Kalai5.Gale.CombX

/-!
# Splitting an extended check prefix by one more code

`checkFromX_of_sub`: all completions of `pre` of length `1 + b` pass the extended check once,
for every one-code extension `q` of `pre`, all completions of `pre ++ q` of length `b` pass.
This keeps the heaviest kernel checks small.
-/

namespace Kalai5.Gale

theorem checkFromX_of_sub (T : Tab) (b last nl : ℕ) (pre : List ℕ)
    (h : ∀ q ∈ gen 1 last nl, checkFromX T b (lastOf last q) (nlOf nl q) (pre ++ q) = true) :
    checkFromX T (1 + b) last nl pre = true := by
  unfold checkFromX
  rw [List.all_eq_true]
  intro cs hcs
  obtain ⟨q, hq, r, hr, rfl⟩ := mem_gen_append 1 b last nl cs hcs
  have := h q hq
  unfold checkFromX at this
  rw [List.all_eq_true] at this
  rw [← List.append_assoc]
  exact this r hr

end Kalai5.Gale
