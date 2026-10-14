import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

/-!
# The integer core of the one-full-pair profile

The nine multiplicities count antipodal pairs of seven-vertex, zero-stress
rows, in catalogue order. The full pair has row (8,k,k,8;38). The hypotheses
are stated explicitly: connecting the profile counts to geometry is separate.

Subtracting seven times the weight bound from five times the total-face bound
leaves coefficients 4,0,15,30,39,54,69,84 on the eight non-Y counts. At k=20
all positive terms vanish; k≥21 is impossible. At k=19 their sum is at most
three, so they again vanish, and the required integer count of J is impossible.
No enumeration of the nine-dimensional box is necessary.
-/

namespace Kalai5

theorem one_pair_profile_arithmetic
    (k y q j a b c d u v e r : ℕ)
    (hklo : 19 ≤ k) (hkhi : k ≤ 22)
    (hcount : y + q + j + a + b + c + d + u + v = 8)
    (hedges : 3 * e + 122 = 2 * k + 30 * y + 32 * q + 34 * j +
      34 * a + 34 * b + 36 * c + 36 * d + 36 * u + 36 * v)
    (hridges : r = 8 + 6 * y + 7 * q + 7 * j + 8 * a + 9 * b +
      8 * c + 9 * d + 10 * u + 11 * v)
    (hfaces : e + r ≤ 118)
    (hweight : 9 * y + 4 * q + (if k = 19 then 3 else 0) + 3 * e ≤ 210) :
    k = 20 ∧ y = 4 ∧ j = 4 ∧ q = 0 ∧ a = 0 ∧ b = 0 ∧ c = 0 ∧
      d = 0 ∧ u = 0 ∧ v = 0 ∧ e = 58 ∧ r = 60 := by
  have hT : 2 * k + 5 * q + 7 * j + 10 * a + 13 * b + 12 * c +
      15 * d + 18 * u + 21 * v ≤ 68 := by
    linarith only [hcount, hedges, hridges, hfaces]
  have hW : 2 * k + (if k = 19 then 3 else 0) ≤
      20 + 3 * q + 5 * j + 5 * a + 5 * b + 3 * c + 3 * d + 3 * u + 3 * v := by
    linarith only [hcount, hedges, hweight]
  have hcut : 24 * k + 7 * (if k = 19 then 3 else 0) + 4 * q +
      15 * a + 30 * b + 39 * c + 54 * d + 69 * u + 84 * v ≤ 480 := by
    linarith only [hT, hW]
  have hzero : q = 0 ∧ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ u = 0 ∧ v = 0 := by
    clear hcount hedges hridges hfaces hweight hT hW
    split_ifs at hcut with hk <;> omega
  rcases hzero with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_cases hk : k = 19
  · simp only [hk, ite_true] at hweight
    omega
  · simp only [hk, ite_false] at hweight
    omega

end Kalai5
