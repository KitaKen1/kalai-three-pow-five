import Kalai5.LocalData

/-!
# Rows of 4-polytopes with at most seven vertices

The 24 distinct rows `(n, e, p, r; J)` of the 832 face lattices in the bundle's Gale catalogue
(`research/kalai5_audit_14_26/gale_valid_diagrams.json`; extracted independently from the stored
faces of each record).  All local inequalities used by the fourteen-vertex endpoints are checked
here by `decide`; what remains is the classification statement
`IsRealRow R → R.n ≤ 7 → R ∈ smallRows` (obligation `small_classification`).
-/

namespace Kalai5

/-- Rows of all 4-polytopes with at most seven vertices. -/
def smallRows : List Row :=
  [⟨5, 10, 10, 5, 20⟩, ⟨6, 13, 13, 6, 26⟩, ⟨6, 14, 15, 7, 29⟩, ⟨6, 14, 16, 8, 32⟩,
   ⟨6, 15, 18, 9, 36⟩, ⟨7, 15, 14, 6, 29⟩, ⟨7, 16, 16, 7, 32⟩, ⟨7, 17, 17, 7, 32⟩,
   ⟨7, 17, 18, 8, 35⟩, ⟨7, 17, 18, 8, 36⟩, ⟨7, 17, 19, 9, 38⟩, ⟨7, 18, 19, 8, 35⟩,
   ⟨7, 18, 20, 9, 38⟩, ⟨7, 18, 20, 9, 39⟩, ⟨7, 18, 21, 10, 41⟩, ⟨7, 18, 21, 10, 42⟩,
   ⟨7, 18, 22, 11, 44⟩, ⟨7, 19, 22, 10, 42⟩, ⟨7, 19, 23, 11, 45⟩, ⟨7, 19, 23, 11, 46⟩,
   ⟨7, 19, 24, 12, 48⟩, ⟨7, 20, 25, 12, 49⟩, ⟨7, 20, 26, 13, 52⟩, ⟨7, 21, 28, 14, 56⟩]

lemma smallRows_length : smallRows.length = 24 := rfl

/-- Euler's relation `n - e + p - r = 0` holds on every row (sanity check of the data). -/
lemma smallRows_euler : ∀ R ∈ smallRows, (R.n : ℤ) - R.e + R.p - R.r = 0 := by decide +kernel

lemma smallRows_L1 : ∀ R ∈ smallRows, 0 ≤ R.L1 := by decide +kernel
lemma smallRows_L2 : ∀ R ∈ smallRows, 0 ≤ R.L2 := by decide +kernel
lemma smallRows_L3 : ∀ R ∈ smallRows, 0 ≤ R.L3 := by decide +kernel
lemma smallRows_g : ∀ R ∈ smallRows, 0 ≤ R.g := by decide +kernel

end Kalai5
