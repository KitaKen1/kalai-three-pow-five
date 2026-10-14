import Kalai5.Rigidity.LocalG

/-!
# Braced frameworks in an affine 3-space carry no stress

`stressSpace_eq_bot_of_braces3`: a bar framework that braces a point set spanning an affine
3-space and has at most `3 |X| - 6` bars (a triangulated 2-sphere has exactly that many) carries
no stress: by `finrank_stress_add_le_of_braces` (three rotations and three translations),
`dim stress + 3 |X| ≤ |B| + 6`.
-/

namespace Kalai5

/-- **A braced framework in an affine 3-space with at most `3 |X| - 6` bars carries no stress.** -/
theorem stressSpace_eq_bot_of_braces3 {XF : Finset E5} {BF : Finset (Sym2 E5)}
    {L : Submodule ℝ E5} (hL : Module.finrank ℝ L = 3) {p0 : E5} (hp0 : p0 ∈ XF)
    (hdiff : ∀ p ∈ XF, p - p0 ∈ L)
    (hspan : L ≤ Submodule.span ℝ ((fun p => p - p0) '' (XF : Set E5)))
    (hbr : Braces (BF : Set (Sym2 E5)) (XF : Set E5))
    (hcard : BF.card + 6 ≤ 3 * XF.card) :
    stressSpace BF = ⊥ := by
  have h := finrank_stress_add_le_of_braces (c := 3) (by decide) hL hp0 hdiff hspan hbr
  have h0 : Module.finrank ℝ (stressSpace BF) = 0 := by omega
  exact Submodule.finrank_eq_zero.1 h0

end Kalai5
