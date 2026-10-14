import Kalai5.Cube3.IntervalCoordinates

/-! Two positive-height seeds in different saturated faces of a supported triangle edge. -/
namespace Kalai5.Cube3

structure SupportPairSeeds (r A B p : ℝ) where
  t : ℝ
  positive : 0 < t
  coords : Fin 2 → Fin 4 → ℝ
  sum : ∀ i,∑ j,coords i j=(p-r)*t
  bound : ∀ i j,|coords i j|+(![r,A,B,0] : Fin 4 → ℝ) j*t≤1
  triangle : ∀ i,coords i 0+r*t=1
  upper : ∀ i,coords i 1+A*t=1
  lower_first : coords 0 2-B*t= -1
  lower_second : coords 1 3= -1

theorem support_pair_seeds {r A B p : ℝ} (hr : 0 ≤ r) (hB : 0 ≤ B)
    (hBA : B ≤ A) (hp : 0 < p) : Nonempty (SupportPairSeeds r A B p) := by
  let D := 1+r+A+B+p
  have hA : 0 ≤ A := hB.trans hBA
  have hD : 0 < D := by dsimp [D]; linarith
  let t := 1/D
  have ht : 0 < t := one_div_pos.2 hD
  have htD : t*D=1 := by dsimp [t]; field_simp
  have hrt : 0 ≤ r*t := mul_nonneg hr ht.le
  have hAt : 0 ≤ A*t := mul_nonneg hA ht.le
  have hBt : 0 ≤ B*t := mul_nonneg hB ht.le
  have hpt : 0 < p*t := mul_pos hp ht
  have hsum : t+r*t+A*t+B*t+p*t=1 := by dsimp [D] at htD; nlinarith [htD]
  have hq : 0 < (p+A-B)*t := mul_pos (by linarith) ht
  have hrt1 : r*t<1 := by nlinarith
  have hAt1 : A*t<1 := by nlinarith
  have hBt1 : B*t<1 := by nlinarith
  have hpa : (p+A)*t<1 := by nlinarith
  have hq1 : (p+A-B)*t<1 := by nlinarith
  refine ⟨{
    t := t
    positive := ht
    coords := ![![1-r*t,1-A*t,-1+B*t,-1+(p+A-B)*t],
                 ![1-r*t,1-A*t,-1+(p+A)*t,-1]]
    sum := ?_
    bound := ?_
    triangle := ?_
    upper := ?_
    lower_first := by simp
    lower_second := rfl }⟩
  · intro i; fin_cases i <;> simp [Fin.sum_univ_four] <;> ring
  · intro i j; fin_cases i <;> fin_cases j
    · change |1-r*t|+r*t≤1
      rw [abs_of_nonneg (by linarith)]; linarith
    · change |1-A*t|+A*t≤1
      rw [abs_of_nonneg (by linarith)]; linarith
    · change |-1+B*t|+B*t≤1
      rw [abs_of_nonpos (by linarith)]; linarith
    · change |-1+(p+A-B)*t|+0*t≤1
      rw [abs_of_nonpos (by linarith)]; nlinarith
    · change |1-r*t|+r*t≤1
      rw [abs_of_nonneg (by linarith)]; linarith
    · change |1-A*t|+A*t≤1
      rw [abs_of_nonneg (by linarith)]; linarith
    · change |-1+(p+A)*t|+B*t≤1
      rw [abs_of_nonpos (by linarith)]; nlinarith
    · change |(-1 : ℝ)|+0*t≤1
      norm_num
  · intro i; fin_cases i <;> simp
  · intro i; fin_cases i <;> simp

end Kalai5.Cube3
