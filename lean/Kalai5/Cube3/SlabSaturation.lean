import Kalai5.Cube3.TripleSlabCount

/-! A slab vertex must saturate one of any two prescribed zero-width coordinates. -/
namespace Kalai5.Cube3
open Set

theorem tripleSlab_first_two_saturated {η : ℝ} {z : SlabPoint}
    (hz : z ∈ (tripleSlab η).extremePoints ℝ) :
    ∃ i : Fin 2,z.1 i.castSucc=1 ∨ z.1 i.castSucc= -1 := by
  by_contra hnot
  have hlt (i : Fin 2) : |z.1 i.castSucc|<1 := by
    apply lt_of_le_of_ne (hz.1.1 i.castSucc)
    intro he
    apply hnot
    refine ⟨i,?_⟩
    by_cases hpos : 0 ≤ z.1 i.castSucc
    · exact Or.inl (by rwa [abs_of_nonneg hpos] at he)
    · right; rw [abs_of_neg (lt_of_not_ge hpos)] at he; linarith
  have hlt0 : |z.1 0|<1 := hlt 0
  have hlt1 : |z.1 1|<1 := hlt 1
  let δ := min (1-|z.1 0|) (1-|z.1 1|)/2
  have hδ : 0 < δ := by
    apply div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have hδ0 : δ ≤ 1-|z.1 0| := by
    have h := min_le_left (1-|z.1 0|) (1-|z.1 1|)
    dsimp only [δ]; linarith
  have hδ1 : δ ≤ 1-|z.1 1| := by
    have h := min_le_right (1-|z.1 0|) (1-|z.1 1|)
    dsimp only [δ]; linarith
  let p : SlabPoint := (cycle3 (z.1 0+δ) (z.1 1-δ) (z.1 2) 0,z.2)
  let q : SlabPoint := (cycle3 (z.1 0-δ) (z.1 1+δ) (z.1 2) 0,z.2)
  have hp : p ∈ tripleSlab η := by
    refine ⟨?_,?_⟩
    · intro i; fin_cases i
      · change |z.1 0+δ|≤1
        exact (abs_add_le _ _).trans (by rw [abs_of_pos hδ]; linarith)
      · change |z.1 1-δ|≤1
        exact (abs_sub _ _).trans (by rw [abs_of_pos hδ]; linarith)
      · exact hz.1.1 2
    · change |η*z.2-∑ i,cycle3 (z.1 0+δ) (z.1 1-δ) (z.1 2) 0 i|+|z.2|≤1
      rw [cycle3_sum]
      convert hz.1.2 using 1 <;> simp [Fin.sum_univ_three] <;> ring
  have hq : q ∈ tripleSlab η := by
    refine ⟨?_,?_⟩
    · intro i; fin_cases i
      · change |z.1 0-δ|≤1
        exact (abs_sub _ _).trans (by rw [abs_of_pos hδ]; linarith)
      · change |z.1 1+δ|≤1
        exact (abs_add_le _ _).trans (by rw [abs_of_pos hδ]; linarith)
      · exact hz.1.1 2
    · change |η*z.2-∑ i,cycle3 (z.1 0-δ) (z.1 1+δ) (z.1 2) 0 i|+|z.2|≤1
      rw [cycle3_sum]
      convert hz.1.2 using 1 <;> simp [Fin.sum_univ_three] <;> ring
  have he : (1/2 : ℝ) • p+(1/2 : ℝ) • q=z := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [p,q,cycle3] <;> ring
    · change (1/2 : ℝ)*z.2+(1/2 : ℝ)*z.2=z.2; ring
  have hpz := hz.2 hp hq ⟨(1/2 : ℝ),(1/2 : ℝ),by norm_num,by norm_num,by norm_num,he⟩
  have h := congrArg (fun p : SlabPoint => p.1 0) hpz
  change z.1 0+δ=z.1 0 at h
  linarith

end Kalai5.Cube3
