import Kalai5.Cube3.SlabWidthSaturation

/-! A positive slab vertex either saturates a prescribed zero-width coordinate or lies on the cap. -/
namespace Kalai5.Cube3
open Set

theorem tripleSlab_segment_or_cap {η : ℝ} {z : SlabPoint}
    (hz : z ∈ (tripleSlab η).extremePoints ℝ) (ht : 0 < z.2) :
    (z.1 0=1 ∨ z.1 0= -1) ∨ z.2=1 := by
  by_contra hnot
  have hsat := tripleSlab_positive_width_saturated hz ht.le
  have ht1 : z.2<1 := by
    have hle : z.2≤1 := by linarith [abs_nonneg (η*z.2-∑ i,z.1 i)]
    exact lt_of_le_of_ne hle (fun he => hnot (Or.inr he))
  have hx : |z.1 0|<1 := by
    apply lt_of_le_of_ne (hz.1.1 0)
    intro he
    apply hnot
    left
    by_cases hsign : 0 ≤ z.1 0
    · exact Or.inl (by rwa [abs_of_nonneg hsign] at he)
    · right; rw [abs_of_neg (lt_of_not_ge hsign)] at he; linarith
  obtain ⟨σ,hσ,hl⟩ : ∃ σ : ℝ,(σ=1 ∨ σ= -1) ∧
      η*z.2-∑ i,z.1 i=σ*(1-z.2) := by
    by_cases hsign : 0 ≤ η*z.2-∑ i,z.1 i
    · refine ⟨1,Or.inl rfl,?_⟩
      rw [abs_of_nonneg hsign] at hsat; linarith
    · refine ⟨-1,Or.inr rfl,?_⟩
      rw [abs_of_neg (lt_of_not_ge hsign)] at hsat; linarith
  have hσabs : |σ|=1 := by rcases hσ with rfl | rfl <;> norm_num
  have hden : 0 < |η+σ|+1 := by positivity
  let δ := min z.2 (min (1-z.2) ((1-|z.1 0|)/(|η+σ|+1)))/2
  have hδ : 0 < δ := by
    exact div_pos (lt_min ht (lt_min (by linarith) (div_pos (by linarith) hden))) (by norm_num)
  have hδt : δ ≤ z.2 := by
    have h := min_le_left z.2 (min (1-z.2) ((1-|z.1 0|)/(|η+σ|+1)))
    dsimp only [δ] at *; linarith
  have hδone : δ ≤ 1-z.2 := by
    have h := (min_le_right z.2 (min (1-z.2) ((1-|z.1 0|)/(|η+σ|+1)))).trans
      (min_le_left (1-z.2) ((1-|z.1 0|)/(|η+σ|+1)))
    dsimp only [δ] at *; linarith
  have hδx : δ*(|η+σ|+1) ≤ 1-|z.1 0| := by
    apply (le_div_iff₀ hden).1
    have h := (min_le_right z.2 (min (1-z.2) ((1-|z.1 0|)/(|η+σ|+1)))).trans
      (min_le_right (1-z.2) ((1-|z.1 0|)/(|η+σ|+1)))
    dsimp only [δ] at *; linarith
  let p (ε : ℝ) : SlabPoint :=
    (cycle3 (z.1 0+ε*(η+σ)) (z.1 1) (z.1 2) 0,z.2+ε)
  have hmem (ε : ℝ) (hε : |ε|≤δ) : p ε ∈ tripleSlab η := by
    have hεlo := (abs_le.1 hε).1
    have hεhi := (abs_le.1 hε).2
    have hnew0 : 0 ≤ z.2+ε := by linarith
    have hnew1 : z.2+ε ≤ 1 := by linarith
    refine ⟨?_,?_⟩
    · intro i
      fin_cases i
      · change |z.1 0+ε*(η+σ)|≤1
        apply (abs_add_le _ _).trans
        rw [abs_mul]
        have hm := mul_le_mul_of_nonneg_right hε (abs_nonneg (η+σ))
        nlinarith
      · exact hz.1.1 1
      · exact hz.1.1 2
    · change |η*(z.2+ε)-∑ i,cycle3 (z.1 0+ε*(η+σ)) (z.1 1) (z.1 2) 0 i|+|z.2+ε|≤1
      rw [cycle3_sum]
      have he : η*(z.2+ε)-(z.1 0+ε*(η+σ)+z.1 1+z.1 2)=σ*(1-(z.2+ε)) := by
        rw [Fin.sum_univ_three] at hl
        nlinarith [hl]
      rw [he,abs_mul,hσabs,one_mul,abs_of_nonneg (by linarith),abs_of_nonneg hnew0]
      linarith
  have he : (1/2 : ℝ) • p δ+(1/2 : ℝ) • p (-δ)=z := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [p,cycle3] <;> ring
    · change (1/2 : ℝ)*(z.2+δ)+(1/2 : ℝ)*(z.2+(-δ))=z.2; ring
  have hpz := hz.2 (hmem δ (by rw [abs_of_pos hδ]))
    (hmem (-δ) (by rw [abs_neg,abs_of_pos hδ]))
    ⟨(1/2 : ℝ),(1/2 : ℝ),by norm_num,by norm_num,by norm_num,he⟩
  have hh := congrArg Prod.snd hpz
  change z.2+δ=z.2 at hh
  linarith

end Kalai5.Cube3
