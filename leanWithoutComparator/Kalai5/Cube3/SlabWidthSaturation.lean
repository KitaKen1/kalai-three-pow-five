import Kalai5.Cube3.TripleSlabCount

/-! Every extreme point saturates the unique positive-width constraint. -/
namespace Kalai5.Cube3
open Set

theorem tripleSlab_width_saturated {η : ℝ} {z : SlabPoint}
    (hz : z ∈ (tripleSlab η).extremePoints ℝ) :
    |η*z.2-∑ i,z.1 i|+|z.2|=1 := by
  apply le_antisymm hz.1.2
  by_contra hnot
  have hlt : |η*z.2-∑ i,z.1 i|+|z.2|<1 := lt_of_not_ge hnot
  let u := η*z.2-∑ i,z.1 i
  let δ := (1-(|u|+|z.2|))/(2*(|η|+1))
  have hden : 0 < 2*(|η|+1) := by positivity
  have hδ : 0 < δ := div_pos (by dsimp only [u]; linarith) hden
  have hδeq : (2*(|η|+1))*δ=1-(|u|+|z.2|) := by
    dsimp only [δ]
    exact mul_div_cancel₀ _ hden.ne'
  let p : SlabPoint := (z.1,z.2+δ)
  let q : SlabPoint := (z.1,z.2-δ)
  have hp : p ∈ tripleSlab η := by
    refine ⟨hz.1.1,?_⟩
    change |η*(z.2+δ)-∑ i,z.1 i|+|z.2+δ|≤1
    rw [show η*(z.2+δ)-∑ i,z.1 i=u+η*δ by dsimp only [u]; ring]
    have h1 := abs_add_le u (η*δ)
    have h2 := abs_add_le z.2 δ
    rw [abs_mul,abs_of_pos hδ] at h1
    rw [abs_of_pos hδ] at h2
    nlinarith
  have hq : q ∈ tripleSlab η := by
    refine ⟨hz.1.1,?_⟩
    change |η*(z.2-δ)-∑ i,z.1 i|+|z.2-δ|≤1
    rw [show η*(z.2-δ)-∑ i,z.1 i=u-η*δ by dsimp only [u]; ring]
    have h1 := abs_sub u (η*δ)
    have h2 := abs_sub z.2 δ
    rw [abs_mul,abs_of_pos hδ] at h1
    rw [abs_of_pos hδ] at h2
    nlinarith
  have he : (1/2 : ℝ) • p+(1/2 : ℝ) • q=z := by
    apply Prod.ext
    · change (1/2 : ℝ) • z.1+(1/2 : ℝ) • z.1=z.1
      rw [← add_smul]; norm_num
    · change (1/2 : ℝ)*(z.2+δ)+(1/2 : ℝ)*(z.2-δ)=z.2; ring
  have hpz := hz.2 hp hq ⟨(1/2 : ℝ),(1/2 : ℝ),by norm_num,by norm_num,by norm_num,he⟩
  have hh := congrArg Prod.snd hpz
  change z.2+δ=z.2 at hh
  linarith

lemma tripleSlab_positive_width_saturated {η : ℝ} {z : SlabPoint}
    (hz : z ∈ (tripleSlab η).extremePoints ℝ) (ht : 0 ≤ z.2) :
    |η*z.2-∑ i,z.1 i|+z.2=1 := by
  simpa only [abs_of_nonneg ht] using tripleSlab_width_saturated hz

end Kalai5.Cube3
