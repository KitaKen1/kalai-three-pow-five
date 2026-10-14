import Kalai5.Cube3.DistinctSegments

/-! Centered coordinates put every segment constraint in diamond form.
The original balanced relation becomes one sum constraint. -/

namespace Kalai5.Cube3

open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y

noncomputable def balanceSign (j : Fin 4) : ℝ := ![1,-1,-1,1] j

lemma balanceSign_abs (j : Fin 4) : |balanceSign j| = 1 := by
  fin_cases j <;> norm_num [balanceSign]

lemma balanceSign_sq (j : Fin 4) : balanceSign j * balanceSign j = 1 := by
  fin_cases j <;> norm_num [balanceSign]

lemma balanced_iff_signed_sum (a : Fin 4 → ℝ) :
    Balanced a ↔ ∑ j, balanceSign j * a j = 0 := by
  simp [Balanced,balanceSign,Fin.sum_univ_four]
  constructor <;> intro h <;> linarith

lemma abs_pair_iff (a b : ℝ) : (|a-b| ≤ 1 ∧ |a+b| ≤ 1) ↔ |a|+|b| ≤ 1 := by
  constructor
  · rintro ⟨hm,hp⟩
    rcases abs_le.1 hm with ⟨hm0,hm1⟩
    rcases abs_le.1 hp with ⟨hp0,hp1⟩
    rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
    · rw [abs_of_nonneg ha,abs_of_nonneg hb]; linarith
    · rw [abs_of_nonneg ha,abs_of_nonpos hb]; linarith
    · rw [abs_of_nonpos ha,abs_of_nonneg hb]; linarith
    · rw [abs_of_nonpos ha,abs_of_nonpos hb]; linarith
  · intro h
    constructor
    · rw [sub_eq_add_neg]
      exact (abs_add_le a (-b)).trans (by simpa using h)
    · exact (abs_add_le a b).trans h

variable {x : Fin 8 → E5} {C : Config x} (S : SegmentData C)

namespace SegmentData

noncomputable def center (j : Fin 4) : E 2 := (1/2 : ℝ) • (C.k (S.lo j) + C.k (S.hi j))

noncomputable def axis (j : Fin 4) : E 2 := (balanceSign j / 2) • S.direction j

lemma axis_ne_zero (j : Fin 4) : S.axis j ≠ 0 := by
  apply smul_ne_zero _ (S.direction_ne_zero j)
  have h := balanceSign_sq j
  intro he
  have : balanceSign j = 0 := (div_eq_zero_iff).1 he |>.resolve_right (by norm_num)
  rw [this] at h
  norm_num at h

noncomputable def centerEval : E5 →ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearMap.pi fun j => (balanceSign j / 2) •
    (((LinearMap.proj (S.lo j)).comp C.evaluation) + ((LinearMap.proj (S.hi j)).comp C.evaluation))

lemma centerEval_apply (p : E5) (j : Fin 4) :
    S.centerEval p j = (balanceSign j / 2) * (C.value p (S.lo j) + C.value p (S.hi j)) := rfl

lemma centerEval_eq (p : E5) (j : Fin 4) :
    S.centerEval p j = balanceSign j * (offsets p j + ⟪planar p,S.center j⟫) := by
  rw [centerEval_apply]
  simp only [Config.value,S.clo,S.chi,center,inner_smul_right,inner_add_right]
  ring

lemma signed_value_lo (p : E5) (j : Fin 4) :
    balanceSign j * C.value p (S.lo j) = S.centerEval p j - ⟪planar p,S.axis j⟫ := by
  rw [centerEval_apply]
  simp only [Config.value,S.clo,S.chi,axis,direction,inner_smul_right,inner_sub_right]
  ring

lemma signed_value_hi (p : E5) (j : Fin 4) :
    balanceSign j * C.value p (S.hi j) = S.centerEval p j + ⟪planar p,S.axis j⟫ := by
  rw [centerEval_apply]
  simp only [Config.value,S.clo,S.chi,axis,direction,inner_smul_right,inner_sub_right]
  ring

lemma mem_polar_centered (p : E5) : p ∈ C.polarModel ↔
    ∀ j, |S.centerEval p j| + |⟪planar p,S.axis j⟫| ≤ 1 := by
  have hpair : ∀ j, (|C.value p (S.lo j)| ≤ 1 ∧ |C.value p (S.hi j)| ≤ 1) ↔
      |S.centerEval p j| + |⟪planar p,S.axis j⟫| ≤ 1 := by
    intro j
    rw [← abs_pair_iff, ← S.signed_value_lo, ← S.signed_value_hi]
    simp [abs_mul,balanceSign_abs]
  constructor
  · intro hp j
    exact (hpair j).1 ⟨hp _,hp _⟩
  · intro hp v
    have h := (hpair (C.c v)).2 (hp (C.c v))
    rcases S.cover v with hv | hv
    · simpa only [← hv] using h.1
    · simpa only [← hv] using h.2

noncomputable def drift : E 2 →ₗ[ℝ] ℝ where
  toFun b := ∑ j, balanceSign j * ⟪b,S.center j⟫
  map_add' := by intro a b; simp [inner_add_left,mul_add,Finset.sum_add_distrib]
  map_smul' := by
    intro t b
    simp only [real_inner_smul_left,RingHom.id_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _; ring

lemma centerEval_sum (p : E5) : ∑ j, S.centerEval p j = S.drift (planar p) := by
  simp_rw [centerEval_eq,mul_add]
  rw [Finset.sum_add_distrib,(balanced_iff_signed_sum _).1 (offsets_balanced p),zero_add]
  rfl

lemma centered_ext {p q : E5} (hp : planar p = planar q)
    (hu : S.centerEval p = S.centerEval q) : p = q := by
  apply C.evaluation_injective
  funext v
  have he : ∀ j, offsets p j = offsets q j := by
    intro j
    have h := congrFun hu j
    rw [S.centerEval_eq,S.centerEval_eq,hp] at h
    have hne : balanceSign j ≠ 0 := by
      intro hz; have := balanceSign_sq j; simp [hz] at this
    have := mul_left_cancel₀ hne h
    linarith
  change C.value p v = C.value q v
  rw [Config.value,Config.value,hp,he]

noncomputable def centeredOffset (u : Fin 4 → ℝ) (b : E 2) (j : Fin 4) : ℝ :=
  balanceSign j * u j - ⟪b,S.center j⟫

lemma centeredOffset_balanced (u : Fin 4 → ℝ) (b : E 2) (hs : ∑ j, u j = S.drift b) :
    Balanced (S.centeredOffset u b) := by
  rw [balanced_iff_signed_sum]
  simp only [centeredOffset,mul_sub,← mul_assoc,balanceSign_sq,one_mul,Finset.sum_sub_distrib]
  exact sub_eq_zero.2 hs

lemma centerEval_pack (u : Fin 4 → ℝ) (b : E 2) (hs : ∑ j, u j = S.drift b) :
    S.centerEval (pack (S.centeredOffset u b) b) = u := by
  funext j
  rw [centerEval_eq,offsets_pack (S.centeredOffset_balanced u b hs),planar_pack]
  simp only [centeredOffset,sub_add_cancel,← mul_assoc,balanceSign_sq,one_mul]

end SegmentData
end Kalai5.Cube3
