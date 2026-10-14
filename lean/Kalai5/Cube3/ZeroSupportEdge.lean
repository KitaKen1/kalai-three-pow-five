import Kalai5.Cube3.SupportFirstEdge

/-! A nonzero segment parallel to a zero-support line yields a positive transverse edge. -/
namespace Kalai5.Cube3
open Set LemmaB
local notation "⟪" x ", " y "⟫" => inner ℝ x y

structure TransverseSupportEdge (A : Finset (E 2)) (s₀ s₁ c : E 2) where
  normal : E 2
  unit : ‖normal‖=1
  first : E 2
  second : E 2
  first_mem : first ∈ A
  second_mem : second ∈ A
  distinct : second ≠ first
  equal : ⟪normal,second⟫=⟪normal,first⟫
  upper : ∀ u ∈ A,⟪normal,u⟫≤⟪normal,first⟫
  endpoint : E 2
  endpoint_mem : endpoint=s₀ ∨ endpoint=s₁
  transverse : ⟪normal,s₁-s₀⟫ ≠ 0
  positive : 0 < ⟪normal,first+endpoint+c⟫

theorem finite_zero_support_edge {A : Finset (E 2)} (hA : A.Nonempty)
    {b s₀ s₁ c : E 2} (hd : s₁-s₀ ≠ 0) (hbd : ⟪b,s₁-s₀⟫=0)
    (hwidth : ∃ u ∈ A,∃ v ∈ A,⟪b,u⟫<⟪b,v⟫)
    (hzero : ∀ a ∈ amax A b,⟪b,a+s₀+c⟫=0) :
    Nonempty (TransverseSupportEdge A s₀ s₁ c) := by
  classical
  let d := s₁-s₀
  have hdd : 0 < ⟪d,d⟫ := real_inner_self_pos.2 hd
  obtain ⟨a₀,ha₀⟩ := amax_nonempty hA b
  have hdiff : ⟪d,a₀+s₁+c⟫-⟪d,a₀+s₀+c⟫=⟪d,d⟫ := by
    simp only [d,inner_add_right,inner_sub_right]; ring
  obtain ⟨e,s,hs,hed,hpos⟩ : ∃ e s : E 2,(s=s₀ ∨ s=s₁) ∧ ⟪e,d⟫ ≠ 0 ∧
      0 < ⟪e,a₀+s+c⟫ := by
    by_cases hp : 0 < ⟪d,a₀+s₁+c⟫
    · exact ⟨d,s₁,Or.inr rfl,hdd.ne',hp⟩
    · refine ⟨-d,s₀,Or.inl rfl,?_,?_⟩
      · rw [inner_neg_left]; exact neg_ne_zero.2 hdd.ne'
      · rw [inner_neg_left]; linarith
  obtain ⟨a,ha,hamax⟩ := (amax A b).exists_max_image (fun u => ⟪e,u⟫) ⟨a₀,ha₀⟩
  have hapos : 0 < ⟪e,a+s+c⟫ := by
    have h := hamax a₀ ha₀
    simp only [inner_add_right] at hpos ⊢
    linarith
  have hb : ∀ u ∈ A,⟪b,u⟫≤⟪b,a⟫ := (mem_amax.1 ha).2
  have hface (u : E 2) (hu : u ∈ A) (he : ⟪b,u⟫=⟪b,a⟫) : ⟪e,u⟫≤⟪e,a⟫ := by
    apply hamax u
    exact mem_amax.2 ⟨hu,fun v hv => (hb v hv).trans_eq he.symm⟩
  have hlower : ∃ v ∈ A,⟪b,v⟫<⟪b,a⟫ := by
    obtain ⟨u,hu,v,hv,huv⟩ := hwidth
    exact ⟨u,hu,huv.trans_le (hb v hv)⟩
  have hbz : ⟪b,a+s+c⟫=0 := by
    have hh := hzero a ha
    rcases hs with rfl | rfl
    · exact hh
    · simp only [inner_sub_right] at hbd
      simp only [inner_add_right] at hh ⊢
      linarith
  obtain ⟨m,q,hq,hqa,hqm,hm,hmd,hmz⟩ := finite_support_first_edge
    (mem_amax.1 ha).1 hb hface hlower hbd hed hbz hapos
  have hm0 : m ≠ 0 := by intro he; exact hmd (by rw [he,inner_zero_left])
  have hnorm : 0 < ‖m‖ := norm_pos_iff.2 hm0
  let n := ‖m‖⁻¹ • m
  refine ⟨{
    normal := n
    unit := ?_
    first := a
    second := q
    first_mem := (mem_amax.1 ha).1
    second_mem := hq
    distinct := hqa
    equal := ?_
    upper := ?_
    endpoint := s
    endpoint_mem := hs
    transverse := ?_
    positive := ?_ }⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.2 hnorm),inv_mul_cancel₀ hnorm.ne']
  · change ⟪‖m‖⁻¹ • m,q⟫=⟪‖m‖⁻¹ • m,a⟫
    rw [real_inner_smul_left,real_inner_smul_left,hqm]
  · intro u hu
    change ⟪‖m‖⁻¹ • m,u⟫≤⟪‖m‖⁻¹ • m,a⟫
    rw [real_inner_smul_left,real_inner_smul_left]
    exact mul_le_mul_of_nonneg_left (hm u hu) (inv_pos.2 hnorm).le
  · change ⟪‖m‖⁻¹ • m,s₁-s₀⟫ ≠ 0
    rw [real_inner_smul_left]; exact mul_ne_zero (inv_ne_zero hnorm.ne') hmd
  · change 0 < ⟪‖m‖⁻¹ • m,a+s+c⟫
    rw [real_inner_smul_left]; exact mul_pos (inv_pos.2 hnorm) hmz

end Kalai5.Cube3
