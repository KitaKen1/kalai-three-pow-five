import Kalai5.Cube3.PolarGeometry

/-! A zero-width class supplies a polar vertex on either normal ray at either sign.
Compact maximization replaces solving the full active linear system. -/

namespace Kalai5.Cube3

open Set FullPrism Filter
open scoped Topology

local notation "⟪" x ", " y "⟫" => inner ℝ x y

noncomputable def spike (j k : Fin 4) : ℝ :=
  (![1,1/3,1/3,-1/3] : Fin 4 → ℝ) ((classPerm j).symm k)

lemma spike_balanced (j : Fin 4) : Balanced (spike j) :=
  classPerm_balanced j _ (by norm_num [Balanced] <;> dsimp <;> norm_num)

lemma spike_self (j : Fin 4) : spike j j = 1 := by
  have h : (classPerm j).symm j = 0 := by
    apply (classPerm j).injective
    simpa only [Equiv.apply_symm_apply] using (classPerm_zero j).symm
  simp [spike,h]

lemma spike_other (j k : Fin 4) (hkj : k ≠ j) : |spike j k| = 1/3 := by
  have hne : (classPerm j).symm k ≠ 0 := by
    intro h
    have := congrArg (classPerm j) h
    simp only [Equiv.apply_symm_apply,classPerm_zero] at this
    exact hkj this
  have hbase : ∀ l : Fin 4, l ≠ 0 → |(![1,1/3,1/3,-1/3] : Fin 4 → ℝ) l| = 1/3 := by
    intro l hl; fin_cases l <;> norm_num at hl <;> norm_num <;> dsimp <;> norm_num
  exact hbase _ hne

lemma spike_mul_balanced (j : Fin 4) (t : ℝ) : Balanced (fun k => t * spike j k) := by
  unfold Balanced
  dsimp only
  rw [← mul_add,← mul_add]
  exact congrArg (fun r => t * r) (spike_balanced j)

variable {x : Fin 8 → E5} (C : Config x)

namespace Config

lemma value_pack {a : Fin 4 → ℝ} (ha : Balanced a) (b : E 2) (v : Fin 8) :
    C.value (pack a b) v = a (C.c v) + ⟪b,C.k v⟫ := by
  rw [value,offsets_pack ha,planar_pack]

/-- Moving a small positive distance along a class normal retains its saturated
sign and keeps every other class strictly inside the bounds. -/
lemma classFace_positive (j : Fin 4) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (b : E 2) (hb : b ≠ 0) (β : ℝ)
    (hconstant : ∀ v, C.c v = j → ⟪b,C.k v⟫ = β) :
    ∃ p ∈ C.classFace j s, 0 < ⟪b,planar p⟫ := by
  let p0 := pack (fun k => s * spike j k) (0 : E 2)
  let p1 := pack (fun k => -β * spike j k) b
  have h0 : ∀ v, C.value p0 v = s * spike j (C.c v) := by
    intro v; rw [value_pack C (spike_mul_balanced j s)]; simp
  have h1 : ∀ v, C.value p1 v = -β * spike j (C.c v) + ⟪b,C.k v⟫ :=
    fun v => C.value_pack (spike_mul_balanced j (-β)) b v
  have hclass : ∀ (t : ℝ) v, C.c v = j → C.value (p0 + t • p1) v = s := by
    intro t v hv
    rw [C.value_add_smul,h0,h1,hv,spike_self,hconstant v hv]
    ring
  have habs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, ∀ v, C.c v ≠ j → |C.value (p0 + t • p1) v| < 1 := by
    apply Filter.eventually_all.2
    intro v
    by_cases hv : C.c v = j
    · exact Filter.Eventually.of_forall (fun _ h => (h hv).elim)
    have hlt : |C.value p0 v| < 1 := by
      rw [h0,abs_mul,habs,spike_other j _ hv]
      norm_num
    have hcont : Continuous (fun t : ℝ => |C.value (p0 + t • p1) v|) :=
      continuous_abs.comp ((C.value_continuous v).comp (by fun_prop))
    have ht : ∀ᶠ t : ℝ in 𝓝 0, |C.value (p0 + t • p1) v| < 1 :=
      hcont.continuousAt.eventually (gt_mem_nhds (by simpa using hlt))
    exact ht.mono (fun _ ht _ => ht)
  obtain ⟨δ,hδ,hnear⟩ := Metric.mem_nhds_iff.1 hevent
  have ht : 0 < δ / 2 := by positivity
  have hsmall := hnear (show δ/2 ∈ Metric.ball (0 : ℝ) δ by
    change dist (δ/2) 0 < δ
    rw [Real.dist_eq,sub_zero,abs_of_pos ht]
    linarith)
  refine ⟨p0 + (δ/2) • p1,⟨?_,hclass (δ/2)⟩,?_⟩
  · intro v
    by_cases hv : C.c v = j
    · rw [hclass _ _ hv,habs]
    · exact (hsmall v hv).le
  · rw [planar_add_smul,planar_pack,planar_pack,zero_add,inner_smul_right]
    exact mul_pos ht (real_inner_self_pos.2 hb)

theorem class_ray_vertex {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ)
    (j : Fin 4) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (b : E 2) (hb : b ≠ 0) (β : ℝ)
    (hconstant : ∀ v, C.c v = j → ⟪b,C.k v⟫ = β) :
    ∃ p ∈ C.polarModel.extremePoints ℝ,
      (∀ v, C.c v = j → C.value p v = s) ∧ 0 < ⟪b,planar p⟫ := by
  obtain ⟨q,hq,hpos⟩ := C.classFace_positive j hs b hb β hconstant
  let L : E5 →L[ℝ] ℝ := (innerSL ℝ b).comp planarLinear.toContinuousLinearMap
  obtain ⟨p,hp,hmax⟩ := compact_extreme_ge (C.classFace_compact hP hrange j s) L hq
  refine ⟨p,(C.classFace_extreme j hs).extremePoints_subset_extremePoints hp,hp.1.2,?_⟩
  exact lt_of_lt_of_le hpos hmax

lemma classFace_orthogonal {j : Fin 4} {s : ℝ} {p : E5}
    (hp : ∀ v, C.c v = j → C.value p v = s)
    {v w : Fin 8} (hv : C.c v = j) (hw : C.c w = j) :
    ⟪planar p,C.k w - C.k v⟫ = 0 := by
  have hv' := hp v hv
  have hw' := hp w hw
  simp only [value,hv,hw] at hv' hw'
  rw [inner_sub_right]
  linarith

end Config
end Kalai5.Cube3
