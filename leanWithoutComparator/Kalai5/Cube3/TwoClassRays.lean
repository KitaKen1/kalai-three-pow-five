import Kalai5.Cube3.SignedCoordinates

/-! Keep one supporting fibre at +1 and a zero-width fibre at -1. -/

namespace Kalai5.Cube3
open Set FullPrism Filter
open scoped Topology
local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {x : Fin 8 → E5} (C : Config x)
namespace Config

lemma two_class_positive (j i k : Fin 4) (hji : j ≠ i) (hkj : k ≠ j) (hki : k ≠ i)
    (n : E 2) (hn : n ≠ 0) (β γ : ℝ)
    (hupper : ∀ v,C.c v=j → ⟪n,C.signedPoint v⟫≤β)
    (hconstant : ∀ v,C.c v=i → ⟪n,C.signedPoint v⟫=γ) :
    ∃ p ∈ C.polarModel,
      (∀ v,C.c v=j → ⟪n,C.signedPoint v⟫=β → C.signedValue p v=1) ∧
      (∀ v,C.c v=i → C.signedValue p v= -1) ∧ 0 < ⟪n,planar p⟫ := by
  let u0 := fun l => classIndicator j l-classIndicator i l
  let u1 := fun l => -β*classIndicator j l-γ*classIndicator i l+(β+γ)*classIndicator k l
  have hu0 : ∑ l,u0 l=0 := by simp [u0,Finset.sum_sub_distrib,classIndicator_sum]
  have hu1 : ∑ l,u1 l=0 := by
    simp only [u1,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,classIndicator_sum]
    ring
  let p0 := pack (signedOffsets u0) (0 : E 2)
  let p1 := pack (signedOffsets u1) n
  have h0 (v : Fin 8) : C.signedValue p0 v=u0 (C.c v) := by
    rw [signedValue_pack C hu0]; simp
  have h1 (v : Fin 8) : C.signedValue p1 v=u1 (C.c v)+⟪n,C.signedPoint v⟫ :=
    C.signedValue_pack hu1 n v
  have hj (t : ℝ) (v : Fin 8) (hv : C.c v=j) :
      C.signedValue (p0+t • p1) v=1+t*(-β+⟪n,C.signedPoint v⟫) := by
    rw [signedValue_add_smul,h0,h1,hv]
    simp [u0,u1,classIndicator,hji,hji.symm,hkj,hkj.symm]
  have hi (t : ℝ) (v : Fin 8) (hv : C.c v=i) : C.signedValue (p0+t • p1) v= -1 := by
    rw [signedValue_add_smul,h0,h1,hv,hconstant v hv]
    simp [u0,u1,classIndicator,hji,hji.symm,hki,hki.symm]
  have hbase (v : Fin 8) (hvj : C.c v ≠ j) (hvi : C.c v ≠ i) : C.signedValue p0 v=0 := by
    rw [h0]; simp [u0,classIndicator,hvj,hvi]
  have hevent : ∀ᶠ t : ℝ in 𝓝 0,∀ v,
      (C.c v=j → -1 < C.signedValue (p0+t • p1) v) ∧
      (C.c v ≠ j → C.c v ≠ i → |C.signedValue (p0+t • p1) v|<1) := by
    apply Filter.eventually_all.2
    intro v
    have hcont : Continuous (fun t : ℝ => C.signedValue (p0+t • p1) v) :=
      (C.signedValue_continuous v).comp (by fun_prop)
    by_cases hvj : C.c v=j
    · have hh := hcont.continuousAt.eventually (lt_mem_nhds
        (show (-1 : ℝ) < C.signedValue (p0+(0 : ℝ) • p1) v by rw [hj 0 v hvj]; norm_num))
      exact hh.mono (fun _ ht => ⟨fun _ => ht,fun h _ => (h hvj).elim⟩)
    · by_cases hvi : C.c v=i
      · exact Filter.Eventually.of_forall (fun _ => ⟨fun h => (hvj h).elim,fun _ h => (h hvi).elim⟩)
      · have hh := (continuous_abs.comp hcont).continuousAt.eventually (gt_mem_nhds
          (show |C.signedValue (p0+(0 : ℝ) • p1) v|<1 by simp [hbase v hvj hvi]))
        exact hh.mono (fun _ ht => ⟨fun h => (hvj h).elim,fun _ _ => ht⟩)
  obtain ⟨δ,hδ,hnear⟩ := Metric.mem_nhds_iff.1 hevent
  have ht : 0 < δ/2 := by positivity
  have hsmall := hnear (show δ/2 ∈ Metric.ball (0 : ℝ) δ by
    change dist (δ/2) 0 < δ
    rw [Real.dist_eq,sub_zero,abs_of_pos ht]; linarith)
  refine ⟨p0+(δ/2) • p1,?_,?_,hi (δ/2),?_⟩
  · rw [C.mem_polar_signed]
    intro v
    by_cases hvj : C.c v=j
    · apply abs_le.2
      refine ⟨(hsmall v).1 hvj |>.le,?_⟩
      rw [hj _ v hvj]; nlinarith [hupper v hvj]
    · by_cases hvi : C.c v=i
      · rw [hi _ v hvi]; norm_num
      · exact ((hsmall v).2 hvj hvi).le
  · intro v hv hβ
    rw [hj _ v hv,hβ]; ring
  · rw [planar_add_smul,planar_pack,planar_pack,zero_add,inner_smul_right]
    exact mul_pos ht (real_inner_self_pos.2 hn)

theorem two_class_ray_vertex {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ)
    (j i k : Fin 4) (hji : j ≠ i) (hkj : k ≠ j) (hki : k ≠ i)
    (n : E 2) (hn : n ≠ 0) (β γ : ℝ)
    (hupper : ∀ v,C.c v=j → ⟪n,C.signedPoint v⟫≤β)
    (hconstant : ∀ v,C.c v=i → ⟪n,C.signedPoint v⟫=γ) :
    ∃ p ∈ C.polarModel.extremePoints ℝ,
      (∀ v,C.c v=j → ⟪n,C.signedPoint v⟫=β → C.signedValue p v=1) ∧
      (∀ v,C.c v=i → C.signedValue p v= -1) ∧ 0 < ⟪n,planar p⟫ := by
  classical
  obtain ⟨q,hq,hqj,hqi,hpos⟩ := C.two_class_positive j i k hji hkj hki n hn β γ hupper hconstant
  let T := Finset.univ.filter fun v => (C.c v=j ∧ ⟪n,C.signedPoint v⟫=β) ∨ C.c v=i
  let s := fun v => if C.c v=j then (1 : ℝ) else -1
  have hs : ∀ v ∈ T,s v=1 ∨ s v= -1 := by intro v _; dsimp [s]; split <;> simp
  have hqs : ∀ v ∈ T,C.signedValue q v=s v := by
    intro v hv
    have hv' : (C.c v=j ∧ ⟪n,C.signedPoint v⟫=β) ∨ C.c v=i := by simpa [T] using hv
    rcases hv' with ⟨hv,hβ⟩ | hv
    · simpa [s,hv] using hqj v hv hβ
    · simpa [s,hv,hji.symm] using hqi v hv
  obtain ⟨p,hp,hps,hppos⟩ := C.signed_activeFace_ray_vertex hP hrange T s hs n hq hqs hpos
  refine ⟨p,hp,?_,?_,hppos⟩
  · intro v hv hβ
    simpa [s,hv] using hps v (by simp [T,hv,hβ])
  · intro v hv
    simpa [s,hv,hji.symm] using hps v (by simp [T,hv])

end Config
end Kalai5.Cube3
