import Kalai5.Cube3.SupportPairSeeds

/-! Put both supported-edge seeds in the actual polar and preserve their active evaluations. -/
namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x} {n : E 2}
namespace ProjectionIntervals
variable (I : ProjectionIntervals C n)

theorem support_pair_points (τ : Equiv.Perm (Fin 4))
    (hz : I.radius (τ 3)=0) (hle : I.radius (τ 2)≤I.radius (τ 1))
    (hp : 0 < I.drift n+I.radius (τ 0)) :
    ∃ t : ℝ,0 < t ∧ ∃ q : Fin 2 → E5,
      (∀ i,q i ∈ C.polarModel) ∧ (∀ i,planar (q i)=t • n) ∧
      (∀ i,C.signedValue (q i) (I.hi (τ 0))=1) ∧
      (∀ i,C.signedValue (q i) (I.hi (τ 1))=1) ∧
      C.signedValue (q 0) (I.lo (τ 2))= -1 ∧ C.signedValue (q 1) (I.lo (τ 3))= -1 := by
  obtain ⟨G⟩ := support_pair_seeds (I.radius_nonneg (τ 0)) (I.radius_nonneg (τ 2)) hle hp
  let u (i : Fin 2) (j : Fin 4) := G.coords i (τ.symm j)
  have hu (i : Fin 2) (j : Fin 4) : u i (τ j)=G.coords i j := by simp [u]
  have hsum (i : Fin 2) : ∑ j,u i j=I.drift (G.t • n) := by
    simp only [u]
    rw [Equiv.sum_comp τ.symm,G.sum,map_smul,smul_eq_mul]
    ring
  let q (i : Fin 2) := pack (I.centeredOffset (u i) (G.t • n)) (G.t • n)
  have hplane (i : Fin 2) : planar (q i)=G.t • n := planar_pack _ _
  have hcenter (i : Fin 2) : I.centerEval (q i)=u i := I.centerEval_pack _ _ (hsum i)
  have hwidth (j : Fin 4) : I.radius (τ j)=
      (![I.radius (τ 0),I.radius (τ 1),I.radius (τ 2),0] : Fin 4 → ℝ) j := by
    fin_cases j <;> first | rfl | exact hz
  refine ⟨G.t,G.positive,q,?_,hplane,?_,?_,?_,?_⟩
  · intro i
    apply (I.mem_polar_on_line (hplane i)).2
    intro j; obtain ⟨j,rfl⟩ := τ.surjective j
    rw [hcenter,hu,abs_of_pos G.positive]
    calc
      _ = |G.coords i j|+(![I.radius (τ 0),I.radius (τ 1),I.radius (τ 2),0] : Fin 4 → ℝ) j*G.t :=
        congrArg (fun a : ℝ => |G.coords i j|+a*G.t) (hwidth j)
      _ ≤ 1 := G.bound i j
  · intro i
    rw [I.signed_hi,hcenter,hu,hplane,real_inner_smul_left]
    change G.coords i 0+G.t*I.radius (τ 0)=1
    simpa only [mul_comm] using G.triangle i
  · intro i
    rw [I.signed_hi,hcenter,hu,hplane,real_inner_smul_left]
    change G.coords i 1+G.t*I.radius (τ 1)=1
    simpa only [mul_comm] using G.upper i
  · rw [I.signed_lo,hcenter,hu,hplane,real_inner_smul_left]
    change G.coords 0 2-G.t*I.radius (τ 2)= -1
    simpa only [mul_comm] using G.lower_first
  · rw [I.signed_lo,hcenter,hu,hplane,real_inner_smul_left]
    change G.coords 1 3-G.t*I.radius (τ 3)= -1
    rw [hz,mul_zero,sub_zero]; exact G.lower_second

lemma equal_value_on_line {p : E5} {t : ℝ} (hp : planar p=t • n)
    {v w : Fin 8} (hc : C.c v=C.c w)
    (he : ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint w⟫) :
    C.signedValue p v=C.signedValue p w := by
  rw [Config.signedValue_eq,Config.signedValue_eq,hc,hp]
  simp only [real_inner_smul_left,he]

end ProjectionIntervals
end Kalai5.Cube3
