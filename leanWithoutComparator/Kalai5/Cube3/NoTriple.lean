import Kalai5.Cube3.TripleCount

/-! Three parallel segment directions and a transverse fourth force 20 facets. -/

namespace Kalai5.Cube3

open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y

lemma det2_smul (a b : E 2) (r s : ℝ) :
    det2 (r • a) (s • b) = r*s*det2 a b := by
  simp only [det2,PiLp.smul_apply,smul_eq_mul]
  ring

variable {x : Fin 8 → E5} {C : Config x} (S : SegmentData C)

namespace SegmentData

lemma axis_det (i j : Fin 4) :
    det2 (S.axis i) (S.axis j) =
      (balanceSign i / 2) * (balanceSign j / 2) * det2 (S.direction i) (S.direction j) :=
  det2_smul _ _ _ _

lemma axis_det_ne_zero {i j : Fin 4} (h : det2 (S.direction i) (S.direction j) ≠ 0) :
    det2 (S.axis i) (S.axis j) ≠ 0 := by
  rw [S.axis_det]
  have hs (k : Fin 4) : balanceSign k / 2 ≠ 0 := by
    apply div_ne_zero _ (by norm_num)
    intro hh
    have hk := balanceSign_sq k
    rw [hh] at hk
    norm_num at hk
  exact mul_ne_zero (mul_ne_zero (hs i) (hs j)) h

theorem tripleFrame_of_directions (τ : Equiv.Perm (Fin 4))
    (hz : ∀ i : Fin 3, det2 (S.direction (τ 0)) (S.direction (τ i.castSucc)) = 0)
    (ht : det2 (S.direction (τ 0)) (S.direction (τ 3)) ≠ 0) :
    Nonempty (TripleFrame S) := by
  let d := det2 (S.axis (τ 0)) (S.axis (τ 3))
  have hd : d ≠ 0 := S.axis_det_ne_zero ht
  refine ⟨⟨τ,d⁻¹ • normal2 (S.axis (τ 0)),?_,?_⟩⟩
  · intro i
    rw [real_inner_smul_left,normal2_inner,S.axis_det,hz,mul_zero,mul_zero]
  · rw [real_inner_smul_left,normal2_inner]
    exact inv_mul_cancel₀ hd

/-- A triple of parallel classes forces the remaining class to be parallel too. -/
def NoTriple : Prop :=
  ∀ τ : Equiv.Perm (Fin 4),
    (∀ i : Fin 3, det2 (S.direction (τ 0)) (S.direction (τ i.castSucc)) = 0) →
      det2 (S.direction (τ 0)) (S.direction (τ 3)) = 0

theorem no_triple_parallel {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (hno : ¬ C.ExtraPM) : S.NoTriple := by
  intro τ hz
  by_contra ht
  obtain ⟨F⟩ := S.tripleFrame_of_directions τ hz ht
  have h20 := F.twenty_facets hP hrange hno
  omega

end SegmentData

theorem Config.segments_residual {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (hno : ¬ C.ExtraPM) (hsize : ∀ j, (C.cls j).card = 2) :
    ∃ S : SegmentData C, S.MixedDirections ∧ S.NoTriple := by
  obtain ⟨S⟩ := C.segments_of_size_two hsize
  exact ⟨S,S.mixed_directions hP hrange hh hno,S.no_triple_parallel hP hrange hh hno⟩

end Kalai5.Cube3
