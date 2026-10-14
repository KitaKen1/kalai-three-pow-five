import Kalai5.Cube3.EdgeRays
import Kalai5.Cube3.SegmentCoordinates

/-! Absorb the balanced signs into all fibres, including polygons and singletons. -/

namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y

lemma balanceSign_sign (j : Fin 4) : balanceSign j=1 ∨ balanceSign j= -1 := by
  fin_cases j <;> norm_num [balanceSign]

noncomputable def signedOffsets (u : Fin 4 → ℝ) (j : Fin 4) : ℝ := balanceSign j*u j

lemma signedOffsets_balanced {u : Fin 4 → ℝ} (hu : ∑ j,u j=0) : Balanced (signedOffsets u) := by
  rw [balanced_iff_signed_sum]
  simpa only [signedOffsets,← mul_assoc,balanceSign_sq,one_mul] using hu

noncomputable def classIndicator (i : Fin 4) (j : Fin 4) : ℝ := if j=i then 1 else 0

lemma classIndicator_sum (i : Fin 4) : ∑ j,classIndicator i j=1 := by simp [classIndicator]

variable {x : Fin 8 → E5} (C : Config x)

namespace Config

noncomputable def signedPoint (v : Fin 8) : E 2 := balanceSign (C.c v) • C.k v

noncomputable def signedValue (p : E5) (v : Fin 8) : ℝ := balanceSign (C.c v)*C.value p v

lemma signedValue_eq (p : E5) (v : Fin 8) :
    C.signedValue p v=balanceSign (C.c v)*offsets p (C.c v)+⟪planar p,C.signedPoint v⟫ := by
  simp only [signedValue,value,signedPoint,inner_smul_right]; ring

lemma signedValue_eq_iff (p : E5) (v : Fin 8) (t : ℝ) :
    C.signedValue p v=t ↔ C.value p v=balanceSign (C.c v)*t := by
  constructor
  · intro h
    have he := congrArg (fun a => balanceSign (C.c v)*a) h
    simpa only [signedValue,← mul_assoc,balanceSign_sq,one_mul] using he
  · intro h
    simp only [signedValue,h,← mul_assoc,balanceSign_sq,one_mul]

lemma signedValue_pack {u : Fin 4 → ℝ} (hu : ∑ j,u j=0) (b : E 2) (v : Fin 8) :
    C.signedValue (pack (signedOffsets u) b) v=u (C.c v)+⟪b,C.signedPoint v⟫ := by
  rw [signedValue_eq,offsets_pack (signedOffsets_balanced hu),planar_pack]
  simp only [signedOffsets,← mul_assoc,balanceSign_sq,one_mul]

lemma signedValue_add_smul (p q : E5) (t : ℝ) (v : Fin 8) :
    C.signedValue (p+t • q) v=C.signedValue p v+t*C.signedValue q v := by
  simp only [signedValue,value_add_smul]; ring

lemma signedValue_continuous (v : Fin 8) : Continuous (fun p => C.signedValue p v) :=
  continuous_const.mul (C.value_continuous v)

lemma signedValue_abs (p : E5) (v : Fin 8) : |C.signedValue p v|=|C.value p v| := by
  rw [signedValue,abs_mul,balanceSign_abs,one_mul]

lemma mem_polar_signed (p : E5) : p ∈ C.polarModel ↔ ∀ v,|C.signedValue p v|≤1 := by
  simp only [signedValue_abs]; rfl

lemma signedValue_sum (rep : Fin 4 → Fin 8) (hc : ∀ j,C.c (rep j)=j) (p : E5) :
    ∑ j,C.signedValue p (rep j)=⟪planar p,∑ j,C.signedPoint (rep j)⟫ := by
  simp_rw [signedValue_eq,hc]
  rw [Finset.sum_add_distrib,(balanced_iff_signed_sum _).1 (offsets_balanced p),zero_add,inner_sum]

lemma signedValue_sum_ordered (τ : Equiv.Perm (Fin 4)) (rep : Fin 4 → Fin 8)
    (hc : ∀ j,C.c (rep j)=τ j) (p : E5) :
    ∑ j,C.signedValue p (rep j)=⟪planar p,∑ j,C.signedPoint (rep j)⟫ := by
  simp_rw [signedValue_eq,hc]
  rw [Finset.sum_add_distrib]
  have hz : ∑ j,balanceSign (τ j)*offsets p (τ j)=0 := by
    calc
      _ = ∑ j,balanceSign j*offsets p j := Equiv.sum_comp τ (fun j => balanceSign j*offsets p j)
      _ = 0 := (balanced_iff_signed_sum _).1 (offsets_balanced p)
  rw [hz,zero_add,inner_sum]

lemma equal_signedValue_orthogonal {p : E5} {v w : Fin 8} (hclass : C.c v=C.c w)
    (hvalue : C.signedValue p v=C.signedValue p w) :
    ⟪planar p,C.signedPoint w-C.signedPoint v⟫=0 := by
  simp only [signedValue_eq,hclass] at hvalue
  rw [inner_sub_right]; linarith

theorem signed_activeFace_ray_vertex {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (T : Finset (Fin 8)) (s : Fin 8 → ℝ)
    (hs : ∀ v ∈ T,s v=1 ∨ s v= -1) (n : E 2)
    {q : E5} (hq : q ∈ C.polarModel) (hqs : ∀ v ∈ T,C.signedValue q v=s v)
    (hpos : 0 < ⟪n,planar q⟫) :
    ∃ p ∈ C.polarModel.extremePoints ℝ,(∀ v ∈ T,C.signedValue p v=s v) ∧ 0 < ⟪n,planar p⟫ := by
  obtain ⟨p,hp,hps,hppos⟩ := C.activeFace_ray_vertex hP hrange T
    (fun v => balanceSign (C.c v)*s v) (fun v hv => by
      rcases balanceSign_sign (C.c v) with h | h <;> rcases hs v hv with hs | hs <;>
        rw [h,hs] <;> norm_num) n ⟨hq,fun v hv => (C.signedValue_eq_iff q v (s v)).1 (hqs v hv)⟩ hpos
  exact ⟨p,hp,fun v hv => (C.signedValue_eq_iff p v (s v)).2 (hps v hv),hppos⟩

end Config
end Kalai5.Cube3
