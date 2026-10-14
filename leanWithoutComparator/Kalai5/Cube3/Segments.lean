import Kalai5.Cube3.RayVertices

/-! Endpoints and exact normal directions for four two-point fibres. -/

namespace Kalai5.Cube3

open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y

noncomputable def det2 (a b : E 2) : ℝ := a 0 * b 1 - a 1 * b 0

noncomputable def normal2 (a : E 2) : E 2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![-a 1,a 0]

lemma normal2_ne_zero {a : E 2} (ha : a ≠ 0) : normal2 a ≠ 0 := by
  intro h
  have h0 := congrArg (fun b : E 2 => b 0) h
  have h1 := congrArg (fun b : E 2 => b 1) h
  have ha0 : a 0 = 0 := by simpa [normal2] using h1
  have ha1 : a 1 = 0 := by simpa [normal2] using h0
  apply ha
  ext i; fin_cases i <;> assumption

lemma normal2_orthogonal (a : E 2) : ⟪normal2 a,a⟫ = 0 := by
  rw [LemmaB.Eight.inner_E2]
  simp [normal2]
  ring

lemma normal2_inner (a b : E 2) : ⟪normal2 a,b⟫ = det2 a b := by
  rw [LemmaB.Eight.inner_E2]
  simp [normal2,det2]
  ring

lemma orthogonal_two_eq_zero {a b z : E 2} (hd : det2 a b ≠ 0)
    (ha : ⟪z,a⟫ = 0) (hb : ⟪z,b⟫ = 0) : z = 0 := by
  rw [LemmaB.Eight.inner_E2] at ha hb
  have hz0 : z 0 * det2 a b = 0 := by
    calc
      _ = b 1 * (z 0 * a 0 + z 1 * a 1) - a 1 * (z 0 * b 0 + z 1 * b 1) := by
        unfold det2; ring
      _ = 0 := by rw [ha,hb]; ring
  have hz1 : z 1 * det2 a b = 0 := by
    calc
      _ = a 0 * (z 0 * b 0 + z 1 * b 1) - b 0 * (z 0 * a 0 + z 1 * a 1) := by
        unfold det2; ring
      _ = 0 := by rw [ha,hb]; ring
  have h0 := (mul_eq_zero.1 hz0).resolve_right hd
  have h1 := (mul_eq_zero.1 hz1).resolve_right hd
  ext i; fin_cases i <;> assumption

variable {x : Fin 8 → E5}

structure SegmentData (C : Config x) where
  lo : Fin 4 → Fin 8
  hi : Fin 4 → Fin 8
  clo : ∀ j, C.c (lo j) = j
  chi : ∀ j, C.c (hi j) = j
  ne : ∀ j, lo j ≠ hi j
  cover : ∀ v, v = lo (C.c v) ∨ v = hi (C.c v)

namespace Config

theorem segments_of_size_two (C : Config x) (hsize : ∀ j, (C.cls j).card = 2) :
    Nonempty (SegmentData C) := by
  classical
  have hex : ∀ j, ∃ v w : Fin 8, v ≠ w ∧ C.cls j = {v,w} :=
    fun j => Finset.card_eq_two.1 (hsize j)
  choose lo hi hne hcls using hex
  have hclo : ∀ j, C.c (lo j) = j := by
    intro j
    have h : lo j ∈ C.cls j := by rw [hcls]; simp
    simpa [cls] using h
  have hchi : ∀ j, C.c (hi j) = j := by
    intro j
    have h : hi j ∈ C.cls j := by rw [hcls]; simp
    simpa [cls] using h
  refine ⟨⟨lo,hi,hclo,hchi,hne,?_⟩⟩
  intro v
  have h : v ∈ C.cls (C.c v) := by simp [cls]
  rw [hcls] at h
  simpa using h

end Config

namespace SegmentData

variable {C : Config x} (S : SegmentData C)

noncomputable def direction (j : Fin 4) : E 2 := C.k (S.hi j) - C.k (S.lo j)

lemma direction_ne_zero (j : Fin 4) : S.direction j ≠ 0 := by
  intro h
  have he := sub_eq_zero.1 h
  have heq := C.inj (S.hi j) (S.lo j) ((S.chi j).trans (S.clo j).symm) he
  exact S.ne j heq.symm

lemma normal_constant (j : Fin 4) (v : Fin 8) (hv : C.c v = j) :
    ⟪normal2 (S.direction j),C.k v⟫ = ⟪normal2 (S.direction j),C.k (S.lo j)⟫ := by
  have h := S.cover v
  rw [hv] at h
  rcases h with rfl | rfl
  · rfl
  · have hz := normal2_orthogonal (S.direction j)
    rw [direction,inner_sub_right] at hz
    exact sub_eq_zero.1 hz

lemma class_orthogonal {j : Fin 4} {s : ℝ} {p : E5}
    (hp : ∀ v, C.c v = j → C.value p v = s) : ⟪planar p,S.direction j⟫ = 0 :=
  C.classFace_orthogonal hp (S.clo j) (S.chi j)

lemma not_all_parallel (hno : ¬ C.ExtraPM) :
    ∃ j : Fin 4, det2 (S.direction 0) (S.direction j) ≠ 0 := by
  by_contra h
  push_neg at h
  have hc : ∀ v, ⟪normal2 (S.direction 0),C.k v⟫ =
      ⟪normal2 (S.direction 0),C.k (S.lo (C.c v))⟫ := by
    intro v
    obtain hv | hv := S.cover v
    · exact congrArg (fun w => ⟪normal2 (S.direction 0),C.k w⟫) hv
    · have he : ⟪normal2 (S.direction 0),S.direction (C.c v)⟫ = 0 := by
        rw [normal2_inner,h]
      change ⟪normal2 (S.direction 0),C.k (S.hi (C.c v)) - C.k (S.lo (C.c v))⟫ = 0 at he
      rw [inner_sub_right] at he
      exact (congrArg (fun w => ⟪normal2 (S.direction 0),C.k w⟫) hv).trans (sub_eq_zero.1 he)
  apply normal2_ne_zero (S.direction_ne_zero 0)
  apply C.span_of_no_extra hno
  intro v w hvw
  rw [hc v,hc w,hvw]

end SegmentData
end Kalai5.Cube3
