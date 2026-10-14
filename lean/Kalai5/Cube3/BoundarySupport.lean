import Kalai5.Cube3.ZeroSupportEdge
import Kalai5.Cube3.SegmentCenters

/-! The two shared-edge drift boundaries supply the zero-support line for ray shooting. -/
namespace Kalai5.Cube3
open Set LemmaB
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} (C : Config x)

noncomputable def Config.signedFibre (j : Fin 4) : Finset (E 2) := (C.cls j).image C.signedPoint

lemma Config.signedFibre_mem (v : Fin 8) : C.signedPoint v ∈ C.signedFibre (C.c v) := by
  classical
  exact Finset.mem_image.2 ⟨v,by simp [Config.cls],rfl⟩

theorem Config.boundary_support_edge (τ : Equiv.Perm (Fin 4))
    (h0 : 3 ≤ (C.cls (τ 0)).card) (S : SegmentFibre C (τ 1))
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1)
    {n : E 2} (hn : n ≠ 0) (hSn : ⟪n,S.direction⟫=0) (I : ProjectionIntervals C n)
    (he : I.drift n=I.radius (τ 0) ∨ I.drift n= -I.radius (τ 0)) :
    Nonempty (TransverseSupportEdge (C.signedFibre (τ 0))
      (C.signedPoint S.first) (C.signedPoint S.second)
      (C.signedPoint (I.hi (τ 2))+C.signedPoint (I.hi (τ 3)))) := by
  classical
  let A := C.signedFibre (τ 0)
  let c := C.signedPoint (I.hi (τ 2))+C.signedPoint (I.hi (τ 3))
  have hmem (v : Fin 8) (hv : C.c v=τ 0) : C.signedPoint v ∈ A := by
    dsimp only [A]
    rw [← hv]; exact C.signedFibre_mem v
  have hA : A.Nonempty := ⟨_,hmem _ (I.chi _)⟩
  have hhi : ⟪n,C.signedPoint (I.hi (τ 0))⟫=⟪n,I.center (τ 0)⟫+I.radius (τ 0) := by
    simp only [ProjectionIntervals.center,ProjectionIntervals.radius,ProjectionIntervals.axis,
      inner_smul_right,inner_add_right,inner_sub_right]; ring
  have hlo : ⟪n,C.signedPoint (I.lo (τ 0))⟫=⟪n,I.center (τ 0)⟫-I.radius (τ 0) := by
    simp only [ProjectionIntervals.center,ProjectionIntervals.radius,ProjectionIntervals.axis,
      inner_smul_right,inner_add_right,inner_sub_right]; ring
  have hp := I.radius_positive h0 hn
  have hlt : ⟪n,C.signedPoint (I.lo (τ 0))⟫<⟪n,C.signedPoint (I.hi (τ 0))⟫ := by
    rw [hhi,hlo]; linarith
  have hs : ⟪n,I.center (τ 1)⟫=⟪n,C.signedPoint S.first⟫ := by
    simp only [ProjectionIntervals.center,inner_smul_right,inner_add_right]
    rw [S.constant hSn _ (I.clo _),S.constant hSn _ (I.chi _)]
    ring
  have hsum : I.drift n=⟪n,I.center (τ 0)⟫+⟪n,C.signedPoint S.first+c⟫ := by
    change (∑ j,⟪n,I.center j⟫)=_
    rw [← Equiv.sum_comp τ (fun j => ⟪n,I.center j⟫),Fin.sum_univ_four,hs,
      I.singleton_center h2 _ (I.chi _),I.singleton_center h3 _ (I.chi _)]
    simp only [c,inner_add_right]; ring
  have hmax (a : E 2) (ha : a ∈ amax A n) : ⟪n,a⟫=⟪n,C.signedPoint (I.hi (τ 0))⟫ := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.1 (mem_amax.1 ha).1
    have hv' : C.c v=τ 0 := by simpa [Config.cls] using hv
    have h1 := I.upper v
    rw [hv'] at h1
    exact le_antisymm h1 ((mem_amax.1 ha).2 _ (hmem _ (I.chi _)))
  have hmin (a : E 2) (ha : a ∈ amax A (-n)) : ⟪n,a⟫=⟪n,C.signedPoint (I.lo (τ 0))⟫ := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.1 (mem_amax.1 ha).1
    have hv' : C.c v=τ 0 := by simpa [Config.cls] using hv
    have h1 := I.lower v
    rw [hv'] at h1
    have h2 := (mem_amax.1 ha).2 _ (hmem _ (I.clo _))
    simp only [inner_neg_left] at h2
    linarith
  rcases he with he | he
  · apply finite_zero_support_edge hA S.direction_ne_zero
      (b := -n) (by rw [inner_neg_left]; change -⟪n,S.direction⟫=0; rw [hSn,neg_zero])
    · exact ⟨_,hmem _ (I.chi _),_,hmem _ (I.clo _),by simpa only [inner_neg_left] using neg_lt_neg hlt⟩
    · intro a ha
      rw [inner_neg_left,inner_add_right,inner_add_right,hmin a ha,hlo]
      simp only [inner_add_right] at hsum
      linarith
  · apply finite_zero_support_edge hA S.direction_ne_zero (b := n) hSn
    · exact ⟨_,hmem _ (I.clo _),_,hmem _ (I.chi _),hlt⟩
    · intro a ha
      rw [inner_add_right,inner_add_right,hmax a ha,hhi]
      simp only [inner_add_right] at hsum
      linarith

end Kalai5.Cube3
