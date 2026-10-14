import Kalai5.Cube3.TripleTransfer
import Kalai5.Small.General

/-! Ten vertices on the triple normal, four on the remaining normal, and six central vertices. -/

namespace Kalai5.Cube3

open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y

lemma sum_family_injective {α β γ : Type*} (f : α → γ) (g : β → γ)
    (hf : Function.Injective f) (hg : Function.Injective g) (hd : ∀ i j, f i ≠ g j) :
    Function.Injective (Sum.elim f g) := by
  intro i j h
  rcases i with i | i <;> rcases j with j | j
  · exact congrArg Sum.inl (hf h)
  · exact (hd i j h).elim
  · exact (hd j i h.symm).elim
  · exact congrArg Sum.inr (hg h)

variable {x : Fin 8 → E5} {C : Config x} {S : SegmentData C}

lemma Config.polarModel_neg {p : E5} (hp : p ∈ C.polarModel) : -p ∈ C.polarModel := by
  intro v
  have hh := congrFun (C.evaluation.map_neg p) v
  change C.value (-p) v = -C.value p v at hh
  rw [hh,abs_neg]
  exact hp v

lemma Config.polarModel_neg_extreme {p : E5} (hp : p ∈ C.polarModel.extremePoints ℝ) :
    -p ∈ C.polarModel.extremePoints ℝ :=
  CS.neg_mem_extremePoints (fun _ h => C.polarModel_neg h) hp

namespace TripleFrame

variable (F : TripleFrame S)

include F in
theorem twenty_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ) (hno : ¬ C.ExtraPM) :
    20 ≤ fvec P 4 := by
  obtain ⟨f,hf,hfmem,hfpos,hfplane⟩ := F.five_positive hno
  let A := Sum.elim f (fun i => -f i)
  have hn (p : E5) : (F.project (-p)).2 = -(F.project p).2 := by rw [map_neg]; rfl
  have hAinj : Function.Injective A := by
    apply sum_family_injective f (fun i => -f i) hf (neg_injective.comp hf)
    intro i j he
    have hh := congrArg (fun p => (F.project p).2) he
    rw [hn] at hh
    linarith [hfpos i,hfpos j]
  have hAmem : ∀ i, A i ∈ C.polarModel.extremePoints ℝ := by
    rintro (i | i)
    · exact hfmem i
    · exact C.polarModel_neg_extreme (hfmem i)
  have hAheight : ∀ i, (F.project (A i)).2 ≠ 0 := by
    rintro (i | i)
    · exact ne_of_gt (hfpos i)
    · change (F.project (-f i)).2 ≠ 0
      rw [hn]; exact neg_ne_zero.2 (ne_of_gt (hfpos i))
  obtain ⟨g,hgmem,hgclass,hgpos⟩ := S.four_rays hP hrange
  let B : Fin 2 × Fin 2 → E5 := fun i => g (F.order 3,i)
  have hBheight : ∀ i, (F.project (B i)).2 = 0 := by
    intro i
    rw [F.project_last]
    have hh := S.class_orthogonal (hgclass (F.order 3,i))
    rw [SegmentData.axis,inner_smul_right,hh,mul_zero]
  have hBnz : ∀ i, planar (B i) ≠ 0 := by
    intro i hz
    have hh := hgpos (F.order 3,i)
    change 0 < sign2 i.2 * ⟪normal2 (S.direction (F.order 3)),planar (B i)⟫ at hh
    rw [hz,inner_zero_right,mul_zero] at hh
    exact (lt_irrefl 0) hh
  have hBinj : Function.Injective B := by
    intro i j he
    have hsign : i.1 = j.1 := by
      obtain ⟨v,hv⟩ := C.surj (F.order 3)
      apply sign2_injective
      have hi := hgclass (F.order 3,i) v hv
      have hj := hgclass (F.order 3,j) v hv
      change C.value (B i) v = sign2 i.1 at hi
      change C.value (B j) v = sign2 j.1 at hj
      rw [← hi,he,hj]
    have hray : i.2 = j.2 := by
      apply sign2_eq_of_positive (hgpos (F.order 3,i))
      change 0 < sign2 j.2 * ⟪normal2 (S.direction (F.order 3)),planar (B i)⟫
      rw [he]
      exact hgpos (F.order 3,j)
    exact Prod.ext hsign hray
  let H := Sum.elim A B
  have hHinj : Function.Injective H := by
    apply sum_family_injective A B hAinj hBinj
    intro i j he
    apply hAheight i
    rw [he,hBheight]
  have hHmem : ∀ i, H i ∈ C.polarModel.extremePoints ℝ := by
    rintro (i | i)
    · exact hAmem i
    · exact hgmem (F.order 3,i)
  let K := Sum.elim centralVertex H
  have hKinj : Function.Injective K := by
    apply sum_family_injective centralVertex H centralVertex_injective hHinj
    intro i j he
    rcases j with j | j
    · apply hAheight j
      have hh := congrArg (fun p => (F.project p).2) he
      rw [project_last,centralVertex_planar,inner_zero_left] at hh
      exact hh.symm
    · apply hBnz j
      have hh := congrArg planar he
      rw [centralVertex_planar] at hh
      exact hh.symm
  have hKmem : ∀ i, K i ∈ C.polarModel.extremePoints ℝ := by
    rintro (i | i)
    · exact C.centralVertex_extreme i
    · exact hHmem i
  have hh := C.model_vertices_le_facets hP hrange K hKinj hKmem
  simpa [Fintype.card_sum,Fintype.card_prod] using hh

end TripleFrame
end Kalai5.Cube3
