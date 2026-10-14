import Kalai5.Cube3.AuxGeometry

/-!
# Three extreme points in a full planar section

Compactness and Krein-Milman suffice. No vertex enumeration or finite
halfspace-to-polytope conversion for the section is required.
-/

namespace Kalai5.Cube3

open Set

/-- A compact convex planar set with interior has three distinct extreme points. -/
theorem compact_planar_three {S : Set (E 2)} (hcomp : IsCompact S) (hconv : Convex ℝ S)
    (hint : (interior S).Nonempty) :
    ∃ f : Fin 3 → E 2, Function.Injective f ∧ ∀ i, f i ∈ S.extremePoints ℝ := by
  classical
  have hnot : ∀ T : Finset (E 2), T.card ≤ 2 → ¬ S.extremePoints ℝ ⊆ (T : Set (E 2)) := by
    intro T hcard hsub
    have hST : S ⊆ convexHull ℝ (T : Set (E 2)) := by
      rw [← closure_convexHull_extremePoints hcomp hconv]
      exact closure_minimal (convexHull_mono hsub) (T.finite_toSet.isClosed_convexHull ℝ)
    have hintT := hint.mono (interior_mono hST)
    have hdim := dim_eq_of_interior (convex_convexHull ℝ (T : Set (E 2))) hintT
    have hT : T.Nonempty := by
      by_contra h
      have he := Finset.not_nonempty_iff_eq_empty.1 h
      simpa [he] using hintT
    have hlo := dim_add_one_le_ncard_extremePoints T hT
    have hhi := Set.ncard_le_ncard
      (extremePoints_convexHull_subset (𝕜 := ℝ) (A := (T : Set (E 2)))) T.finite_toSet
    rw [hdim] at hlo
    rw [Set.ncard_coe_finset] at hhi
    omega
  obtain ⟨a,ha⟩ := hcomp.extremePoints_nonempty (hint.mono interior_subset)
  obtain ⟨b,hb,hba⟩ : ∃ b ∈ S.extremePoints ℝ, b ≠ a := by
    by_contra h
    push_neg at h
    exact hnot {a} (by simp) (fun b hb => by simpa using h b hb)
  obtain ⟨c,hc,hca,hcb⟩ : ∃ c ∈ S.extremePoints ℝ, c ≠ a ∧ c ≠ b := by
    by_contra h
    push_neg at h
    apply hnot {a,b} (by
      have hcard := Finset.card_insert_le a ({b} : Finset (E 2))
      simpa using hcard)
    intro c hc
    by_cases hca : c = a
    · simp [hca]
    · simp [h c hc hca]
  refine ⟨![a,b,c], ?_, ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i; fin_cases i <;> assumption

noncomputable def heightPlane (s : ℝ) : E 2 →ᵃ[ℝ] E 3 :=
  let L : E 2 →ₗ[ℝ] E 3 :=
    { toFun := fun b => (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0,b 0,b 1]
      map_add' := by intro b c; ext i; fin_cases i <;> simp
      map_smul' := by intro t b; ext i; fin_cases i <;> simp }
  AffineMap.const ℝ (E 2) ((WithLp.equiv 2 (Fin 3 → ℝ)).symm ![s,0,0]) + L.toAffineMap

noncomputable def planeTail : E 3 →ₗ[ℝ] E 2 where
  toFun y := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![y 1,y 2]
  map_add' := by intro y z; ext i; fin_cases i <;> simp
  map_smul' := by intro t y; ext i; fin_cases i <;> simp

lemma heightPlane_zero (s : ℝ) (b : E 2) : heightPlane s b 0 = s := by simp [heightPlane]

lemma planeTail_heightPlane (s : ℝ) (b : E 2) : planeTail (heightPlane s b) = b := by
  ext i; fin_cases i <;> simp [heightPlane,planeTail]

lemma heightPlane_tail {s : ℝ} {y : E 3} (hy : y 0 = s) : heightPlane s (planeTail y) = y := by
  ext i; fin_cases i <;> simp [heightPlane,planeTail,hy]

lemma heightPlane_injective (s : ℝ) : Function.Injective (heightPlane s) := by
  intro b c h
  simpa only [planeTail_heightPlane] using congrArg planeTail h

lemma heightPlane_image (D : Set (E 3)) (s : ℝ) :
    heightPlane s '' (heightPlane s ⁻¹' D) = D ∩ {y | y 0 = s} := by
  ext y
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact ⟨hb,heightPlane_zero s b⟩
  · rintro ⟨hy,hs⟩
    exact ⟨planeTail y,by change heightPlane s (planeTail y) ∈ D; rwa [heightPlane_tail hs],
      heightPlane_tail hs⟩

lemma planeTail_image (D : Set (E 3)) (s : ℝ) :
    planeTail '' (D ∩ {y | y 0 = s}) = heightPlane s ⁻¹' D := by
  ext b
  constructor
  · rintro ⟨y,⟨hy,hs⟩,rfl⟩
    change heightPlane s (planeTail y) ∈ D
    rwa [heightPlane_tail hs]
  · intro hb
    exact ⟨heightPlane s b,⟨hb,heightPlane_zero s b⟩,planeTail_heightPlane s b⟩

/-- Three section vertices, obtained directly from compact planar convexity. -/
theorem compact_height_section_three {D : Set (E 3)} (hD : IsCompact D) (hc : Convex ℝ D)
    (s : ℝ) (hint : ∃ z ∈ interior D, z 0 = s) :
    ∃ f : Fin 3 → E 3, Function.Injective f ∧
      ∀ i, f i ∈ (D ∩ {y | y 0 = s}).extremePoints ℝ := by
  have hcomp : IsCompact (heightPlane s ⁻¹' D) := by
    rw [← planeTail_image]
    apply (hD.inter_right (isClosed_eq (by fun_prop) continuous_const)).image
    exact planeTail.continuous_of_finiteDimensional
  have hconv : Convex ℝ (heightPlane s ⁻¹' D) := hc.affine_preimage _
  have hfull : (interior (heightPlane s ⁻¹' D)).Nonempty := by
    obtain ⟨z,hz,hs⟩ := hint
    refine ⟨planeTail z,preimage_interior_subset_interior_preimage
      (heightPlane s).continuous_of_finiteDimensional ?_⟩
    change heightPlane s (planeTail z) ∈ interior D
    rwa [heightPlane_tail hs]
  obtain ⟨f,hf,hext⟩ := compact_planar_three hcomp hconv hfull
  refine ⟨fun i => heightPlane s (f i), ?_, ?_⟩
  · intro i j h; exact hf (heightPlane_injective s h)
  · intro i
    rw [← heightPlane_image]
    exact extreme_affine_image (heightPlane s) (heightPlane_injective s) (hext i)

/-- A tall point gives an interior point of the height-one section by scaling. -/
lemma height_one_interior {D : Set (E 3)} (hc : Convex ℝ D)
    (h0 : (0 : E 3) ∈ interior D) {y : E 3} (hy : y ∈ D) (ht : 3 ≤ y 0) :
    ∃ z ∈ interior D, z 0 = 1 := by
  have hpos : 0 < y 0 := by linarith
  have hi : 0 < (y 0)⁻¹ := inv_pos.2 hpos
  have hi1 : (y 0)⁻¹ < 1 := (inv_lt_one₀ hpos).2 (by linarith)
  have h := hc.combo_interior_self_mem_interior h0 hy
    (by linarith : 0 < 1 - (y 0)⁻¹) hi.le (by ring : 1 - (y 0)⁻¹ + (y 0)⁻¹ = 1)
  refine ⟨(y 0)⁻¹ • y,by simpa using h,?_⟩
  simp [hpos.ne']

/-- The height-three section is nonempty even when three is the extreme height. -/
lemma height_three_nonempty {D : Set (E 3)} (hc : Convex ℝ D)
    (h0 : (0 : E 3) ∈ D) {y : E 3} (hy : y ∈ D) (ht : 3 ≤ y 0) :
    (D ∩ {z | z 0 = 3}).Nonempty := by
  have hpos : 0 < y 0 := by linarith
  have hle : 3 / y 0 ≤ 1 := (div_le_one hpos).2 ht
  have h := hc h0 hy (by linarith : 0 ≤ 1 - 3 / y 0)
    (by positivity : 0 ≤ 3 / y 0) (by ring : 1 - 3 / y 0 + 3 / y 0 = 1)
  refine ⟨(3 / y 0) • y,by simpa using h,?_⟩
  simp [hpos.ne']

end Kalai5.Cube3
