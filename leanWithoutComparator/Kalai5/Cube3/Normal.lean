import Kalai5.Cube3.Config
import Kalai5.Endpoints.ThreePairNormals

/-!
# A putative three-pair counterexample gives four genuine planar fibres

This is a geometric normalization, not a finite row relaxation. The points
are actual vertex representatives; the fibres are in convex position, and
any extra full normal contradicts the already proved rank-four endpoint.
-/

namespace Kalai5.Cube3

open Set Module LemmaA FullPrism LemmaB LemmaB.Eight

local notation "⟪" x ", " y "⟫" => inner ℝ x y

lemma clsRep_first (j : Fin 4) : clsRep j 0 = 1 := by fin_cases j <;> rfl

lemma clsRep_injective : Function.Injective clsRep := by
  intro j k h
  fin_cases j <;> fin_cases k <;>
    simp_all [clsRep, funext_iff, Fin.forall_fin_succ] <;> norm_num at *

lemma clsRep_not_neg (j k : Fin 4) : clsRep j ≠ -clsRep k := by
  intro h
  have h0 := congrFun h 0
  simp only [Pi.neg_apply, clsRep_first] at h0
  norm_num at h0

variable {P : Set E5}

/-- The cube-type geometric model for every counterexample with three full pairs. -/
theorem IsCSPolytope5.cube3_normal (hP : IsCSPolytope5 P)
    (hv : fvec P 0 = 16) (hh : fvec P 4 ≤ 18)
    (hc8 : 6 ≤ cnt8 (facetRows P)) (hlt : (faces P).ncard < 243) :
    ∃ x : Fin 8 → E5, Function.Injective (FullPrism.pm16 x) ∧
      range (FullPrism.pm16 x) = P.extremePoints ℝ ∧
      ∃ C : Config x, ¬ C.ExtraPM := by
  classical
  obtain ⟨u, hu, hpm⟩ := hP.three_indep_full_normals hv hc8
  have hall := hP.all_cube_classes_of_faces_lt hv hh hlt hu hpm
  -- representatives
  obtain ⟨V, hV⟩ := hP.polytope
  set X := (extremePoints_finite V).toFinset with hXdef
  have hXcoe : (X : Set E5) = P.extremePoints ℝ := by rw [hXdef, Set.Finite.coe_toFinset, hV]
  have hXcard : X.card = 16 := by
    have h1 := fvec_zero_eq V
    rw [Set.ncard_eq_toFinset_card _ (extremePoints_finite V)] at h1
    rw [hV] at hv
    rw [hXdef, ← h1]
    exact hv
  have hXsymm : ∀ y ∈ X, -y ∈ X := by
    intro y hy
    rw [← Finset.mem_coe, hXcoe] at hy ⊢
    exact neg_mem_extremePoints hP.symm hy
  have hX0 : (0 : E5) ∉ X := by
    rw [← Finset.mem_coe, hXcoe]
    exact hP.zero_not_mem_extremePoints
  obtain ⟨x0, hx0inj, hx0range⟩ := exists_reps16 hXcard hXsymm hX0
  rw [hXcoe] at hx0range
  have hx0ext : ∀ v, x0 v ∈ P.extremePoints ℝ := fun v => by
    rw [← hx0range]; exact ⟨_, pm16_lo x0 v⟩
  set q : Fin 8 → (Fin 3 → ℝ) := fun v i => ⟪u i, x0 v⟫ with hq
  have hq0 : ∀ v, q v 0 = 1 ∨ q v 0 = -1 := fun v => hpm 0 _ (hx0ext v)
  have hqrep : ∀ v, q v = q v 0 • clsRep (cls4 (q v)) := fun v =>
    eq_smul_clsRep (hpm 0 _ (hx0ext v)) (hpm 1 _ (hx0ext v)) (hpm 2 _ (hx0ext v))
  set c : Fin 8 → Fin 4 := fun v => cls4 (q v) with hcdef
  set ε : Fin 8 → ℝ := fun v => q v 0 with hε
  have hε1 : ∀ v, ε v = 1 ∨ ε v = -1 := hq0
  set x : Fin 8 → E5 := fun v => ε v • x0 v with hx
  have hxrange : range (FullPrism.pm16 x) = P.extremePoints ℝ := by
    rw [← hx0range]
    exact A16.range_pm16_signed ε hε1 (Equiv.refl _)
  have hxinj : Function.Injective (FullPrism.pm16 x) :=
    A16.pm16_signed_injective hx0inj ε hε1 (Equiv.refl _)
  have hxpos : ∀ v (i : Fin 3), ⟪u i, x v⟫ = clsRep (c v) i := by
    intro v i
    have h := congrFun (hqrep v) i
    simp only [Pi.smul_apply, smul_eq_mul] at h
    simp only [hx, real_inner_smul_right, hcdef]
    change ε v * q v i = _
    rw [h, ← mul_assoc]
    rcases hε1 v with h1 | h1 <;> simp [hε] at h1 ⊢ <;> rw [h1] <;> norm_num
  have hsurj : Function.Surjective c := by
    intro j
    obtain ⟨y, hy, hp⟩ := hall j
    rw [← hxrange] at hy
    obtain ⟨v, rfl | rfl⟩ := mem_range_pm16.1 hy
    · have he : (fun i => ⟪u i, x v⟫) = clsRep (c v) := funext (hxpos v)
      rw [he] at hp
      rcases hp with hp | hp
      · exact ⟨v, clsRep_injective hp⟩
      · exact False.elim (clsRep_not_neg (c v) j hp)
    · have he : (fun i => ⟪u i, -x v⟫) = -clsRep (c v) := by
        funext i; simp only [inner_neg_right, hxpos, Pi.neg_apply]
      rw [he] at hp
      rcases hp with hp | hp
      · exact False.elim (clsRep_not_neg j (c v) hp.symm)
      · exact ⟨v, clsRep_injective (neg_injective hp)⟩
  obtain ⟨w, hw, hw0, hw1, hw2⟩ := Eight.exists_completion3 hu
  have hc : ∀ v, ⟪w 0, x v⟫ = clsRep (c v) 0 ∧
      ⟪w 1, x v⟫ = clsRep (c v) 1 ∧ ⟪w 2, x v⟫ = clsRep (c v) 2 :=
    fun v => ⟨by rw [hw0]; exact hxpos v 0, by rw [hw1]; exact hxpos v 1,
      by rw [hw2]; exact hxpos v 2⟩
  obtain ⟨C, hC⟩ := config_of_basis hP hxinj hxrange hw hc hsurj
  refine ⟨x, hxinj, hxrange, C, fun hE => ?_⟩
  obtain ⟨z, hzspan, hzpm⟩ := hC hE
  apply hzspan
  have he : (![w 0, w 1, w 2] : Fin 3 → E5) = u := by
    funext i
    fin_cases i
    · exact hw0
    · exact hw1
    · exact hw2
  rw [he]
  exact hP.full_normal_mem_span_three_of_faces_lt hv hh hlt hu hpm hzpm

end Kalai5.Cube3
