import Kalai5.Full.Basic
import Kalai5.Pyramid.Parity

/-!
# Coordinates from linear functionals

* `coordMapOf w`: `x ↦ (⟪w i, x⟫)_i`, a linear map `E 5 → E 5`; injective when the five vectors
  `w i` are linearly independent (`coordMapOf_injective`), so face numbers are preserved.
* `exists_completion`: four linearly independent vectors extend to a basis.
* `not_three_on_line`: three distinct extreme points of a convex set cannot agree in all
  coordinates but one.
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- `x ↦ (⟪w i, x⟫)_i`. -/
noncomputable def coordMapOf (w : Fin 5 → E5) : E5 →ₗ[ℝ] E5 where
  toFun x := (WithLp.equiv 2 (Fin 5 → ℝ)).symm fun i => ⟪w i, x⟫
  map_add' x y := by ext i; simp [inner_add_right]
  map_smul' r x := by ext i; simp [real_inner_smul_right]

lemma coordMapOf_apply (w : Fin 5 → E5) (x : E5) (i : Fin 5) : coordMapOf w x i = ⟪w i, x⟫ := rfl

lemma coordMapOf_injective {w : Fin 5 → E5} (hw : LinearIndependent ℝ w) :
    Function.Injective (coordMapOf w) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have h0 : ∀ i, ⟪w i, x⟫ = 0 := fun i => by
    have := congrArg (fun y : E5 => y i) (LinearMap.mem_ker.1 hx)
    simpa [coordMapOf_apply] using this
  have hspan : Submodule.span ℝ (Set.range w) = ⊤ :=
    hw.span_eq_top_of_card_eq_finrank (by simp [finrank_euclideanSpace_fin])
  have hx : ∀ v ∈ Submodule.span ℝ (Set.range w), ⟪v, x⟫ = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h0 i
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul r a _ ha => rw [real_inner_smul_left, ha, mul_zero]
  exact inner_self_eq_zero.1 (hx x (by rw [hspan]; exact Submodule.mem_top))

/-- **Four linearly independent vectors extend to a basis.** -/
lemma exists_completion {u : Fin 4 → E5} (hu : LinearIndependent ℝ u) :
    ∃ w : Fin 5 → E5, LinearIndependent ℝ w ∧ ∀ i : Fin 4, w i.castSucc = u i := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_snoc_of_lt_finrank hu
    (by rw [finrank_euclideanSpace_fin]; norm_num)
  exact ⟨Fin.snoc u v, hv, fun i => by simp⟩

/-- **No three extreme points on a coordinate line**: if three distinct points of `K` agree in
every coordinate except `j`, one of them is not extreme. -/
lemma not_three_on_line {K : Set E5} {x y z : E5} (hx : x ∈ K.extremePoints ℝ)
    (hy : y ∈ K.extremePoints ℝ) (hz : z ∈ K.extremePoints ℝ) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (j : Fin 5) (hxy' : ∀ i ≠ j, x i = y i) (hxz' : ∀ i ≠ j, x i = z i) : False := by
  -- order the three `j`-th coordinates; the middle point is a convex combination
  have hne : ∀ a b : E5, (∀ i ≠ j, a i = b i) → a ≠ b → a j ≠ b j := by
    intro a b h hab hj
    apply hab; ext i
    by_cases hi : i = j
    · subst hi; exact hj
    · exact h i hi
  have key : ∀ a b c : E5, a ∈ K → c ∈ K → b ∈ K.extremePoints ℝ → (∀ i ≠ j, a i = b i) →
      (∀ i ≠ j, a i = c i) → a j < b j → b j < c j → False := by
    intro a b c ha hc hb hab hac h1 h2
    set t := (b j - a j) / (c j - a j)
    have hpos : 0 < c j - a j := by linarith
    have ht0 : 0 < t := div_pos (by linarith) hpos
    have ht1 : t < 1 := (div_lt_one hpos).2 (by linarith)
    have hb_eq : b = (1 - t) • a + t • c := by
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      by_cases hi : i = j
      · subst hi
        simp only [t]; field_simp; ring
      · rw [← hab i hi, ← hac i hi]; ring
    have hseg : b ∈ openSegment ℝ a c := ⟨1 - t, t, by linarith, ht0, by ring, hb_eq.symm⟩
    have hmem := hb.2 ha hc hseg
    have : a j = b j := by rw [hmem]
    linarith
  have hxyj := hne x y hxy' hxy
  have hxzj := hne x z hxz' hxz
  have hyz' : ∀ i ≠ j, y i = z i := fun i hi => (hxy' i hi).symm.trans (hxz' i hi)
  have hyzj := hne y z hyz' hyz
  have sym : ∀ {a b : E5}, (∀ i ≠ j, a i = b i) → ∀ i ≠ j, b i = a i := fun h i hi => (h i hi).symm
  rcases lt_or_gt_of_ne hxyj with h1 | h1 <;> rcases lt_or_gt_of_ne hxzj with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyzj with h3 | h3
  · exact key x y z hx.1 hz.1 hy hxy' hxz' h1 h3
  · exact key x z y hx.1 hy.1 hz hxz' hxy' h2 h3
  · linarith
  · exact key z x y hz.1 hy.1 hx (sym hxz') (sym hyz') h2 h1
  · exact key y x z hy.1 hz.1 hx (sym hxy') hyz' h1 h2
  · linarith
  · exact key y z x hy.1 hx.1 hz hyz' (sym hxy') h3 h2
  · exact key z y x hz.1 hx.1 hy (sym hyz') (sym hxz') h3 h1

end Kalai5
