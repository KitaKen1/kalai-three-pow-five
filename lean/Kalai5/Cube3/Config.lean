import Kalai5.LemmaB.Eight.Normal

/-!
# Four planar fibres above the antipodal classes of a three-dimensional cube

The four class offsets obey a₀+a₃=a₁+a₂. Unlike the octahedral model, arbitrary
independent offsets are not allowed. This relation is explicit in every
realization and extra-normal hypothesis.
-/

namespace Kalai5.Cube3

open Set Module LemmaA FullPrism LemmaB LemmaB.Eight

local notation "⟪" x ", " y "⟫" => inner ℝ x y

noncomputable def fibre (c : Fin 8 → Fin 4) (k : Fin 8 → E 2) (j : Fin 4) : Finset (E 2) :=
  (Finset.univ.filter fun v => c v = j).image k

/-- Precisely the affine relation among the four normalized cube classes. -/
def Balanced (a : Fin 4 → ℝ) : Prop := a 0 + a 3 = a 1 + a 2

structure Config (x : Fin 8 → E5) where
  c : Fin 8 → Fin 4
  k : Fin 8 → E 2
  surj : Function.Surjective c
  inj : ∀ v w, c v = c w → k v = k w → v = w
  convpos : ∀ v, k v ∈ (convexHull ℝ (fibre c k (c v) : Set (E 2))).extremePoints ℝ
  real : ∀ (a : Fin 4 → ℝ), Balanced a → ∀ b : E 2,
    ∃ z : E5, ∀ v, ⟪z, x v⟫ = a (c v) + ⟪b, k v⟫
  faithful : ∀ (a : Fin 4 → ℝ), Balanced a → ∀ b : E 2,
    (∀ v, a (c v) + ⟪b, k v⟫ = 0) → b = 0

def Config.ExtraPM {x : Fin 8 → E5} (C : Config x) : Prop :=
  ∃ (a : Fin 4 → ℝ) (b : E 2), Balanced a ∧ b ≠ 0 ∧
    ∀ v, a (C.c v) + ⟪b, C.k v⟫ = 1 ∨ a (C.c v) + ⟪b, C.k v⟫ = -1

lemma solve_four (a : Fin 4 → ℝ) (ha : Balanced a) : ∃ l : Fin 3 → ℝ, ∀ j : Fin 4,
    l 0 * clsRep j 0 + l 1 * clsRep j 1 + l 2 * clsRep j 2 = a j := by
  refine ⟨![(a 1 + a 2) / 2, (a 0 - a 2) / 2, (a 0 - a 1) / 2], fun j => ?_⟩
  change a 0 + a 3 = a 1 + a 2 at ha
  fin_cases j <;> simp [clsRep] <;> linarith

variable {P : Set E5}

section basis

variable (hP : IsCSPolytope5 P) {x : Fin 8 → E5} (hinj : Function.Injective (FullPrism.pm16 x))
  (hrange : range (FullPrism.pm16 x) = P.extremePoints ℝ) {w : Fin 5 → E5} (hw : LinearIndependent ℝ w)
  {c : Fin 8 → Fin 4}
  (hc : ∀ v, ⟪w 0, x v⟫ = clsRep (c v) 0 ∧
    ⟪w 1, x v⟫ = clsRep (c v) 1 ∧ ⟪w 2, x v⟫ = clsRep (c v) 2)
  (hsurj : Function.Surjective c)
include hP hinj hrange hw hc hsurj

lemma basis_real (a : Fin 4 → ℝ) (ha : Balanced a) (b : E 2) :
    ∃ l : Fin 3 → ℝ, ∀ v, ⟪formOf w l b, x v⟫ = a (c v) + ⟪b, kOf w (x v)⟫ := by
  obtain ⟨l, hl⟩ := solve_four a ha
  refine ⟨l, fun v => ?_⟩
  rw [inner_formOf, (hc v).1, (hc v).2.1, (hc v).2.2, hl (c v)]

lemma basis_inj (v v' : Fin 8) (hcc : c v = c v') (hk : kOf w (x v) = kOf w (x v')) : v = v' := by
  have hx : x v = x v' := coordMapOf_injective hw (by
    ext i
    rw [coordMapOf_apply, coordMapOf_apply]
    fin_cases i
    · show ⟪w 0, x v⟫ = ⟪w 0, x v'⟫
      rw [(hc v).1, (hc v').1, hcc]
    · show ⟪w 1, x v⟫ = ⟪w 1, x v'⟫
      rw [(hc v).2.1, (hc v').2.1, hcc]
    · show ⟪w 2, x v⟫ = ⟪w 2, x v'⟫
      rw [(hc v).2.2, (hc v').2.2, hcc]
    · show ⟪w 3, x v⟫ = ⟪w 3, x v'⟫
      exact congrArg (fun k : E 2 => k 0) hk
    · show ⟪w 4, x v⟫ = ⟪w 4, x v'⟫
      exact congrArg (fun k : E 2 => k 1) hk)
  exact (A16.pm16_inj_iff.1 hinj).1 hx

lemma basis_faithful (a : Fin 4 → ℝ) (ha : Balanced a) (b : E 2)
    (hb : ∀ v, a (c v) + ⟪b, kOf w (x v)⟫ = 0) : b = 0 := by
  obtain ⟨l, hl⟩ := basis_real hP hinj hrange hw hc hsurj a ha b
  have hzero : formOf w l b = 0 := by
    apply hP.eq_zero_of_inner_vertices
    intro y hy
    rw [← hrange] at hy
    obtain ⟨v, rfl | rfl⟩ := mem_range_pm16.1 hy
    · rw [hl v, hb v]
    · rw [inner_neg_right, hl v, hb v, neg_zero]
  exact (formOf_eq_zero hw hzero).2

lemma basis_extra {a : Fin 4 → ℝ} (ha : Balanced a) {b : E 2} (hb : b ≠ 0)
    (hpm : ∀ v, a (c v) + ⟪b, kOf w (x v)⟫ = 1 ∨ a (c v) + ⟪b, kOf w (x v)⟫ = -1) :
    ∃ z : E5, z ∉ Submodule.span ℝ (range ![w 0, w 1, w 2]) ∧
      ∀ y ∈ P.extremePoints ℝ, ⟪z, y⟫ = 1 ∨ ⟪z, y⟫ = -1 := by
  obtain ⟨l, hl⟩ := basis_real hP hinj hrange hw hc hsurj a ha b
  refine ⟨formOf w l b, formOf_not_mem_span hw l hb, fun y hy => ?_⟩
  rw [← hrange] at hy
  obtain ⟨v, rfl | rfl⟩ := mem_range_pm16.1 hy
  · rw [hl v]; exact hpm v
  · rw [inner_neg_right, hl v]
    rcases hpm v with h | h
    · right; rw [h]
    · left; rw [h]; norm_num

lemma basis_convpos (v : Fin 8) :
    kOf w (x v) ∈ (convexHull ℝ (fibre c (fun v => kOf w (x v)) (c v) : Set (E 2))).extremePoints ℝ := by
  classical
  set e := LinearEquiv.ofInjectiveEndo (coordMapOf w) (coordMapOf_injective hw) with he
  set R := clsRep (c v) with hR
  let lin : E 2 →ₗ[ℝ] E5 :=
    { toFun := fun k => (WithLp.equiv 2 (Fin 5 → ℝ)).symm ![0, 0, 0, k 0, k 1]
      map_add' := fun k k' => by ext i; fin_cases i <;> simp
      map_smul' := fun r k => by ext i; fin_cases i <;> simp }
  set base : E5 := (WithLp.equiv 2 (Fin 5 → ℝ)).symm ![R 0, R 1, R 2, 0, 0] with hbase
  let L : E 2 →ᵃ[ℝ] E5 := AffineMap.const ℝ (E 2) (e.symm base) + (e.symm.toLinearMap.comp lin).toAffineMap
  have hL : ∀ k, L k = e.symm (base + lin k) := by
    intro k
    simp [L, map_add]
  have hLinj : Function.Injective L := by
    intro k k' h
    rw [hL, hL] at h
    have h' := e.symm.injective h
    ext i
    fin_cases i
    · have := congrArg (fun y : E5 => y 3) h'
      simpa [hbase, lin] using this
    · have := congrArg (fun y : E5 => y 4) h'
      simpa [hbase, lin] using this
  have hLx : ∀ v', c v' = c v → L (kOf w (x v')) = x v' := by
    intro v' hv'
    rw [hL]
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.coe_ofInjectiveEndo]
    ext i
    rw [coordMapOf_apply]
    fin_cases i
    · simp [hbase, lin, hR, (hc v').1, hv']
    · simp [hbase, lin, hR, (hc v').2.1, hv']
    · simp [hbase, lin, hR, (hc v').2.2, hv']
    · simp [hbase, lin, kOf_apply0]
    · simp [hbase, lin, kOf_apply1]
  have hLP : ∀ k ∈ convexHull ℝ (fibre c (fun v => kOf w (x v)) (c v) : Set (E 2)), L k ∈ P := by
    intro k hk
    have himg : L '' convexHull ℝ (fibre c (fun v => kOf w (x v)) (c v) : Set (E 2)) ⊆ P := by
      rw [AffineMap.image_convexHull]
      obtain ⟨V, hV⟩ := hP.polytope
      refine convexHull_min ?_ hP.convex
      rintro _ ⟨k', hk', rfl⟩
      simp only [fibre, Finset.coe_image, Finset.coe_filter, Set.mem_image, Set.mem_setOf_eq,
        Finset.mem_univ, true_and] at hk'
      obtain ⟨v', hv', rfl⟩ := hk'
      rw [hLx v' hv']
      have : x v' ∈ P.extremePoints ℝ := by rw [← hrange]; exact ⟨_, pm16_lo x v'⟩
      exact this.1
    exact himg ⟨k, hk, rfl⟩
  have hxv : x v ∈ P.extremePoints ℝ := by rw [← hrange]; exact ⟨_, pm16_lo x v⟩
  rw [mem_extremePoints]
  refine ⟨subset_convexHull ℝ _ (by simp only [fibre, Finset.coe_image, Finset.coe_filter]; exact ⟨v, by simp, rfl⟩), fun y1 hy1 y2 hy2 hseg => ?_⟩
  have hseg' : x v ∈ openSegment ℝ (L y1) (L y2) := by
    rw [← image_openSegment ℝ L y1 y2, ← hLx v rfl]
    exact ⟨_, hseg, rfl⟩
  obtain ⟨h1, h2⟩ := (mem_extremePoints.1 hxv).2 _ (hLP y1 hy1) _ (hLP y2 hy2) hseg'
  exact ⟨hLinj (h1.trans (hLx v rfl).symm), hLinj (h2.trans (hLx v rfl).symm)⟩

/-- Packaging the actual coordinates retains all geometric hypotheses. -/
theorem config_of_basis : ∃ C : Config x, C.ExtraPM → ∃ z : E5,
    z ∉ Submodule.span ℝ (range ![w 0, w 1, w 2]) ∧
      ∀ y ∈ P.extremePoints ℝ, ⟪z, y⟫ = 1 ∨ ⟪z, y⟫ = -1 := by
  refine ⟨⟨c, fun v => kOf w (x v), hsurj,
    fun v v' h1 h2 => basis_inj hP hinj hrange hw hc hsurj v v' h1 h2,
    fun v => basis_convpos hP hinj hrange hw hc hsurj v,
    fun a ha b => ?_, fun a ha b hb => basis_faithful hP hinj hrange hw hc hsurj a ha b hb⟩, ?_⟩
  · obtain ⟨l, hl⟩ := basis_real hP hinj hrange hw hc hsurj a ha b
    exact ⟨formOf w l b, hl⟩
  · rintro ⟨a, b, ha, hb, hpm⟩
    exact basis_extra hP hinj hrange hw hc hsurj ha hb hpm

end basis

end Kalai5.Cube3
