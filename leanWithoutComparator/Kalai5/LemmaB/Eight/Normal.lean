import Kalai5.LemmaB.Eight.Config
import Kalai5.LemmaA.Geom
import Kalai5.A16.ReduceSound
import Kalai5.Cube5.Geom
import Kalai5.Full.Normals

/-!
# Lemma B at sixteen vertices: the rank-three normal form

`config_of_basis`: representatives `x_v` of the vertex pairs, a basis `w₀, …, w₄` whose first three
members see every `x_v` in the class position `R_{c v}` (`R₀ = (1,1,1)`, `R₁ = (1,1,-1)`,
`R₂ = (1,-1,1)`), give a rank-three configuration with planar coordinates `k_v = (w₃, w₄)(x_v)`.
A fourth `±1`-functional of the configuration pulls back to a `±1`-functional of `P` outside the
span of `w₀, w₁, w₂` (to be handed to Lemma A).
-/

namespace Kalai5.LemmaB.Eight

open Set Module LemmaA FullPrism

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {P : Set E5}

lemma inner_E2 (b k : E 2) : ⟪b, k⟫ = b 0 * k 0 + b 1 * k 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- **Three independent vectors extend to a basis.** -/
lemma exists_completion3 {u : Fin 3 → E5} (hu : LinearIndependent ℝ u) :
    ∃ w : Fin 5 → E5, LinearIndependent ℝ w ∧ w 0 = u 0 ∧ w 1 = u 1 ∧ w 2 = u 2 := by
  obtain ⟨v4, hv4⟩ := exists_linearIndependent_snoc_of_lt_finrank hu
    (by rw [finrank_euclideanSpace_fin]; norm_num)
  obtain ⟨v5, hv5⟩ := exists_linearIndependent_snoc_of_lt_finrank hv4
    (by rw [finrank_euclideanSpace_fin]; norm_num)
  refine ⟨Fin.snoc (Fin.snoc u v4) v5, hv5, ?_, ?_, ?_⟩ <;> rfl

/-- The planar coordinates. -/
noncomputable def kOf (w : Fin 5 → E5) (y : E5) : E 2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![⟪w 3, y⟫, ⟪w 4, y⟫]

lemma kOf_apply0 (w : Fin 5 → E5) (y : E5) : kOf w y 0 = ⟪w 3, y⟫ := rfl
lemma kOf_apply1 (w : Fin 5 → E5) (y : E5) : kOf w y 1 = ⟪w 4, y⟫ := rfl

/-- The linear form with coordinates `l` on `w₀, w₁, w₂` and `b` on `w₃, w₄`. -/
noncomputable def formOf (w : Fin 5 → E5) (l : Fin 3 → ℝ) (b : E 2) : E5 :=
  l 0 • w 0 + l 1 • w 1 + l 2 • w 2 + b 0 • w 3 + b 1 • w 4

lemma inner_formOf (w : Fin 5 → E5) (l : Fin 3 → ℝ) (b : E 2) (y : E5) :
    ⟪formOf w l b, y⟫ = l 0 * ⟪w 0, y⟫ + l 1 * ⟪w 1, y⟫ + l 2 * ⟪w 2, y⟫ + ⟪b, kOf w y⟫ := by
  simp only [formOf, inner_add_left, real_inner_smul_left, inner_E2, kOf_apply0, kOf_apply1]
  ring

/-- A form vanishing identically has zero coordinates. -/
lemma formOf_eq_zero {w : Fin 5 → E5} (hw : LinearIndependent ℝ w) {l : Fin 3 → ℝ} {b : E 2}
    (h : formOf w l b = 0) : l = 0 ∧ b = 0 := by
  have h' := (Fintype.linearIndependent_iff.1 hw) ![l 0, l 1, l 2, b 0, b 1] (by
    simp only [Fin.sum_univ_five, formOf] at h ⊢
    simpa using h)
  refine ⟨funext fun i => ?_, ?_⟩
  · fin_cases i
    · exact h' 0
    · exact h' 1
    · exact h' 2
  · ext i
    fin_cases i
    · exact h' 3
    · exact h' 4

/-- A form with `b ≠ 0` is outside the span of `w₀, w₁, w₂`. -/
lemma formOf_not_mem_span {w : Fin 5 → E5} (hw : LinearIndependent ℝ w) (l : Fin 3 → ℝ) {b : E 2}
    (hb : b ≠ 0) : formOf w l b ∉ Submodule.span ℝ (range ![w 0, w 1, w 2]) := by
  intro hmem
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  simp only [Fin.sum_univ_three] at hm
  simp at hm
  have h0 : formOf w (fun i => l i - m i) b = 0 := by
    have : formOf w (fun i => l i - m i) b = formOf w l b - (m 0 • w 0 + m 1 • w 1 + m 2 • w 2) := by
      simp only [formOf, sub_smul]; abel
    rw [this, hm, sub_self]
  exact hb (formOf_eq_zero hw h0).2

section basis

variable (hP : IsCSPolytope5 P) {x : Fin 8 → E5} (hinj : Function.Injective (FullPrism.pm16 x))
  (hrange : range (FullPrism.pm16 x) = P.extremePoints ℝ) {w : Fin 5 → E5} (hw : LinearIndependent ℝ w)
  {c : Fin 8 → Fin 3}
  (hc : ∀ v, ⟪w 0, x v⟫ = clsRep (Fin.castSucc (c v)) 0 ∧
    ⟪w 1, x v⟫ = clsRep (Fin.castSucc (c v)) 1 ∧ ⟪w 2, x v⟫ = clsRep (Fin.castSucc (c v)) 2)
  (hsurj : Function.Surjective c)
include hP hinj hrange hw hc hsurj

lemma basis_real (a : Fin 3 → ℝ) (b : E 2) :
    ∃ l : Fin 3 → ℝ, ∀ v, ⟪formOf w l b, x v⟫ = a (c v) + ⟪b, kOf w (x v)⟫ := by
  obtain ⟨l, hl⟩ := solve_three a
  refine ⟨l, fun v => ?_⟩
  rw [inner_formOf, (hc v).1, (hc v).2.1, (hc v).2.2, ← hl (c v)]

/-- Coordinates determine points. -/
lemma basis_eq {y y' : E5} (h : ∀ i, ⟪w i, y⟫ = ⟪w i, y'⟫) : y = y' :=
  coordMapOf_injective hw (by ext i; exact h i)

lemma basis_inj (v v' : Fin 8) (hcc : c v = c v') (hk : kOf w (x v) = kOf w (x v')) : v = v' := by
  have hx : x v = x v' := basis_eq hP hinj hrange hw hc hsurj fun i => by
    fin_cases i
    · show ⟪w 0, x v⟫ = ⟪w 0, x v'⟫; rw [(hc v).1, (hc v').1, hcc]
    · show ⟪w 1, x v⟫ = ⟪w 1, x v'⟫; rw [(hc v).2.1, (hc v').2.1, hcc]
    · show ⟪w 2, x v⟫ = ⟪w 2, x v'⟫; rw [(hc v).2.2, (hc v').2.2, hcc]
    · show ⟪w 3, x v⟫ = ⟪w 3, x v'⟫; exact congrArg (fun k : E 2 => k 0) hk
    · show ⟪w 4, x v⟫ = ⟪w 4, x v'⟫; exact congrArg (fun k : E 2 => k 1) hk
  exact (A16.pm16_inj_iff.1 hinj).1 hx

/-- **Full dimension**: the fibre differences span the plane. -/
lemma basis_span (b : E 2)
    (hb : ∀ v v', c v = c v' → ⟪b, kOf w (x v)⟫ = ⟪b, kOf w (x v')⟫) : b = 0 := by
  classical
  obtain ⟨rep, hrep⟩ : ∃ rep : Fin 3 → Fin 8, ∀ j, c (rep j) = j :=
    ⟨fun j => (hsurj j).choose, fun j => (hsurj j).choose_spec⟩
  obtain ⟨l, hl⟩ := basis_real hP hinj hrange hw hc hsurj (fun j => -⟪b, kOf w (x (rep j))⟫) b
  have hz : ∀ v, ⟪formOf w l b, x v⟫ = 0 := by
    intro v
    rw [hl v, hb v (rep (c v)) (hrep (c v)).symm]
    ring
  have hzero : formOf w l b = 0 := by
    apply hP.eq_zero_of_inner_vertices
    intro y hy
    rw [← hrange] at hy
    obtain ⟨v, rfl | rfl⟩ := mem_range_pm16.1 hy
    · exact hz v
    · rw [inner_neg_right, hz v, neg_zero]
  exact (formOf_eq_zero hw hzero).2

/-- **A fourth `±1`-functional** of the configuration pulls back to `P`. -/
lemma basis_extra {a : Fin 3 → ℝ} {b : E 2} (hb : b ≠ 0)
    (hpm : ∀ v, a (c v) + ⟪b, kOf w (x v)⟫ = 1 ∨ a (c v) + ⟪b, kOf w (x v)⟫ = -1) :
    ∃ z : E5, z ∉ Submodule.span ℝ (range ![w 0, w 1, w 2]) ∧
      ∀ y ∈ P.extremePoints ℝ, ⟪z, y⟫ = 1 ∨ ⟪z, y⟫ = -1 := by
  obtain ⟨l, hl⟩ := basis_real hP hinj hrange hw hc hsurj a b
  refine ⟨formOf w l b, formOf_not_mem_span hw l hb, fun y hy => ?_⟩
  rw [← hrange] at hy
  obtain ⟨v, rfl | rfl⟩ := mem_range_pm16.1 hy
  · rw [hl v]; exact hpm v
  · rw [inner_neg_right, hl v]
    rcases hpm v with h | h
    · right; rw [h]
    · left; rw [h]; norm_num

/-- **Convex position**: each `k_v` is a vertex of its fibre polygon (lift the fibre plane back
into `ℝ⁵` affinely and use that `x_v` is a vertex of `P`). -/
lemma basis_convpos (v : Fin 8) :
    kOf w (x v) ∈ (convexHull ℝ (fibre c (fun v => kOf w (x v)) (c v) : Set (E 2))).extremePoints ℝ := by
  classical
  set e := LinearEquiv.ofInjectiveEndo (coordMapOf w) (coordMapOf_injective hw) with he
  set R := clsRep (Fin.castSucc (c v)) with hR
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

/-- **The configuration** (packaging the lemmas above). -/
theorem config_of_basis : ∃ C : Config x, C.ExtraPM → ∃ z : E5,
    z ∉ Submodule.span ℝ (range ![w 0, w 1, w 2]) ∧
      ∀ y ∈ P.extremePoints ℝ, ⟪z, y⟫ = 1 ∨ ⟪z, y⟫ = -1 := by
  refine ⟨⟨c, fun v => kOf w (x v), fun a b => ?_, hsurj,
    fun v v' h1 h2 => basis_inj hP hinj hrange hw hc hsurj v v' h1 h2,
    fun v => basis_convpos hP hinj hrange hw hc hsurj v,
    fun b hb => basis_span hP hinj hrange hw hc hsurj b hb⟩, ?_⟩
  · obtain ⟨l, hl⟩ := basis_real hP hinj hrange hw hc hsurj a b
    exact ⟨formOf w l b, hl⟩
  · rintro ⟨a, b, hb, hpm⟩
    exact basis_extra hP hinj hrange hw hc hsurj hb hpm

end basis

/-! ### From the polytope -/

/-- Sign changes moving class `m` to class `3`. -/
def flipS : Fin 4 → (Fin 3 → ℝ)
  | 0 => ![1, -1, -1]
  | 1 => ![1, -1, 1]
  | 2 => ![1, 1, -1]
  | 3 => ![1, 1, 1]

lemma flipS_rep (m : Fin 4) (i : Fin 3) : flipS m i * clsRep 3 i = clsRep m i := by
  fin_cases m <;> fin_cases i <;> simp [flipS, clsRep]

lemma flipS_sq (m : Fin 4) (i : Fin 3) : flipS m i * flipS m i = 1 := by
  fin_cases m <;> fin_cases i <;> simp [flipS]

lemma flipS_ne (m : Fin 4) (i : Fin 3) : flipS m i ≠ 0 := by
  intro h; have := flipS_sq m i; rw [h, zero_mul] at this; norm_num at this

/-- Normals to two of the three classes `R₀, R₁, R₂`. -/
def crossA : Fin 3 → (Fin 3 → ℝ)
  | 0 => ![0, 1, 1]
  | 1 => ![1, 0, -1]
  | 2 => ![-1, 1, 0]

lemma crossA_rep (j k : Fin 3) (hjk : k ≠ j) :
    crossA j 0 * clsRep (Fin.castSucc k) 0 + crossA j 1 * clsRep (Fin.castSucc k) 1 +
      crossA j 2 * clsRep (Fin.castSucc k) 2 = 0 := by
  fin_cases j <;> fin_cases k <;> simp_all [crossA, clsRep] <;> norm_num

lemma crossA_ne (j : Fin 3) : crossA j ≠ 0 := by
  intro h
  fin_cases j
  · have := congrFun h 1; simp [crossA] at this
  · have := congrFun h 0; simp [crossA] at this
  · have := congrFun h 1; simp [crossA] at this

/-- **The rank-three normal form.** -/
theorem IsCSPolytope5.rank3_normal (hP : IsCSPolytope5 P) (h16 : fvec P 0 = 16)
    {u : Fin 3 → E5} (hu : LinearIndependent ℝ u)
    (hpm : ∀ i, ∀ y ∈ P.extremePoints ℝ, ⟪u i, y⟫ = 1 ∨ ⟪u i, y⟫ = -1) {m : Fin 4}
    (hmiss : ∀ y ∈ P.extremePoints ℝ,
      (fun i => ⟪u i, y⟫) ≠ clsRep m ∧ (fun i => ⟪u i, y⟫) ≠ -clsRep m) :
    ∃ x : Fin 8 → E5, Function.Injective (FullPrism.pm16 x) ∧ range (FullPrism.pm16 x) = P.extremePoints ℝ ∧
      ∃ C : Config x, C.ExtraPM → ∃ u4 : Fin 4 → E5, LinearIndependent ℝ u4 ∧
        ∀ i, ∀ y ∈ P.extremePoints ℝ, ⟪u4 i, y⟫ = 1 ∨ ⟪u4 i, y⟫ = -1 := by
  classical
  -- move the missing class to `3`
  set u' : Fin 3 → E5 := fun i => flipS m i • u i with hu'
  have hu'li : LinearIndependent ℝ u' := by
    rw [hu']
    exact hu.units_smul (fun i => Units.mk0 (flipS m i) (flipS_ne m i))
  have hval : ∀ i y, ⟪u' i, y⟫ = flipS m i * ⟪u i, y⟫ := fun i y => by
    simp [hu', real_inner_smul_left]
  have hpm' : ∀ i, ∀ y ∈ P.extremePoints ℝ, ⟪u' i, y⟫ = 1 ∨ ⟪u' i, y⟫ = -1 := by
    intro i y hy
    rw [hval]
    have h := flipS_sq m i
    rcases hpm i y hy with h1 | h1 <;> rw [h1]
    · fin_cases m <;> fin_cases i <;> simp [flipS]
    · fin_cases m <;> fin_cases i <;> simp [flipS]
  have hmiss' : ∀ y ∈ P.extremePoints ℝ,
      (fun i => ⟪u' i, y⟫) ≠ clsRep 3 ∧ (fun i => ⟪u' i, y⟫) ≠ -clsRep 3 := by
    intro y hy
    refine ⟨fun h => (hmiss y hy).1 (funext fun i => ?_), fun h => (hmiss y hy).2 (funext fun i => ?_)⟩
    · have := congrFun h i
      rw [hval] at this
      calc ⟪u i, y⟫ = flipS m i * (flipS m i * ⟪u i, y⟫) := by rw [← mul_assoc, flipS_sq, one_mul]
        _ = clsRep m i := by rw [this, flipS_rep]
    · have := congrFun h i
      rw [hval] at this
      calc ⟪u i, y⟫ = flipS m i * (flipS m i * ⟪u i, y⟫) := by rw [← mul_assoc, flipS_sq, one_mul]
        _ = (-clsRep m) i := by rw [this, Pi.neg_apply, Pi.neg_apply, mul_neg, flipS_rep]
  -- representatives
  obtain ⟨V, hV⟩ := hP.polytope
  set X := (extremePoints_finite V).toFinset with hXdef
  have hXcoe : (X : Set E5) = P.extremePoints ℝ := by rw [hXdef, Set.Finite.coe_toFinset, hV]
  have hXcard : X.card = 16 := by
    have h1 := fvec_zero_eq V
    rw [Set.ncard_eq_toFinset_card _ (extremePoints_finite V)] at h1
    rw [hV] at h16
    rw [hXdef, ← h1]
    exact h16
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
  -- positions, signs and classes
  set q : Fin 8 → (Fin 3 → ℝ) := fun v i => ⟪u' i, x0 v⟫ with hq
  have hq0 : ∀ v, q v 0 = 1 ∨ q v 0 = -1 := fun v => hpm' 0 _ (hx0ext v)
  have hqrep : ∀ v, q v = q v 0 • clsRep (cls4 (q v)) := fun v =>
    eq_smul_clsRep (hpm' 0 _ (hx0ext v)) (hpm' 1 _ (hx0ext v)) (hpm' 2 _ (hx0ext v))
  have hcls3 : ∀ v, (cls4 (q v)).val < 3 := by
    intro v
    by_contra hge
    have h3 : cls4 (q v) = 3 := Fin.ext (by have := (cls4 (q v)).2; omega)
    have h := hqrep v
    rw [h3] at h
    rcases hq0 v with h1 | h1
    · rw [h1, one_smul] at h; exact (hmiss' _ (hx0ext v)).1 h
    · rw [h1, neg_one_smul] at h; exact (hmiss' _ (hx0ext v)).2 h
  set c : Fin 8 → Fin 3 := fun v => ⟨(cls4 (q v)).val, hcls3 v⟩ with hcdef
  have hcs : ∀ v, Fin.castSucc (c v) = cls4 (q v) := fun v => Fin.ext rfl
  set ε : Fin 8 → ℝ := fun v => q v 0 with hε
  have hε1 : ∀ v, ε v = 1 ∨ ε v = -1 := hq0
  set x : Fin 8 → E5 := fun v => ε v • x0 v with hx
  have hxrange : range (FullPrism.pm16 x) = P.extremePoints ℝ := by
    rw [← hx0range]
    exact A16.range_pm16_signed ε hε1 (Equiv.refl _)
  have hxinj : Function.Injective (FullPrism.pm16 x) := A16.pm16_signed_injective hx0inj ε hε1 (Equiv.refl _)
  have hxpos : ∀ v (i : Fin 3), ⟪u' i, x v⟫ = clsRep (Fin.castSucc (c v)) i := by
    intro v i
    have h := congrFun (hqrep v) i
    simp only [Pi.smul_apply, smul_eq_mul] at h
    simp only [hx, real_inner_smul_right, hcs]
    change ε v * q v i = _
    rw [h, ← mul_assoc]
    rcases hε1 v with h1 | h1 <;> simp [hε] at h1 ⊢ <;> rw [h1] <;> norm_num
  -- the basis
  obtain ⟨w, hw, hw0, hw1, hw2⟩ := exists_completion3 hu'li
  have hc : ∀ v, ⟪w 0, x v⟫ = clsRep (Fin.castSucc (c v)) 0 ∧
      ⟪w 1, x v⟫ = clsRep (Fin.castSucc (c v)) 1 ∧ ⟪w 2, x v⟫ = clsRep (Fin.castSucc (c v)) 2 :=
    fun v => ⟨by rw [hw0]; exact hxpos v 0, by rw [hw1]; exact hxpos v 1,
      by rw [hw2]; exact hxpos v 2⟩
  -- every class occurs (else a nonzero combination of `w₀, w₁, w₂` kills every vertex)
  have hsurj : Function.Surjective c := by
    intro j
    by_contra hno
    push_neg at hno
    have hz : ∀ v, ⟪crossA j 0 • w 0 + crossA j 1 • w 1 + crossA j 2 • w 2, x v⟫ = 0 := by
      intro v
      simp only [inner_add_left, real_inner_smul_left, (hc v).1, (hc v).2.1, (hc v).2.2]
      exact crossA_rep j (c v) (hno v)
    have hzero : crossA j 0 • w 0 + crossA j 1 • w 1 + crossA j 2 • w 2 = 0 := by
      apply hP.eq_zero_of_inner_vertices
      intro y hy
      rw [← hxrange] at hy
      obtain ⟨v, rfl | rfl⟩ := mem_range_pm16.1 hy
      · exact hz v
      · rw [inner_neg_right, hz v, neg_zero]
    have h := formOf_eq_zero hw (l := crossA j) (b := 0) (by
      simp only [formOf]
      rw [← hzero]
      simp)
    exact crossA_ne j h.1
  obtain ⟨C, hC⟩ := config_of_basis hP hxinj hxrange hw hc hsurj
  refine ⟨x, hxinj, hxrange, C, fun hE => ?_⟩
  obtain ⟨z, hzspan, hzpm⟩ := hC hE
  have hspan : Submodule.span ℝ (range ![w 0, w 1, w 2]) = Submodule.span ℝ (range u') := by
    congr 1
    have : (![w 0, w 1, w 2] : Fin 3 → E5) = u' := by
      funext i; fin_cases i
      · exact hw0
      · exact hw1
      · exact hw2
    rw [this]
  refine ⟨Fin.snoc u' z, (linearIndependent_fin_snoc).2 ⟨hu'li, by rw [← hspan]; exact hzspan⟩,
    fun i y hy => ?_⟩
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [Fin.snoc_last]; exact hzpm y hy
  · simp only [Fin.snoc_castSucc]; exact hpm' i y hy

end Kalai5.LemmaB.Eight
