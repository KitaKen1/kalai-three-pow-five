import Kalai5.Rigidity.Step

/-!
# The fan triangulation of a convex polygon is rigid in its plane

For a polygon `R = conv V` (`V` in convex position, `dim R = 2`) and a vertex `a`, the edges of
`R` together with the bars from `a` to all vertices brace `V` (`braces_fan`).

Proof (no cyclic order of the polygon is needed).  Slice `R` at `a`; the slice points `e x` lie on
a line with direction `d`, and `s x = ⟪d, e x⟫` orders `V \ {a}` (injectively).  For a fixed `x`,
the linear form `ψ v = ⟪c, x - a⟫ ⟪d, v⟫ - ⟪d, x - a⟫ ⟪c, v⟫` (a cross product with `x - a`)
satisfies `ψ (z - x) = t (s x - s z) / (τ x τ z)` (`psi_sub`).  Writing a lower point `z₀` in the
vertex cone at `x` (`cone_edges`) and applying `ψ` shows that `x` has an edge to a lower vertex
(`exists_lower_neighbour`).  Adding the vertices in the order of `s`, each with a bar to `a` and an
edge to a lower vertex, is a sequence of Henneberg steps.
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

/-- The edges of `R`, as bars between points of `S` (the vertices). -/
def edgeBars (S R : Set (E n)) : Set (Sym2 (E n)) :=
  {b | ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ b = s(p, q) ∧ ∃ F ∈ faces R, dim F = 1 ∧ p ∈ F ∧ q ∈ F}

/-- The fan bars at `a`. -/
def fanBars (a : E n) (S : Set (E n)) : Set (Sym2 (E n)) := (fun x => s(a, x)) '' S

/-- Three distinct extreme points are not collinear. -/
lemma not_collinear_of_extreme {K : Set (E n)} {p q r : E n} (hp : p ∈ K.extremePoints ℝ)
    (hq : q ∈ K.extremePoints ℝ) (hr : r ∈ K.extremePoints ℝ) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (μ : ℝ) : r - p ≠ μ • (q - p) := by
  intro h
  rcases lt_trichotomy μ 0 with hμ | hμ | hμ
  · -- `p` lies strictly between `q` and `r`
    have hseg : p ∈ openSegment ℝ q r := by
      rw [openSegment_eq_image']
      refine ⟨1 / (1 - μ), ⟨div_pos one_pos (by linarith), ?_⟩, ?_⟩
      · rw [div_lt_one (by linarith)]; linarith
      · have hrq : r - q = (1 - μ) • (p - q) := by
          have : r - q = (r - p) + (p - q) := by abel
          rw [this, h, sub_smul, one_smul, smul_sub, smul_sub]; abel
        dsimp only
        rw [hrq, smul_smul, div_mul_cancel₀ _ (by linarith : (1 - μ) ≠ 0), one_smul]
        abel
    exact hpq ((mem_extremePoints.1 hp).2 q hq.1 r hr.1 hseg).1.symm
  · rw [hμ, zero_smul, sub_eq_zero] at h; exact hpr h.symm
  · rcases lt_trichotomy μ 1 with hμ1 | hμ1 | hμ1
    · -- `r` lies strictly between `p` and `q`
      have hseg : r ∈ openSegment ℝ p q := by
        rw [openSegment_eq_image']
        refine ⟨μ, ⟨hμ, hμ1⟩, ?_⟩
        dsimp only
        rw [← h]; abel
      exact hpr ((mem_extremePoints.1 hr).2 p hp.1 q hq.1 hseg).1
    · rw [hμ1, one_smul, sub_left_inj] at h; exact hqr h.symm
    · -- `q` lies strictly between `p` and `r`
      have hseg : q ∈ openSegment ℝ p r := by
        rw [openSegment_eq_image']
        refine ⟨1 / μ, ⟨div_pos one_pos hμ, by rw [div_lt_one hμ]; exact hμ1⟩, ?_⟩
        dsimp only
        rw [h, smul_smul, div_mul_cancel₀ _ hμ.ne', one_smul]
        abel
      exact hpq ((mem_extremePoints.1 hq).2 p hp.1 r hr.1 hseg).1

/-- Two vectors of a plane through three distinct extreme points span the plane. -/
lemma span_pair_eq {V : Finset (E n)} (h2 : dim (convexHull ℝ (V : Set (E n))) = 2) {p q r : E n}
    (hp : p ∈ (convexHull ℝ (V : Set (E n))).extremePoints ℝ)
    (hq : q ∈ (convexHull ℝ (V : Set (E n))).extremePoints ℝ)
    (hr : r ∈ (convexHull ℝ (V : Set (E n))).extremePoints ℝ) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) :
    Submodule.span ℝ {q - p, r - p} = vectorSpan ℝ (convexHull ℝ (V : Set (E n))) := by
  have hli : LinearIndependent ℝ ![q - p, r - p] := by
    rw [LinearIndependent.pair_iff]
    intro α β hαβ
    by_cases hβ : β = 0
    · rw [hβ, zero_smul, add_zero] at hαβ
      refine ⟨?_, hβ⟩
      rcases smul_eq_zero.1 hαβ with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) hpq.symm
    · exfalso
      have hβr : β • (r - p) = -(α • (q - p)) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hαβ
      have hcol : r - p = (-α / β) • (q - p) := by
        calc r - p = β⁻¹ • (β • (r - p)) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
          _ = β⁻¹ • (-(α • (q - p))) := by rw [hβr]
          _ = (-α / β) • (q - p) := by
            rw [smul_neg, smul_smul, ← neg_smul]; congr 1; ring
      exact not_collinear_of_extreme hp hq hr hpq hpr hqr (-α / β) hcol
  have hle : Submodule.span ℝ {q - p, r - p} ≤ vectorSpan ℝ (convexHull ℝ (V : Set (E n))) := by
    rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact vsub_mem_vectorSpan ℝ hq.1 hp.1
    · exact vsub_mem_vectorSpan ℝ hr.1 hp.1
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have h := finrank_span_eq_card hli
  rw [show Set.range ![q - p, r - p] = {q - p, r - p} by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]] at h
  rw [h, Fintype.card_fin]
  exact h2.symm

open Classical in
/-- **The vertex cone**: every point of `V` is a nonnegative combination of edge directions. -/
theorem cone_edges {V : Finset (E n)} (hcp : ConvPos V) {x : E n} (hx : x ∈ V) {z : E n}
    (hz : z ∈ V) : ∃ μ : E n → ℝ, (∀ y, 0 ≤ μ y) ∧
      z - x = ∑ y ∈ V.filter (fun y => y ≠ x ∧ ∃ F ∈ faces (convexHull ℝ (V : Set (E n))),
        dim F = 1 ∧ x ∈ F ∧ y ∈ F), μ y • (y - x) := by
  classical
  set Nb := V.filter (fun y => y ≠ x ∧ ∃ F ∈ faces (convexHull ℝ (V : Set (E n))),
    dim F = 1 ∧ x ∈ F ∧ y ∈ F)
  by_cases hzx : z = x
  · exact ⟨0, fun _ => le_rfl, by simp [hzx]⟩
  obtain ⟨σ⟩ := exists_vslice (hcp x hx)
  -- `e z` is in the hull of the slice vertices, which are slice points of neighbours
  have hzQ : σ.e z ∈ σ.Q := by
    rw [σ.Q_eq']
    exact subset_convexHull ℝ _ (by rw [σ.coe_W]; exact ⟨z, ⟨hz, by simpa using hzx⟩, rfl⟩)
  have hext := convexHull_extremePoints_eq σ.W
  rw [← σ.Q_eq'] at hext
  have hsub : σ.Q.extremePoints ℝ ⊆ ((Nb.image σ.e : Finset (E n)) : Set (E n)) := by
    intro w hw
    obtain ⟨y, hyV, hyx, rfl, F, hF, hF1, hxF, hyF⟩ := σ.extremePoints_Q hw
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hyV, hyx, F, hF, hF1,
      hxF, hyF⟩))
  rw [← hext] at hzQ
  have hzQ' := convexHull_mono hsub hzQ
  obtain ⟨w, hw0, hw1, hwz⟩ := Finset.mem_convexHull'.1 hzQ'
  -- transport the weights to the neighbours
  refine ⟨fun y => if y ∈ Nb then w (σ.e y) * σ.τ y / σ.τ z else 0, fun y => ?_, ?_⟩
  · dsimp only
    split_ifs with hy
    · obtain ⟨hyV, hyx, -⟩ := Finset.mem_filter.1 hy
      exact div_nonneg (mul_nonneg (hw0 _ (Finset.mem_image_of_mem _ hy))
        (σ.τ_pos hyV hyx).le) (σ.τ_pos hz hzx).le
    · exact le_rfl
  · have hinj : Set.InjOn σ.e (Nb : Set (E n)) := by
      intro y hy y' hy' h
      obtain ⟨hyV, hyx, -⟩ := Finset.mem_filter.1 hy
      obtain ⟨hy'V, hy'x, -⟩ := Finset.mem_filter.1 hy'
      exact σ.e_injOn hcp hyV hyx hy'V hy'x h
    rw [Finset.sum_image hinj] at hw1 hwz
    have hτz := σ.τ_pos hz hzx
    have key : σ.τ z • (z - x) = ∑ y ∈ Nb, w (σ.e y) • (σ.e y - x) := by
      rw [← σ.e_sub]
      have : ∑ y ∈ Nb, w (σ.e y) • (σ.e y - x) = ∑ y ∈ Nb, w (σ.e y) • σ.e y -
          (∑ y ∈ Nb, w (σ.e y)) • x := by
        rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun y _ => smul_sub _ _ _
      rw [this, hw1, one_smul, hwz]
    have e1 : z - x = (σ.τ z)⁻¹ • (σ.τ z • (z - x)) := by
      rw [smul_smul, inv_mul_cancel₀ hτz.ne', one_smul]
    rw [e1, key, Finset.smul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨hyV, hyx, -⟩ := Finset.mem_filter.1 hy
    dsimp only
    rw [if_pos hy, σ.e_sub, smul_smul, smul_smul]
    congr 1
    field_simp

namespace VSlice

variable {V : Finset (E n)} {a : E n} (σ : VSlice V a)

/-- The cross-product form at `x`. -/
noncomputable def psi (d x v : E n) : ℝ := ⟪σ.c, x - a⟫ * ⟪d, v⟫ - ⟪d, x - a⟫ * ⟪σ.c, v⟫

lemma psi_add (d x v w : E n) : σ.psi d x (v + w) = σ.psi d x v + σ.psi d x w := by
  simp only [psi, inner_add_right]; ring

lemma psi_smul (d x v : E n) (r : ℝ) : σ.psi d x (r • v) = r * σ.psi d x v := by
  simp only [psi, real_inner_smul_right]; ring

lemma psi_sum (d x : E n) {ι : Type*} (s : Finset ι) (f : ι → E n) :
    σ.psi d x (∑ i ∈ s, f i) = ∑ i ∈ s, σ.psi d x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [psi]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, psi_add, ih]

/-- **The cross product sees the order along the slice.** -/
lemma psi_sub (d : E n) {x z : E n} (hx : x ∈ V) (hxa : x ≠ a) (hz : z ∈ V) (hza : z ≠ a) :
    σ.psi d x (z - x) = σ.t * (⟪d, σ.e x⟫ - ⟪d, σ.e z⟫) / (σ.τ x * σ.τ z) := by
  have hτx := σ.τ_pos hx hxa
  have hτz := σ.τ_pos hz hza
  have hcx : ⟪σ.c, σ.e x - a⟫ = -σ.t := by
    rw [inner_sub_right, σ.inner_e hx hxa, lev]; ring
  have hcz : ⟪σ.c, σ.e z - a⟫ = -σ.t := by
    rw [inner_sub_right, σ.inner_e hz hza, lev]; ring
  have ex : x - a = (σ.τ x)⁻¹ • (σ.e x - a) := by
    rw [σ.e_sub, smul_smul, inv_mul_cancel₀ hτx.ne', one_smul]
  have ez : z - a = (σ.τ z)⁻¹ • (σ.e z - a) := by
    rw [σ.e_sub, smul_smul, inv_mul_cancel₀ hτz.ne', one_smul]
  have hA : ⟪σ.c, x - a⟫ = -σ.t / σ.τ x := by
    rw [ex, real_inner_smul_right, hcx]; field_simp
  have hA' : ⟪σ.c, z - a⟫ = -σ.t / σ.τ z := by
    rw [ez, real_inner_smul_right, hcz]; field_simp
  have hB : ⟪d, x - a⟫ = (⟪d, σ.e x⟫ - ⟪d, a⟫) / σ.τ x := by
    rw [ex, real_inner_smul_right, inner_sub_right]; field_simp
  have hB' : ⟪d, z - a⟫ = (⟪d, σ.e z⟫ - ⟪d, a⟫) / σ.τ z := by
    rw [ez, real_inner_smul_right, inner_sub_right]; field_simp
  have hC : ⟪σ.c, z - x⟫ = ⟪σ.c, z - a⟫ - ⟪σ.c, x - a⟫ := by
    rw [← inner_sub_right]; congr 1; abel
  have hD : ⟪d, z - x⟫ = ⟪d, z - a⟫ - ⟪d, x - a⟫ := by
    rw [← inner_sub_right]; congr 1; abel
  simp only [psi]
  rw [hC, hD, hA, hA', hB, hB']
  field_simp
  ring

end VSlice

/-- **A non-lowest vertex has an edge to a lower vertex.** -/
theorem exists_lower_neighbour {V : Finset (E n)} (hcp : ConvPos V) {a : E n} (σ : VSlice V a)
    (d : E n) {x z₀ : E n} (hx : x ∈ V) (hxa : x ≠ a) (hz₀ : z₀ ∈ V) (hz₀a : z₀ ≠ a)
    (hlow : ⟪d, σ.e z₀⟫ < ⟪d, σ.e x⟫)
    (hinj : ∀ y ∈ V, y ≠ a → ⟪d, σ.e y⟫ = ⟪d, σ.e x⟫ → y = x) :
    ∃ y ∈ V, y ≠ a ∧ ⟪d, σ.e y⟫ < ⟪d, σ.e x⟫ ∧
      ∃ F ∈ faces (convexHull ℝ (V : Set (E n))), dim F = 1 ∧ x ∈ F ∧ y ∈ F := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨μ, hμ, hsum⟩ := cone_edges hcp hx hz₀
  have h := congrArg (σ.psi d x) hsum
  rw [σ.psi_sum, σ.psi_sub d hx hxa hz₀ hz₀a] at h
  -- the left side is positive
  have hpos : 0 < σ.t * (⟪d, σ.e x⟫ - ⟪d, σ.e z₀⟫) / (σ.τ x * σ.τ z₀) :=
    div_pos (mul_pos σ.ht (by linarith)) (mul_pos (σ.τ_pos hx hxa) (σ.τ_pos hz₀ hz₀a))
  -- every term on the right is `≤ 0`
  have hneg : ∀ y ∈ V.filter (fun y => y ≠ x ∧ ∃ F ∈ faces (convexHull ℝ (V : Set (E n))),
      dim F = 1 ∧ x ∈ F ∧ y ∈ F), σ.psi d x (μ y • (y - x)) ≤ 0 := by
    intro y hy
    obtain ⟨hyV, hyx, F, hF, hF1, hxF, hyF⟩ := Finset.mem_filter.1 hy
    rw [σ.psi_smul]
    by_cases hya : y = a
    · rw [hya]
      have : σ.psi d x (a - x) = 0 := by
        simp only [VSlice.psi, show a - x = -(x - a) by abel, inner_neg_right]; ring
      rw [this, mul_zero]
    · have hge := hcon y hyV hya
      have hne : ⟪d, σ.e y⟫ ≠ ⟪d, σ.e x⟫ := fun h' => hyx (hinj y hyV hya h')
      have hgt : ⟪d, σ.e x⟫ < ⟪d, σ.e y⟫ := by
        by_contra hle
        push_neg at hle
        exact hge (lt_of_le_of_ne hle hne) F hF hF1 hxF hyF
      rw [σ.psi_sub d hx hxa hyV hya]
      apply mul_nonpos_of_nonneg_of_nonpos (hμ y)
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos σ.ht.le (by linarith))
        (mul_pos (σ.τ_pos hx hxa) (σ.τ_pos hyV hya)).le
  have := Finset.sum_nonpos hneg
  linarith

/-- **The fan triangulation braces the polygon.** -/
theorem braces_fan {V : Finset (E n)} (hcp : ConvPos V) (h2 : dim (convexHull ℝ (V : Set (E n))) = 2)
    {a : E n} (ha : a ∈ V) :
    Braces (edgeBars (V : Set (E n)) (convexHull ℝ (V : Set (E n))) ∪ fanBars a (V : Set (E n)))
      (V : Set (E n)) := by
  classical
  set R := convexHull ℝ (V : Set (E n)) with hR
  set B := edgeBars (V : Set (E n)) R ∪ fanBars a (V : Set (E n))
  obtain ⟨σ⟩ := exists_vslice (hcp a ha)
  have hext : ∀ {y : E n}, y ∈ V → y ∈ R.extremePoints ℝ := fun hy => hcp _ hy
  -- the slice is a segment: a direction `d`
  have hdimQ := σ.dim_Q_add_one (by rw [← hR]; omega)
  rw [σ.Q_eq', ← hR, h2, dim_convexHull'] at hdimQ
  have hW1 : finrank ℝ (vectorSpan ℝ (σ.W : Set (E n))) = 1 := by unfold dim at hdimQ; omega
  have hne : vectorSpan ℝ (σ.W : Set (E n)) ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hW1; exact zero_ne_one hW1
  obtain ⟨d, hdW, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  -- the order `s` is injective
  have hWpt : ∀ {y : E n}, y ∈ V → y ≠ a → σ.e y ∈ (σ.W : Set (E n)) := fun hy hya => by
    rw [σ.coe_W]; exact ⟨_, ⟨hy, by simpa using hya⟩, rfl⟩
  have hinj : ∀ {x y : E n}, x ∈ V → x ≠ a → y ∈ V → y ≠ a → ⟪d, σ.e y⟫ = ⟪d, σ.e x⟫ → y = x := by
    intro x y hx hxa hy hya h
    have hmem : σ.e y - σ.e x ∈ vectorSpan ℝ (σ.W : Set (E n)) :=
      vsub_mem_vectorSpan ℝ (hWpt hy hya) (hWpt hx hxa)
    have hdne : (⟨d, hdW⟩ : vectorSpan ℝ (σ.W : Set (E n))) ≠ 0 := by
      intro h0; apply hd0; simpa using congrArg Subtype.val h0
    obtain ⟨μ, hμ⟩ := (finrank_eq_one_iff_of_nonzero' _ hdne).1 hW1 ⟨_, hmem⟩
    have hμ' : σ.e y - σ.e x = μ • d := by simpa using (congrArg Subtype.val hμ).symm
    have h0 : ⟪d, σ.e y - σ.e x⟫ = 0 := by rw [inner_sub_right, h, sub_self]
    rw [hμ', real_inner_smul_right, real_inner_self_eq_norm_sq] at h0
    have hμ0 : μ = 0 := by
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exfalso; exact hd0 (by simpa using h)
    rw [hμ0, zero_smul, sub_eq_zero] at hμ'
    exact σ.e_injOn hcp hy hya hx hxa hμ'
  set s : E n → ℝ := fun y => ⟪d, σ.e y⟫ with hs
  set S' := V.erase a
  have hS' : ∀ {y : E n}, y ∈ S' ↔ y ∈ V ∧ y ≠ a := fun {y} => by
    rw [Finset.mem_erase]; exact and_comm
  -- the initial segments
  set L : E n → Set (E n) := fun x => insert a {z | z ∈ V ∧ z ≠ a ∧ s z ≤ s x} with hL
  set rk : E n → ℕ := fun x => (S'.filter fun z => s z < s x).card with hrk
  have hbar_fan : ∀ {y : E n}, y ∈ V → s(a, y) ∈ B := fun hy => Or.inr ⟨_, hy, rfl⟩
  have hbar_edge : ∀ {x y : E n}, x ∈ V → y ∈ V → x ≠ y →
      (∃ F ∈ faces R, dim F = 1 ∧ x ∈ F ∧ y ∈ F) → s(x, y) ∈ B :=
    fun hx hy hxy hF => Or.inl ⟨_, by exact_mod_cast hx, _, by exact_mod_cast hy, hxy, rfl, hF⟩
  have hpairs : ∀ {u : E n → E n} {p q : E n}, IsMotion B u → s(p, q) ∈ B →
      ⟪u p - u q, p - q⟫ = 0 := fun hu hb => by simpa using hu _ hb
  have hsym : ∀ {u : E n → E n} {p q : E n}, ⟪u p - u q, p - q⟫ = 0 → ⟪u q - u p, q - p⟫ = 0 :=
    fun {u p q} h => by rw [← neg_sub (u p) (u q), ← neg_sub p q, inner_neg_neg]; exact h
  have key : ∀ N, ∀ x ∈ S', rk x = N → Braces B (L x) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro x hxS hN
      obtain ⟨hxV, hxa⟩ := hS'.1 hxS
      by_cases h0 : N = 0
      · -- `L x = {a, x}`
        have hempty : S'.filter (fun z => s z < s x) = ∅ := by
          rw [← Finset.card_eq_zero, ← h0]; exact hN
        have hLx : L x = {a, x} := by
          ext z
          simp only [hL, Set.mem_insert_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · rintro (h | ⟨hzV, hza, hzs⟩)
            · exact Or.inl h
            · right
              rcases hzs.lt_or_eq with hlt | heq
              · exfalso
                have : z ∈ S'.filter fun z => s z < s x :=
                  Finset.mem_filter.2 ⟨hS'.2 ⟨hzV, hza⟩, hlt⟩
                rw [hempty] at this; simp at this
              · exact hinj hxV hxa hzV hza heq
          · rintro (h | h)
            · exact Or.inl h
            · rw [h]; exact Or.inr ⟨hxV, hxa, le_rfl⟩
        rw [hLx]
        intro u hu p hp q hq
        have hb := hpairs hu (hbar_fan hxV)
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
        rcases hp with hp | hp <;> rcases hq with hq | hq <;> rw [hp, hq]
        · simp
        · exact hb
        · exact hsym hb
        · simp
      -- the predecessor `x⁻`
      have hbelow : (S'.filter fun z => s z < s x).Nonempty := by
        rw [← Finset.card_pos]; rw [hrk] at hN; simp only at hN; omega
      obtain ⟨x', hx'f, hx'max⟩ := (S'.filter fun z => s z < s x).exists_max_image s hbelow
      obtain ⟨hx'S, hx'lt⟩ := Finset.mem_filter.1 hx'f
      obtain ⟨hx'V, hx'a⟩ := hS'.1 hx'S
      have hrk' : rk x' < N := by
        rw [← hN]
        apply Finset.card_lt_card
        refine ⟨fun z hz => ?_, fun h => ?_⟩
        · obtain ⟨hzS, hzlt⟩ := Finset.mem_filter.1 hz
          exact Finset.mem_filter.2 ⟨hzS, hzlt.trans hx'lt⟩
        · have := Finset.mem_filter.1 (h hx'f)
          exact lt_irrefl _ this.2
      have hIH := ih _ hrk' x' hx'S rfl
      have hLsplit : L x = insert x (L x') := by
        ext z
        simp only [hL, Set.mem_insert_iff, Set.mem_setOf_eq]
        constructor
        · rintro (rfl | ⟨hzV, hza, hzs⟩)
          · exact Or.inr (Or.inl rfl)
          · rcases hzs.lt_or_eq with hlt | heq
            · exact Or.inr (Or.inr ⟨hzV, hza, hx'max z (Finset.mem_filter.2 ⟨hS'.2 ⟨hzV, hza⟩, hlt⟩)⟩)
            · exact Or.inl (hinj hxV hxa hzV hza heq)
        · rintro (rfl | rfl | ⟨hzV, hza, hzs⟩)
          · exact Or.inr ⟨hxV, hxa, le_rfl⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hzV, hza, hzs.trans hx'lt.le⟩
      -- an edge from `x` to a lower vertex
      obtain ⟨y, hyV, hya, hylt, F, hF, hF1, hxF, hyF⟩ :=
        exists_lower_neighbour hcp σ d hxV hxa hx'V hx'a hx'lt (fun y hy hya h => hinj hxV hxa hy hya h)
      have hyL : y ∈ L x' := Or.inr ⟨hyV, hya, hx'max y (Finset.mem_filter.2 ⟨hS'.2 ⟨hyV, hya⟩, hylt⟩)⟩
      have hyx : y ≠ x := fun h => by rw [h] at hylt; exact lt_irrefl _ hylt
      rw [hLsplit]
      by_cases hN1 : rk x' = 0
      · -- a triangle `a, x', x`
        have hempty : S'.filter (fun w => s w < s x') = ∅ := by
          rw [← Finset.card_eq_zero]; exact hN1
        have hLx' : L x' = {a, x'} := by
          ext z
          simp only [hL, Set.mem_insert_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · rintro (h | ⟨hzV, hza, hzs⟩)
            · exact Or.inl h
            · right
              rcases hzs.lt_or_eq with hlt | heq
              · exfalso
                have : z ∈ S'.filter fun w => s w < s x' :=
                  Finset.mem_filter.2 ⟨hS'.2 ⟨hzV, hza⟩, hlt⟩
                rw [hempty] at this; simp at this
              · exact hinj hx'V hx'a hzV hza heq
          · rintro (h | h)
            · exact Or.inl h
            · rw [h]; exact Or.inr ⟨hx'V, hx'a, le_rfl⟩
        rw [hLx'] at hyL ⊢
        have hyx' : y = x' := by
          rcases hyL with h | h
          · exact absurd h hya
          · exact h
        rw [hyx'] at hyV hyx hyF
        intro u hu p hp q hq
        have hb1 := hpairs hu (hbar_fan hxV)
        have hb2 := hpairs hu (hbar_fan hyV)
        have hb3 := hpairs hu (hbar_edge hxV hyV (Ne.symm hyx) ⟨F, hF, hF1, hxF, hyF⟩)
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
        rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;> rw [hp, hq] <;>
          first | simp | exact hb1 | exact hb2 | exact hb3 | exact hsym hb1 | exact hsym hb2 |
            exact hsym hb3
      · -- a Henneberg step
        have hx'' : (S'.filter fun z => s z < s x').Nonempty := by
          rw [← Finset.card_pos]; rw [hrk] at hN1; simp only at hN1; omega
        obtain ⟨z₁, hz₁f⟩ := hx''
        obtain ⟨hz₁S, hz₁lt⟩ := Finset.mem_filter.1 hz₁f
        obtain ⟨hz₁V, hz₁a⟩ := hS'.1 hz₁S
        have hz₁x' : z₁ ≠ x' := fun h => by rw [h] at hz₁lt; exact lt_irrefl _ hz₁lt
        have hLR : ∀ z ∈ insert x (L x'), z ∈ R := by
          intro z hz
          rcases hz with rfl | rfl | hz
          · exact subset_convexHull ℝ _ (by exact_mod_cast hxV)
          · exact subset_convexHull ℝ _ (by exact_mod_cast ha)
          · exact subset_convexHull ℝ _ (by exact_mod_cast hz.1)
        have hvsL : vectorSpan ℝ (L x') = vectorSpan ℝ R := by
          refine le_antisymm (vectorSpan_mono ℝ (fun z hz => hLR z (Or.inr hz))) ?_
          rw [← span_pair_eq h2 (hext ha) (hext hz₁V) (hext hx'V) (Ne.symm hz₁a) (Ne.symm hx'a) hz₁x',
            Submodule.span_le]
          rintro _ (rfl | rfl)
          · exact vsub_mem_vectorSpan ℝ (Or.inr ⟨hz₁V, hz₁a, hz₁lt.le⟩) (Or.inl rfl)
          · exact vsub_mem_vectorSpan ℝ (Or.inr ⟨hx'V, hx'a, le_rfl⟩) (Or.inl rfl)
        refine (hIH.henneberg (X := {a, y}) ⟨a, Or.inl rfl⟩ ?_ ?_ ?_).mono ?_ subset_rfl
        · rw [hvsL]; exact vectorSpan_mono ℝ hLR
        · rintro z (rfl | rfl)
          · exact Or.inl rfl
          · exact hyL
        · rw [hvsL, ← span_pair_eq h2 (hext hxV) (hext ha) (hext hyV) hxa (Ne.symm hyx)
            (Ne.symm hya)]
          rw [Submodule.span_le]
          rintro _ (rfl | rfl)
          · have : a - x = -(x - a) := by abel
            rw [SetLike.mem_coe, this]
            exact Submodule.neg_mem _ (Submodule.subset_span ⟨a, Or.inl rfl, rfl⟩)
          · have : y - x = -(x - y) := by abel
            rw [SetLike.mem_coe, this]
            exact Submodule.neg_mem _ (Submodule.subset_span ⟨y, Or.inr rfl, rfl⟩)
        · rintro b (hb | ⟨z, hz, rfl⟩)
          · exact hb
          · rcases hz with hz | hz <;> rw [hz] <;> dsimp only
            · rw [Sym2.eq_swap]; exact hbar_fan hxV
            · exact hbar_edge hxV hyV (Ne.symm hyx) ⟨F, hF, hF1, hxF, hyF⟩
  -- the top vertex
  have hS'ne : S'.Nonempty := by
    obtain ⟨b, hb, hba⟩ : ∃ b ∈ V, b ≠ a := by
      by_contra hcon
      push_neg at hcon
      have : (V : Set (E n)) = {a} := by
        ext z; simp only [Finset.mem_coe, Set.mem_singleton_iff]
        exact ⟨hcon z, fun h => h ▸ ha⟩
      rw [hR, this, convexHull_singleton, dim_singleton] at h2
      omega
    exact ⟨b, hS'.2 ⟨hb, hba⟩⟩
  obtain ⟨xm, hxmS, hxmmax⟩ := S'.exists_max_image s hS'ne
  have htop := key _ xm hxmS rfl
  refine htop.mono subset_rfl (fun z hz => ?_)
  by_cases hza : z = a
  · exact Or.inl hza
  · exact Or.inr ⟨hz, hza, hxmmax z (hS'.2 ⟨hz, hza⟩)⟩

end Kalai5
