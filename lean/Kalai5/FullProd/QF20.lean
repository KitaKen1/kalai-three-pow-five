import Kalai5.FullProd.QF20Aux

/-!
# A `Δ2 × Δ2` facet in a cs 5-polytope with twenty vertices forces 62 edges

**Theorem** (`IsCSPolytope5.edges_ge_62_of_qRow`): if a centrally symmetric 5-polytope `P` with
20 vertices has a facet `F` with the row `qRow` of `Δ2 × Δ2`, then `P` has at least 62 edges.

The vertices are the nine vertices `x a b` of `F`, their negatives, and one more pair `±z`.  For the
36 candidate side edges `[x i j, -x i' j']` the exposing functionals of the full case are
`L = Σ (u k γ k) h k + Σ (v l δ l) g l` with potentials `u = (1, -1, α)`, `v = (1, -1, β)`
(`α, β ∈ (-1, 1)` on the third indices); their value at `z` is `A + α a + β b`.
* If this can be made `< 1` in absolute value, the side edge survives;
* if `A - |a| - |b| ≥ 1` (*`z` above*), tilting `L` by the facet functional makes `[z, x i j]`
  and `[z, -x i' j']` edges; symmetrically below with `-z`;
* the degenerate ties (`a = b = 0`, `A = ±1`) give a triangle face, hence the side edge again.
Counting: `e ≥ 18 + 18 + (36 - 2|B|) + 2(|first B| + |second B|) ≥ 62` by
`card_le_cells_add_five`, where `B` is the set of candidates with `z` above.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-! ### The data of a `Δ2 × Δ2` facet -/

/-- The data of a `Δ2 × Δ2` facet `F` of `P`: vertices, the facet functional and the side
functionals with a positive representation. -/
structure QFacet (P F : Set E5) where
  x : Fin 3 → Fin 3 → E5
  cF : E5
  h : Fin 3 → E5
  g : Fin 3 → E5
  γ : Fin 3 → ℝ
  δ : Fin 3 → ℝ
  inj : ∀ a b a' b', x a b = x a' b' → a = a' ∧ b = b'
  ext : ∀ a b, x a b ∈ P.extremePoints ℝ
  memF : ∀ a b, x a b ∈ F
  all : ∀ z ∈ P.extremePoints ℝ, z ∈ F → ∃ a b, z = x a b
  cF_le : ∀ y ∈ P, ⟪y, cF⟫ ≤ 1
  cF_eq : ∀ y ∈ P, (y ∈ F ↔ ⟪y, cF⟫ = 1)
  h0 : ∀ a b i, i ≠ a → ⟪x a b, h i⟫ = 0
  hpos : ∀ a b, 0 < ⟪x a b, h a⟫
  g0 : ∀ a b j, j ≠ b → ⟪x a b, g j⟫ = 0
  gpos : ∀ a b, 0 < ⟪x a b, g b⟫
  γpos : ∀ a, 0 < γ a
  δpos : ∀ b, 0 < δ b
  rep : cF = ∑ i, γ i • h i + ∑ j, δ j • g j

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.qFacet {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = qRow) : Nonempty (QFacet P F) := by
  classical
  obtain ⟨x, R, C, hinj, hx, hall, hR, hC, hxR, hxC⟩ := hP.prodTri_facet hF h4 hrow
  have hFP : F ≠ P := hP.ne_of_dim_ne (by rw [h4]; norm_num)
  have hxP : ∀ a b, x a b ∈ P := fun a b => (hx a b).1.1
  obtain ⟨cF, hcFle, hcF⟩ := hP.exists_dual hF hFP
  choose cR hcRle hcR using fun i =>
    hP.exists_dual (hR i).1 (hP.ne_of_dim_ne (by rw [(hR i).2.2]; norm_num))
  choose cC hcCle hcC using fun j =>
    hP.exists_dual (hC j).1 (hP.ne_of_dim_ne (by rw [(hC j).2.2]; norm_num))
  set h : Fin 3 → E5 := fun i => cF - cR i with hh
  set g : Fin 3 → E5 := fun j => cF - cC j with hg
  have hcFx : ∀ a b, ⟪x a b, cF⟫ = 1 := fun a b => (hcF _ (hxP a b)).1 (hx a b).2
  have hh0 : ∀ a b i, i ≠ a → ⟪x a b, h i⟫ = 0 := by
    intro a b i hi
    rw [hh, inner_sub_right, hcFx, (hcR i _ (hxP a b)).1 ((hxR a b i).2 (Ne.symm hi)), sub_self]
  have hhpos : ∀ a b, 0 < ⟪x a b, h a⟫ := by
    intro a b
    have h1 := hcRle a _ (hxP a b)
    have h2 : ⟪x a b, cR a⟫ ≠ 1 := fun he => (hxR a b a).1 ((hcR a _ (hxP a b)).2 he) rfl
    rw [hh, inner_sub_right, hcFx]
    have := lt_of_le_of_ne h1 h2
    linarith
  have hg0 : ∀ a b j, j ≠ b → ⟪x a b, g j⟫ = 0 := by
    intro a b j hj
    rw [hg, inner_sub_right, hcFx, (hcC j _ (hxP a b)).1 ((hxC a b j).2 (Ne.symm hj)), sub_self]
  have hgpos : ∀ a b, 0 < ⟪x a b, g b⟫ := by
    intro a b
    have h1 := hcCle b _ (hxP a b)
    have h2 : ⟪x a b, cC b⟫ ≠ 1 := fun he => (hxC a b b).1 ((hcC b _ (hxP a b)).2 he) rfl
    rw [hg, inner_sub_right, hcFx]
    have := lt_of_le_of_ne h1 h2
    linarith
  obtain ⟨γ, δ, hγ, hδ, hrep⟩ := exists_pos_repr h g x cF hh0 hhpos hg0 hgpos hcFx
  exact ⟨⟨x, cF, h, g, γ, δ, hinj, fun a b => (hx a b).1, fun a b => (hx a b).2, hall, hcFle,
    hcF, hh0, hhpos, hg0, hgpos, hγ, hδ, hrep⟩⟩

end cs

namespace QFacet

variable {P F : Set E5} (Q : QFacet P F)

lemma xP (a b : Fin 3) : Q.x a b ∈ P := (Q.ext a b).1

lemma cFx (a b : Fin 3) : ⟪Q.x a b, Q.cF⟫ = 1 := (Q.cF_eq _ (Q.xP a b)).1 (Q.memF a b)

/-- The two weights at `x a b`. -/
noncomputable def w1 (a b : Fin 3) : ℝ := Q.γ a * ⟪Q.x a b, Q.h a⟫
noncomputable def w2 (a b : Fin 3) : ℝ := Q.δ b * ⟪Q.x a b, Q.g b⟫

lemma w1_pos (a b : Fin 3) : 0 < Q.w1 a b := mul_pos (Q.γpos a) (Q.hpos a b)
lemma w2_pos (a b : Fin 3) : 0 < Q.w2 a b := mul_pos (Q.δpos b) (Q.gpos a b)

/-- The potential functional. -/
noncomputable def Lv (u v : Fin 3 → ℝ) : E5 := ∑ k, (u k * Q.γ k) • Q.h k + ∑ l, (v l * Q.δ l) • Q.g l

lemma val (y : E5) (u v : Fin 3 → ℝ) :
    ⟪y, Q.Lv u v⟫ = ∑ k, u k * (Q.γ k * ⟪y, Q.h k⟫) + ∑ l, v l * (Q.δ l * ⟪y, Q.g l⟫) := by
  simp only [Lv, inner_add_right, inner_sum, real_inner_smul_right, mul_assoc]

lemma val_x (a b : Fin 3) (u v : Fin 3 → ℝ) :
    ⟪Q.x a b, Q.Lv u v⟫ = u a * Q.w1 a b + v b * Q.w2 a b := by
  have := inner_eval Q.h Q.g Q.x Q.h0 Q.g0 (fun k => u k * Q.γ k) (fun l => v l * Q.δ l) a b
  simp only [Lv, w1, w2] at this ⊢
  rw [this]
  ring

lemma Lv_one : Q.Lv (fun _ => 1) (fun _ => 1) = Q.cF := by
  simp only [Lv, one_mul, Q.rep]

lemma w_sum (a b : Fin 3) : Q.w1 a b + Q.w2 a b = 1 := by
  have h1 := Q.val_x a b (fun _ => 1) (fun _ => 1)
  rw [Q.Lv_one, Q.cFx] at h1
  linarith

end QFacet

/-! ### Generalized potentials -/

/-- The potential `1` at `i`, `-1` at `i'` and `α` at the third index. -/
def potA (p : Idx) (α : ℝ) (k : Fin 3) : ℝ :=
  if k = p.1.1 then 1 else if k = p.1.2 then -1 else α

lemma potA_fst (p : Idx) (α : ℝ) : potA p α p.1.1 = 1 := by simp [potA]

lemma potA_snd (p : Idx) (α : ℝ) : potA p α p.1.2 = -1 := by
  simp [potA, Ne.symm p.2]

lemma potA_le_one (p : Idx) {α : ℝ} (hα : α < 1) (k : Fin 3) : potA p α k ≤ 1 := by
  unfold potA; split_ifs <;> linarith

lemma neg_potA_le_one (p : Idx) {α : ℝ} (hα : -1 < α) (k : Fin 3) : -potA p α k ≤ 1 := by
  unfold potA; split_ifs <;> linarith

lemma eq_of_potA_eq_one (p : Idx) {α : ℝ} (hα : α < 1) {k : Fin 3} (h : potA p α k = 1) :
    k = p.1.1 := by
  unfold potA at h; split_ifs at h with h1 h2 <;> first | exact h1 | linarith

lemma eq_of_neg_potA_eq_one (p : Idx) {α : ℝ} (hα : -1 < α) {k : Fin 3} (h : -potA p α k = 1) :
    k = p.1.2 := by
  unfold potA at h; split_ifs at h with h1 h2 <;> first | exact h2 | linarith

lemma sum_potA (p : Idx) (α : ℝ) (Z : Fin 3 → ℝ) :
    ∑ k, potA p α k * Z k = Z p.1.1 - Z p.1.2 + α * Z (third p.1.1 p.1.2) := by
  obtain ⟨⟨i, i'⟩, hii⟩ := p
  simp only at hii ⊢
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases i' <;> (try simp at hii) <;> simp [potA, third] <;> ring

/-! ### Twenty vertices: one extra antipodal pair -/

/-- The data of a `Δ2 × Δ2` facet of a cs 5-polytope with twenty vertices: the extra vertex `z`
and the vertex set `X`. -/
structure Q20 (P F : Set E5) extends QFacet P F where
  z : E5
  X : Finset E5
  zext : z ∈ P.extremePoints ℝ
  znF : z ∉ F
  nznF : -z ∉ F
  zz : z ≠ -z
  hPX : P = convexHull ℝ (X : Set E5)
  memX : ∀ v, v ∈ X ↔ ((∃ a b, v = x a b) ∨ (∃ a b, v = -x a b) ∨ v = z ∨ v = -z)

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.q20 (hv : fvec P 0 = 20) {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = qRow) : Nonempty (Q20 P F) := by
  classical
  obtain ⟨Q⟩ := hP.qFacet hF h4 hrow
  have hFP : F ≠ P := hP.ne_of_dim_ne (by rw [h4]; norm_num)
  have hdisj : ∀ y ∈ F, -y ∉ F := fun y hy hny => hFP (hP.eq_of_mem_of_neg_mem hF hy hny)
  let vtx : Bool × Fin 3 × Fin 3 → E5 := fun s => cond s.1 (Q.x s.2.1 s.2.2) (-Q.x s.2.1 s.2.2)
  have hvtx_inj : Function.Injective vtx := by
    rintro ⟨s, a, b⟩ ⟨s', a', b'⟩ he
    cases s <;> cases s' <;> simp only [vtx, Bool.cond_true, Bool.cond_false] at he
    · obtain ⟨rfl, rfl⟩ := Q.inj a b a' b' (neg_injective he); rfl
    · exact absurd (by rw [he]; exact Q.memF a' b' : -Q.x a b ∈ F) (hdisj _ (Q.memF a b))
    · exact absurd (by rw [← he]; exact Q.memF a b : -Q.x a' b' ∈ F) (hdisj _ (Q.memF a' b'))
    · obtain ⟨rfl, rfl⟩ := Q.inj a b a' b' he; rfl
  set X18 : Finset E5 := Finset.univ.image vtx with hX18
  have hmem18 : ∀ v, v ∈ X18 ↔ ((∃ a b, v = Q.x a b) ∨ (∃ a b, v = -Q.x a b)) := by
    intro v
    rw [hX18, Finset.mem_image]
    constructor
    · rintro ⟨⟨s, a, b⟩, -, rfl⟩
      cases s
      · exact Or.inr ⟨a, b, rfl⟩
      · exact Or.inl ⟨a, b, rfl⟩
    · rintro (⟨a, b, rfl⟩ | ⟨a, b, rfl⟩)
      · exact ⟨(true, a, b), Finset.mem_univ _, rfl⟩
      · exact ⟨(false, a, b), Finset.mem_univ _, rfl⟩
  have hX18ext : (X18 : Set E5) ⊆ P.extremePoints ℝ := by
    intro v hv
    rcases (hmem18 v).1 hv with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
    · exact Q.ext a b
    · exact hP.neg_mem_extremePoints (Q.ext a b)
  have hX18card : X18.card = 18 := by
    rw [hX18, Finset.card_image_of_injective _ hvtx_inj]
    rfl
  obtain ⟨V, hV⟩ := hP.polytope
  have hextfin : (P.extremePoints ℝ).Finite := by rw [hV]; exact extremePoints_finite V
  have hextcard : (P.extremePoints ℝ).ncard = 20 := by rw [← hv, hV, fvec_zero_eq]
  obtain ⟨z, hz, hzX⟩ : ∃ z ∈ P.extremePoints ℝ, z ∉ X18 := by
    by_contra hcon
    push_neg at hcon
    have hsub : P.extremePoints ℝ ⊆ (X18 : Set E5) := fun y hy => hcon y hy
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, hX18card, hextcard] at this
    omega
  have hnz : -z ∈ P.extremePoints ℝ := hP.neg_mem_extremePoints hz
  have hnzX : -z ∉ X18 := by
    intro h
    apply hzX
    rcases (hmem18 _).1 h with ⟨a, b, hab⟩ | ⟨a, b, hab⟩
    · exact (hmem18 _).2 (Or.inr ⟨a, b, by rw [← hab, neg_neg]⟩)
    · exact (hmem18 _).2 (Or.inl ⟨a, b, by rw [← neg_neg z, hab, neg_neg]⟩)
  have hznF : z ∉ F := fun h => by
    obtain ⟨a, b, rfl⟩ := Q.all z hz h
    exact hzX ((hmem18 _).2 (Or.inl ⟨a, b, rfl⟩))
  have hnznF : -z ∉ F := fun h => by
    obtain ⟨a, b, hab⟩ := Q.all (-z) hnz h
    exact hzX ((hmem18 _).2 (Or.inr ⟨a, b, by rw [← neg_neg z, hab]⟩))
  have hzz : z ≠ -z := by
    intro h
    have h0 : z = 0 := by
      have h2 : (2 : ℝ) • z = 0 := by
        rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel z
      rcases smul_eq_zero.1 h2 with h3 | h3
      · norm_num at h3
      · exact h3
    have hseg : (0 : E5) ∈ openSegment ℝ (Q.x 0 0) (-Q.x 0 0) :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
        rw [smul_neg, add_neg_cancel]⟩
    rw [h0] at hz
    have := (mem_extremePoints.1 hz).2 _ (Q.xP 0 0) _ (hP.symm _ (Q.xP 0 0)) hseg
    have hx0 : Q.x 0 0 = 0 := this.1
    exact hdisj _ (Q.memF 0 0) (by rw [hx0, neg_zero, ← hx0]; exact Q.memF 0 0)
  set X : Finset E5 := insert z (insert (-z) X18) with hX
  have hXext : (X : Set E5) ⊆ P.extremePoints ℝ := by
    intro v hv
    rw [hX, Finset.coe_insert, Finset.coe_insert] at hv
    rcases hv with rfl | rfl | hv
    · exact hz
    · exact hnz
    · exact hX18ext hv
  have hXcard : X.card = 20 := by
    have h1 : z ∉ insert (-z) X18 := by
      rw [Finset.mem_insert]; push_neg; exact ⟨hzz, hzX⟩
    rw [hX, Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem hnzX, hX18card]
  have hextX : (X : Set E5) = P.extremePoints ℝ :=
    Set.eq_of_subset_of_ncard_le hXext (by rw [hextcard, Set.ncard_coe_finset, hXcard]) hextfin
  have hPX : P = convexHull ℝ (X : Set E5) := by
    rw [hextX, hV]
    exact (convexHull_extremePoints_eq V).symm
  have hmemX : ∀ v, v ∈ X ↔ ((∃ a b, v = Q.x a b) ∨ (∃ a b, v = -Q.x a b) ∨ v = z ∨ v = -z) := by
    intro v
    rw [hX, Finset.mem_insert, Finset.mem_insert, hmem18]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rintro (h | h | h | h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  exact ⟨⟨Q, z, X, hz, hznF, hnznF, hzz, hPX, hmemX⟩⟩

end cs

namespace Q20

variable {P F : Set E5} (Q : Q20 P F)

lemma zP : Q.z ∈ P := Q.zext.1

lemma x_mem (a b : Fin 3) : Q.x a b ∈ Q.X := (Q.memX _).2 (Or.inl ⟨a, b, rfl⟩)
lemma nx_mem (a b : Fin 3) : -Q.x a b ∈ Q.X := (Q.memX _).2 (Or.inr (Or.inl ⟨a, b, rfl⟩))
lemma z_mem : Q.z ∈ Q.X := (Q.memX _).2 (Or.inr (Or.inr (Or.inl rfl)))
lemma nz_mem : -Q.z ∈ Q.X := (Q.memX _).2 (Or.inr (Or.inr (Or.inr rfl)))

/-- The coordinates of `z`. -/
noncomputable def Zc (k : Fin 3) : ℝ := Q.γ k * ⟪Q.z, Q.h k⟫
noncomputable def Wc (l : Fin 3) : ℝ := Q.δ l * ⟪Q.z, Q.g l⟫

lemma val_z (u v : Fin 3 → ℝ) :
    ⟪Q.z, Q.Lv u v⟫ = ∑ k, u k * Q.Zc k + ∑ l, v l * Q.Wc l := Q.val Q.z u v

/-- The data of a candidate `c = ((i, i'), (j, j'))`. -/
noncomputable def A (c : Idx × Idx) : ℝ :=
  Q.Zc c.1.1.1 - Q.Zc c.1.1.2 + (Q.Wc c.2.1.1 - Q.Wc c.2.1.2)
noncomputable def aa (c : Idx × Idx) : ℝ := Q.Zc (third c.1.1.1 c.1.1.2)
noncomputable def bb (c : Idx × Idx) : ℝ := Q.Wc (third c.2.1.1 c.2.1.2)

/-- `z` lies above the candidate. -/
def up (c : Idx × Idx) : Prop :=
  1 ≤ Q.A c - |Q.aa c| - |Q.bb c| ∧ ¬ (Q.aa c = 0 ∧ Q.bb c = 0 ∧ Q.A c = 1)

/-- `z` lies below the candidate. -/
def dn (c : Idx × Idx) : Prop :=
  1 ≤ -Q.A c - |Q.aa c| - |Q.bb c| ∧ ¬ (Q.aa c = 0 ∧ Q.bb c = 0 ∧ Q.A c = -1)

lemma val_z_potA (c : Idx × Idx) (α β : ℝ) :
    ⟪Q.z, Q.Lv (potA c.1 α) (potA c.2 β)⟫ = Q.A c + α * Q.aa c + β * Q.bb c := by
  rw [Q.val_z, sum_potA, sum_potA]
  simp only [A, aa, bb]
  ring

/-- The candidate edge. -/
def side (c : Idx × Idx) : Set E5 := segment ℝ (Q.x c.1.1.1 c.2.1.1) (-Q.x c.1.1.2 c.2.1.2)

end Q20

/-! ### Real-number lemmas -/

/-- If the interval `(A - |a| - |b|, A + |a| + |b|)` meets `(-1, 1)`, a point of it is attained by
`A + α a + β b` with `α, β ∈ (-1, 1)`. -/
lemma exists_small (A a b : ℝ) (h1 : A - |a| - |b| < 1) (h2 : -A - |a| - |b| < 1) :
    ∃ α β : ℝ, -1 < α ∧ α < 1 ∧ -1 < β ∧ β < 1 ∧ |A + α * a + β * b| < 1 := by
  by_cases h0 : |a| + |b| = 0
  · have ha : a = 0 := abs_eq_zero.1 (by linarith [abs_nonneg a, abs_nonneg b])
    have hb : b = 0 := abs_eq_zero.1 (by linarith [abs_nonneg a, abs_nonneg b])
    refine ⟨0, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [ha, hb] at h1 h2
    simp only [abs_zero, sub_zero, mul_zero, add_zero] at h1 h2 ⊢
    rw [abs_lt]; constructor <;> linarith
  · have hpos : 0 < |a| + |b| := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    set c := (max (A - |a| - |b|) (-1) + min (A + |a| + |b|) 1) / 2 with hc
    have e1 := le_max_left (A - |a| - |b|) (-1)
    have e2 := le_max_right (A - |a| - |b|) (-1)
    have e3 := min_le_left (A + |a| + |b|) 1
    have e4 := min_le_right (A + |a| + |b|) 1
    have e5 : A - |a| - |b| < min (A + |a| + |b|) 1 := lt_min (by linarith) h1
    have e6 : -1 < min (A + |a| + |b|) 1 := lt_min (by linarith) (by norm_num)
    have e7 : max (A - |a| - |b|) (-1) < A + |a| + |b| := max_lt (by linarith) (by linarith)
    have e8 : max (A - |a| - |b|) (-1) < 1 := max_lt h1 (by norm_num)
    have hc1 : A - |a| - |b| < c := by rw [hc]; linarith
    have hc2 : c < A + |a| + |b| := by rw [hc]; linarith
    have hc3 : -1 < c := by rw [hc]; linarith
    have hc4 : c < 1 := by rw [hc]; linarith
    set lam := (c - A) / (|a| + |b|) with hlam
    have hl1 : lam < 1 := by rw [hlam, div_lt_one hpos]; linarith
    have hl2 : -1 < lam := by rw [hlam, lt_div_iff₀ hpos]; linarith
    have hlv : lam * (|a| + |b|) = c - A := by rw [hlam]; field_simp
    set sa : ℝ := if 0 ≤ a then 1 else -1 with hsa
    set sb : ℝ := if 0 ≤ b then 1 else -1 with hsb
    have hsaa : sa * a = |a| := by
      rw [hsa]; split_ifs with h
      · rw [one_mul, abs_of_nonneg h]
      · rw [abs_of_neg (lt_of_not_ge h)]; ring
    have hsbb : sb * b = |b| := by
      rw [hsb]; split_ifs with h
      · rw [one_mul, abs_of_nonneg h]
      · rw [abs_of_neg (lt_of_not_ge h)]; ring
    have hsa1 : sa = 1 ∨ sa = -1 := by rw [hsa]; split_ifs <;> simp
    have hsb1 : sb = 1 ∨ sb = -1 := by rw [hsb]; split_ifs <;> simp
    refine ⟨lam * sa, lam * sb, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hsa1 with h | h <;> rw [h] <;> linarith
    · rcases hsa1 with h | h <;> rw [h] <;> linarith
    · rcases hsb1 with h | h <;> rw [h] <;> linarith
    · rcases hsb1 with h | h <;> rw [h] <;> linarith
    · have : A + lam * sa * a + lam * sb * b = c := by
        rw [mul_assoc, mul_assoc, hsaa, hsbb]; linarith
      rw [this, abs_lt]; exact ⟨hc3, hc4⟩

lemma idx_cases (p : Idx) : p.1 = (0, 1) ∨ p.1 = (0, 2) ∨ p.1 = (1, 0) ∨ p.1 = (1, 2) ∨
    p.1 = (2, 0) ∨ p.1 = (2, 1) := by
  revert p; decide

/-- The sign classes: two distinct same-sign "permutations" have `φ` summing to `≤ 0`. -/
lemma phi_add_le (Z : Fin 3 → ℝ) (p p' : Idx) (hne : p ≠ p') (hs : p.sgn = p'.sgn) :
    (Z p.1.1 - Z p.1.2 - |Z (third p.1.1 p.1.2)|) +
      (Z p'.1.1 - Z p'.1.2 - |Z (third p'.1.1 p'.1.2)|) ≤ 0 := by
  have a0 := le_abs_self (Z 0); have a1 := le_abs_self (Z 1); have a2 := le_abs_self (Z 2)
  have b0 := neg_abs_le (Z 0); have b1 := neg_abs_le (Z 1); have b2 := neg_abs_le (Z 2)
  have hne' : p.1 ≠ p'.1 := fun h => hne (Subtype.ext h)
  unfold Idx.sgn at hs
  rcases idx_cases p with h | h | h | h | h | h <;>
  rcases idx_cases p' with h' | h' | h' | h' | h' | h' <;>
  rw [h, h'] at hne' hs ⊢ <;> simp [third] at hne' hs ⊢ <;> linarith

namespace Q20

variable {P F : Set E5} (Q : Q20 P F)

lemma z0_lt : ⟪Q.z, Q.cF⟫ < 1 :=
  lt_of_le_of_ne (Q.cF_le _ Q.zP) (fun h => Q.znF ((Q.cF_eq _ Q.zP).2 h))

/-- Edges of `P` from a functional on the twenty vertices, at a positive level `m`. -/
lemma edge_of (L : E5) (m : ℝ) (hm : 0 < m) {p1 p2 : E5} (hp1 : p1 ∈ Q.X) (hp2 : p2 ∈ Q.X)
    (hne : p1 ≠ p2)
    (hx : ∀ a b, ⟪Q.x a b, L⟫ ≤ m ∧ (⟪Q.x a b, L⟫ = m → Q.x a b = p1 ∨ Q.x a b = p2))
    (hnx : ∀ a b, ⟪-Q.x a b, L⟫ ≤ m ∧ (⟪-Q.x a b, L⟫ = m → -Q.x a b = p1 ∨ -Q.x a b = p2))
    (hz : ⟪Q.z, L⟫ ≤ m ∧ (⟪Q.z, L⟫ = m → Q.z = p1 ∨ Q.z = p2))
    (hnz : ⟪-Q.z, L⟫ ≤ m ∧ (⟪-Q.z, L⟫ = m → -Q.z = p1 ∨ -Q.z = p2))
    (h1 : ⟪p1, L⟫ = m) (h2 : ⟪p2, L⟫ = m) :
    segment ℝ p1 p2 ∈ faces P ∧ dim (segment ℝ p1 p2) = 1 := by
  have hval : ∀ v, ⟪v, m⁻¹ • L⟫ = m⁻¹ * ⟪v, L⟫ := fun v => real_inner_smul_right _ _ _
  have hle : ∀ t : ℝ, t ≤ m → m⁻¹ * t ≤ 1 := fun t ht => by
    rw [inv_mul_le_iff₀ hm, mul_one]; exact ht
  have heq : ∀ t : ℝ, m⁻¹ * t = 1 → t = m := fun t ht => by
    field_simp at ht; linarith
  refine (segment_mem_faces_of_functional Q.hPX (m⁻¹ • L) hp1 hp2 hne ?_ ?_ ?_ ?_).imp_right
    And.left
  · intro v hv
    rw [hval]
    rcases (Q.memX v).1 hv with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | rfl | rfl
    exacts [hle _ (hx a b).1, hle _ (hnx a b).1, hle _ hz.1, hle _ hnz.1]
  · rw [hval, h1, inv_mul_cancel₀ hm.ne']
  · rw [hval, h2, inv_mul_cancel₀ hm.ne']
  · intro v hv hv1
    rw [hval] at hv1
    have hv2 := heq _ hv1
    rcases (Q.memX v).1 hv with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | rfl | rfl
    exacts [(hx a b).2 hv2, (hnx a b).2 hv2, hz.2 hv2, hnz.2 hv2]

lemma xvals (p q : Idx) {α β : ℝ} (hα1 : α < 1) (hα2 : -1 < α) (hβ1 : β < 1) (hβ2 : -1 < β)
    (a b : Fin 3) :
    (⟪Q.x a b, Q.Lv (potA p α) (potA q β)⟫ ≤ 1 ∧
      (⟪Q.x a b, Q.Lv (potA p α) (potA q β)⟫ = 1 → a = p.1.1 ∧ b = q.1.1)) ∧
    (⟪-Q.x a b, Q.Lv (potA p α) (potA q β)⟫ ≤ 1 ∧
      (⟪-Q.x a b, Q.Lv (potA p α) (potA q β)⟫ = 1 → a = p.1.2 ∧ b = q.1.2)) := by
  rw [inner_neg_left, Q.val_x]
  obtain ⟨h1, h2⟩ := conv_le_one (Q.w1_pos a b) (Q.w2_pos a b) (Q.w_sum a b) (potA_le_one p hα1 a)
    (potA_le_one q hβ1 b)
  obtain ⟨h3, h4⟩ := conv_le_one (Q.w1_pos a b) (Q.w2_pos a b) (Q.w_sum a b)
    (neg_potA_le_one p hα2 a) (neg_potA_le_one q hβ2 b)
  refine ⟨⟨h1, fun he => ⟨eq_of_potA_eq_one p hα1 (h2 he).1, eq_of_potA_eq_one q hβ1 (h2 he).2⟩⟩,
    ⟨by linarith, fun he => ?_⟩⟩
  have h5 := h4 (by linarith)
  exact ⟨eq_of_neg_potA_eq_one p hα2 h5.1, eq_of_neg_potA_eq_one q hβ2 h5.2⟩

lemma val_fst (c : Idx × Idx) (α β : ℝ) :
    ⟪Q.x c.1.1.1 c.2.1.1, Q.Lv (potA c.1 α) (potA c.2 β)⟫ = 1 := by
  rw [Q.val_x, potA_fst, potA_fst, one_mul, one_mul, Q.w_sum]

lemma val_snd (c : Idx × Idx) (α β : ℝ) :
    ⟪-Q.x c.1.1.2 c.2.1.2, Q.Lv (potA c.1 α) (potA c.2 β)⟫ = 1 := by
  rw [inner_neg_left, Q.val_x, potA_snd, potA_snd]
  linarith [Q.w_sum c.1.1.2 c.2.1.2]

/-- `φ` values. -/
noncomputable def phiZ (p : Idx) : ℝ := Q.Zc p.1.1 - Q.Zc p.1.2 - |Q.Zc (third p.1.1 p.1.2)|
noncomputable def phiW (q : Idx) : ℝ := Q.Wc q.1.1 - Q.Wc q.1.2 - |Q.Wc (third q.1.1 q.1.2)|

lemma A_sub (c : Idx × Idx) : Q.A c - |Q.aa c| - |Q.bb c| = Q.phiZ c.1 + Q.phiW c.2 := by
  simp only [A, aa, bb, phiZ, phiW]; ring

/-- **No two candidates with `z` above in the same triangle.** -/
lemma up_conflict (c d : Idx × Idx) (hc : Q.up c) (hd : Q.up d) (h1 : c.1 ≠ d.1)
    (h2 : c.1.sgn = d.1.sgn) (h3 : c.2 ≠ d.2) (h4 : c.2.sgn = d.2.sgn) : False := by
  have e1 := phi_add_le Q.Zc c.1 d.1 h1 h2
  have e2 := phi_add_le Q.Wc c.2 d.2 h3 h4
  have f1 := hc.1; have f2 := hd.1
  rw [Q.A_sub] at f1 f2
  simp only [phiZ, phiW] at f1 f2
  linarith

lemma A_swap (c : Idx × Idx) : Q.A (c.1.swap, c.2.swap) = -Q.A c := by
  simp only [A, Idx.swap]; ring

lemma aa_swap (c : Idx × Idx) : Q.aa (c.1.swap, c.2.swap) = Q.aa c := by
  simp only [aa]; rw [third_swap]

lemma bb_swap (c : Idx × Idx) : Q.bb (c.1.swap, c.2.swap) = Q.bb c := by
  simp only [bb]; rw [third_swap]

lemma dn_iff (c : Idx × Idx) : Q.dn c ↔ Q.up (c.1.swap, c.2.swap) := by
  simp only [dn, up, Q.A_swap, Q.aa_swap, Q.bb_swap]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 ⟨h.1, h.2.1, by linarith [h.2.2]⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 ⟨h.1, h.2.1, by linarith [h.2.2]⟩⟩

lemma not_up_and_dn (c : Idx × Idx) (hu : Q.up c) (hd : Q.dn c) : False := by
  have := hu.1; have := hd.1
  linarith [abs_nonneg (Q.aa c), abs_nonneg (Q.bb c)]

section cs

variable (hP : IsCSPolytope5 P) (hF : F ∈ faces P) (h4 : dim F = 4)
include hP hF h4

lemma disj : ∀ y ∈ F, -y ∉ F := by
  have hFP : F ≠ P := hP.ne_of_dim_ne (by rw [h4]; norm_num)
  exact fun y hy hny => hFP (hP.eq_of_mem_of_neg_mem hF hy hny)

omit hF h4 in
lemma z0_gt : -1 < ⟪Q.z, Q.cF⟫ := by
  have hnzP : -Q.z ∈ P := hP.symm _ Q.zP
  have := lt_of_le_of_ne (Q.cF_le _ hnzP) (fun h => Q.nznF ((Q.cF_eq _ hnzP).2 h))
  rw [inner_neg_left] at this
  linarith

lemma x_ne_nx (a b a' b' : Fin 3) : Q.x a b ≠ -Q.x a' b' := fun h =>
  disj hP hF h4 _ (Q.memF a' b') (by rw [← h]; exact Q.memF a b)

omit hP hF h4 in
lemma x_ne_z (a b : Fin 3) : Q.x a b ≠ Q.z := fun h => Q.znF (h ▸ Q.memF a b)

omit hP hF h4 in
lemma nx_ne_z (a b : Fin 3) : -Q.x a b ≠ Q.z := fun h =>
  Q.nznF (by rw [← h, neg_neg]; exact Q.memF a b)

omit hP hF h4 in
lemma x_ne_nz (a b : Fin 3) : Q.x a b ≠ -Q.z := fun h => Q.nznF (h ▸ Q.memF a b)

omit hP hF h4 in
lemma nx_ne_nz (a b : Fin 3) : -Q.x a b ≠ -Q.z := fun h =>
  Q.znF (by rw [neg_inj] at h; rw [← h]; exact Q.memF a b)

/-- **The side edge survives** when its interval meets `(-1, 1)`. -/
lemma side_mem_main (c : Idx × Idx) (h1 : Q.A c - |Q.aa c| - |Q.bb c| < 1)
    (h2 : -Q.A c - |Q.aa c| - |Q.bb c| < 1) : Q.side c ∈ faces P ∧ dim (Q.side c) = 1 := by
  obtain ⟨α, β, hα2, hα1, hβ2, hβ1, hsmall⟩ := exists_small _ _ _ h1 h2
  have hzv := Q.val_z_potA c α β
  rw [abs_lt] at hsmall
  refine Q.edge_of (Q.Lv (potA c.1 α) (potA c.2 β)) 1 one_pos (Q.x_mem _ _) (Q.nx_mem _ _)
    (Q.x_ne_nx hP hF h4 _ _ _ _) ?_ ?_ ?_ ?_ (Q.val_fst c α β) (Q.val_snd c α β)
  · intro a b
    obtain ⟨⟨e1, e2⟩, -⟩ := Q.xvals c.1 c.2 hα1 hα2 hβ1 hβ2 a b
    exact ⟨e1, fun he => by obtain ⟨rfl, rfl⟩ := e2 he; exact Or.inl rfl⟩
  · intro a b
    obtain ⟨-, ⟨e1, e2⟩⟩ := Q.xvals c.1 c.2 hα1 hα2 hβ1 hβ2 a b
    exact ⟨e1, fun he => by obtain ⟨rfl, rfl⟩ := e2 he; exact Or.inr rfl⟩
  · rw [hzv]
    exact ⟨by linarith, fun h => absurd h (by linarith)⟩
  · rw [inner_neg_left, hzv]
    exact ⟨by linarith, fun h => absurd h (by linarith)⟩

/-- **The side edge survives** in the degenerate ties (a triangle face). -/
lemma side_mem_deg (c : Idx × Idx) (ha : Q.aa c = 0) (hb : Q.bb c = 0)
    (hA : Q.A c = 1 ∨ Q.A c = -1) : Q.side c ∈ faces P ∧ dim (Q.side c) = 1 := by
  set L := Q.Lv (potA c.1 0) (potA c.2 0) with hL
  have hzv : ⟪Q.z, L⟫ = Q.A c := by rw [hL, Q.val_z_potA, ha, hb]; ring
  have hxv := fun a b => Q.xvals c.1 c.2 (α := 0) (β := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) a b
  have hp := Q.ext c.1.1.1 c.2.1.1
  have hq := hP.neg_mem_extremePoints (Q.ext c.1.1.2 c.2.1.2)
  have hpq := Q.x_ne_nx hP hF h4 c.1.1.1 c.2.1.1 c.1.1.2 c.2.1.2
  -- the third vertex `r` on the level set: `z` or `-z`
  obtain ⟨r, hrX, hrext, hr1, hrz, hrp, hrq, hrother⟩ : ∃ r ∈ Q.X, r ∈ P.extremePoints ℝ ∧
      ⟪r, L⟫ = 1 ∧ (r = Q.z ∨ r = -Q.z) ∧ Q.x c.1.1.1 c.2.1.1 ≠ r ∧ -Q.x c.1.1.2 c.2.1.2 ≠ r ∧
      (⟪Q.z, L⟫ = 1 → Q.z = r) ∧ (⟪-Q.z, L⟫ = 1 → -Q.z = r) := by
    rcases hA with hA | hA
    · refine ⟨Q.z, Q.z_mem, Q.zext, (by rw [hzv, hA]), Or.inl rfl, Q.x_ne_z _ _, Q.nx_ne_z _ _,
        fun _ => rfl, fun h => ?_⟩
      rw [inner_neg_left, hzv, hA] at h; norm_num at h
    · refine ⟨-Q.z, Q.nz_mem, hP.neg_mem_extremePoints Q.zext,
        (by rw [inner_neg_left, hzv, hA]; norm_num), Or.inr rfl, Q.x_ne_nz _ _, Q.nx_ne_nz _ _,
        fun h => ?_, fun _ => rfl⟩
      rw [hzv, hA] at h; norm_num at h
  refine segment_mem_faces_of_functional3 Q.hPX L (Q.x_mem _ _) (Q.nx_mem _ _) hrX hpq ?_ ?_
    (Q.val_fst c 0 0) (Q.val_snd c 0 0) ?_
  · intro hmem
    obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.1 hmem
    have hsum : s + t = 1 := by
      have hv1 : ⟪Q.x c.1.1.1 c.2.1.1, L⟫ = 1 := Q.val_fst c 0 0
      have hv2 : ⟪-Q.x c.1.1.2 c.2.1.2, L⟫ = 1 := Q.val_snd c 0 0
      have := congrArg (fun w => ⟪w, L⟫) hst
      simp only [inner_add_left, real_inner_smul_left, hr1] at this
      rw [hv1, hv2] at this
      linarith
    exact extreme_not_collinear hp hq hrext hpq hrp hrq s
      (by rw [← hst, show t = 1 - s by linarith])
  · intro v hv
    rcases (Q.memX v).1 hv with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | rfl | rfl
    · exact (hxv a b).1.1
    · exact (hxv a b).2.1
    · rw [hzv]; rcases hA with hA | hA <;> rw [hA] <;> norm_num
    · rw [inner_neg_left, hzv]; rcases hA with hA | hA <;> rw [hA] <;> norm_num
  · intro v hv hv1
    rcases (Q.memX v).1 hv with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | rfl | rfl
    · obtain ⟨rfl, rfl⟩ := (hxv a b).1.2 hv1; exact Or.inl rfl
    · obtain ⟨rfl, rfl⟩ := (hxv a b).2.2 hv1; exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (hrother.1 hv1))
    · exact Or.inr (Or.inr (hrother.2 hv1))

/-- **Survivors**: neither above nor below. -/
lemma side_mem (c : Idx × Idx) (hu : ¬ Q.up c) (hd : ¬ Q.dn c) :
    Q.side c ∈ faces P ∧ dim (Q.side c) = 1 := by
  by_cases h1 : Q.A c - |Q.aa c| - |Q.bb c| < 1
  · by_cases h2 : -Q.A c - |Q.aa c| - |Q.bb c| < 1
    · exact Q.side_mem_main hP hF h4 c h1 h2
    · push_neg at h2
      have : Q.aa c = 0 ∧ Q.bb c = 0 ∧ Q.A c = -1 := by
        by_contra h; exact hd ⟨h2, h⟩
      exact Q.side_mem_deg hP hF h4 c this.1 this.2.1 (Or.inr this.2.2)
  · push_neg at h1
    have : Q.aa c = 0 ∧ Q.bb c = 0 ∧ Q.A c = 1 := by
      by_contra h; exact hu ⟨h1, h⟩
    exact Q.side_mem_deg hP hF h4 c this.1 this.2.1 (Or.inl this.2.2)

/-- **Two edges at `z`** when `z` lies above a candidate (tilting by the facet functional). -/
lemma adj_up (c : Idx × Idx) (hup : Q.up c) :
    (segment ℝ Q.z (Q.x c.1.1.1 c.2.1.1) ∈ faces P ∧
      dim (segment ℝ Q.z (Q.x c.1.1.1 c.2.1.1)) = 1) ∧
    (segment ℝ Q.z (-Q.x c.1.1.2 c.2.1.2) ∈ faces P ∧
      dim (segment ℝ Q.z (-Q.x c.1.1.2 c.2.1.2)) = 1) := by
  have hA1 : 1 < Q.A c := by
    by_contra hle
    push_neg at hle
    have h0 := hup.1
    have ha : Q.aa c = 0 := abs_eq_zero.1 (by linarith [abs_nonneg (Q.aa c), abs_nonneg (Q.bb c)])
    have hb : Q.bb c = 0 := abs_eq_zero.1 (by linarith [abs_nonneg (Q.aa c), abs_nonneg (Q.bb c)])
    rw [ha, hb, abs_zero] at h0
    exact hup.2 ⟨ha, hb, by linarith⟩
  set L0 := Q.Lv (potA c.1 0) (potA c.2 0) with hL0
  have hz0 : ⟪Q.z, L0⟫ = Q.A c := by rw [hL0, Q.val_z_potA]; ring
  have hxv := fun a b => Q.xvals c.1 c.2 (α := 0) (β := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) a b
  set z0 := ⟪Q.z, Q.cF⟫ with hz0def
  have hz1 : z0 < 1 := Q.z0_lt
  have hz2 : -1 < z0 := Q.z0_gt hP
  have hval : ∀ v : E5, ∀ s : ℝ, ⟪v, L0 + s • Q.cF⟫ = ⟪v, L0⟫ + s * ⟪v, Q.cF⟫ := fun v s => by
    rw [inner_add_right, real_inner_smul_right]
  constructor
  · -- tilt up: `z` and `x i j`
    set s := (Q.A c - 1) / (1 - z0) with hs
    have hspos : 0 < s := div_pos (by linarith) (by linarith)
    have hsz : Q.A c + s * z0 = 1 + s := by
      have hne : 1 - z0 ≠ 0 := by linarith
      rw [hs]; field_simp; ring
    rw [segment_symm]
    refine Q.edge_of (L0 + s • Q.cF) (1 + s) (by linarith) (Q.x_mem _ _) Q.z_mem (Q.x_ne_z _ _)
      ?_ ?_ ?_ ?_ ?_ ?_
    · intro a b
      rw [hval, Q.cFx, mul_one]
      obtain ⟨⟨e1, e2⟩, -⟩ := hxv a b
      exact ⟨by linarith, fun he => by obtain ⟨rfl, rfl⟩ := e2 (by linarith); exact Or.inl rfl⟩
    · intro a b
      rw [hval, inner_neg_left, inner_neg_left, Q.cFx]
      obtain ⟨-, ⟨e1, -⟩⟩ := hxv a b
      rw [inner_neg_left] at e1
      exact ⟨by linarith, fun he => absurd he (by linarith)⟩
    · rw [hval, hz0, ← hz0def, hsz]
      exact ⟨le_refl _, fun _ => Or.inr rfl⟩
    · rw [hval, inner_neg_left, inner_neg_left, hz0, ← hz0def]
      exact ⟨by linarith, fun he => absurd he (by linarith)⟩
    · rw [hval, Q.cFx, mul_one, Q.val_fst]
    · rw [hval, hz0, ← hz0def, hsz]
  · -- tilt down: `z` and `-x i' j'`
    set s := (Q.A c - 1) / (1 + z0) with hs
    have hspos : 0 < s := div_pos (by linarith) (by linarith)
    have hsz : Q.A c - s * z0 = 1 + s := by
      have hne : 1 + z0 ≠ 0 := by linarith
      rw [hs]; field_simp; ring
    have hval' : ∀ v : E5, ⟪v, L0 - s • Q.cF⟫ = ⟪v, L0⟫ - s * ⟪v, Q.cF⟫ := fun v => by
      rw [inner_sub_right, real_inner_smul_right]
    rw [segment_symm]
    refine Q.edge_of (L0 - s • Q.cF) (1 + s) (by linarith) (Q.nx_mem _ _) Q.z_mem (Q.nx_ne_z _ _)
      ?_ ?_ ?_ ?_ ?_ ?_
    · intro a b
      rw [hval', Q.cFx, mul_one]
      obtain ⟨⟨e1, -⟩, -⟩ := hxv a b
      exact ⟨by linarith, fun he => absurd he (by linarith)⟩
    · intro a b
      rw [hval', inner_neg_left (Q.x a b) Q.cF, Q.cFx]
      obtain ⟨-, ⟨e1, e2⟩⟩ := hxv a b
      exact ⟨by linarith, fun he => by obtain ⟨rfl, rfl⟩ := e2 (by linarith); exact Or.inl rfl⟩
    · rw [hval', hz0, ← hz0def, hsz]
      exact ⟨le_refl _, fun _ => Or.inr rfl⟩
    · rw [hval', inner_neg_left, inner_neg_left, hz0, ← hz0def]
      exact ⟨by linarith, fun he => absurd he (by linarith)⟩
    · rw [hval', inner_neg_left (Q.x _ _) Q.cF, Q.cFx, Q.val_snd]; ring
    · rw [hval', hz0, ← hz0def, hsz]

end cs

end Q20

/-! ### Membership of special vertices in the edges -/

namespace Q20

variable {P F : Set E5} (Q : Q20 P F)

section cs

variable (hP : IsCSPolytope5 P) (hF : F ∈ faces P) (h4 : dim F = 4)
include hP

omit hP in
lemma nxP (a b : Fin 3) (hP : IsCSPolytope5 P) : -Q.x a b ∈ P := hP.symm _ (Q.xP a b)

lemma nzext : -Q.z ∈ P.extremePoints ℝ := hP.neg_mem_extremePoints Q.zext

lemma nxext (a b : Fin 3) : -Q.x a b ∈ P.extremePoints ℝ := hP.neg_mem_extremePoints (Q.ext a b)

include hF h4

lemma z_nmem_side (c : Idx × Idx) : Q.z ∉ Q.side c := fun h => by
  rcases eq_of_extreme_mem_segment Q.zext (Q.xP _ _) (Q.nxP _ _ hP) h with h1 | h1
  · exact Q.x_ne_z _ _ h1.symm
  · exact Q.nx_ne_z _ _ h1.symm

lemma nz_nmem_side (c : Idx × Idx) : -Q.z ∉ Q.side c := fun h => by
  rcases eq_of_extreme_mem_segment (Q.nzext hP) (Q.xP _ _) (Q.nxP _ _ hP) h with h1 | h1
  · exact Q.x_ne_nz _ _ h1.symm
  · exact Q.nx_ne_nz _ _ h1.symm

lemma nz_nmem_zx (a b : Fin 3) : -Q.z ∉ segment ℝ Q.z (Q.x a b) := fun h => by
  rcases eq_of_extreme_mem_segment (Q.nzext hP) Q.zP (Q.xP _ _) h with h1 | h1
  · exact Q.zz h1.symm
  · exact Q.x_ne_nz _ _ h1.symm

lemma nz_nmem_znx (a b : Fin 3) : -Q.z ∉ segment ℝ Q.z (-Q.x a b) := fun h => by
  rcases eq_of_extreme_mem_segment (Q.nzext hP) Q.zP (Q.nxP _ _ hP) h with h1 | h1
  · exact Q.zz h1.symm
  · exact Q.nx_ne_nz _ _ h1.symm

lemma side_inj (c d : Idx × Idx) (h : Q.side c = Q.side d) : c = d := by
  have h1 : Q.x c.1.1.1 c.2.1.1 ∈ Q.side d := h ▸ left_mem_segment ℝ _ _
  have h2 : -Q.x c.1.1.2 c.2.1.2 ∈ Q.side d := h ▸ right_mem_segment ℝ _ _
  rcases eq_of_extreme_mem_segment (Q.ext _ _) (Q.xP _ _) (Q.nxP _ _ hP) h1 with e1 | e1
  · rcases eq_of_extreme_mem_segment (Q.nxext hP _ _) (Q.xP _ _) (Q.nxP _ _ hP) h2 with e2 | e2
    · exact absurd e2.symm (Q.x_ne_nx hP hF h4 _ _ _ _)
    · have f1 := Q.inj _ _ _ _ e1
      have f2 := Q.inj _ _ _ _ (neg_injective e2)
      exact cells_inj c d (Prod.ext f1.1 f1.2) (Prod.ext f2.1 f2.2)
  · exact absurd e1 (Q.x_ne_nx hP hF h4 _ _ _ _)

lemma zx_inj (a b a' b' : Fin 3) (h : segment ℝ Q.z (Q.x a b) = segment ℝ Q.z (Q.x a' b')) :
    (a, b) = (a', b') := by
  have h1 : Q.x a b ∈ segment ℝ Q.z (Q.x a' b') := h ▸ right_mem_segment ℝ _ _
  rcases eq_of_extreme_mem_segment (Q.ext _ _) Q.zP (Q.xP _ _) h1 with e | e
  · exact absurd e (Q.x_ne_z _ _)
  · have := Q.inj _ _ _ _ e; exact Prod.ext this.1 this.2

lemma znx_inj (a b a' b' : Fin 3) (h : segment ℝ Q.z (-Q.x a b) = segment ℝ Q.z (-Q.x a' b')) :
    (a, b) = (a', b') := by
  have h1 : -Q.x a b ∈ segment ℝ Q.z (-Q.x a' b') := h ▸ right_mem_segment ℝ _ _
  rcases eq_of_extreme_mem_segment (Q.nxext hP _ _) Q.zP (Q.nxP _ _ hP) h1 with e | e
  · exact absurd e (Q.nx_ne_z _ _)
  · have := Q.inj _ _ _ _ (neg_injective e); exact Prod.ext this.1 this.2

lemma zx_ne_znx (a b a' b' : Fin 3) : segment ℝ Q.z (Q.x a b) ≠ segment ℝ Q.z (-Q.x a' b') :=
  fun h => by
  have h1 : -Q.x a' b' ∈ segment ℝ Q.z (Q.x a b) := h ▸ right_mem_segment ℝ _ _
  rcases eq_of_extreme_mem_segment (Q.nxext hP _ _) Q.zP (Q.xP _ _) h1 with e | e
  · exact Q.nx_ne_z _ _ e
  · exact Q.x_ne_nx hP hF h4 _ _ _ _ e.symm

end cs

end Q20

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **A `Δ2 × Δ2` facet in a cs 5-polytope with twenty vertices forces 62 edges.** -/
theorem IsCSPolytope5.edges_ge_62_of_qRow (hv : fvec P 0 = 20) {F : Set E5} (hF : F ∈ faces P)
    (h4 : dim F = 4) (hrow : faceRow P F = qRow) : 62 ≤ fvec P 1 := by
  classical
  obtain ⟨Q⟩ := hP.q20 hv hF h4 hrow
  have hdisj := Q20.disj hP hF h4
  -- the three outcomes
  set Up := Finset.univ.filter (fun c : Idx × Idx => Q.up c) with hUp
  set Dn := Finset.univ.filter (fun c : Idx × Idx => Q.dn c) with hDn
  set Sv := Finset.univ.filter (fun c : Idx × Idx => ¬ Q.up c ∧ ¬ Q.dn c) with hSv
  have hcard : Up.card + Dn.card + Sv.card = 36 := by
    have h1 : (Finset.univ : Finset (Idx × Idx)).card = 36 := by rfl
    have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun c : Idx × Idx => Q.up c)
    have h3 := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun c : Idx × Idx => ¬ Q.up c)) (fun c => Q.dn c)
    have e1 : (Finset.univ.filter (fun c : Idx × Idx => ¬ Q.up c)).filter (fun c => Q.dn c) = Dn := by
      rw [hDn, Finset.filter_filter]
      apply Finset.filter_congr
      intro c _
      exact ⟨fun h => h.2, fun h => ⟨fun hu => Q.not_up_and_dn c hu h, h⟩⟩
    have e2 : (Finset.univ.filter (fun c : Idx × Idx => ¬ Q.up c)).filter (fun c => ¬ Q.dn c) = Sv := by
      rw [hSv, Finset.filter_filter]
    rw [e1, e2] at h3
    rw [← hUp] at h2
    omega
  have hDnUp : Dn.card = Up.card := by
    refine Finset.card_bij (fun c _ => (c.1.swap, c.2.swap)) ?_ ?_ ?_
    · intro c hc
      rw [hDn, Finset.mem_filter] at hc
      rw [hUp, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (Q.dn_iff c).1 hc.2⟩
    · intro c1 _ c2 _ h
      simp only [Prod.mk.injEq] at h
      have e1 : c1.1 = c2.1 := by
        have := congrArg Subtype.val h.1
        simp only [Idx.swap, Prod.mk.injEq] at this
        exact Subtype.ext (Prod.ext this.2 this.1)
      have e2 : c1.2 = c2.2 := by
        have := congrArg Subtype.val h.2
        simp only [Idx.swap, Prod.mk.injEq] at this
        exact Subtype.ext (Prod.ext this.2 this.1)
      exact Prod.ext e1 e2
    · intro d hd
      rw [hUp, Finset.mem_filter] at hd
      refine ⟨(d.1.swap, d.2.swap), ?_, ?_⟩
      · rw [hDn, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, (Q.dn_iff _).2 ?_⟩
        have hs1 : d.1.swap.swap = d.1 := Subtype.ext rfl
        have hs2 : d.2.swap.swap = d.2 := Subtype.ext rfl
        simp only [hs1, hs2]
        exact hd.2
      · exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
  have hcomb := card_le_cells_add_five Up (fun c hc d hd h1 h2 h3 h4 =>
    Q.up_conflict c d (Finset.mem_filter.1 hc).2 (Finset.mem_filter.1 hd).2 h1 h2 h3 h4)
  -- the edge families
  set E1 := {G : Set E5 | G ∈ faces P ∧ dim G = 1} with hE1
  set EF := {G : Set E5 | G ∈ faces P ∧ G ⊆ F ∧ dim G = 1} with hEF
  set EnF := {G : Set E5 | G ∈ faces P ∧ G ⊆ -F ∧ dim G = 1} with hEnF
  set ES := Q.side '' (Sv : Set (Idx × Idx)) with hES
  set EZ1 := (fun c : Fin 3 × Fin 3 => segment ℝ Q.z (Q.x c.1 c.2)) ''
    ((Up.image cellF : Finset (Fin 3 × Fin 3)) : Set (Fin 3 × Fin 3)) with hEZ1
  set EZ2 := (fun c : Fin 3 × Fin 3 => segment ℝ Q.z (-Q.x c.1 c.2)) ''
    ((Up.image cellS : Finset (Fin 3 × Fin 3)) : Set (Fin 3 × Fin 3)) with hEZ2
  set EZ := EZ1 ∪ EZ2 with hEZ
  set EmZ := (fun G : Set E5 => -G) '' EZ with hEmZ
  have hfin : ∀ S : Set (Set E5), (∀ G ∈ S, G ∈ faces P) → S.Finite :=
    fun S hS => hP.faces_finite.subset hS
  -- memberships
  have hESsub : ES ⊆ E1 := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
    exact Q.side_mem hP hF h4 c hc'.1 hc'.2
  have hEZ1sub : EZ1 ⊆ E1 := by
    rintro _ ⟨cell, hcell, rfl⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hcell)
    exact (Q.adj_up hP hF h4 c (Finset.mem_filter.1 hc).2).1
  have hEZ2sub : EZ2 ⊆ E1 := by
    rintro _ ⟨cell, hcell, rfl⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hcell)
    exact (Q.adj_up hP hF h4 c (Finset.mem_filter.1 hc).2).2
  have hEZsub : EZ ⊆ E1 := Set.union_subset hEZ1sub hEZ2sub
  have hEmZsub : EmZ ⊆ E1 := by
    rintro _ ⟨G, hG, rfl⟩
    obtain ⟨h1, h2⟩ := hEZsub hG
    exact ⟨neg_mem_faces hP.symm h1, by rw [dim_neg]; exact h2⟩
  -- special points
  have hzEZ : ∀ G ∈ EZ, Q.z ∈ G := by
    rintro _ (⟨cell, -, rfl⟩ | ⟨cell, -, rfl⟩) <;> exact left_mem_segment ℝ _ _
  have hnzEZ : ∀ G ∈ EZ, -Q.z ∉ G := by
    rintro _ (⟨cell, -, rfl⟩ | ⟨cell, -, rfl⟩)
    · exact Q.nz_nmem_zx hP hF h4 _ _
    · exact Q.nz_nmem_znx hP hF h4 _ _
  have hnzEmZ : ∀ G ∈ EmZ, -Q.z ∈ G := by
    rintro _ ⟨G, hG, rfl⟩
    exact Set.neg_mem_neg.2 (hzEZ G hG)
  have hzEmZ : ∀ G ∈ EmZ, Q.z ∉ G := by
    rintro _ ⟨G, hG, rfl⟩ h
    exact hnzEZ G hG (by simpa using Set.neg_mem_neg.2 h)
  -- disjointness
  have hznF' : Q.z ∉ -F := fun h => Q.nznF (Set.mem_neg.1 h)
  have hnznF' : -Q.z ∉ -F := fun h => Q.znF (by simpa using Set.mem_neg.1 h)
  have d1 : Disjoint EF EnF := by
    rw [Set.disjoint_left]
    rintro G ⟨hG, hGF, -⟩ ⟨-, hGnF, -⟩
    obtain ⟨y, hy⟩ := hG.1
    exact hdisj y (hGF hy) (Set.mem_neg.1 (hGnF hy))
  have d2 : Disjoint (EF ∪ EnF) ES := by
    rw [Set.disjoint_left]
    rintro G hG ⟨c, -, rfl⟩
    rcases hG with ⟨-, hGF, -⟩ | ⟨-, hGnF, -⟩
    · exact hdisj _ (Q.memF c.1.1.2 c.2.1.2) (by simpa using hGF (right_mem_segment ℝ _ _))
    · exact hdisj _ (Q.memF c.1.1.1 c.2.1.1) (Set.mem_neg.1 (hGnF (left_mem_segment ℝ _ _)))
  have d3 : Disjoint (EF ∪ EnF ∪ ES) EZ := by
    rw [Set.disjoint_left]
    intro G hG hGZ
    have hz := hzEZ G hGZ
    rcases hG with (⟨-, hGF, -⟩ | ⟨-, hGnF, -⟩) | ⟨c, -, rfl⟩
    · exact Q.znF (hGF hz)
    · exact hznF' (hGnF hz)
    · exact Q.z_nmem_side hP hF h4 c hz
  have d4 : Disjoint (EF ∪ EnF ∪ ES ∪ EZ) EmZ := by
    rw [Set.disjoint_left]
    intro G hG hGZ
    have hz := hnzEmZ G hGZ
    rcases hG with ((⟨-, hGF, -⟩ | ⟨-, hGnF, -⟩) | ⟨c, -, rfl⟩) | hG
    · exact Q.nznF (hGF hz)
    · exact hnznF' (hGnF hz)
    · exact Q.nz_nmem_side hP hF h4 c hz
    · exact hnzEZ G hG hz
  -- cardinalities
  have hEFc : EF.ncard = 18 := congrArg Row.e hrow
  have hEnFc : EnF.ncard = 18 := by
    have h1 : EnF.ncard = cnt P (-F) 1 := rfl
    rw [h1, hP.cnt_neg]
    exact hEFc
  have hESc : ES.ncard = Sv.card := by
    rw [hES, Set.InjOn.ncard_image (fun c _ d _ h => Q.side_inj hP hF h4 c d h),
      Set.ncard_coe_finset]
  have hEZ1c : EZ1.ncard = (Up.image cellF).card := by
    rw [hEZ1, Set.InjOn.ncard_image (fun c _ d _ h => Q.zx_inj hP hF h4 c.1 c.2 d.1 d.2 h),
      Set.ncard_coe_finset]
  have hEZ2c : EZ2.ncard = (Up.image cellS).card := by
    rw [hEZ2, Set.InjOn.ncard_image (fun c _ d _ h => Q.znx_inj hP hF h4 c.1 c.2 d.1 d.2 h),
      Set.ncard_coe_finset]
  have dZ : Disjoint EZ1 EZ2 := by
    rw [Set.disjoint_left]
    rintro _ ⟨c, -, rfl⟩ ⟨d, -, hd⟩
    exact Q.zx_ne_znx hP hF h4 c.1 c.2 d.1 d.2 hd.symm
  have hEZ1fin : EZ1.Finite := (Finset.finite_toSet _).image _
  have hEZ2fin : EZ2.Finite := (Finset.finite_toSet _).image _
  have hEZc : EZ.ncard = (Up.image cellF).card + (Up.image cellS).card := by
    rw [hEZ, Set.ncard_union_eq dZ hEZ1fin hEZ2fin, hEZ1c, hEZ2c]
  have hEmZc : EmZ.ncard = EZ.ncard := by
    rw [hEmZ]
    exact Set.InjOn.ncard_image (fun G _ G' _ h => by simpa using h)
  have hEFfin : EF.Finite := hfin _ fun G hG => hG.1
  have hEnFfin : EnF.Finite := hfin _ fun G hG => hG.1
  have hESfin : ES.Finite := (Finset.finite_toSet _).image _
  have hEZfin : EZ.Finite := hEZ1fin.union hEZ2fin
  have hEmZfin : EmZ.Finite := hEZfin.image _
  have hE1fin : E1.Finite := hfin _ fun G hG => hG.1
  have hsub : EF ∪ EnF ∪ ES ∪ EZ ∪ EmZ ⊆ E1 := by
    refine Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset ?_ ?_) hESsub)
      hEZsub) hEmZsub
    · exact fun G hG => ⟨hG.1, hG.2.2⟩
    · exact fun G hG => ⟨hG.1, hG.2.2⟩
  have htot : (EF ∪ EnF ∪ ES ∪ EZ ∪ EmZ).ncard = 36 + Sv.card + 2 * EZ.ncard := by
    rw [Set.ncard_union_eq d4 (((hEFfin.union hEnFfin).union hESfin).union hEZfin) hEmZfin,
      Set.ncard_union_eq d3 ((hEFfin.union hEnFfin).union hESfin) hEZfin,
      Set.ncard_union_eq d2 (hEFfin.union hEnFfin) hESfin,
      Set.ncard_union_eq d1 hEFfin hEnFfin, hEFc, hEnFc, hESc, hEmZc]
    ring
  have hle := Set.ncard_le_ncard hsub hE1fin
  rw [htot, hEZc] at hle
  have h1 : fvec P 1 = E1.ncard := rfl
  rw [h1]
  omega

end cs

end Kalai5
