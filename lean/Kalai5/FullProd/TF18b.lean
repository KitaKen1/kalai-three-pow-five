import Kalai5.FullProd.TF18a

/-!
# A facet `Δ1 × Δ3` with one extra antipodal pair: side edges

Eighteen vertices: the eight vertices `x s k` of `F`, their negatives, and `±z`.

* **Opposite-sign candidates** `side (s, p) = [x s k, -x s̄ k']` (`p = (k, k')`): the potentials
  `potu s`, `potv p β` at `τ ∈ (0, τm]` are admissible; at `z` they take the value
  `Aop + Σ β Wc + τ K`.  With the corner bounds `CU : Aop - Sabs ≥ 1`, `CD : Aop + Sabs ≤ -1`:
  `¬CU ∧ ¬CD` gives the edge (`side_edge`); `CU` and not an edge gives two edges at `z`
  (`adj_opp`).
* **Same-sign candidates** `sideS p = [x s0 k, -x s0 k']` (only when `γ (oth s0) > 0`): the corner
  potentials `potS s0 α`, `potv p β` (value `α Zc + Asm + Σ β Wc`).
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The negative of a segment. -/
lemma neg_segment_eq {d : ℕ} (a b : E d) : -(segment ℝ a b) = segment ℝ (-a) (-b) := by
  ext y
  simp only [Set.mem_neg, segment, Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, t, hs, ht, hst, h⟩
    exact ⟨s, t, hs, ht, hst, by rw [smul_neg, smul_neg, ← neg_add, h, neg_neg]⟩
  · rintro ⟨s, t, hs, ht, hst, h⟩
    exact ⟨s, t, hs, ht, hst, by rw [← h, smul_neg, smul_neg, neg_add, neg_neg, neg_neg]⟩

/-- A sign. -/
noncomputable def sgnR (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

lemma sgnR_mul (x : ℝ) : sgnR x * x = |x| := by
  unfold sgnR; split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h)]; ring

lemma sgnR_cases (x : ℝ) : sgnR x = 1 ∨ sgnR x = -1 := by unfold sgnR; split_ifs <;> simp

lemma sum_sgn (S : Finset (Fin 4)) (t : ℝ) (W : Fin 4 → ℝ) :
    ∑ j ∈ S, (t * sgnR (W j)) * W j = t * ∑ j ∈ S, |W j| := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_assoc, sgnR_mul]

lemma sgn_bounds {t : ℝ} (ht1 : t < 1) (ht2 : -1 < t) (W : Fin 4 → ℝ) :
    (∀ j, t * sgnR (W j) < 1) ∧ (∀ j, -1 < t * sgnR (W j)) := by
  refine ⟨fun j => ?_, fun j => ?_⟩ <;> rcases sgnR_cases (W j) with h | h <;> rw [h] <;> linarith

/-- Choosing a small parameter: if `|C| < 1` then `|C + τ K| < 1` for some `τ ∈ (0, τm]`. -/
lemma exists_tau {C K τm : ℝ} (hC : |C| < 1) (hτm : 0 < τm) :
    ∃ τ, 0 < τ ∧ τ ≤ τm ∧ |C + τ * K| < 1 := by
  set τ := min τm ((1 - |C|) / (2 * (|K| + 1))) with hτ
  have hden : 0 < 2 * (|K| + 1) := by positivity
  have hpos2 : 0 < (1 - |C|) / (2 * (|K| + 1)) := div_pos (by linarith) hden
  have hτpos : 0 < τ := lt_min hτm hpos2
  have hτle : τ ≤ (1 - |C|) / (2 * (|K| + 1)) := min_le_right _ _
  refine ⟨τ, hτpos, min_le_left _ _, ?_⟩
  have hK : τ * |K| ≤ (1 - |C|) / 2 := by
    have h1 : τ * |K| ≤ (1 - |C|) / (2 * (|K| + 1)) * |K| :=
      mul_le_mul_of_nonneg_right hτle (abs_nonneg K)
    have h2 : (1 - |C|) / (2 * (|K| + 1)) * |K| ≤ (1 - |C|) / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hden (by norm_num)]
      nlinarith [abs_nonneg K, abs_nonneg C]
    linarith
  calc |C + τ * K| ≤ |C| + |τ * K| := abs_add_le _ _
    _ = |C| + τ * |K| := by rw [abs_mul, abs_of_pos hτpos]
    _ < 1 := by linarith

/-! ### Eighteen vertices: one extra antipodal pair -/

/-- The data of a `Δ1 × Δ3` facet of a cs 5-polytope with eighteen vertices. -/
structure T18 (P F : Set E5) extends TFacet P F where
  z : E5
  X : Finset E5
  zext : z ∈ P.extremePoints ℝ
  znF : z ∉ F
  nznF : -z ∉ F
  zz : z ≠ -z
  hPX : P = convexHull ℝ (X : Set E5)
  memX : ∀ v, v ∈ X ↔ ((∃ s k, v = x s k) ∨ (∃ s k, v = -x s k) ∨ v = z ∨ v = -z)

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.t18 (hv : fvec P 0 = 18) {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = tRow) : Nonempty (T18 P F) := by
  classical
  obtain ⟨Q⟩ := hP.tFacet hF h4 hrow
  have hFP : F ≠ P := hP.ne_of_dim_ne (by rw [h4]; norm_num)
  have hdisj : ∀ y ∈ F, -y ∉ F := fun y hy hny => hFP (hP.eq_of_mem_of_neg_mem hF hy hny)
  let vtx : Bool × Fin 2 × Fin 4 → E5 := fun s => cond s.1 (Q.x s.2.1 s.2.2) (-Q.x s.2.1 s.2.2)
  have hvtx_inj : Function.Injective vtx := by
    rintro ⟨s, a, b⟩ ⟨s', a', b'⟩ he
    cases s <;> cases s' <;> simp only [vtx, Bool.cond_true, Bool.cond_false] at he
    · obtain ⟨rfl, rfl⟩ := Q.inj a b a' b' (neg_injective he); rfl
    · exact absurd (by rw [he]; exact Q.memF a' b' : -Q.x a b ∈ F) (hdisj _ (Q.memF a b))
    · exact absurd (by rw [← he]; exact Q.memF a b : -Q.x a' b' ∈ F) (hdisj _ (Q.memF a' b'))
    · obtain ⟨rfl, rfl⟩ := Q.inj a b a' b' he; rfl
  set X16 : Finset E5 := Finset.univ.image vtx with hX16
  have hmem16 : ∀ v, v ∈ X16 ↔ ((∃ a b, v = Q.x a b) ∨ (∃ a b, v = -Q.x a b)) := by
    intro v
    rw [hX16, Finset.mem_image]
    constructor
    · rintro ⟨⟨s, a, b⟩, -, rfl⟩
      cases s
      · exact Or.inr ⟨a, b, rfl⟩
      · exact Or.inl ⟨a, b, rfl⟩
    · rintro (⟨a, b, rfl⟩ | ⟨a, b, rfl⟩)
      · exact ⟨(true, a, b), Finset.mem_univ _, rfl⟩
      · exact ⟨(false, a, b), Finset.mem_univ _, rfl⟩
  have hX16ext : (X16 : Set E5) ⊆ P.extremePoints ℝ := by
    intro v hv
    rcases (hmem16 v).1 hv with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
    · exact Q.ext a b
    · exact hP.neg_mem_extremePoints (Q.ext a b)
  have hX16card : X16.card = 16 := by
    rw [hX16, Finset.card_image_of_injective _ hvtx_inj]
    rfl
  obtain ⟨V, hV⟩ := hP.polytope
  have hextfin : (P.extremePoints ℝ).Finite := by rw [hV]; exact extremePoints_finite V
  have hextcard : (P.extremePoints ℝ).ncard = 18 := by rw [← hv, hV, fvec_zero_eq]
  obtain ⟨z, hz, hzX⟩ : ∃ z ∈ P.extremePoints ℝ, z ∉ X16 := by
    by_contra hcon
    push_neg at hcon
    have hsub : P.extremePoints ℝ ⊆ (X16 : Set E5) := fun y hy => hcon y hy
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, hX16card, hextcard] at this
    omega
  have hnz : -z ∈ P.extremePoints ℝ := hP.neg_mem_extremePoints hz
  have hnzX : -z ∉ X16 := by
    intro h
    apply hzX
    rcases (hmem16 _).1 h with ⟨a, b, hab⟩ | ⟨a, b, hab⟩
    · exact (hmem16 _).2 (Or.inr ⟨a, b, by rw [← hab, neg_neg]⟩)
    · exact (hmem16 _).2 (Or.inl ⟨a, b, by rw [← neg_neg z, hab, neg_neg]⟩)
  have hznF : z ∉ F := fun h => by
    obtain ⟨a, b, rfl⟩ := Q.all z hz h
    exact hzX ((hmem16 _).2 (Or.inl ⟨a, b, rfl⟩))
  have hnznF : -z ∉ F := fun h => by
    obtain ⟨a, b, hab⟩ := Q.all (-z) hnz h
    exact hzX ((hmem16 _).2 (Or.inr ⟨a, b, by rw [← neg_neg z, hab]⟩))
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
  set X : Finset E5 := insert z (insert (-z) X16) with hX
  have hXext : (X : Set E5) ⊆ P.extremePoints ℝ := by
    intro v hv
    rw [hX, Finset.coe_insert, Finset.coe_insert] at hv
    rcases hv with rfl | rfl | hv
    · exact hz
    · exact hnz
    · exact hX16ext hv
  have hXcard : X.card = 18 := by
    have h1 : z ∉ insert (-z) X16 := by
      rw [Finset.mem_insert]; push_neg; exact ⟨hzz, hzX⟩
    rw [hX, Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem hnzX, hX16card]
  have hextX : (X : Set E5) = P.extremePoints ℝ :=
    Set.eq_of_subset_of_ncard_le hXext (by rw [hextcard, Set.ncard_coe_finset, hXcard]) hextfin
  have hPX : P = convexHull ℝ (X : Set E5) := by
    rw [hextX, hV]
    exact (convexHull_extremePoints_eq V).symm
  have hmemX : ∀ v, v ∈ X ↔ ((∃ a b, v = Q.x a b) ∨ (∃ a b, v = -Q.x a b) ∨ v = z ∨ v = -z) := by
    intro v
    rw [hX, Finset.mem_insert, Finset.mem_insert, hmem16]
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

namespace T18

variable {P F : Set E5} (T : T18 P F)

lemma zP : T.z ∈ P := T.zext.1

lemma x_mem (s : Fin 2) (k : Fin 4) : T.x s k ∈ T.X := (T.memX _).2 (Or.inl ⟨s, k, rfl⟩)
lemma nx_mem (s : Fin 2) (k : Fin 4) : -T.x s k ∈ T.X := (T.memX _).2 (Or.inr (Or.inl ⟨s, k, rfl⟩))
lemma z_mem : T.z ∈ T.X := (T.memX _).2 (Or.inr (Or.inr (Or.inl rfl)))
lemma nz_mem : -T.z ∈ T.X := (T.memX _).2 (Or.inr (Or.inr (Or.inr rfl)))

/-- The coordinates of `z` at the corner, and their derivatives along the kernel. -/
noncomputable def Zc (s : Fin 2) : ℝ := T.γ s * ⟪T.z, T.h s⟫
noncomputable def Wc (k : Fin 4) : ℝ := T.δ k * ⟪T.z, T.g k⟫
noncomputable def Zd (s : Fin 2) : ℝ := T.κ1 s * ⟪T.z, T.h s⟫
noncomputable def Wd (k : Fin 4) : ℝ := T.κ2 k * ⟪T.z, T.g k⟫

lemma Zc_s0 : T.Zc T.s0 = 0 := by simp [Zc, T.γs0]

lemma val_z (τ : ℝ) (u : Fin 2 → ℝ) (v : Fin 4 → ℝ) :
    ⟪T.z, T.Lv τ u v⟫ = ∑ i, u i * (T.Zc i + τ * T.Zd i) + ∑ j, v j * (T.Wc j + τ * T.Wd j) := by
  rw [T.val]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by simp only [TFacet.γt, Zc, Zd]; ring
  · exact Finset.sum_congr rfl fun j _ => by simp only [TFacet.δt, Wc, Wd]; ring

lemma z0_eq : ⟪T.z, T.cF⟫ = ∑ i, T.Zc i + ∑ j, T.Wc j := by
  have h := T.val_z 0 (fun _ => 1) (fun _ => 1)
  rw [T.Lv_one] at h
  rw [h]
  simp

/-- The data of the opposite-sign candidate `c = (s, (k, k'))`. -/
noncomputable def Aop (c : Fin 2 × Pr) : ℝ :=
  T.Zc c.1 - T.Zc (oth c.1) + (T.Wc c.2.1.1 - T.Wc c.2.1.2)
noncomputable def Kop (c : Fin 2 × Pr) (β : Fin 4 → ℝ) : ℝ :=
  T.Zd c.1 - T.Zd (oth c.1) + (T.Wd c.2.1.1 - T.Wd c.2.1.2) + ∑ j ∈ c.2.rest, β j * T.Wd j
noncomputable def Sabs (p : Pr) : ℝ := ∑ j ∈ p.rest, |T.Wc j|

lemma Sabs_nonneg (p : Pr) : 0 ≤ T.Sabs p := Finset.sum_nonneg fun j _ => abs_nonneg _

lemma val_opp (c : Fin 2 × Pr) (τ : ℝ) (β : Fin 4 → ℝ) :
    ⟪T.z, T.Lv τ (potu c.1) (potv c.2 β)⟫ =
      T.Aop c + ∑ j ∈ c.2.rest, β j * T.Wc j + τ * T.Kop c β := by
  rw [T.val_z, sum_potu c.1 (fun i => T.Zc i + τ * T.Zd i),
    sum_potv c.2 β (fun j => T.Wc j + τ * T.Wd j)]
  have e : ∑ j ∈ c.2.rest, β j * (T.Wc j + τ * T.Wd j) =
      ∑ j ∈ c.2.rest, β j * T.Wc j + τ * ∑ j ∈ c.2.rest, β j * T.Wd j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  simp only [Aop, Kop]
  ring

/-- `z` lies (at the corner) above the opposite-sign candidate. -/
def CU (c : Fin 2 × Pr) : Prop := 1 ≤ T.Aop c - T.Sabs c.2
/-- `z` lies (at the corner) below the opposite-sign candidate. -/
def CD (c : Fin 2 × Pr) : Prop := T.Aop c + T.Sabs c.2 ≤ -1

/-- The data of the same-sign candidate `p = (k, k')`. -/
noncomputable def Asm (p : Pr) : ℝ := T.Wc p.1.1 - T.Wc p.1.2

lemma val_same (p : Pr) (α : ℝ) (β : Fin 4 → ℝ) :
    ⟪T.z, T.Lv 0 (potS T.s0 α) (potv p β)⟫ =
      α * T.Zc (oth T.s0) + T.Asm p + ∑ j ∈ p.rest, β j * T.Wc j := by
  rw [T.val_z]
  simp only [zero_mul, add_zero]
  rw [sum_potS, sum_potv]
  simp only [Asm]
  ring

def CUs (p : Pr) : Prop := 1 ≤ T.Asm p - |T.Zc (oth T.s0)| - T.Sabs p
def CDs (p : Pr) : Prop := T.Asm p + |T.Zc (oth T.s0)| + T.Sabs p ≤ -1

/-- The candidate edges. -/
def side (c : Fin 2 × Pr) : Set E5 := segment ℝ (T.x c.1 c.2.1.1) (-T.x (oth c.1) c.2.1.2)
def sideS (p : Pr) : Set E5 := segment ℝ (T.x T.s0 p.1.1) (-T.x T.s0 p.1.2)

/-- The mirror candidate. -/
def mir (c : Fin 2 × Pr) : Fin 2 × Pr := (oth c.1, c.2.swap)

lemma mir_mir (c : Fin 2 × Pr) : mir (mir c) = c := by
  obtain ⟨s, p⟩ := c
  simp only [mir, oth_oth]
  rfl

lemma Sabs_swap (p : Pr) : T.Sabs p.swap = T.Sabs p := by
  simp only [Sabs, Pr.rest_swap]

lemma Aop_mir (c : Fin 2 × Pr) : T.Aop (mir c) = -T.Aop c := by
  simp only [Aop, mir, oth_oth, Pr.swap]; ring

lemma CD_iff (c : Fin 2 × Pr) : T.CD c ↔ T.CU (mir c) := by
  simp only [CD, CU, T.Aop_mir]
  rw [show (mir c).2 = c.2.swap from rfl, T.Sabs_swap]
  constructor <;> intro h <;> linarith

lemma side_mir (c : Fin 2 × Pr) : T.side (mir c) = -T.side c := by
  simp only [side, mir, oth_oth, Pr.swap, neg_segment_eq, neg_neg]
  exact segment_symm ℝ _ _

lemma Asm_swap (p : Pr) : T.Asm p.swap = -T.Asm p := by simp only [Asm, Pr.swap]; ring

lemma CDs_iff (p : Pr) : T.CDs p ↔ T.CUs p.swap := by
  simp only [CDs, CUs, T.Asm_swap, T.Sabs_swap]
  constructor <;> intro h <;> linarith

lemma sideS_swap (p : Pr) : T.sideS p.swap = -T.sideS p := by
  simp only [sideS, Pr.swap, neg_segment_eq, neg_neg]
  exact segment_symm ℝ _ _

lemma z0_lt : ⟪T.z, T.cF⟫ < 1 :=
  lt_of_le_of_ne (T.cF_le _ T.zP) (fun h => T.znF ((T.cF_eq _ T.zP).2 h))

/-- Edges of `P` from a functional on the eighteen vertices, at a positive level `m`. -/
lemma edge_of (L : E5) (m : ℝ) (hm : 0 < m) {p1 p2 : E5} (hp1 : p1 ∈ T.X) (hp2 : p2 ∈ T.X)
    (hne : p1 ≠ p2)
    (hx : ∀ s k, ⟪T.x s k, L⟫ ≤ m ∧ (⟪T.x s k, L⟫ = m → T.x s k = p1 ∨ T.x s k = p2))
    (hnx : ∀ s k, ⟪-T.x s k, L⟫ ≤ m ∧ (⟪-T.x s k, L⟫ = m → -T.x s k = p1 ∨ -T.x s k = p2))
    (hz : ⟪T.z, L⟫ ≤ m ∧ (⟪T.z, L⟫ = m → T.z = p1 ∨ T.z = p2))
    (hnz : ⟪-T.z, L⟫ ≤ m ∧ (⟪-T.z, L⟫ = m → -T.z = p1 ∨ -T.z = p2))
    (h1 : ⟪p1, L⟫ = m) (h2 : ⟪p2, L⟫ = m) :
    segment ℝ p1 p2 ∈ faces P ∧ dim (segment ℝ p1 p2) = 1 := by
  have hval : ∀ v, ⟪v, m⁻¹ • L⟫ = m⁻¹ * ⟪v, L⟫ := fun v => real_inner_smul_right _ _ _
  have hle : ∀ t : ℝ, t ≤ m → m⁻¹ * t ≤ 1 := fun t ht => by
    rw [inv_mul_le_iff₀ hm, mul_one]; exact ht
  have heq : ∀ t : ℝ, m⁻¹ * t = 1 → t = m := fun t ht => by
    field_simp at ht; linarith
  refine (segment_mem_faces_of_functional T.hPX (m⁻¹ • L) hp1 hp2 hne ?_ ?_ ?_ ?_).imp_right
    And.left
  · intro v hv
    rw [hval]
    rcases (T.memX v).1 hv with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | rfl | rfl
    exacts [hle _ (hx a b).1, hle _ (hnx a b).1, hle _ hz.1, hle _ hnz.1]
  · rw [hval, h1, inv_mul_cancel₀ hm.ne']
  · rw [hval, h2, inv_mul_cancel₀ hm.ne']
  · intro v hv hv1
    rw [hval] at hv1
    have hv2 := heq _ hv1
    rcases (T.memX v).1 hv with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | rfl | rfl
    exacts [(hx a b).2 hv2, (hnx a b).2 hv2, hz.2 hv2, hnz.2 hv2]

section cs

variable (hP : IsCSPolytope5 P) (hF : F ∈ faces P) (h4 : dim F = 4)
include hP hF h4

lemma disj : ∀ y ∈ F, -y ∉ F := by
  have hFP : F ≠ P := hP.ne_of_dim_ne (by rw [h4]; norm_num)
  exact fun y hy hny => hFP (hP.eq_of_mem_of_neg_mem hF hy hny)

omit hF h4 in
lemma z0_gt : -1 < ⟪T.z, T.cF⟫ := by
  have hnzP : -T.z ∈ P := hP.symm _ T.zP
  have := lt_of_le_of_ne (T.cF_le _ hnzP) (fun h => T.nznF ((T.cF_eq _ hnzP).2 h))
  rw [inner_neg_left] at this
  linarith

lemma x_ne_nx (a : Fin 2) (b : Fin 4) (a' : Fin 2) (b' : Fin 4) : T.x a b ≠ -T.x a' b' := fun h =>
  disj hP hF h4 _ (T.memF a' b') (by rw [← h]; exact T.memF a b)

omit hP hF h4 in
lemma x_ne_z (a : Fin 2) (b : Fin 4) : T.x a b ≠ T.z := fun h => T.znF (h ▸ T.memF a b)

omit hP hF h4 in
lemma nx_ne_z (a : Fin 2) (b : Fin 4) : -T.x a b ≠ T.z := fun h =>
  T.nznF (by rw [← h, neg_neg]; exact T.memF a b)

omit hP hF h4 in
lemma x_ne_nz (a : Fin 2) (b : Fin 4) : T.x a b ≠ -T.z := fun h => T.nznF (h ▸ T.memF a b)

omit hP hF h4 in
lemma nx_ne_nz (a : Fin 2) (b : Fin 4) : -T.x a b ≠ -T.z := fun h =>
  T.znF (by rw [neg_inj] at h; rw [← h]; exact T.memF a b)

/-- **An edge from an admissible functional** with `|L z| < 1`. -/
lemma edge_of_pattern (L : E5) {a a' : Fin 2} {b b' : Fin 4}
    (hx : ∀ s k, ⟪T.x s k, L⟫ ≤ 1 ∧ (⟪T.x s k, L⟫ = 1 → s = a ∧ k = b))
    (hnx : ∀ s k, ⟪-T.x s k, L⟫ ≤ 1 ∧ (⟪-T.x s k, L⟫ = 1 → s = a' ∧ k = b'))
    (h1 : ⟪T.x a b, L⟫ = 1) (h2 : ⟪-T.x a' b', L⟫ = 1) (hz : |⟪T.z, L⟫| < 1) :
    segment ℝ (T.x a b) (-T.x a' b') ∈ faces P ∧
      dim (segment ℝ (T.x a b) (-T.x a' b')) = 1 := by
  rw [abs_lt] at hz
  refine T.edge_of L 1 one_pos (T.x_mem _ _) (T.nx_mem _ _) (T.x_ne_nx hP hF h4 _ _ _ _)
    ?_ ?_ ?_ ?_ h1 h2
  · intro s k
    exact ⟨(hx s k).1, fun he => by obtain ⟨rfl, rfl⟩ := (hx s k).2 he; exact Or.inl rfl⟩
  · intro s k
    exact ⟨(hnx s k).1, fun he => by obtain ⟨rfl, rfl⟩ := (hnx s k).2 he; exact Or.inr rfl⟩
  · exact ⟨by linarith, fun h => absurd h (by linarith)⟩
  · rw [inner_neg_left]
    exact ⟨by linarith, fun h => absurd h (by linarith)⟩

/-- **Two edges at `z`** from an admissible functional with `L z ≥ 1`: tilting by `± cF` (or a
triangle face in the tie). -/
lemma adj_of_pattern (L : E5) {a a' : Fin 2} {b b' : Fin 4}
    (hx : ∀ s k, ⟪T.x s k, L⟫ ≤ 1 ∧ (⟪T.x s k, L⟫ = 1 → s = a ∧ k = b))
    (hnx : ∀ s k, ⟪-T.x s k, L⟫ ≤ 1 ∧ (⟪-T.x s k, L⟫ = 1 → s = a' ∧ k = b'))
    (h1 : ⟪T.x a b, L⟫ = 1) (h2 : ⟪-T.x a' b', L⟫ = 1) (hz : 1 ≤ ⟪T.z, L⟫) :
    (segment ℝ T.z (T.x a b) ∈ faces P ∧ dim (segment ℝ T.z (T.x a b)) = 1) ∧
    (segment ℝ T.z (-T.x a' b') ∈ faces P ∧ dim (segment ℝ T.z (-T.x a' b')) = 1) := by
  have hp := T.ext a b
  have hq := hP.neg_mem_extremePoints (T.ext a' b')
  have hpq := T.x_ne_nx hP hF h4 a b a' b'
  rcases lt_or_eq_of_le hz with hA1 | hA1
  · -- tilting
    set A := ⟪T.z, L⟫ with hAdef
    set z0 := ⟪T.z, T.cF⟫ with hz0def
    have hz1 : z0 < 1 := T.z0_lt
    have hz2 : -1 < z0 := T.z0_gt hP
    constructor
    · set s := (A - 1) / (1 - z0) with hs
      have hspos : 0 < s := div_pos (by linarith) (by linarith)
      have hsz : A + s * z0 = 1 + s := by
        have hne : 1 - z0 ≠ 0 := by linarith
        rw [hs]; field_simp; ring
      have hval : ∀ v : E5, ⟪v, L + s • T.cF⟫ = ⟪v, L⟫ + s * ⟪v, T.cF⟫ := fun v => by
        rw [inner_add_right, real_inner_smul_right]
      rw [segment_symm]
      refine T.edge_of (L + s • T.cF) (1 + s) (by linarith) (T.x_mem _ _) T.z_mem (T.x_ne_z _ _)
        ?_ ?_ ?_ ?_ ?_ ?_
      · intro s' k
        rw [hval, T.cFx, mul_one]
        obtain ⟨e1, e2⟩ := hx s' k
        exact ⟨by linarith, fun he => by obtain ⟨rfl, rfl⟩ := e2 (by linarith); exact Or.inl rfl⟩
      · intro s' k
        rw [hval, inner_neg_left (T.x s' k) T.cF, T.cFx]
        have e1 := (hnx s' k).1
        exact ⟨by linarith, fun he => absurd he (by linarith)⟩
      · rw [hval, ← hAdef, ← hz0def, hsz]
        exact ⟨le_refl _, fun _ => Or.inr rfl⟩
      · rw [hval, inner_neg_left, inner_neg_left, ← hAdef, ← hz0def]
        exact ⟨by linarith, fun he => absurd he (by linarith)⟩
      · rw [hval, T.cFx, mul_one, h1]
      · rw [hval, ← hAdef, ← hz0def, hsz]
    · set s := (A - 1) / (1 + z0) with hs
      have hspos : 0 < s := div_pos (by linarith) (by linarith)
      have hsz : A - s * z0 = 1 + s := by
        have hne : 1 + z0 ≠ 0 := by linarith
        rw [hs]; field_simp; ring
      have hval : ∀ v : E5, ⟪v, L - s • T.cF⟫ = ⟪v, L⟫ - s * ⟪v, T.cF⟫ := fun v => by
        rw [inner_sub_right, real_inner_smul_right]
      rw [segment_symm]
      refine T.edge_of (L - s • T.cF) (1 + s) (by linarith) (T.nx_mem _ _) T.z_mem (T.nx_ne_z _ _)
        ?_ ?_ ?_ ?_ ?_ ?_
      · intro s' k
        rw [hval, T.cFx, mul_one]
        have e1 := (hx s' k).1
        exact ⟨by linarith, fun he => absurd he (by linarith)⟩
      · intro s' k
        rw [hval, inner_neg_left (T.x s' k) T.cF, T.cFx]
        obtain ⟨e1, e2⟩ := hnx s' k
        exact ⟨by linarith, fun he => by obtain ⟨rfl, rfl⟩ := e2 (by linarith); exact Or.inl rfl⟩
      · rw [hval, ← hAdef, ← hz0def, hsz]
        exact ⟨le_refl _, fun _ => Or.inr rfl⟩
      · rw [hval, inner_neg_left, inner_neg_left, ← hAdef, ← hz0def]
        exact ⟨by linarith, fun he => absurd he (by linarith)⟩
      · rw [hval, inner_neg_left (T.x _ _) T.cF, T.cFx, h2]; ring
      · rw [hval, ← hAdef, ← hz0def, hsz]
  · -- the tie: a triangle face `{x a b, -x a' b', z}`
    have hz1 : ⟪T.z, L⟫ = 1 := hA1.symm
    have hle : ∀ v ∈ T.X, ⟪v, L⟫ ≤ 1 := by
      intro v hv
      rcases (T.memX v).1 hv with ⟨s, k, rfl⟩ | ⟨s, k, rfl⟩ | rfl | rfl
      · exact (hx s k).1
      · exact (hnx s k).1
      · rw [hz1]
      · rw [inner_neg_left, hz1]; norm_num
    have heq : ∀ v ∈ T.X, ⟪v, L⟫ = 1 → v = T.x a b ∨ v = T.z ∨ v = -T.x a' b' := by
      intro v hv hv1
      rcases (T.memX v).1 hv with ⟨s, k, rfl⟩ | ⟨s, k, rfl⟩ | rfl | rfl
      · obtain ⟨rfl, rfl⟩ := (hx s k).2 hv1; exact Or.inl rfl
      · obtain ⟨rfl, rfl⟩ := (hnx s k).2 hv1; exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
      · rw [inner_neg_left, hz1] at hv1; norm_num at hv1
    have hnc : ∀ {p q r : E5}, p ∈ P.extremePoints ℝ → q ∈ P.extremePoints ℝ →
        r ∈ P.extremePoints ℝ → p ≠ q → p ≠ r → q ≠ r → ⟪p, L⟫ = 1 → ⟪q, L⟫ = 1 → ⟪r, L⟫ = 1 →
        r ∉ Submodule.span ℝ ({p, q} : Set E5) := by
      intro p q r hp hq hr hpq hpr hqr hp1 hq1 hr1 hmem
      obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.1 hmem
      have hsum : s + t = 1 := by
        have := congrArg (fun w => ⟪w, L⟫) hst
        simp only [inner_add_left, real_inner_smul_left, hp1, hq1, hr1] at this
        linarith
      exact extreme_not_collinear hp hq hr hpq hpr hqr s
        (by rw [← hst, show t = 1 - s by linarith])
    have hzx : T.z ≠ T.x a b := (T.x_ne_z a b).symm
    have hznx : T.z ≠ -T.x a' b' := (T.nx_ne_z a' b').symm
    constructor
    · rw [segment_symm]
      refine segment_mem_faces_of_functional3 T.hPX L (T.x_mem _ _) T.z_mem (T.nx_mem _ _)
        (T.x_ne_z a b) (hnc hp T.zext hq (T.x_ne_z a b) hpq hznx h1 hz1 h2) hle h1 hz1 ?_
      intro v hv hv1
      rcases heq v hv hv1 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rw [segment_symm]
      refine segment_mem_faces_of_functional3 T.hPX L (T.nx_mem _ _) T.z_mem (T.x_mem _ _)
        (T.nx_ne_z a' b') (hnc hq T.zext hp (T.nx_ne_z a' b') hpq.symm hzx h2 hz1 h1) hle h2 hz1 ?_
      intro v hv hv1
      rcases heq v hv hv1 with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h

/-! ### Opposite-sign candidates -/

omit hP hF h4 in
lemma xvals_opp' (c : Fin 2 × Pr) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ T.τm) {β : Fin 4 → ℝ}
    (hβ1 : ∀ j, β j < 1) (hβ2 : ∀ j, -1 < β j) :
    (∀ s k, ⟪T.x s k, T.Lv τ (potu c.1) (potv c.2 β)⟫ ≤ 1 ∧
      (⟪T.x s k, T.Lv τ (potu c.1) (potv c.2 β)⟫ = 1 → s = c.1 ∧ k = c.2.1.1)) ∧
    (∀ s k, ⟪-T.x s k, T.Lv τ (potu c.1) (potv c.2 β)⟫ ≤ 1 ∧
      (⟪-T.x s k, T.Lv τ (potu c.1) (potv c.2 β)⟫ = 1 → s = oth c.1 ∧ k = c.2.1.2)) :=
  ⟨fun s k => (T.xvals_opp c.1 c.2 hτ0 hτ1 hβ1 hβ2 s k).1,
    fun s k => (T.xvals_opp c.1 c.2 hτ0 hτ1 hβ1 hβ2 s k).2⟩

/-- **Survivors**: neither above nor below at the corner. -/
lemma side_edge (c : Fin 2 × Pr) (hu : ¬ T.CU c) (hd : ¬ T.CD c) :
    T.side c ∈ faces P ∧ dim (T.side c) = 1 := by
  simp only [CU, CD, not_le] at hu hd
  obtain ⟨α, β', hα2, hα1, -, -, hsmall⟩ :=
    exists_small (T.Aop c) (T.Sabs c.2) 0 (by rw [abs_zero, abs_of_nonneg (T.Sabs_nonneg _)]; linarith)
      (by rw [abs_zero, abs_of_nonneg (T.Sabs_nonneg _)]; linarith)
  set β : Fin 4 → ℝ := fun j => α * sgnR (T.Wc j) with hβ
  obtain ⟨hb1, hb2⟩ := sgn_bounds hα1 hα2 T.Wc
  have hC : |T.Aop c + ∑ j ∈ c.2.rest, β j * T.Wc j| < 1 := by
    rw [hβ, sum_sgn]
    simpa [Sabs] using hsmall
  obtain ⟨τ, hτ0, hτ1, hτ⟩ := exists_tau (K := T.Kop c β) hC T.τmpos
  obtain ⟨hx, hnx⟩ := T.xvals_opp' c hτ0 hτ1 hb1 hb2
  exact T.edge_of_pattern hP hF h4 _ hx hnx (T.val_fst_opp c.1 c.2 τ β)
    (T.val_snd_opp c.1 c.2 τ β) (by rw [T.val_opp]; exact hτ)

/-- **Two edges at `z`** when `z` lies above the candidate at the corner and the candidate is not
an edge. -/
lemma adj_opp (c : Fin 2 × Pr) (hu : T.CU c) (hne : ¬ (T.side c ∈ faces P ∧ dim (T.side c) = 1)) :
    (segment ℝ T.z (T.x c.1 c.2.1.1) ∈ faces P ∧ dim (segment ℝ T.z (T.x c.1 c.2.1.1)) = 1) ∧
    (segment ℝ T.z (-T.x (oth c.1) c.2.1.2) ∈ faces P ∧
      dim (segment ℝ T.z (-T.x (oth c.1) c.2.1.2)) = 1) := by
  set β : Fin 4 → ℝ := fun _ => 0 with hβ
  have hb1 : ∀ j, β j < 1 := fun j => by simp [hβ]
  have hb2 : ∀ j, -1 < β j := fun j => by simp [hβ]
  set K := T.Kop c β with hK
  set τ := min T.τm (1 / (2 * (|K| + 1))) with hτ
  have hden : 0 < 2 * (|K| + 1) := by positivity
  have hτ0 : 0 < τ := lt_min T.τmpos (div_pos one_pos hden)
  have hτ1 : τ ≤ T.τm := min_le_left _ _
  have hτK : τ * |K| ≤ 1 / 2 := by
    have h1 : τ * |K| ≤ 1 / (2 * (|K| + 1)) * |K| :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg K)
    have h2 : 1 / (2 * (|K| + 1)) * |K| ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hden (by norm_num)]
      nlinarith [abs_nonneg K]
    linarith
  obtain ⟨hx, hnx⟩ := T.xvals_opp' c hτ0 hτ1 hb1 hb2
  have hval := T.val_opp c τ β
  have hsum0 : ∑ j ∈ c.2.rest, β j * T.Wc j = 0 := by simp [hβ]
  rw [hsum0, add_zero] at hval
  have hA : 1 ≤ T.Aop c := by have := T.Sabs_nonneg c.2; unfold CU at hu; linarith
  have hKb : -(1 / 2) ≤ τ * K := by
    have := neg_abs_le K
    nlinarith [hτ0.le]
  have hpos : 0 < ⟪T.z, T.Lv τ (potu c.1) (potv c.2 β)⟫ := by rw [hval]; linarith
  have hge : 1 ≤ ⟪T.z, T.Lv τ (potu c.1) (potv c.2 β)⟫ := by
    by_contra hlt
    push_neg at hlt
    apply hne
    exact T.edge_of_pattern hP hF h4 _ hx hnx (T.val_fst_opp c.1 c.2 τ β)
      (T.val_snd_opp c.1 c.2 τ β) (by rw [abs_lt]; constructor <;> linarith)
  exact T.adj_of_pattern hP hF h4 _ hx hnx (T.val_fst_opp c.1 c.2 τ β) (T.val_snd_opp c.1 c.2 τ β)
    hge

/-! ### Same-sign candidates -/

omit hP hF h4 in
lemma xvals_same' (hγ : 0 < T.γ (oth T.s0)) (p : Pr) {α : ℝ} (hα1 : α < 1) (hα2 : -1 < α)
    {β : Fin 4 → ℝ} (hβ1 : ∀ j, β j < 1) (hβ2 : ∀ j, -1 < β j) :
    (∀ s k, ⟪T.x s k, T.Lv 0 (potS T.s0 α) (potv p β)⟫ ≤ 1 ∧
      (⟪T.x s k, T.Lv 0 (potS T.s0 α) (potv p β)⟫ = 1 → s = T.s0 ∧ k = p.1.1)) ∧
    (∀ s k, ⟪-T.x s k, T.Lv 0 (potS T.s0 α) (potv p β)⟫ ≤ 1 ∧
      (⟪-T.x s k, T.Lv 0 (potS T.s0 α) (potv p β)⟫ = 1 → s = T.s0 ∧ k = p.1.2)) :=
  ⟨fun s k => (T.xvals_same hγ p hα1 hα2 hβ1 hβ2 s k).1,
    fun s k => (T.xvals_same hγ p hα1 hα2 hβ1 hβ2 s k).2⟩

lemma sideS_edge (hγ : 0 < T.γ (oth T.s0)) (p : Pr) (hu : ¬ T.CUs p) (hd : ¬ T.CDs p) :
    T.sideS p ∈ faces P ∧ dim (T.sideS p) = 1 := by
  simp only [CUs, CDs, not_le] at hu hd
  obtain ⟨α, β', hα2, hα1, hβ2', hβ1', hsmall⟩ :=
    exists_small (T.Asm p) (T.Zc (oth T.s0)) (T.Sabs p)
      (by rw [abs_of_nonneg (T.Sabs_nonneg _)]; linarith)
      (by rw [abs_of_nonneg (T.Sabs_nonneg _)]; linarith)
  set β : Fin 4 → ℝ := fun j => β' * sgnR (T.Wc j) with hβ
  obtain ⟨hb1, hb2⟩ := sgn_bounds hβ1' hβ2' T.Wc
  obtain ⟨hx, hnx⟩ := T.xvals_same' hγ p hα1 hα2 hb1 hb2
  refine T.edge_of_pattern hP hF h4 _ hx hnx (T.val_fst_same p α β) (T.val_snd_same p α β) ?_
  rw [T.val_same, sum_sgn]
  have : α * T.Zc (oth T.s0) + T.Asm p + β' * ∑ j ∈ p.rest, |T.Wc j| =
      T.Asm p + α * T.Zc (oth T.s0) + β' * T.Sabs p := by simp only [Sabs]; ring
  rw [this]
  exact hsmall

lemma adj_same (hγ : 0 < T.γ (oth T.s0)) (p : Pr) (hu : T.CUs p) :
    (segment ℝ T.z (T.x T.s0 p.1.1) ∈ faces P ∧ dim (segment ℝ T.z (T.x T.s0 p.1.1)) = 1) ∧
    (segment ℝ T.z (-T.x T.s0 p.1.2) ∈ faces P ∧
      dim (segment ℝ T.z (-T.x T.s0 p.1.2)) = 1) := by
  have hb1 : ∀ j : Fin 4, (fun _ => (0 : ℝ)) j < 1 := fun j => by norm_num
  have hb2 : ∀ j : Fin 4, -1 < (fun _ => (0 : ℝ)) j := fun j => by norm_num
  obtain ⟨hx, hnx⟩ := T.xvals_same' hγ p (α := 0) (by norm_num) (by norm_num) hb1 hb2
  refine T.adj_of_pattern hP hF h4 _ hx hnx (T.val_fst_same p 0 _) (T.val_snd_same p 0 _) ?_
  rw [T.val_same]
  simp only [zero_mul, zero_add, Finset.sum_const_zero, add_zero]
  have := T.Sabs_nonneg p
  have := abs_nonneg (T.Zc (oth T.s0))
  unfold CUs at hu
  linarith

end cs

end T18

end Kalai5
