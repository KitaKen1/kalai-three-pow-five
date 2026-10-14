import Kalai5.LemmaB.Count

/-!
# Lemma B: fibre shapes, the rank-three exclusions, equatorial counts

* `perm`: relabelling the classes gives a configuration for the same points.
* Fibre shapes: `≥ 3` points span the plane and carry `≥ |K_j|` edge normals; a point has width
  `0`; a segment has a unit normal of width `0`.
* `extraPM_of_levels` (Lemma R, the easy direction): if every class lies on two parallel lines
  `⟪b, ·⟫ = hi, lo` and all positive widths are equal, a fourth `±1`-functional exists.
* Equatorial counts, with `j` the unique widest class:
  - `two_le_card_pats`: the directions `α, -α`;
  - `six_le_card_pats`: a *zero-width direction* `α` of a segment fibre `k`
    (`⟪α, q - p⟫ = 0`): the six directions `±α, ±(tα + (q - p)), ±(tα - (q - p))` (`t` large)
    give distinct patterns when `S k` is a sign;
  - `card_cls_le_pats`: exposing directions of the vertices of `K_j` (other classes points);
  - `card_le_pats_of_dirs`: directions with distinct argmax sets of `K_j`.
-/

namespace Kalai5.LemmaB

open Set Module
open scoped Pointwise

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace Config

variable {x : Fin 7 → E5} (C : Config x)

/-! ### Relabelling -/

/-- Relabel the classes by a permutation. -/
def perm (σ : Equiv.Perm (Fin 3)) : Config x where
  c := fun v => σ (C.c v)
  k := C.k
  real := by
    intro a b
    obtain ⟨z, hz⟩ := C.real (fun j => a (σ j)) b
    exact ⟨z, hz⟩
  surj := σ.surjective.comp C.surj
  inj := fun v w h hk => C.inj v w (σ.injective h) hk
  convpos := by
    intro v
    have hf : fibre (fun v => σ (C.c v)) C.k (σ (C.c v)) = fibre C.c C.k (C.c v) := by
      unfold fibre
      congr 1
      ext w
      simp [σ.injective.eq_iff]
    rw [hf]; exact C.convpos v
  span := by
    intro b hb
    exact C.span b fun v w h => hb v w (by simp only [h])

lemma extraPM_of_perm (σ : Equiv.Perm (Fin 3)) (h : (C.perm σ).ExtraPM) : C.ExtraPM := by
  obtain ⟨a, b, hb, h⟩ := h
  exact ⟨fun j => a (σ j), b, hb, h⟩

lemma cls_perm (σ : Equiv.Perm (Fin 3)) (j : Fin 3) : (C.perm σ).cls j = C.cls (σ.symm j) := by
  ext v
  simp [cls, perm, Equiv.apply_eq_iff_eq_symm_apply]

lemma exists_perm_antitone (f : Fin 3 → ℕ) :
    ∃ τ : Equiv.Perm (Fin 3), f (τ 1) ≤ f (τ 0) ∧ f (τ 2) ≤ f (τ 1) := by
  have hm := Tuple.monotone_sort f
  refine ⟨Fin.revPerm.trans (Tuple.sort f), ?_, ?_⟩
  · show f (Tuple.sort f (Fin.rev 1)) ≤ f (Tuple.sort f (Fin.rev 0))
    exact hm (show Fin.rev (1 : Fin 3) ≤ Fin.rev 0 by decide)
  · show f (Tuple.sort f (Fin.rev 2)) ≤ f (Tuple.sort f (Fin.rev 1))
    exact hm (show Fin.rev (2 : Fin 3) ≤ Fin.rev 1 by decide)

lemma sum_card_cls : (C.cls 0).card + (C.cls 1).card + (C.cls 2).card = 7 := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := C.c) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  rw [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_three] at h
  simp only [cls]
  omega

/-! ### Fibre shapes -/

lemma dim_convexHull (S : Set (E 2)) : dim (convexHull ℝ S) = dim S := by
  unfold dim
  rw [← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]

lemma dim_K_eq_two {j : Fin 3} (h3 : 3 ≤ (C.cls j).card) :
    dim (convexHull ℝ (C.K j : Set (E 2))) = 2 :=
  dim_eq_two_of_convpos (C.convpos_K j) (by rw [C.card_K]; exact h3)

lemma exists_normals_K {j : Fin 3} (h3 : 3 ≤ (C.cls j).card) :
    ∃ N : Finset (E 2), (∀ n ∈ N, IsEdgeNormal (C.K j) n) ∧ (C.cls j).card ≤ N.card := by
  obtain ⟨N, hN, hc⟩ := exists_edgeNormals (C.convpos_K j) (C.dim_K_eq_two h3)
  exact ⟨N, hN, by rw [← C.card_K]; exact hc⟩

lemma wd_pos_of_three_le {j : Fin 3} (h3 : 3 ≤ (C.cls j).card) {b : E 2} (hb : b ≠ 0) :
    0 < C.wd j b := by
  rcases (C.wd_nonneg j b).lt_or_eq with h | h
  · exact h
  · exfalso
    have hc : ∀ p ∈ (C.K j : Set (E 2)), ⟪p, b⟫ = C.hi j b := by
      intro p hp
      obtain ⟨v, hv, rfl⟩ := C.mem_K.1 hp
      have h1 := C.le_hi' hv b
      have h2 := C.lo_le' hv b
      simp only [wd] at h
      rw [real_inner_comm]; linarith
    have h1 := dim_le_one_of_const hb hc
    rw [← dim_convexHull, C.dim_K_eq_two h3] at h1
    omega

lemma wd_eq_zero_of_card_one {j : Fin 3} (h1 : (C.cls j).card = 1) (b : E 2) : C.wd j b = 0 := by
  obtain ⟨v1, hv1, h1'⟩ := C.exists_hi j b
  obtain ⟨v2, hv2, h2'⟩ := C.exists_lo j b
  have : v1 = v2 :=
    Finset.card_le_one.1 h1.le v1 (by simp [cls, hv1]) v2 (by simp [cls, hv2])
  simp only [wd]; rw [← h1', ← h2', this, sub_self]

lemma exists_pair {j : Fin 3} (h2 : (C.cls j).card = 2) :
    ∃ vp vq, C.c vp = j ∧ C.c vq = j ∧ C.k vp ≠ C.k vq ∧ ∀ v, C.c v = j → v = vp ∨ v = vq := by
  obtain ⟨vp, vq, hne, hpq⟩ := Finset.card_eq_two.1 h2
  have hmem : ∀ v, v ∈ C.cls j ↔ C.c v = j := fun v => by simp [cls]
  have hp : C.c vp = j := (hmem vp).1 (by rw [hpq]; simp)
  have hq : C.c vq = j := (hmem vq).1 (by rw [hpq]; simp)
  refine ⟨vp, vq, hp, hq, fun h => hne (C.inj vp vq (by rw [hp, hq]) h), fun v hv => ?_⟩
  have := (hmem v).2 hv
  rw [hpq] at this
  simpa using this

lemma exists_unit_orth (v : E 2) : ∃ n : E 2, ‖n‖ = 1 ∧ ⟪v, n⟫ = 0 := by
  by_cases hv : v = 0
  · exact ⟨EuclideanSpace.single 0 1, by simp, by rw [hv, inner_zero_left]⟩
  · have hne : (ℝ ∙ v)ᗮ ≠ ⊥ := by
      intro h
      have := finrank_orth_eq_one hv
      rw [h, finrank_bot] at this
      exact zero_ne_one this
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hpos : 0 < ‖w‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hw0)
    refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0)]
    · rw [real_inner_smul_right, Submodule.mem_orthogonal_singleton_iff_inner_right.1 hw,
        mul_zero]

/-- A segment fibre `{p, q}` and a unit normal `α`: both `±α` are edge normals, width `0`. -/
lemma segment_normal {j : Fin 3} {vp vq : Fin 7} (hvp : C.c vp = j) (hvq : C.c vq = j)
    (hne : C.k vp ≠ C.k vq) (hcls : ∀ v, C.c v = j → v = vp ∨ v = vq) {α : E 2} (hα1 : ‖α‖ = 1)
    (hα : ⟪α, C.k vq⟫ = ⟪α, C.k vp⟫) :
    IsEdgeNormal (C.K j) α ∧ IsEdgeNormal (C.K j) (-α) ∧ C.wd j α = 0 := by
  have hK : C.K j = {C.k vp, C.k vq} := by
    ext p
    rw [C.mem_K, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rcases hcls v hv with rfl | rfl
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨vp, hvp, rfl⟩
      · exact ⟨vq, hvq, rfl⟩
  have hall : ∀ b : E 2, ⟪b, C.k vq⟫ = ⟪b, C.k vp⟫ → amax (C.K j) b = C.K j := by
    intro b hb
    ext p
    rw [mem_amax]
    refine ⟨fun h => h.1, fun hp => ⟨hp, fun q hq => ?_⟩⟩
    rw [hK, Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> linarith
  have hcard : (C.K j).card = 2 := by rw [hK, Finset.card_pair hne]
  refine ⟨⟨hα1, by rw [hall α hα, hcard]; norm_num⟩,
    ⟨by rw [norm_neg]; exact hα1, by
      rw [hall (-α) (by rw [inner_neg_left, inner_neg_left, hα]), hcard]; norm_num⟩, ?_⟩
  obtain ⟨v1, hv1, h1⟩ := C.exists_hi j α
  obtain ⟨v2, hv2, h2⟩ := C.exists_lo j α
  simp only [wd]
  rw [← h1, ← h2]
  rcases hcls v1 hv1 with rfl | rfl <;> rcases hcls v2 hv2 with rfl | rfl <;> linarith

/-! ### Two levels and the fourth `±1`-functional -/

/-- A fibre whose two support lines carry all its points. -/
lemma two_level_of_card {j : Fin 3} {b : E 2}
    (h : (C.K j).card ≤ (amax (C.K j) b).card + (amax (C.K j) (-b)).card) :
    ∀ v, C.c v = j → ⟪b, C.k v⟫ = C.hi j b ∨ ⟪b, C.k v⟫ = C.lo j b := by
  intro v hv
  by_cases hdisj : Disjoint (amax (C.K j) b) (amax (C.K j) (-b))
  · have hu : amax (C.K j) b ∪ amax (C.K j) (-b) = C.K j := by
      refine Finset.eq_of_subset_of_card_le
        (Finset.union_subset (amax_subset _ _) (amax_subset _ _)) ?_
      rw [Finset.card_union_of_disjoint hdisj]; exact h
    have hk : C.k v ∈ C.K j := C.mem_K.2 ⟨v, hv, rfl⟩
    rw [← hu, Finset.mem_union] at hk
    rcases hk with hk | hk
    · obtain ⟨w, -, hkw, hh⟩ := C.mem_amax_K.1 hk
      left; rw [← hkw]; exact hh
    · obtain ⟨w, -, hkw, hl⟩ := C.mem_amax_K_neg.1 hk
      right; rw [← hkw]; exact hl
  · rw [Finset.not_disjoint_iff] at hdisj
    obtain ⟨p, hp, hp'⟩ := hdisj
    obtain ⟨w, -, rfl, hh⟩ := C.mem_amax_K.1 hp
    obtain ⟨w', -, hkw', hl⟩ := C.mem_amax_K_neg.1 hp'
    rw [hkw'] at hl
    left
    have h1 := C.le_hi' hv b
    have h2 := C.lo_le' hv b
    linarith

/-- **Lemma R (easy direction).** Two levels in every class with a common positive width give a
fourth `±1`-functional. -/
theorem extraPM_of_levels {b : E 2} (hb : b ≠ 0) {W : ℝ} (hW : 0 < W)
    (hlev : ∀ v, ⟪b, C.k v⟫ = C.hi (C.c v) b ∨ ⟪b, C.k v⟫ = C.lo (C.c v) b)
    (hwd : ∀ j, C.wd j b = 0 ∨ C.wd j b = W) : C.ExtraPM := by
  refine ⟨fun j => 1 - 2 / W * C.hi j b, (2 / W) • b, smul_ne_zero (by positivity) hb,
    fun v => ?_⟩
  rw [real_inner_smul_left]
  have hlo : ⟪b, C.k v⟫ = C.hi (C.c v) b ∨ ⟪b, C.k v⟫ = C.hi (C.c v) b - W := by
    rcases hlev v with h | h
    · exact Or.inl h
    · rcases hwd (C.c v) with h' | h' <;> simp only [wd] at h'
      · left; linarith
      · right; linarith
  rcases hlo with h | h <;> rw [h]
  · left; ring
  · right; field_simp; ring

/-! ### Equatorial counts -/

/-- Patterns at directions on opposite sides differ (class `j` with both signs). -/
lemma equPat_ne_of_amax_subset {S : Fin 3 → ELab} {j : Fin 3} (hSj : S j = some none)
    {α b b' : E 2} (hw : 0 < C.wd j α) (hb : amax (C.K j) b ⊆ amax (C.K j) α)
    (hb' : amax (C.K j) b' ⊆ amax (C.K j) (-α)) : C.equPat S b ≠ C.equPat S b' := by
  intro h
  obtain ⟨v, hv, hh⟩ := C.exists_hi j b
  have h1 : C.equPat S b v = 1 :=
    C.equPat_eq_one_iff.2 ⟨by rw [hv, hSj]; simp, by rw [hv]; exact hh⟩
  rw [h, C.equPat_eq_one_iff, hv] at h1
  have hm' : C.k v ∈ amax (C.K j) b' := C.mem_amax_K.2 ⟨v, hv, rfl, h1.2⟩
  have hm : C.k v ∈ amax (C.K j) b := C.mem_amax_K.2 ⟨v, hv, rfl, hh⟩
  obtain ⟨w, -, hkw, hlo⟩ := C.mem_amax_K_neg.1 (hb' hm')
  obtain ⟨w2, -, hkw2, hhi⟩ := C.mem_amax_K.1 (hb hm)
  rw [hkw] at hlo; rw [hkw2] at hhi
  simp only [wd] at hw
  linarith

lemma wd_pos_of_unique {j : Fin 3} {α : E 2} (hJ : ∀ i, i ≠ j → C.wd i α < C.wd j α) :
    0 < C.wd j α := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, i ≠ j := by
    by_cases hj : j = 0
    · exact ⟨1, by rw [hj]; decide⟩
    · exact ⟨0, fun h => hj h.symm⟩
  exact lt_of_le_of_lt (C.wd_nonneg i α) (hJ i hi)

/-- **Two directions `±α`.** -/
theorem two_le_card_pats {S : Fin 3 → ELab} {j : Fin 3} (hS : ∀ i, S i = some none ↔ i = j)
    {α : E 2} (hJ : ∀ i, i ≠ j → C.wd i α < C.wd j α) : 2 ≤ (C.pats S).card := by
  have hSj : S j = some none := (hS j).2 rfl
  have hw := C.wd_pos_of_unique hJ
  have hJ' : ∀ i, i ≠ j → C.wd i (-α) < C.wd j (-α) := fun i hi => by
    rw [C.wd_neg, C.wd_neg]; exact hJ i hi
  have h := C.card_le_pats (S := S) (fun g : Bool => if g then α else -α)
    (fun g => by cases g <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      exact C.adm_of_unique hS (by assumption))
    (by
      intro g g' hgg
      cases g <;> cases g'
      · rfl
      · exact absurd hgg.symm (C.equPat_ne_of_amax_subset hSj hw subset_rfl subset_rfl)
      · exact absurd hgg (C.equPat_ne_of_amax_subset hSj hw subset_rfl subset_rfl)
      · rfl)
  simpa using h

lemma wd_smul_add_le (i : Fin 3) {t : ℝ} (ht : 0 ≤ t) (α d : E 2) :
    C.wd i (t • α + d) ≤ t * C.wd i α + C.wd i d := by
  obtain ⟨v, hv, h1⟩ := C.exists_hi i (t • α + d)
  obtain ⟨w, hw, h2⟩ := C.exists_lo i (t • α + d)
  rw [inner_add_left, real_inner_smul_left] at h1 h2
  have a1 := C.le_hi' hv α
  have a2 := C.le_hi' hv d
  have a3 := C.lo_le' hw α
  have a4 := C.lo_le' hw d
  have m1 : t * ⟪α, C.k v⟫ ≤ t * C.hi i α := mul_le_mul_of_nonneg_left a1 ht
  have m2 : t * C.lo i α ≤ t * ⟪α, C.k w⟫ := mul_le_mul_of_nonneg_left a3 ht
  simp only [wd]
  have : t * (C.hi i α - C.lo i α) = t * C.hi i α - t * C.lo i α := by ring
  linarith

lemma le_wd_smul_add (i : Fin 3) {t : ℝ} (ht : 0 ≤ t) (α d : E 2) :
    t * C.wd i α - C.wd i d ≤ C.wd i (t • α + d) := by
  obtain ⟨v, hv, h1⟩ := C.exists_hi i α
  obtain ⟨w, hw, h2⟩ := C.exists_lo i α
  have a1 := C.le_hi' hv (t • α + d)
  have a2 := C.lo_le' hw (t • α + d)
  rw [inner_add_left, real_inner_smul_left] at a1 a2
  have a3 := C.lo_le' hv d
  have a4 := C.le_hi' hw d
  simp only [wd]
  have : t * (C.hi i α - C.lo i α) = t * C.hi i α - t * C.lo i α := by ring
  rw [h1] at a1; rw [h2] at a2
  linarith

lemma eventually_unique {j : Fin 3} {α : E 2} (hJ : ∀ i, i ≠ j → C.wd i α < C.wd j α)
    (d : E 2) :
    ∀ᶠ t : ℝ in Filter.atTop, ∀ i, i ≠ j → C.wd i (t • α + d) < C.wd j (t • α + d) := by
  rw [Filter.eventually_all]
  intro i
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ h => absurd hij h
  · have hδ : 0 < C.wd j α - C.wd i α := by linarith [hJ i hij]
    filter_upwards [Filter.eventually_ge_atTop 0,
      Filter.eventually_gt_atTop ((C.wd i d + C.wd j d) / (C.wd j α - C.wd i α))] with t ht0 ht _
    have h1 := C.wd_smul_add_le i ht0 α d
    have h2 := C.le_wd_smul_add j ht0 α d
    rw [div_lt_iff₀ hδ] at ht
    have : t * (C.wd j α - C.wd i α) = t * C.wd j α - t * C.wd i α := by ring
    linarith

lemma sign_eq_of_iff {r r' : ℝ} (h1 : r ≤ 0 ↔ r' ≤ 0) (h2 : 0 ≤ r ↔ 0 ≤ r') :
    SignType.sign r = SignType.sign r' := by
  rcases lt_trichotomy r 0 with h | h | h
  · have : r' < 0 := by
      rcases (h1.1 h.le).lt_or_eq with a | a
      · exact a
      · exfalso; rw [a] at h2; have := h2.2 le_rfl; linarith
    rw [sign_neg h, sign_neg this]
  · rw [h] at h1 h2
    rw [h, le_antisymm (h1.1 le_rfl) (h2.1 le_rfl)]
  · have : 0 < r' := by
      rcases (h2.1 h.le).lt_or_eq with a | a
      · exact a
      · exfalso; rw [← a] at h1; have := h1.2 le_rfl; linarith
    rw [sign_pos h, sign_pos this]

/-- For a two-point class `k = {p, q}` used with a sign, the pattern sees the sign of
`⟪b, q - p⟫`. -/
lemma sign_eq_of_equPat_eq {S : Fin 3 → ELab} {k : Fin 3}
    (hSk : S k = some (some true) ∨ S k = some (some false)) {vp vq : Fin 7} (hvp : C.c vp = k)
    (hvq : C.c vq = k) (hcls : ∀ v, C.c v = k → v = vp ∨ v = vq) {b b' : E 2}
    (h : C.equPat S b = C.equPat S b') :
    SignType.sign (⟪b, C.k vq⟫ - ⟪b, C.k vp⟫) = SignType.sign (⟪b', C.k vq⟫ - ⟪b', C.k vp⟫) := by
  have hcls' : ∀ u, C.c u = k → u = vq ∨ u = vp := fun u hu => (hcls u hu).symm
  have hhi : ∀ (b : E 2) (v w : Fin 7), C.c v = k → C.c w = k →
      (∀ u, C.c u = k → u = v ∨ u = w) → (⟪b, C.k v⟫ = C.hi k b ↔ ⟪b, C.k w⟫ ≤ ⟪b, C.k v⟫) := by
    intro b v w hv hw hvw
    constructor
    · intro he; rw [he]; exact C.le_hi' hw b
    · intro hle
      obtain ⟨u, hu, hh⟩ := C.exists_hi k b
      rcases hvw u hu with rfl | rfl
      · exact hh
      · exact le_antisymm (C.le_hi' hv b) (by rw [← hh]; exact hle)
  have hlo : ∀ (b : E 2) (v w : Fin 7), C.c v = k → C.c w = k →
      (∀ u, C.c u = k → u = v ∨ u = w) → (⟪b, C.k v⟫ = C.lo k b ↔ ⟪b, C.k v⟫ ≤ ⟪b, C.k w⟫) := by
    intro b v w hv hw hvw
    constructor
    · intro he; rw [he]; exact C.lo_le' hw b
    · intro hle
      obtain ⟨u, hu, hl⟩ := C.exists_lo k b
      rcases hvw u hu with rfl | rfl
      · exact hl
      · exact le_antisymm (by rw [← hl]; exact hle) (C.lo_le' hv b)
  have hp := congrFun h vp
  have hq := congrFun h vq
  apply sign_eq_of_iff
  · rcases hSk with hS | hS
    · have e : ∀ b, C.equPat S b vp = 1 ↔ ⟪b, C.k vq⟫ - ⟪b, C.k vp⟫ ≤ 0 := by
        intro b
        rw [C.equPat_eq_one_iff, hvp, hS, hhi b vp vq hvp hvq hcls]
        simp
      rw [← e b, ← e b', hp]
    · have e : ∀ b, C.equPat S b vq = -1 ↔ ⟪b, C.k vq⟫ - ⟪b, C.k vp⟫ ≤ 0 := by
        intro b
        rw [C.equPat_eq_neg_one_iff, hvq, hS, hlo b vq vp hvq hvp hcls']
        simp
      rw [← e b, ← e b', hq]
  · rcases hSk with hS | hS
    · have e : ∀ b, C.equPat S b vq = 1 ↔ 0 ≤ ⟪b, C.k vq⟫ - ⟪b, C.k vp⟫ := by
        intro b
        rw [C.equPat_eq_one_iff, hvq, hS, hhi b vq vp hvq hvp hcls']
        simp
      rw [← e b, ← e b', hq]
    · have e : ∀ b, C.equPat S b vp = -1 ↔ 0 ≤ ⟪b, C.k vq⟫ - ⟪b, C.k vp⟫ := by
        intro b
        rw [C.equPat_eq_neg_one_iff, hvp, hS, hlo b vp vq hvp hvq hcls]
        simp
      rw [← e b, ← e b', hp]

/-- **Six directions at a zero-width direction of a segment fibre.** -/
theorem six_le_card_pats {S : Fin 3 → ELab} {j k : Fin 3}
    (hS : ∀ i, S i = some none ↔ i = j) (hSk : S k = some (some true) ∨ S k = some (some false))
    {vp vq : Fin 7} (hvp : C.c vp = k) (hvq : C.c vq = k) (hne : C.k vp ≠ C.k vq)
    (hcls : ∀ v, C.c v = k → v = vp ∨ v = vq)
    {α : E 2} (hα : ⟪α, C.k vq⟫ = ⟪α, C.k vp⟫) (hJ : ∀ i, i ≠ j → C.wd i α < C.wd j α) :
    6 ≤ (C.pats S).card := by
  have hSj : S j = some none := (hS j).2 rfl
  have hw := C.wd_pos_of_unique hJ
  set d := C.k vq - C.k vp with hd
  have hD : 0 < ⟪d, d⟫ := real_inner_self_pos.2 (sub_ne_zero.2 hne.symm)
  have hD' : 0 < ‖d‖ ^ 2 := by rw [← real_inner_self_eq_norm_sq]; exact hD
  have hαd : ⟪α, d⟫ = 0 := by rw [hd, inner_sub_right, hα, sub_self]
  obtain ⟨t, h1, h2, h3, h4, h5, h6⟩ := ((C.eventually_unique hJ d).and
    ((C.eventually_unique hJ (-d)).and ((eventually_amax_subset (C.K j) α d).and
    ((eventually_amax_subset (C.K j) α (-d)).and ((eventually_amax_subset (C.K j) (-α) d).and
    (eventually_amax_subset (C.K j) (-α) (-d))))))).exists
  set base : Fin 3 → E 2 := ![α, t • α + d, t • α + (-d)] with hbase
  set dir : Bool × Fin 3 → E 2 := fun gm => if gm.1 then base gm.2 else -base gm.2 with hdir
  have hJb : ∀ m, ∀ i, i ≠ j → C.wd i (base m) < C.wd j (base m) := by
    intro m; fin_cases m
    · exact hJ
    · exact h1
    · exact h2
  have hJd : ∀ gm, ∀ i, i ≠ j → C.wd i (dir gm) < C.wd j (dir gm) := by
    rintro ⟨g, m⟩ i hi
    cases g
    · simp only [hdir, Bool.false_eq_true, if_false]
      rw [C.wd_neg, C.wd_neg]; exact hJb m i hi
    · exact hJb m i hi
  have hsub : ∀ m, amax (C.K j) (base m) ⊆ amax (C.K j) α := by
    intro m; fin_cases m
    · exact subset_rfl
    · exact h3
    · exact h4
  have hsubneg : ∀ m, amax (C.K j) (-base m) ⊆ amax (C.K j) (-α) := by
    intro m; fin_cases m
    · exact subset_rfl
    · show amax (C.K j) (-(t • α + d)) ⊆ _
      rw [neg_add, ← smul_neg]; exact h6
    · show amax (C.K j) (-(t • α + -d)) ⊆ _
      rw [neg_add, ← smul_neg, neg_neg]; exact h5
  -- the value of `⟪b, q - p⟫` along the six directions
  have e : ∀ b : E 2, ⟪b, C.k vq⟫ - ⟪b, C.k vp⟫ = ⟪b, d⟫ := fun b => by
    rw [hd, inner_sub_right]
  have hb0 : ⟪t • α + d, d⟫ = ⟪d, d⟫ := by
    rw [inner_add_left, real_inner_smul_left, hαd, mul_zero, zero_add]
  have hb1 : ⟪t • α + -d, d⟫ = -⟪d, d⟫ := by
    rw [inner_add_left, real_inner_smul_left, hαd, mul_zero, zero_add, inner_neg_left]
  have hval : ∀ gm : Bool × Fin 3, ⟪dir gm, d⟫ =
      (if gm.1 then 1 else -1) * ![0, ⟪d, d⟫, -⟪d, d⟫] gm.2 := by
    rintro ⟨g, m⟩
    cases g <;> fin_cases m
    · show ⟪-α, d⟫ = -1 * 0
      rw [inner_neg_left, hαd]; ring
    · show ⟪-(t • α + d), d⟫ = -1 * ⟪d, d⟫
      rw [inner_neg_left, hb0]; ring
    · show ⟪-(t • α + -d), d⟫ = -1 * -⟪d, d⟫
      rw [inner_neg_left, hb1]; ring
    · show ⟪α, d⟫ = 1 * 0
      rw [hαd]; ring
    · show ⟪t • α + d, d⟫ = 1 * ⟪d, d⟫
      rw [hb0]; ring
    · show ⟪t • α + -d, d⟫ = 1 * -⟪d, d⟫
      rw [hb1]; ring
  have hinj : Function.Injective fun gm => C.equPat S (dir gm) := by
    rintro ⟨g, m⟩ ⟨g', m'⟩ h
    simp only at h
    have hg : g = g' := by
      cases g <;> cases g'
      · rfl
      · exact absurd h.symm (C.equPat_ne_of_amax_subset hSj hw (hsub m') (hsubneg m))
      · exact absurd h (C.equPat_ne_of_amax_subset hSj hw (hsub m) (hsubneg m'))
      · rfl
    subst hg
    have := C.sign_eq_of_equPat_eq hSk hvp hvq hcls h
    rw [e, e, hval, hval] at this
    cases g <;> fin_cases m <;> fin_cases m' <;>
      first
      | rfl
      | (exfalso; simp [sign_pos hD, sign_neg (neg_neg_of_pos hD), sign_pos hD',
          sign_neg (neg_neg_of_pos hD')] at this)
  have := C.card_le_pats dir (fun gm => C.adm_of_unique hS (hJd gm)) hinj
  simpa using this

/-! ### Exposing directions -/

lemma exists_expose (v : Fin 7) :
    ∃ e : E 2, ∀ w, C.c w = C.c v → w ≠ v → ⟪e, C.k w⟫ < ⟪e, C.k v⟫ := by
  have hF := singleton_mem_faces_of_extreme (C.convpos v)
  obtain ⟨l, hl⟩ := exists_functional hF
  refine ⟨(InnerProductSpace.toDual ℝ (E 2)).symm l, fun w hw hwv => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply, InnerProductSpace.toDual_symm_apply]
  have hkv : C.k v ∈ ({C.k v} : Set (E 2)) := rfl
  rw [hl] at hkv
  have hkw : C.k w ∈ convexHull ℝ (fibre C.c C.k (C.c v) : Set (E 2)) := by
    apply subset_convexHull
    simp only [fibre, Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and]
    exact ⟨w, hw, rfl⟩
  by_contra hle
  push_neg at hle
  have : C.k w ∈ ({C.k v} : Set (E 2)) := by
    rw [hl]; exact ⟨hkw, fun y hy => (hkv.2 y hy).trans hle⟩
  exact hwv (C.inj w v hw this)

/-- **Exposing directions**: the other classes have width zero. -/
theorem card_cls_le_pats {S : Fin 3 → ELab} {j : Fin 3} (hS : ∀ i, S i = some none ↔ i = j)
    (hpt : ∀ i, i ≠ j → ∀ b, C.wd i b = 0) (h2 : 2 ≤ (C.cls j).card) :
    (C.cls j).card ≤ (C.pats S).card := by
  choose e he using C.exists_expose
  have hcard : Fintype.card {v // C.c v = j} = (C.cls j).card := by
    rw [Fintype.card_subtype]; rfl
  rw [← hcard]
  have hother : ∀ v, C.c v = j → ∃ w, C.c w = j ∧ w ≠ v := by
    intro v _
    obtain ⟨w, hw, hwv⟩ := Finset.exists_mem_ne (by omega : 1 < (C.cls j).card) v
    exact ⟨w, by simpa [cls] using hw, hwv⟩
  have hhi : ∀ v, C.c v = j → ⟪e v, C.k v⟫ = C.hi j (e v) := by
    intro v hv
    obtain ⟨u, hu, hh⟩ := C.exists_hi j (e v)
    by_cases huv : u = v
    · rw [huv] at hh; exact hh
    · have := he v u (by rw [hu, hv]) huv
      have := C.le_hi' hv (e v)
      linarith
  refine C.card_le_pats (fun v : {v // C.c v = j} => e v) (fun v => ?_) ?_
  · apply C.adm_of_unique hS
    intro i hi
    rw [hpt i hi]
    obtain ⟨w, hw, hwv⟩ := hother v v.2
    have h1 := he v w (by rw [hw, v.2]) hwv
    have h2 := C.lo_le' hw (e v)
    have h3 := hhi v v.2
    simp only [wd]; linarith
  · rintro ⟨v, hv⟩ ⟨w, hw⟩ h
    simp only at h
    by_contra hne
    have hne' : v ≠ w := fun h' => hne (Subtype.ext h')
    have h1 : C.equPat S (e v) v = 1 :=
      C.equPat_eq_one_iff.2 ⟨by rw [hv, (hS j).2 rfl]; simp, by rw [hv]; exact hhi v hv⟩
    rw [h, C.equPat_eq_one_iff, hv] at h1
    have := he w v (by rw [hv, hw]) hne'
    linarith [h1.2, hhi w hw]

/-- **Directions with distinct argmax sets of `K_j`**, class `j` the unique widest one. -/
theorem card_le_pats_of_dirs {S : Fin 3 → ELab} {j : Fin 3} (hS : ∀ i, S i = some none ↔ i = j)
    (D : Finset (E 2)) (hJ : ∀ b ∈ D, ∀ i, i ≠ j → C.wd i b < C.wd j b)
    (hinj : ∀ b ∈ D, ∀ b' ∈ D, amax (C.K j) b = amax (C.K j) b' → b = b') :
    D.card ≤ (C.pats S).card := by
  have hSj : S j = some none := (hS j).2 rfl
  have hc : Fintype.card D = D.card := Fintype.card_coe D
  rw [← hc]
  refine C.card_le_pats (fun b : D => (b : E 2)) (fun b => C.adm_of_unique hS (hJ b b.2)) ?_
  rintro ⟨b, hb⟩ ⟨b', hb'⟩ h
  simp only at h
  apply Subtype.ext
  apply hinj b hb b' hb'
  ext p
  rw [C.mem_amax_K, C.mem_amax_K]
  have key : ∀ (c : E 2) (v : Fin 7), C.c v = j →
      (⟪c, C.k v⟫ = C.hi j c ↔ C.equPat S c v = 1) := by
    intro c v hv
    rw [C.equPat_eq_one_iff, hv, hSj]
    simp
  constructor
  · rintro ⟨v, hv, hkv, hh⟩
    exact ⟨v, hv, hkv, (key b' v hv).2 (h ▸ (key b v hv).1 hh)⟩
  · rintro ⟨v, hv, hkv, hh⟩
    exact ⟨v, hv, hkv, (key b v hv).2 (h ▸ (key b' v hv).1 hh)⟩

end Config

end Kalai5.LemmaB
