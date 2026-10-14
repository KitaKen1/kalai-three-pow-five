import Kalai5.Alexandrov.FaceTrans

/-!
# The face lemma: the rotation case

An in-plane infinitesimal rotation about a centre `z` gives `σ v w = ⟪w - v, A (v - z)⟫`
(`A` skew and nondegenerate on the plane).  A same corner at `v` means that the line `zv` supports
the polygon only at `v`; a zero edge means that its line passes through `z`.

* `z ∈ conv T`: no same corners, and the zero edges contain `z`: at most two of them.
* `z ∉ conv T`: project centrally from `z` onto a line (`π p = (f p - f z)⁻¹ • (p - z)` for a
  separating functional `f`).  Same corners and zero edges give distinct extreme points of the
  projected set, which lies on a line: at most two (`card_le_two_of_line`).
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

/-- Where a form nonnegative on `T` vanishes on the hull, it vanishes on the vertices used. -/
lemma mem_hull_zero {T : Finset (E n)} {v D z : E n} (hnn : ∀ p ∈ T, 0 ≤ ⟪p - v, D⟫)
    (hz : z ∈ convexHull ℝ (T : Set (E n))) (hz0 : ⟪z - v, D⟫ = 0) :
    z ∈ convexHull ℝ ((T.filter fun p => ⟪p - v, D⟫ = 0 : Finset (E n)) : Set (E n)) := by
  classical
  obtain ⟨w, hw0, hw1, hwz⟩ := Finset.mem_convexHull'.1 hz
  have hzv : z - v = ∑ p ∈ T, w p • (p - v) := by
    rw [← hwz]
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul]
  have hnn' : ∀ p ∈ T, 0 ≤ w p * ⟪p - v, D⟫ := fun p hp => mul_nonneg (hw0 p hp) (hnn p hp)
  have hterms : ∀ p ∈ T, w p * ⟪p - v, D⟫ = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg hnn').1 ?_
    rw [← inner_sum_smul, ← hzv, hz0]
  have hwout : ∀ p ∈ T, ¬ ⟪p - v, D⟫ = 0 → w p = 0 := by
    intro p hp hne
    rcases mul_eq_zero.1 (hterms p hp) with h | h
    · exact h
    · exact absurd h hne
  rw [Finset.mem_convexHull']
  refine ⟨w, fun p hp => hw0 p (Finset.mem_filter.1 hp).1, ?_, ?_⟩
  · rw [← hw1, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p hp => ?_
    split_ifs with h
    · rfl
    · exact (hwout p hp h).symm
  · rw [← hwz, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p hp => ?_
    split_ifs with h
    · rfl
    · rw [hwout p hp h, zero_smul]

/-- In a subspace of dimension `≤ 1`, every vector is a multiple of a nonzero one. -/
lemma exists_smul_of_finrank_le_one {U : Submodule ℝ (E n)} (hU : finrank ℝ U ≤ 1) {x y : E n}
    (hx : x ∈ U) (hy : y ∈ U) (hx0 : x ≠ 0) : ∃ μ : ℝ, y = μ • x := by
  obtain ⟨e, he⟩ := finrank_le_one_iff.1 hU
  obtain ⟨c₁, hc₁⟩ := he ⟨x, hx⟩
  obtain ⟨c₂, hc₂⟩ := he ⟨y, hy⟩
  have e₁ : c₁ • (e : E n) = x := by rw [← Submodule.coe_smul, hc₁]
  have e₂ : c₂ • (e : E n) = y := by rw [← Submodule.coe_smul, hc₂]
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at e₁
    exact hx0 e₁.symm
  refine ⟨c₂ / c₁, ?_⟩
  rw [← e₁, ← e₂, smul_smul, div_mul_cancel₀ _ hc₁0]

section rot

variable {T : Finset (E n)} (hcp : ConvPos T) (h2 : dim (convexHull ℝ (T : Set (E n))) = 2)
  {A : E n →ₗ[ℝ] E n} {z : E n}
  (hskew : ∀ x ∈ vectorSpan ℝ (T : Set (E n)), ∀ y ∈ vectorSpan ℝ (T : Set (E n)),
    ⟪A x, y⟫ = -⟪x, A y⟫)
  (hz : ∀ p ∈ T, p - z ∈ vectorSpan ℝ (T : Set (E n)))
  (hnd : ∀ x ∈ vectorSpan ℝ (T : Set (E n)), x ≠ 0 →
    ∃ y ∈ vectorSpan ℝ (T : Set (E n)), ⟪A x, y⟫ ≠ 0)

include hskew hz in
lemma rot_self {v : E n} (hv : v ∈ T) : ⟪z - v, A (v - z)⟫ = 0 := by
  have h := hskew (v - z) (hz v hv) (v - z) (hz v hv)
  rw [real_inner_comm (A (v - z)) (v - z)] at h
  have h0 : ⟪A (v - z), v - z⟫ = 0 := by linarith
  rw [show z - v = -(v - z) by abel, inner_neg_left, real_inner_comm, h0, neg_zero]

include h2 hz hnd in
lemma rot_line {v : E n} (hv : v ∈ T) (hvz : v ≠ z) :
    finrank ℝ ↥(vectorSpan ℝ (T : Set (E n)) ⊓ (ℝ ∙ A (v - z))ᗮ) ≤ 1 := by
  obtain ⟨y, hy, hyne⟩ := hnd (v - z) (hz v hv) (sub_ne_zero.2 hvz)
  exact finrank_ker_le_one h2 hy (by rwa [real_inner_comm])

lemma mem_rot_line {v w : E n} (hv : v ∈ T) (hw : w ∈ T) (h0 : ⟪w - v, A (v - z)⟫ = 0) :
    w - v ∈ vectorSpan ℝ (T : Set (E n)) ⊓ (ℝ ∙ A (v - z))ᗮ :=
  Submodule.mem_inf.2 ⟨vsub_mem_vs hv hw,
    Submodule.mem_orthogonal_singleton_iff_inner_left.2 h0⟩

include hskew hz in
lemma mem_rot_line_z {v : E n} (hv : v ∈ T) :
    z - v ∈ vectorSpan ℝ (T : Set (E n)) ⊓ (ℝ ∙ A (v - z))ᗮ := by
  refine Submodule.mem_inf.2 ⟨?_, Submodule.mem_orthogonal_singleton_iff_inner_left.2
    (rot_self hskew hz hv)⟩
  rw [show z - v = -(v - z) by abel]
  exact Submodule.neg_mem _ (hz v hv)

include hcp h2 hz hnd in
/-- Away from the centre, a vertex has at most one zero edge. -/
lemma rot_zer_le_one {v : E n} (hv : v ∈ T) (hvz : v ≠ z) :
    zerC T (fun v w => ⟪w - v, A (v - z)⟫) v ≤ 1 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hle := pos_neg_zer hcp h2 (fun v w => ⟪w - v, A (v - z)⟫) hv
  have hZ2 : ((nbrs T v).filter fun w => ⟪w - v, A (v - z)⟫ = 0).card = 2 := by
    unfold zerC at hcon hle; beta_reduce at hcon hle; omega
  obtain ⟨x, y, hxy, hxyeq⟩ := Finset.card_eq_two.1 hZ2
  have hx : x ∈ (nbrs T v).filter fun w => ⟪w - v, A (v - z)⟫ = 0 := by rw [hxyeq]; simp
  have hy : y ∈ (nbrs T v).filter fun w => ⟪w - v, A (v - z)⟫ = 0 := by rw [hxyeq]; simp
  obtain ⟨hxn, hx0⟩ := Finset.mem_filter.1 hx
  obtain ⟨hyn, hy0⟩ := Finset.mem_filter.1 hy
  obtain ⟨hxT, hxv, -⟩ := mem_nbrs.1 hxn
  obtain ⟨hyT, hyv, -⟩ := mem_nbrs.1 hyn
  exact no_three_on_line hcp (rot_line h2 hz hnd hv hvz) hv hxT hyT (Ne.symm hxv) (Ne.symm hyv)
    hxy (mem_rot_line hv hxT hx0) (mem_rot_line hv hyT hy0)

include hcp h2 hskew hz hnd in
/-- At a zero edge `vw` (away from the centre), a signed version of the form is nonnegative on
`T` and vanishes exactly at `v, w`. -/
lemma rot_zero_nbr {v w : E n} (hv : v ∈ T) (hvz : v ≠ z) (hw : w ∈ nbrs T v)
    (hw0 : ⟪w - v, A (v - z)⟫ = 0) :
    ∃ D : E n, (∀ p ∈ T, 0 ≤ ⟪p - v, D⟫) ∧ (∀ p ∈ T, ⟪p - v, D⟫ = 0 → p = v ∨ p = w) ∧
      ⟪z - v, D⟫ = 0 := by
  classical
  obtain ⟨hwT, hwv, -⟩ := mem_nbrs.1 hw
  -- the other neighbour
  obtain ⟨x, y, hxy, hxyeq⟩ := Finset.card_eq_two.1 (card_nbrs hcp h2 hv)
  have hwxy : w = x ∨ w = y := by
    have : w ∈ ({x, y} : Finset (E n)) := by rw [← hxyeq]; exact hw
    simpa using this
  obtain ⟨o, ho, hwo, hnbo⟩ : ∃ o ∈ nbrs T v, o ≠ w ∧ ∀ u ∈ nbrs T v, u = w ∨ u = o := by
    rcases hwxy with rfl | rfl
    · exact ⟨y, by rw [hxyeq]; simp, Ne.symm hxy, fun u hu => by
        rw [hxyeq] at hu; simpa using hu⟩
    · exact ⟨x, by rw [hxyeq]; simp, hxy, fun u hu => by
        rw [hxyeq] at hu; simp at hu; tauto⟩
  obtain ⟨hoT, hov, -⟩ := mem_nbrs.1 ho
  have ho0 : ⟪o - v, A (v - z)⟫ ≠ 0 := by
    intro h
    exact no_three_on_line hcp (rot_line h2 hz hnd hv hvz) hv hwT hoT (Ne.symm hwv) (Ne.symm hov)
      (Ne.symm hwo) (mem_rot_line hv hwT hw0) (mem_rot_line hv hoT h)
  -- choose the sign
  obtain ⟨D, hDo, hDw, hDz, hDline⟩ : ∃ D : E n, 0 < ⟪o - v, D⟫ ∧ ⟪w - v, D⟫ = 0 ∧
      ⟪z - v, D⟫ = 0 ∧ ∀ p, ⟪p - v, D⟫ = 0 → ⟪p - v, A (v - z)⟫ = 0 := by
    rcases lt_or_gt_of_ne ho0 with hlt | hgt
    · refine ⟨-A (v - z), by rw [inner_neg_right]; linarith, by rw [inner_neg_right, hw0, neg_zero],
        by rw [inner_neg_right, rot_self hskew hz hv, neg_zero], fun p hp => ?_⟩
      rw [inner_neg_right, neg_eq_zero] at hp; exact hp
    · exact ⟨A (v - z), hgt, hw0, rot_self hskew hz hv, fun p hp => hp⟩
  have hnbr : ∀ u ∈ nbrs T v, 0 ≤ ⟪u - v, D⟫ := by
    intro u hu
    rcases hnbo u hu with rfl | rfl
    · rw [hDw]
    · exact hDo.le
  refine ⟨D, fun p hp => nonneg_of_nbrs hcp hv D hnbr hp, fun p hp hp0 => ?_, hDz⟩
  by_cases hpv : p = v
  · exact Or.inl hpv
  by_cases hpw : p = w
  · exact Or.inr hpw
  exfalso
  exact no_three_on_line hcp (rot_line h2 hz hnd hv hvz) hv hwT hp (Ne.symm hwv) (Ne.symm hpv)
    (Ne.symm hpw) (mem_rot_line hv hwT hw0) (mem_rot_line hv hp (hDline p hp0))

include hcp h2 hz hnd in
/-- A same corner: the signed form is positive on `T \ {v}`. -/
lemma rot_same_pos {v : E n} (hv : v ∈ sameC T fun v w => ⟪w - v, A (v - z)⟫) :
    ∃ D : E n, (D = A (v - z) ∨ D = -A (v - z)) ∧ ∀ p ∈ T, p ≠ v → 0 < ⟪p - v, D⟫ := by
  classical
  obtain ⟨hvT, h⟩ := mem_sameC.1 hv
  have hcard := card_nbrs hcp h2 hvT
  rcases h with h | h
  · refine ⟨A (v - z), Or.inl rfl, fun p hp hpv => pos_of_nbrs hcp hvT _ (fun w hw => ?_) hp hpv⟩
    have hsub : (nbrs T v).filter (fun w => 0 < ⟪w - v, A (v - z)⟫) = nbrs T v :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by unfold posC at h; beta_reduce at h; omega)
    rw [← hsub] at hw
    exact (Finset.mem_filter.1 hw).2
  · refine ⟨-A (v - z), Or.inr rfl, fun p hp hpv => pos_of_nbrs hcp hvT _ (fun w hw => ?_) hp hpv⟩
    have hsub : (nbrs T v).filter (fun w => ⟪w - v, A (v - z)⟫ < 0) = nbrs T v :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by unfold negC at h; beta_reduce at h; omega)
    rw [← hsub] at hw
    rw [inner_neg_right]
    linarith [(Finset.mem_filter.1 hw).2]

/-! #### The centre inside the polygon -/

include hcp h2 hskew hz hnd in
lemma rot_same_empty_of_mem (hzT : z ∈ convexHull ℝ (T : Set (E n))) :
    sameC T (fun v w => ⟪w - v, A (v - z)⟫) = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  obtain ⟨hvT, hvs⟩ := mem_sameC.1 hv
  obtain ⟨D, hD, hpos⟩ := rot_same_pos hcp h2 hz hnd hv
  have hnn : ∀ p ∈ T, 0 ≤ ⟪p - v, D⟫ := fun p hp => by
    by_cases hpv : p = v
    · rw [hpv, sub_self, inner_zero_left]
    · exact (hpos p hp hpv).le
  have hz0 : ⟪z - v, D⟫ = 0 := by
    rcases hD with rfl | rfl
    · exact rot_self hskew hz hvT
    · rw [inner_neg_right, rot_self hskew hz hvT, neg_zero]
  have hzmem := mem_hull_zero hnn hzT hz0
  have hfil : (T.filter fun p => ⟪p - v, D⟫ = 0) = {v} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hp0⟩
      by_contra hpv
      exact (hpos p hp hpv).ne' hp0
    · rintro rfl; exact ⟨hvT, by rw [sub_self, inner_zero_left]⟩
  rw [hfil, Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] at hzmem
  -- then the velocity at `v` vanishes, and no corner can be strict
  have hvz : v - z = 0 := by rw [hzmem, sub_self]
  have hcard := card_nbrs hcp h2 hvT
  rcases hvs with h | h
  · unfold posC at h
    beta_reduce at h
    obtain ⟨w, hw⟩ := Finset.card_pos.1 (by omega :
      0 < ((nbrs T v).filter fun w => 0 < ⟪w - v, A (v - z)⟫).card)
    have := (Finset.mem_filter.1 hw).2
    rw [hvz, map_zero, inner_zero_right] at this
    exact lt_irrefl _ this
  · unfold negC at h
    beta_reduce at h
    obtain ⟨w, hw⟩ := Finset.card_pos.1 (by omega :
      0 < ((nbrs T v).filter fun w => ⟪w - v, A (v - z)⟫ < 0).card)
    have := (Finset.mem_filter.1 hw).2
    rw [hvz, map_zero, inner_zero_right] at this
    exact lt_irrefl _ this

include hcp h2 hskew hz hnd in
/-- A zero edge at `v ≠ z` contains the centre, when the centre is in the polygon. -/
lemma rot_zero_edge_mem (hzT : z ∈ convexHull ℝ (T : Set (E n))) {v w : E n} (hv : v ∈ T)
    (hvz : v ≠ z) (hw : w ∈ nbrs T v) (hw0 : ⟪w - v, A (v - z)⟫ = 0) :
    z ∈ convexHull ℝ ({v, w} : Set (E n)) := by
  classical
  obtain ⟨D, hnn, hzero, hzD⟩ := rot_zero_nbr hcp h2 hskew hz hnd hv hvz hw hw0
  have hzmem := mem_hull_zero hnn hzT hzD
  refine convexHull_mono ?_ hzmem
  intro p hp
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp
  rcases hzero p hp.1 hp.2 with rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

include hcp h2 hskew hz hnd in
theorem rot_count_of_mem (hzT : z ∈ convexHull ℝ (T : Set (E n))) :
    2 * (sameC T fun v w => ⟪w - v, A (v - z)⟫).card +
      ∑ v ∈ T, zerC T (fun v w => ⟪w - v, A (v - z)⟫) v ≤ 4 := by
  classical
  set σ : E n → E n → ℝ := fun v w => ⟪w - v, A (v - z)⟫ with hσ
  rw [rot_same_empty_of_mem hcp h2 hskew hz hnd hzT, Finset.card_empty, mul_zero, zero_add]
  -- zero neighbours away from the centre
  have hzero_nbr : ∀ v ∈ T, v ≠ z → ∀ w ∈ nbrs T v, σ v w = 0 →
      z ∈ convexHull ℝ ({v, w} : Set (E n)) :=
    fun v hv hvz w hw hw0 => rot_zero_edge_mem hcp h2 hskew hz hnd hzT hv hvz hw hw0
  by_cases hzV : z ∈ T
  · -- the centre is a vertex: only edges at `z` are zero edges
    have hbound : ∀ v ∈ T, zerC T σ v ≤ (if v = z then 2 else if v ∈ nbrs T z then 1 else 0) := by
      intro v hv
      by_cases hvz : v = z
      · rw [if_pos hvz]
        have := pos_neg_zer hcp h2 σ hv
        omega
      rw [if_neg hvz]
      have hle1 := rot_zer_le_one hcp h2 hz hnd hv hvz
      split_ifs with hvn
      · exact hle1
      · by_contra hpos
        push_neg at hpos
        obtain ⟨w, hw⟩ := Finset.card_pos.1 (by unfold zerC at hpos; omega :
          0 < ((nbrs T v).filter fun w => σ v w = 0).card)
        obtain ⟨hwn, hw0⟩ := Finset.mem_filter.1 hw
        have hzvw := hzero_nbr v hv hvz w hwn hw0
        -- `z` is extreme, hence an endpoint
        have hsub : convexHull ℝ ({v, w} : Set (E n)) ⊆ convexHull ℝ (T : Set (E n)) :=
          convexHull_min (by
            rintro u (rfl | rfl)
            · exact subset_convexHull ℝ _ (by exact_mod_cast hv)
            · exact subset_convexHull ℝ _ (by exact_mod_cast (mem_nbrs.1 hwn).1))
            (convex_convexHull ℝ _)
        have hext : z ∈ (convexHull ℝ ({v, w} : Set (E n))).extremePoints ℝ :=
          inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hzvw, hcp z hzV⟩
        have := extremePoints_convexHull_subset hext
        rcases this with h | h
        · exact hvz h.symm
        · rw [Set.mem_singleton_iff] at h
          exact hvn (mem_nbrs_symm hv (h ▸ hwn))
    calc ∑ v ∈ T, zerC T σ v
        ≤ ∑ v ∈ T, (if v = z then 2 else if v ∈ nbrs T z then 1 else 0) :=
          Finset.sum_le_sum hbound
      _ = 2 + (nbrs T z).card := by
          rw [Finset.sum_ite, Finset.sum_const, Finset.sum_ite, Finset.sum_const,
            Finset.sum_const_zero, smul_eq_mul, smul_eq_mul, mul_one, add_zero]
          have h1 : (T.filter fun v => v = z).card = 1 := by
            rw [Finset.card_eq_one]
            refine ⟨z, ?_⟩
            ext v
            simp only [Finset.mem_filter, Finset.mem_singleton]
            constructor
            · rintro ⟨-, h⟩; exact h
            · rintro rfl; exact ⟨hzV, rfl⟩
          have h2' : ((T.filter fun v => ¬ v = z).filter fun v => v ∈ nbrs T z).card =
              (nbrs T z).card := by
            congr 1
            ext v
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨-, h⟩; exact h
            · intro h
              obtain ⟨hvT, hvz, -⟩ := mem_nbrs.1 h
              exact ⟨⟨hvT, hvz⟩, h⟩
          rw [h1, h2']
      _ = 4 := by rw [card_nbrs hcp h2 hzV]
  · -- the centre is not a vertex: all zero edges coincide
    have hzer1 : ∀ v ∈ T, zerC T σ v ≤ 1 := fun v hv =>
      rot_zer_le_one hcp h2 hz hnd hv (fun h => hzV (h ▸ hv))
    by_cases hZ : ∃ v ∈ T, 1 ≤ zerC T σ v
    · obtain ⟨v₀, hv₀, hZ₀⟩ := hZ
      obtain ⟨w₀, hw₀⟩ := Finset.card_pos.1 (by unfold zerC at hZ₀; omega :
        0 < ((nbrs T v₀).filter fun w => σ v₀ w = 0).card)
      obtain ⟨hw₀n, hw₀0⟩ := Finset.mem_filter.1 hw₀
      obtain ⟨hw₀T, hw₀v, F₀, hF₀, hF₀1, hv₀F, hw₀F⟩ := mem_nbrs.1 hw₀n
      have hseg₀ := edge_eq_segment hF₀ hF₀1 (hcp v₀ hv₀) (hcp w₀ hw₀T) (Ne.symm hw₀v) hv₀F hw₀F
      have hzF₀ : z ∈ F₀ := by
        rw [hseg₀]; exact hzero_nbr v₀ hv₀ (fun h => hzV (h ▸ hv₀)) w₀ hw₀n hw₀0
      -- every vertex with a zero edge is an endpoint of `F₀`
      have hsub : ∀ v ∈ T, 1 ≤ zerC T σ v → v = v₀ ∨ v = w₀ := by
        intro v hv hZv
        obtain ⟨w, hw⟩ := Finset.card_pos.1 (by unfold zerC at hZv; omega :
          0 < ((nbrs T v).filter fun w => σ v w = 0).card)
        obtain ⟨hwn, hw0⟩ := Finset.mem_filter.1 hw
        obtain ⟨hwT, hwv, -⟩ := mem_nbrs.1 hwn
        have hzvw := hzero_nbr v hv (fun h => hzV (h ▸ hv)) w hwn hw0
        rw [convexHull_pair] at hzvw
        have hopen : z ∈ openSegment ℝ v w :=
          mem_openSegment_of_ne_left_right (fun h => hzV (h ▸ hv)) (fun h => hzV (h ▸ hwT)) hzvw
        have hvF := hF₀.2.isExtreme.left_mem_of_mem_openSegment
          (subset_convexHull ℝ _ (by exact_mod_cast hv))
          (subset_convexHull ℝ _ (by exact_mod_cast hwT)) hzF₀ hopen
        obtain ⟨p, q, -, -, -, hpq, hiff⟩ := filter_mem_edge hcp hF₀ hF₀1
        have h1 := (hiff v hv).1 hvF
        have h2' := (hiff v₀ hv₀).1 hv₀F
        have h3 := (hiff w₀ hw₀T).1 hw₀F
        rcases h1 with rfl | rfl <;> rcases h2' with h | h <;> rcases h3 with h' | h'
        all_goals first
          | exact Or.inl h.symm
          | exact Or.inr h'.symm
          | (exfalso; exact hw₀v (h'.trans h.symm))
      calc ∑ v ∈ T, zerC T σ v
          = ∑ v ∈ T.filter (fun v => 1 ≤ zerC T σ v), zerC T σ v := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun v _ => ?_
            split_ifs with h
            · rfl
            · omega
        _ ≤ ∑ v ∈ T.filter (fun v => 1 ≤ zerC T σ v), 1 :=
            Finset.sum_le_sum fun v hv => hzer1 v (Finset.mem_filter.1 hv).1
        _ = (T.filter fun v => 1 ≤ zerC T σ v).card := by rw [Finset.card_eq_sum_ones]
        _ ≤ ({v₀, w₀} : Finset (E n)).card := by
            refine Finset.card_le_card fun v hv => ?_
            obtain ⟨hvT, hZv⟩ := Finset.mem_filter.1 hv
            rcases hsub v hvT hZv with rfl | rfl <;> simp
        _ ≤ 4 := (Finset.card_le_two).trans (by norm_num)
    · push_neg at hZ
      calc ∑ v ∈ T, zerC T σ v = 0 := Finset.sum_eq_zero fun v hv => by
            have := hZ v hv; omega
        _ ≤ 4 := Nat.zero_le _

end rot

end Kalai5
