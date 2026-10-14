import Kalai5.Alexandrov.Cut

/-!
# Corner counts in a polygon

For a polygon `T` (vertices in convex position, `dim = 2`) and a signed function `σ v w` on pairs of
vertices, `posC σ v`, `negC σ v`, `zerC σ v` count the neighbours `w` of `v` with `σ v w > 0`,
`< 0`, `= 0`.  A corner is *same* if both neighbours have the same strict sign.

* `trans_count`: for `σ v w = ⟪w - v, c⟫` (an in-plane translation) not identically zero on edges,
  `2 #same + Σ zerC ≤ 4`: same corners and zero edges sit at the minimum or the maximum of `⟪·, c⟫`.
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

section counts

variable (T : Finset (E n)) (σ : E n → E n → ℝ)

open Classical in
noncomputable def posC (v : E n) : ℕ := ((nbrs T v).filter fun w => 0 < σ v w).card

open Classical in
noncomputable def negC (v : E n) : ℕ := ((nbrs T v).filter fun w => σ v w < 0).card

open Classical in
noncomputable def zerC (v : E n) : ℕ := ((nbrs T v).filter fun w => σ v w = 0).card

open Classical in
/-- The corners with both neighbours of the same strict sign. -/
noncomputable def sameC : Finset (E n) := T.filter fun v => posC T σ v = 2 ∨ negC T σ v = 2

end counts

lemma mem_sameC {T : Finset (E n)} {σ : E n → E n → ℝ} {v : E n} :
    v ∈ sameC T σ ↔ v ∈ T ∧ (posC T σ v = 2 ∨ negC T σ v = 2) := by
  classical
  unfold sameC; rw [Finset.mem_filter]

lemma pos_neg_zer {T : Finset (E n)} (hcp : ConvPos T) (h2 : dim (convexHull ℝ (T : Set (E n))) = 2)
    (σ : E n → E n → ℝ) {v : E n} (hv : v ∈ T) : posC T σ v + negC T σ v + zerC T σ v = 2 := by
  classical
  rw [← card_nbrs hcp h2 hv]
  unfold posC negC zerC
  rw [← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint]
  · congr 1
    ext w
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hw
      rcases lt_trichotomy (σ v w) 0 with h | h | h
      · exact Or.inl (Or.inr ⟨hw, h⟩)
      · exact Or.inr ⟨hw, h⟩
      · exact Or.inl (Or.inl ⟨hw, h⟩)
  · rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [Finset.mem_union, Finset.mem_filter] at hw hw'
    rcases hw with h | h <;> linarith [h.2, hw'.2]
  · rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [Finset.mem_filter] at hw hw'
    linarith [hw.2, hw'.2]

/-- Counts depend only on the values on edges. -/
lemma counts_congr {T : Finset (E n)} {σ σ' : E n → E n → ℝ} {v : E n}
    (h : ∀ w ∈ nbrs T v, σ v w = σ' v w) :
    posC T σ v = posC T σ' v ∧ negC T σ v = negC T σ' v ∧ zerC T σ v = zerC T σ' v := by
  classical
  unfold posC negC zerC
  refine ⟨?_, ?_, ?_⟩ <;> congr 1 <;> exact Finset.filter_congr fun w hw => by rw [h w hw]

lemma sameC_congr {T : Finset (E n)} {σ σ' : E n → E n → ℝ}
    (h : ∀ v ∈ T, ∀ w ∈ nbrs T v, σ v w = σ' v w) : sameC T σ = sameC T σ' := by
  ext v
  rw [mem_sameC, mem_sameC]
  constructor
  · rintro ⟨hv, h'⟩
    obtain ⟨e1, e2, -⟩ := counts_congr (h v hv)
    exact ⟨hv, by rwa [← e1, ← e2]⟩
  · rintro ⟨hv, h'⟩
    obtain ⟨e1, e2, -⟩ := counts_congr (h v hv)
    exact ⟨hv, by rwa [e1, e2]⟩

/-- **Three distinct vertices are never on a line.** -/
lemma no_three_on_line {T : Finset (E n)} (hcp : ConvPos T) {U : Submodule ℝ (E n)}
    (hU : finrank ℝ U ≤ 1) {p q r : E n} (hp : p ∈ T) (hq : q ∈ T) (hr : r ∈ T)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hqU : q - p ∈ U) (hrU : r - p ∈ U) : False := by
  have hext : ∀ x ∈ T, ∀ y₁ ∈ T, ∀ y₂ ∈ T, x ∈ openSegment ℝ y₁ y₂ → y₁ = x := by
    intro x hx y₁ hy₁ y₂ hy₂ h
    exact ((mem_extremePoints.1 (hcp x hx)).2 y₁ (subset_convexHull ℝ _ (by exact_mod_cast hy₁))
      y₂ (subset_convexHull ℝ _ (by exact_mod_cast hy₂)) h).1
  rcases between_of_finrank_le_one hU hqU hrU hpq hpr hqr with h | h | h
  · exact hpq (hext p hp q hq r hr h).symm
  · exact hpq (hext q hq p hp r hr h)
  · exact hpr (hext r hr p hp q hq h)

/-- The kernel of a linear form inside the plane is a line. -/
lemma finrank_ker_le_one {T : Finset (E n)} (h2 : dim (convexHull ℝ (T : Set (E n))) = 2) {D y : E n}
    (hy : y ∈ vectorSpan ℝ (T : Set (E n))) (hyD : ⟪y, D⟫ ≠ 0) :
    finrank ℝ ↥(vectorSpan ℝ (T : Set (E n)) ⊓ (ℝ ∙ D)ᗮ) ≤ 1 := by
  have hvs : vectorSpan ℝ (convexHull ℝ (T : Set (E n))) = vectorSpan ℝ (T : Set (E n)) := by
    rw [← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]
  have h2' : finrank ℝ (vectorSpan ℝ (T : Set (E n))) = 2 := by rw [← hvs]; exact h2
  have hlt : vectorSpan ℝ (T : Set (E n)) ⊓ (ℝ ∙ D)ᗮ < vectorSpan ℝ (T : Set (E n)) := by
    refine lt_of_le_of_ne inf_le_left fun h => hyD ?_
    have : y ∈ vectorSpan ℝ (T : Set (E n)) ⊓ (ℝ ∙ D)ᗮ := by rw [h]; exact hy
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (Submodule.mem_inf.1 this).2
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

lemma vsub_mem_vs {T : Finset (E n)} {p q : E n} (hp : p ∈ T) (hq : q ∈ T) :
    q - p ∈ vectorSpan ℝ (T : Set (E n)) :=
  vsub_mem_vectorSpan ℝ (by exact_mod_cast hq) (by exact_mod_cast hp)

/-! ### The translation case -/

/-- One level (the minimum) of a linear form contributes at most `2`. -/
lemma min_level_count {T : Finset (E n)} (hcp : ConvPos T)
    (h2 : dim (convexHull ℝ (T : Set (E n))) = 2) (c : E n)
    (hnc : ∃ v ∈ T, ∃ w ∈ nbrs T v, ⟪w - v, c⟫ ≠ 0) {m : ℝ}
    (hm : ∀ p ∈ T, m ≤ ⟪p, c⟫) [DecidablePred fun v : E n => ⟪v, c⟫ = m] :
    ∑ v ∈ T.filter (fun v => ⟪v, c⟫ = m),
      (2 * (if posC T (fun v w => ⟪w - v, c⟫) v = 2 then 1 else 0) +
        zerC T (fun v w => ⟪w - v, c⟫) v) ≤ 2 := by
  classical
  set σ : E n → E n → ℝ := fun v w => ⟪w - v, c⟫ with hσ
  set Tm := T.filter fun v => ⟪v, c⟫ = m with hTm
  -- a vertex all of whose neighbours lie on its level makes the form constant
  have hnotZ2 : ∀ v ∈ T, zerC T σ v ≠ 2 := by
    intro v hv hZ
    obtain ⟨v₀, hv₀, w₀, hw₀, hne⟩ := hnc
    have hall : ∀ w ∈ nbrs T v, ⟪w - v, c⟫ = 0 := by
      have hsub : (nbrs T v).filter (fun w => σ v w = 0) = nbrs T v :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
          (by rw [card_nbrs hcp h2 hv]; unfold zerC at hZ; omega)
      intro w hw
      rw [← hsub] at hw
      exact (Finset.mem_filter.1 hw).2
    have hconst : ∀ p ∈ T, ⟪p - v, c⟫ = 0 := by
      intro p hp
      obtain ⟨μ, -, hsum⟩ := nbrs_cone hcp hv hp
      rw [hsum, inner_sum_smul]
      exact Finset.sum_eq_zero fun y hy => by rw [hall y hy, mul_zero]
    apply hne
    have h1 := hconst w₀ (mem_nbrs.1 hw₀).1
    have h2' := hconst v₀ hv₀
    rw [inner_sub_left] at h1 h2' ⊢
    linarith
  by_cases hsame : ∃ v ∈ Tm, posC T σ v = 2
  · obtain ⟨v, hvTm, hv2⟩ := hsame
    obtain ⟨hv, hvm⟩ := Finset.mem_filter.1 hvTm
    -- `v` is the unique minimum
    have hpos : ∀ w ∈ nbrs T v, 0 < ⟪w - v, c⟫ := by
      have hsub : (nbrs T v).filter (fun w => 0 < σ v w) = nbrs T v :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
          (by rw [card_nbrs hcp h2 hv]; unfold posC at hv2; omega)
      intro w hw
      rw [← hsub] at hw
      exact (Finset.mem_filter.1 hw).2
    have huniq : ∀ p ∈ T, p ≠ v → m < ⟪p, c⟫ := by
      intro p hp hpv
      have := pos_of_nbrs hcp hv c hpos hp hpv
      rw [inner_sub_left, hvm] at this; linarith
    have hTm1 : Tm = {v} := by
      ext p
      simp only [hTm, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hp, hpm⟩
        by_contra hpv
        have := huniq p hp hpv; linarith
      · rintro rfl; exact ⟨hv, hvm⟩
    have hZ0 : zerC T σ v = 0 := by
      unfold zerC
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w hw hw0
      exact (hpos w hw).ne' hw0
    rw [hTm1, Finset.sum_singleton, if_pos hv2, hZ0]
  · push_neg at hsame
    -- each vertex of the level has at most one neighbour on the level
    have hZle : ∀ v ∈ Tm, zerC T σ v ≤ 1 := by
      intro v hv
      have hvT := (Finset.mem_filter.1 hv).1
      have h3 := pos_neg_zer hcp h2 σ hvT
      have := hnotZ2 v hvT
      -- `negC = 0` at the minimum
      have hneg0 : negC T σ v = 0 := by
        unfold negC
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro w hw hw0
        have hwm := hm w (mem_nbrs.1 hw).1
        have hvm := (Finset.mem_filter.1 hv).2
        simp only [hσ, inner_sub_left] at hw0
        linarith
      have := hsame v hv
      omega
    by_cases hZ : ∃ v ∈ Tm, zerC T σ v = 1
    · obtain ⟨v, hvTm, hv1⟩ := hZ
      obtain ⟨hv, hvm⟩ := Finset.mem_filter.1 hvTm
      -- the zero neighbour
      obtain ⟨w, hw⟩ : ∃ w, w ∈ (nbrs T v).filter (fun w => σ v w = 0) := by
        apply Finset.card_pos.1; unfold zerC at hv1; omega
      obtain ⟨hwn, hw0⟩ := Finset.mem_filter.1 hw
      obtain ⟨hwT, hwv, -⟩ := mem_nbrs.1 hwn
      -- the form is nonnegative on edge directions at `v`
      have hnn : ∀ y ∈ nbrs T v, 0 ≤ ⟪y - v, c⟫ := by
        intro y hy
        have := hm y (mem_nbrs.1 hy).1
        rw [inner_sub_left, hvm]; linarith
      -- the level is `{v, w}`
      have hlevel : Tm ⊆ {v, w} := by
        intro p hp
        obtain ⟨hpT, hpm⟩ := Finset.mem_filter.1 hp
        have h0 : ⟪p - v, c⟫ = 0 := by rw [inner_sub_left, hpm, hvm, sub_self]
        obtain ⟨μ, hμ, hsum⟩ := cone_of_zero hcp hv c hnn hpT h0
        -- the zero neighbours of `v` are just `w`
        have hfil : (nbrs T v).filter (fun y => ⟪y - v, c⟫ = 0) = {w} := by
          refine (Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨hwn, hw0⟩, ?_⟩)
          intro y hy
          have hcard : ((nbrs T v).filter (fun y => σ v y = 0)).card = 1 := hv1
          obtain ⟨y₀, hy₀⟩ := Finset.card_eq_one.1 hcard
          have h1 : y ∈ ({y₀} : Finset (E n)) := by rw [← hy₀]; exact hy
          have h2' : w ∈ ({y₀} : Finset (E n)) := by rw [← hy₀]; exact hw
          rw [Finset.mem_singleton] at h1 h2'
          rw [h1, h2']
        rw [hfil, Finset.sum_singleton] at hsum
        by_cases hpv : p = v
        · rw [hpv]; simp
        by_cases hpw : p = w
        · rw [hpw]; simp
        exfalso
        -- `v, w, p` would be collinear
        have hU : finrank ℝ ↥(ℝ ∙ (w - v)) ≤ 1 :=
          (finrank_span_singleton (sub_ne_zero.2 hwv)).le
        exact no_three_on_line hcp hU hv hwT hpT (Ne.symm hwv) (Ne.symm hpv) (Ne.symm hpw)
          (Submodule.mem_span_singleton_self _)
          (by rw [hsum]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      calc ∑ v ∈ Tm, (2 * (if posC T σ v = 2 then 1 else 0) + zerC T σ v)
          = ∑ v ∈ Tm, zerC T σ v := by
            refine Finset.sum_congr rfl fun u hu => ?_
            rw [if_neg (hsame u hu)]; ring
        _ ≤ ∑ u ∈ ({v, w} : Finset (E n)), zerC T σ u :=
            Finset.sum_le_sum_of_subset_of_nonneg hlevel fun _ _ _ => Nat.zero_le _
        _ ≤ 2 := by
            rw [Finset.sum_pair (Ne.symm hwv)]
            have hwTm : w ∈ Tm := by
              refine Finset.mem_filter.2 ⟨hwT, ?_⟩
              simp only [hσ, inner_sub_left] at hw0; linarith
            linarith [hZle v hvTm, hZle w hwTm]
    · push_neg at hZ
      calc ∑ v ∈ Tm, (2 * (if posC T σ v = 2 then 1 else 0) + zerC T σ v) = 0 := by
            refine Finset.sum_eq_zero fun u hu => ?_
            rw [if_neg (hsame u hu)]
            have := hZle u hu
            have := hZ u hu
            omega
        _ ≤ 2 := Nat.zero_le _

end Kalai5
