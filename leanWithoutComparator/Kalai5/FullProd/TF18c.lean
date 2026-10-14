import Kalai5.FullProd.TF18b
import Kalai5.Rows.Box
import Kalai5.Polar.Intervals
import Kalai5.Faces.Facets

/-!
# A facet `Δ1 × Δ3` with one extra antipodal pair: degree and combinatorics

* `IsCSPolytope5.five_le_edges_at`: every vertex of a cs 5-polytope lies in at least five edges
  (the edges through `z` are the ridges of the facet `z♦` of the polar, and facet rows have
  `r ≥ 5`).
* `psi_conflict`: for `ψ (k, k') = W k - W k' - Σ_{d ≠ k, k'} |W d|`, two pairs with different
  first and different second indices have `ψ p + ψ q ≤ 0` (write `ψ` with `W + |W|` and `|W| - W`).
* `comb_parallel`, `comb_concurrent`: the counting of the candidates with `z` above.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-! ### The degree of a vertex -/

section deg

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.five_le_edges_at {z : E5} (hz : z ∈ P.extremePoints ℝ) :
    5 ≤ {G | G ∈ faces P ∧ z ∈ G ∧ dim G = 1}.ncard := by
  classical
  have hv : ({z} : Set E5) ∈ faces P := by
    obtain ⟨V, hV⟩ := hP.polytope
    have hz' := hz
    rw [hV] at hz'
    have h1 := singleton_mem_faces_of_extreme hz'
    rwa [← hV] at h1
  have hne : ({z} : Set E5) ≠ P := hP.ne_of_dim_ne (by rw [dim_singleton]; norm_num)
  have hup := hP.ncard_up hv hne 1 (by norm_num)
  have e : {G | G ∈ faces P ∧ z ∈ G ∧ dim G = 1} = {F | F ∈ faces P ∧ {z} ⊆ F ∧ dim F = 1} := by
    ext G; simp [Set.singleton_subset_iff]
  rw [e, hup]
  obtain ⟨W, hW, hmem, hdim⟩ := hP.dualFace_facts hv hne
  rw [dim_singleton] at hdim
  have hDf : dualFace P {z} ∈ faces (polarSet P) := by rw [hW]; exact hmem
  have hD4 : dim (dualFace P {z}) = 4 := by omega
  have hrow : faceRow (polarSet P) (dualFace P {z}) ∈ facetRows (polarSet P) := by
    rw [hP.polar.facetRows_eq]
    apply List.mem_map_of_mem
    rw [Finset.mem_toList, Set.Finite.mem_toFinset]
    exact ⟨hDf, hD4⟩
  have h5 := realRow_five_le_r (hP.polar.facetRows_real _ hrow)
  exact h5

end deg

/-! ### Combinatorics of the corner conditions -/

/-- Compatible pairs: the same first or the same second index. -/
def Pr.compat (p q : Pr) : Prop := p.1.1 = q.1.1 ∨ p.1.2 = q.1.2

instance : DecidableRel Pr.compat := fun p q => by unfold Pr.compat; infer_instance

/-- **The conflict inequality.** -/
lemma psi_conflict (W : Fin 4 → ℝ) (p q : Pr) (h1 : p.1.1 ≠ q.1.1) (h2 : p.1.2 ≠ q.1.2) :
    (W p.1.1 - W p.1.2 - ∑ j ∈ p.rest, |W j|) + (W q.1.1 - W q.1.2 - ∑ j ∈ q.rest, |W j|) ≤ 0 := by
  have hp := p.sum_split (fun j => |W j|)
  have hq := q.sum_split (fun j => |W j|)
  have hP1 : (W p.1.1 + |W p.1.1|) + (W q.1.1 + |W q.1.1|) ≤ ∑ j, (W j + |W j|) := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => W j + |W j|)
      (Finset.subset_univ {p.1.1, q.1.1}) (fun j _ _ => by have := neg_abs_le (W j); linarith)
    rw [Finset.sum_pair h1] at this
    exact this
  have hN1 : (|W p.1.2| - W p.1.2) + (|W q.1.2| - W q.1.2) ≤ ∑ j, (|W j| - W j) := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => |W j| - W j)
      (Finset.subset_univ {p.1.2, q.1.2}) (fun j _ _ => by have := le_abs_self (W j); linarith)
    rw [Finset.sum_pair h2] at this
    exact this
  rw [Finset.sum_add_distrib] at hP1
  rw [Finset.sum_sub_distrib] at hN1
  linarith

/-- A pairwise compatible family lies in a row or in a column. -/
lemma compat_row_or_col (W : Finset Pr) (hW : ∀ p ∈ W, ∀ q ∈ W, Pr.compat p q) :
    (∃ k, ∀ p ∈ W, p.1.1 = k) ∨ (∃ k, ∀ p ∈ W, p.1.2 = k) := by
  by_cases h : ∃ p ∈ W, ∃ q ∈ W, p ≠ q
  · obtain ⟨p, hp, q, hq, hpq⟩ := h
    rcases hW p hp q hq with h1 | h2
    · left
      refine ⟨p.1.1, fun r hr => ?_⟩
      rcases hW p hp r hr with e | e
      · exact e.symm
      · rcases hW q hq r hr with e' | e'
        · rw [← e', ← h1]
        · exact absurd (Subtype.ext (Prod.ext h1 (e.trans e'.symm))) hpq
    · right
      refine ⟨p.1.2, fun r hr => ?_⟩
      rcases hW p hp r hr with e | e
      · rcases hW q hq r hr with e' | e'
        · exact absurd (Subtype.ext (Prod.ext (e.trans e'.symm) h2)) hpq
        · rw [← e', ← h2]
      · exact e.symm
  · push_neg at h
    left
    by_cases hne : W.Nonempty
    · obtain ⟨p, hp⟩ := hne
      exact ⟨p.1.1, fun r hr => by rw [h r hr p hp]⟩
    · exact ⟨0, fun r hr => absurd ⟨r, hr⟩ hne⟩

lemma bip_aux : ∀ A1 A2 : Finset (Fin 4),
    (Finset.univ.filter (fun p : Pr => p.1.1 ∈ A1 ∧ p.1.2 ∈ A2)).card ≤ A1.card + A2.card + 4 := by
  decide

/-- A bipartite graph without the diagonal on `4 + 4` vertices. -/
lemma bip (B : Finset Pr) :
    B.card ≤ (B.image fun p => p.1.1).card + (B.image fun p => p.1.2).card + 4 := by
  refine le_trans (Finset.card_le_card ?_) (bip_aux _ _)
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩

lemma card_compat : ∀ p0 : Pr, (Finset.univ.filter (Pr.compat p0)).card = 5 := by
  decide

lemma card_compat2 : ∀ p0 p1 : Pr, p0 ≠ p1 → Pr.compat p0 p1 →
    (Finset.univ.filter (fun q => Pr.compat p0 q ∧ Pr.compat p1 q)).card ≤ 3 := by
  decide

/-- Rows and columns. -/
def rowF (k : Fin 4) : Finset Pr := Finset.univ.filter fun p => p.1.1 = k
def colF (k : Fin 4) : Finset Pr := Finset.univ.filter fun p => p.1.2 = k

lemma card_rowF : ∀ k : Fin 4, (rowF k).card = 3 := by decide

lemma card_colF : ∀ k : Fin 4, (colF k).card = 3 := by decide

lemma par_aux {U0 U1 : Finset Pr} {a0 a1 b0 b1 : ℕ} (h0 : U0.card ≤ 3) (h1 : U1.card ≤ 3)
    (ha0 : U0.Nonempty → 1 ≤ a0) (ha1 : U1.Nonempty → 1 ≤ a1) (hb0 : b0 = U0.card)
    (hb1 : b1 = U1.card) : U0.card + U1.card + 2 ≤ max 5 (a0 + a1 + b0 + b1) := by
  have h5 := le_max_left 5 (a0 + a1 + b0 + b1)
  have hs := le_max_right 5 (a0 + a1 + b0 + b1)
  rcases U0.eq_empty_or_nonempty with e0 | e0 <;> rcases U1.eq_empty_or_nonempty with e1 | e1
  · rw [e0, e1]; simp only [Finset.card_empty]; omega
  · rw [e0]; simp only [Finset.card_empty]; omega
  · rw [e1]; simp only [Finset.card_empty]; omega
  · have := ha0 e0; have := ha1 e1; omega

lemma par_row (k : Fin 4) (U0 U1 : Finset Pr) (hU0 : U0 ⊆ rowF k) (hU1 : U1 ⊆ rowF k) :
    U0.card + U1.card + 2 ≤ max 5 ((U0.image fun p => p.1.1).card +
      (U1.image fun p => p.1.1).card + (U0.image fun p => p.1.2).card +
      (U1.image fun p => p.1.2).card) := by
  have hrow : ∀ {U : Finset Pr}, U ⊆ rowF k → ∀ p ∈ U, p.1.1 = k := fun hU p hp => by
    have := hU hp; simp only [rowF, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
  have hinj : ∀ {U : Finset Pr}, U ⊆ rowF k → (U.image fun p => p.1.2).card = U.card :=
    fun hU => Finset.card_image_of_injOn fun p hp q hq h =>
      Subtype.ext (Prod.ext ((hrow hU p hp).trans (hrow hU q hq).symm) h)
  have hfst : ∀ {U : Finset Pr}, U.Nonempty → 1 ≤ (U.image fun p => p.1.1).card :=
    fun hne => Finset.card_pos.2 (hne.image _)
  exact par_aux ((Finset.card_le_card hU0).trans (card_rowF k).le)
    ((Finset.card_le_card hU1).trans (card_rowF k).le) hfst hfst (hinj hU0) (hinj hU1)

lemma par_col (k : Fin 4) (U0 U1 : Finset Pr) (hU0 : U0 ⊆ colF k) (hU1 : U1 ⊆ colF k) :
    U0.card + U1.card + 2 ≤ max 5 ((U0.image fun p => p.1.1).card +
      (U1.image fun p => p.1.1).card + (U0.image fun p => p.1.2).card +
      (U1.image fun p => p.1.2).card) := by
  have hcol : ∀ {U : Finset Pr}, U ⊆ colF k → ∀ p ∈ U, p.1.2 = k := fun hU p hp => by
    have := hU hp; simp only [colF, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
  have hinj : ∀ {U : Finset Pr}, U ⊆ colF k → (U.image fun p => p.1.1).card = U.card :=
    fun hU => Finset.card_image_of_injOn fun p hp q hq h =>
      Subtype.ext (Prod.ext h ((hcol hU p hp).trans (hcol hU q hq).symm))
  have hsnd : ∀ {U : Finset Pr}, U.Nonempty → 1 ≤ (U.image fun p => p.1.2).card :=
    fun hne => Finset.card_pos.2 (hne.image _)
  have := par_aux (a0 := (U0.image fun p => p.1.2).card) (a1 := (U1.image fun p => p.1.2).card)
    (b0 := (U0.image fun p => p.1.1).card) (b1 := (U1.image fun p => p.1.1).card)
    ((Finset.card_le_card hU0).trans (card_colF k).le)
    ((Finset.card_le_card hU1).trans (card_colF k).le) hsnd hsnd (hinj hU0) (hinj hU1)
  have e : (U0.image fun p => p.1.2).card + (U1.image fun p => p.1.2).card +
      (U0.image fun p => p.1.1).card + (U1.image fun p => p.1.1).card =
      (U0.image fun p => p.1.1).card + (U1.image fun p => p.1.1).card +
      (U0.image fun p => p.1.2).card + (U1.image fun p => p.1.2).card := by ring
  rw [e] at this
  exact this

/-- **Parallel case**: the candidates with `z` above form a star. -/
lemma comb_parallel (ψ : Pr → ℝ)
    (hconf : ∀ p q : Pr, p.1.1 ≠ q.1.1 → p.1.2 ≠ q.1.2 → ψ p + ψ q ≤ 0)
    (U0 U1 : Finset Pr) (h0 : ∀ p ∈ U0, 1 ≤ ψ p) (h1 : ∀ p ∈ U1, 1 ≤ ψ p) :
    U0.card + U1.card + 2 ≤ max 5 ((U0.image fun p => p.1.1).card +
      (U1.image fun p => p.1.1).card + (U0.image fun p => p.1.2).card +
      (U1.image fun p => p.1.2).card) := by
  have hge : ∀ p ∈ U0 ∪ U1, 1 ≤ ψ p := by
    intro p hp
    rcases Finset.mem_union.1 hp with h | h
    exacts [h0 p h, h1 p h]
  have hW : ∀ p ∈ U0 ∪ U1, ∀ q ∈ U0 ∪ U1, Pr.compat p q := by
    intro p hp q hq
    by_contra hc
    unfold Pr.compat at hc
    push_neg at hc
    have := hconf p q hc.1 hc.2
    have := hge p hp
    have := hge q hq
    linarith
  rcases compat_row_or_col _ hW with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine par_row k U0 U1 ?_ ?_
    · intro p hp
      simp only [rowF, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hk p (Finset.mem_union_left _ hp)
    · intro p hp
      simp only [rowF, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hk p (Finset.mem_union_right _ hp)
  · refine par_col k U0 U1 ?_ ?_
    · intro p hp
      simp only [colF, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hk p (Finset.mem_union_left _ hp)
    · intro p hp
      simp only [colF, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hk p (Finset.mem_union_right _ hp)

/-- **Concurrent case.** -/
lemma comb_concurrent (ψ : Pr → ℝ) (ξ : ℝ)
    (hconf : ∀ p q : Pr, p.1.1 ≠ q.1.1 → p.1.2 ≠ q.1.2 → ψ p + ψ q ≤ 0)
    (U0 U1 US : Finset Pr) (h0 : ∀ p ∈ U0, 1 ≤ ψ p - ξ) (h1 : ∀ p ∈ U1, 1 ≤ ψ p + ξ)
    (hS : ∀ p ∈ US, 1 ≤ ψ p - |ξ|) :
    U0.card + U1.card + US.card ≤
      max 5 (max ((U0.image fun p => p.1.1).card + (U0.image fun p => p.1.2).card)
        ((U1.image fun p => p.1.1).card + (U1.image fun p => p.1.2).card)) + 4 := by
  classical
  set a0 := (U0.image fun p => p.1.1).card + (U0.image fun p => p.1.2).card with ha0
  set a1 := (U1.image fun p => p.1.1).card + (U1.image fun p => p.1.2).card with ha1
  set M := max 5 (max a0 a1) with hM
  have hM5 : 5 ≤ M := le_max_left _ _
  have hM0 : a0 ≤ M := le_trans (le_max_left a0 a1) (le_max_right 5 _)
  have hM1 : a1 ≤ M := le_trans (le_max_right a0 a1) (le_max_right 5 _)
  by_cases hB : ∃ p0, 1 + |ξ| ≤ ψ p0
  · obtain ⟨p0, hp0⟩ := hB
    set Ψ1 := Finset.univ.filter (fun q : Pr => 1 - |ξ| ≤ ψ q) with hΨ1
    set Ψ3 := Finset.univ.filter (fun q : Pr => 1 + |ξ| ≤ ψ q) with hΨ3
    have hcompat : ∀ p ∈ Ψ3, ∀ q ∈ Ψ1, Pr.compat p q := by
      intro p hp q hq
      by_contra hc
      unfold Pr.compat at hc
      push_neg at hc
      have e1 := (Finset.mem_filter.1 hp).2
      have e2 := (Finset.mem_filter.1 hq).2
      have := hconf p q hc.1 hc.2
      linarith
    have hp0Ψ3 : p0 ∈ Ψ3 := Finset.mem_filter.2 ⟨Finset.mem_univ _, hp0⟩
    have h31 : Ψ3 ⊆ Ψ1 := fun q hq => Finset.mem_filter.2 ⟨Finset.mem_univ _, by
      have := (Finset.mem_filter.1 hq).2; have := abs_nonneg ξ; linarith⟩
    have hU0 : U0 ⊆ Ψ1 := fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, by
      have := h0 p hp; have := neg_abs_le ξ; linarith⟩
    have hU1 : U1 ⊆ Ψ1 := fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, by
      have := h1 p hp; have := le_abs_self ξ; linarith⟩
    have hUS : US ⊆ Ψ3 := fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, by
      have := hS p hp; linarith⟩
    have htot : U0.card + U1.card + US.card ≤ Ψ1.card + 2 * Ψ3.card := by
      rcases le_total ξ 0 with hξ | hξ
      · have hU1' : U1 ⊆ Ψ3 := fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, by
          have := h1 p hp; rw [abs_of_nonpos hξ]; linarith⟩
        have := Finset.card_le_card hU0
        have := Finset.card_le_card hU1'
        have := Finset.card_le_card hUS
        omega
      · have hU0' : U0 ⊆ Ψ3 := fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, by
          have := h0 p hp; rw [abs_of_nonneg hξ]; linarith⟩
        have := Finset.card_le_card hU0'
        have := Finset.card_le_card hU1
        have := Finset.card_le_card hUS
        omega
    have hΨ1C : Ψ1 ⊆ Finset.univ.filter (Pr.compat p0) := fun q hq =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hcompat p0 hp0Ψ3 q hq⟩
    have hΨ1c5 : Ψ1.card ≤ 5 := (Finset.card_le_card hΨ1C).trans (card_compat p0).le
    have h9 : Ψ1.card + 2 * Ψ3.card ≤ 9 := by
      by_cases h2 : ∃ p1 ∈ Ψ3, p1 ≠ p0
      · obtain ⟨p1, hp1, hp10⟩ := h2
        have hsub : Ψ1 ⊆ Finset.univ.filter (fun q => Pr.compat p0 q ∧ Pr.compat p1 q) :=
          fun q hq => Finset.mem_filter.2
            ⟨Finset.mem_univ _, hcompat p0 hp0Ψ3 q hq, hcompat p1 hp1 q hq⟩
        have h3 := (Finset.card_le_card hsub).trans
          (card_compat2 p0 p1 (Ne.symm hp10) (hcompat p0 hp0Ψ3 p1 (h31 hp1)))
        have := Finset.card_le_card h31
        omega
      · push_neg at h2
        have hsub : Ψ3 ⊆ {p0} := fun q hq => Finset.mem_singleton.2 (h2 q hq)
        have := Finset.card_le_card hsub
        rw [Finset.card_singleton] at this
        omega
    omega
  · push_neg at hB
    have hUS : US.card = 0 := Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun p hp => by
      have := hS p hp; have := hB p; linarith)
    rcases le_total ξ 0 with hξ | hξ
    · have hU1 : U1.card = 0 := Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun p hp => by
        have := h1 p hp; have := hB p; rw [abs_of_nonpos hξ] at this; linarith)
      have := bip U0
      omega
    · have hU0 : U0.card = 0 := Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun p hp => by
        have := h0 p hp; have := hB p; rw [abs_of_nonneg hξ] at this; linarith)
      have := bip U1
      omega

end Kalai5
