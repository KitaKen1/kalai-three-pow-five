import Kalai5.FullProd.TF18e

/-!
# TF18+: the combinatorics with loose adjacency

* `comb_parallel_loose`: in the parallel case (`ξ = 0`), with `Λ` the pairs whose corner interval
  reaches above `1`, the candidates with `z` above satisfy `|U0| + |U1| + 4 ≤ max(5, 2|π₁Λ| + 2|π₂Λ|)`:
  a pair `p₀ = (k, k')` with `ψ(p₀) ≥ 1` forces `Wc k' < 0 < Wc k`, and its four neighbours
  `(k,l), (k,m), (l,k'), (m,k')` reach above `1` unless `Wc l = Wc m = 0`; in that tie only `p₀` has
  `ψ ≥ 1`, and the two candidates of `p₀` cannot both be up (`not_both_up_par`).
* `comb_concurrent_loose`: `|U| ≤ max(5, E) + 2` for the endpoint count `E`; when no pair has
  `ψ ≥ 1 + |ξ|` the loose same-sign candidates add the missing endpoints (otherwise `Wc` would vanish
  and `z₀ = ξ` would leave `(-1, 1)`).
-/

namespace Kalai5

open Set

/-- The sum over the two remaining indices. -/
lemma sabs_eq (W : Fin 4 → ℝ) (p : Pr) :
    ∑ j ∈ p.rest, |W j| = ∑ j, |W j| - |W p.1.1| - |W p.1.2| := by
  have := p.sum_split (fun j => |W j|)
  linarith

/-- The two remaining indices of a pair. -/
lemma Pr.rest_two (p : Pr) : ∃ l m : Fin 4, l ≠ m ∧ l ≠ p.1.1 ∧ l ≠ p.1.2 ∧ m ≠ p.1.1 ∧
    m ≠ p.1.2 ∧ p.rest = {l, m} := by
  have hc : p.rest.card = 2 := by
    obtain ⟨⟨k, k'⟩, hkk⟩ := p
    revert k k'; decide
  obtain ⟨l, m, hlm, he⟩ := Finset.card_eq_two.1 hc
  have hl : l ∈ p.rest := by rw [he]; simp
  have hm : m ∈ p.rest := by rw [he]; simp
  simp only [Pr.rest, Finset.mem_filter, Finset.mem_univ, true_and] at hl hm
  exact ⟨l, m, hlm, hl.1, hl.2, hm.1, hm.2, he⟩

lemma fin4_cover : ∀ k k' l m d : Fin 4, k ≠ k' → l ≠ m → l ≠ k → l ≠ k' → m ≠ k → m ≠ k' →
    d = k ∨ d = k' ∨ d = l ∨ d = m := by decide

lemma sum_four {k k' l m : Fin 4} (h1 : k ≠ k') (h2 : l ≠ m) (h3 : l ≠ k) (h4 : l ≠ k')
    (h5 : m ≠ k) (h6 : m ≠ k') (f : Fin 4 → ℝ) : ∑ j, f j = f k + f k' + f l + f m := by
  have hs := Pr.sum_split ⟨(k, k'), h1⟩ f
  have hr : Pr.rest ⟨(k, k'), h1⟩ = {l, m} := by
    ext d
    simp only [Pr.rest, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hd1, hd2⟩
      rcases fin4_cover k k' l m d h1 h2 h3 h4 h5 h6 with h | h | h | h
      · exact absurd h hd1
      · exact absurd h hd2
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl)
      · exact ⟨h3, h4⟩
      · exact ⟨h5, h6⟩
  rw [hr, Finset.sum_pair h2] at hs
  have e1 : (↑(⟨(k, k'), h1⟩ : Pr) : Fin 4 × Fin 4).1 = k := rfl
  have e2 : (↑(⟨(k, k'), h1⟩ : Pr) : Fin 4 × Fin 4).2 = k' := rfl
  rw [e1, e2] at hs
  linarith

/-- **Parallel case with loose adjacency.** -/
lemma comb_parallel_loose (W : Fin 4 → ℝ) (hz1 : -1 < ∑ j, W j) (hz2 : ∑ j, W j < 1)
    (U0 U1 : Finset Pr)
    (h0 : ∀ p ∈ U0, 1 ≤ W p.1.1 - W p.1.2 - ∑ j ∈ p.rest, |W j|)
    (h1 : ∀ p ∈ U1, 1 ≤ W p.1.1 - W p.1.2 - ∑ j ∈ p.rest, |W j|)
    (hdeg : ∀ p : Pr, (∀ d ∈ p.rest, W d = 0) → W p.1.1 - W p.1.2 = 1 → 0 < W p.1.1 →
      W p.1.2 < 0 → p ∈ U0 → p ∈ U1 → False)
    (L : Finset Pr) (hL : ∀ q : Pr, 1 < W q.1.1 - W q.1.2 + ∑ j ∈ q.rest, |W j| → q ∈ L) :
    U0.card + U1.card + 4 ≤ max 5 (2 * (L.image fun p => p.1.1).card +
      2 * (L.image fun p => p.1.2).card) := by
  classical
  set ψ : Pr → ℝ := fun p => W p.1.1 - W p.1.2 - ∑ j ∈ p.rest, |W j| with hψ
  have hconf : ∀ p q : Pr, p.1.1 ≠ q.1.1 → p.1.2 ≠ q.1.2 → ψ p + ψ q ≤ 0 :=
    fun p q a b => psi_conflict W p q a b
  set Ψ := Finset.univ.filter (fun p : Pr => 1 ≤ ψ p) with hΨ
  have hU0Ψ : U0 ⊆ Ψ := fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, h0 p hp⟩
  have hU1Ψ : U1 ⊆ Ψ := fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, h1 p hp⟩
  have hΨc : Ψ.card ≤ 3 := by
    have hW : ∀ p ∈ Ψ, ∀ q ∈ Ψ, Pr.compat p q := by
      intro p hp q hq
      by_contra hc
      unfold Pr.compat at hc
      push_neg at hc
      have := hconf p q hc.1 hc.2
      have := (Finset.mem_filter.1 hp).2
      have := (Finset.mem_filter.1 hq).2
      linarith
    rcases compat_row_or_col Ψ hW with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine le_trans (Finset.card_le_card fun p hp => ?_) (card_rowF k).le
      simp only [rowF, Finset.mem_filter, Finset.mem_univ, true_and]; exact hk p hp
    · refine le_trans (Finset.card_le_card fun p hp => ?_) (card_colF k).le
      simp only [colF, Finset.mem_filter, Finset.mem_univ, true_and]; exact hk p hp
  have hc0 := (Finset.card_le_card hU0Ψ).trans hΨc
  have hc1 := (Finset.card_le_card hU1Ψ).trans hΨc
  have hm5 := le_max_left 5 (2 * (L.image fun p => p.1.1).card + 2 * (L.image fun p => p.1.2).card)
  have hmx := le_max_right 5 (2 * (L.image fun p => p.1.1).card + 2 * (L.image fun p => p.1.2).card)
  by_cases hsmall : U0.card + U1.card ≤ 1
  · omega
  push_neg at hsmall
  obtain ⟨p0, hp0⟩ : (U0 ∪ U1).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro he
    have := Finset.card_union_le U0 U1
    have h00 : U0 = ∅ := Finset.subset_empty.1 (he ▸ Finset.subset_union_left)
    have h11 : U1 = ∅ := Finset.subset_empty.1 (he ▸ Finset.subset_union_right)
    rw [h00, h11] at hsmall; simp at hsmall
  have hψ0 : 1 ≤ ψ p0 := by
    rcases Finset.mem_union.1 hp0 with h | h
    exacts [h0 p0 h, h1 p0 h]
  obtain ⟨⟨k, k'⟩, hkk⟩ := p0
  obtain ⟨l, m, hlm, hlk, hlk', hmk, hmk', hrest⟩ := Pr.rest_two ⟨(k, k'), hkk⟩
  simp only at hlk hlk' hmk hmk'
  have hsum : ∑ j, W j = W k + W k' + W l + W m := sum_four hkk hlm hlk hlk' hmk hmk' W
  have hsabs : ∑ j, |W j| = |W k| + |W k'| + |W l| + |W m| :=
    sum_four hkk hlm hlk hlk' hmk hmk' (fun j => |W j|)
  have hψ0' : 1 ≤ W k - W k' - (|W l| + |W m|) := by
    have := hψ0; simp only [hψ, sabs_eq] at this; linarith
  have al := abs_nonneg (W l); have am := abs_nonneg (W m)
  have bl := le_abs_self (W l); have bm := le_abs_self (W m)
  have cl := neg_abs_le (W l); have cm := neg_abs_le (W m)
  have hk'neg : W k' < 0 := by linarith
  have hkpos : 0 < W k := by linarith
  have ak' : |W k'| = -W k' := abs_of_neg hk'neg
  have ak : |W k| = W k := abs_of_pos hkpos
  -- the four neighbours
  let q1 : Pr := ⟨(k, l), Ne.symm hlk⟩
  let q2 : Pr := ⟨(k, m), Ne.symm hmk⟩
  let q3 : Pr := ⟨(l, k'), hlk'⟩
  let q4 : Pr := ⟨(m, k'), hmk'⟩
  have hup : ∀ q : Pr, 1 < W q.1.1 - W q.1.2 + (∑ j, |W j| - |W q.1.1| - |W q.1.2|) → q ∈ L :=
    fun q hq => hL q (by rw [sabs_eq]; exact hq)
  have hπ : ∀ (S : Finset Pr) (f : Pr → Fin 4) (q : Pr), q ∈ S → f q ∈ S.image f :=
    fun S f q hq => Finset.mem_image_of_mem f hq
  -- the large cases
  have hbig : 5 ≤ (L.image fun p => p.1.1).card + (L.image fun p => p.1.2).card →
      U0.card + U1.card + 4 ≤ max 5 (2 * (L.image fun p => p.1.1).card +
        2 * (L.image fun p => p.1.2).card) := by
    intro h5; omega
  by_cases hm0 : W m = 0
  · by_cases hl0 : W l = 0
    · -- the tie `Wc l = Wc m = 0`
      have hc1 : 1 ≤ W k - W k' := by rw [hl0, hm0] at hψ0'; simpa using hψ0'
      rcases lt_or_eq_of_le hc1 with hc | hc
      · -- all four neighbours reach above `1`
        have m1 : q1 ∈ L := hup q1 (by show 1 < W k - W l + (∑ j, |W j| - |W k| - |W l|); rw [hsabs, ak, ak', hl0, hm0]; simp only [abs_zero]; linarith)
        have m2 : q2 ∈ L := hup q2 (by show 1 < W k - W m + (∑ j, |W j| - |W k| - |W m|); rw [hsabs, ak, ak', hl0, hm0]; simp only [abs_zero]; linarith)
        have m3 : q3 ∈ L := hup q3 (by show 1 < W l - W k' + (∑ j, |W j| - |W l| - |W k'|); rw [hsabs, ak, ak', hl0, hm0]; simp only [abs_zero]; linarith)
        have m4 : q4 ∈ L := hup q4 (by show 1 < W m - W k' + (∑ j, |W j| - |W m| - |W k'|); rw [hsabs, ak, ak', hl0, hm0]; simp only [abs_zero]; linarith)
        apply hbig
        have e1 : ({k, l, m} : Finset (Fin 4)) ⊆ L.image fun p => p.1.1 := by
          intro d hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl | rfl
          · exact hπ L _ q1 m1
          · exact hπ L _ q3 m3
          · exact hπ L _ q4 m4
        have e2 : ({l, m, k'} : Finset (Fin 4)) ⊆ L.image fun p => p.1.2 := by
          intro d hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl | rfl
          · exact hπ L _ q1 m1
          · exact hπ L _ q2 m2
          · exact hπ L _ q3 m3
        have c1 : ({k, l, m} : Finset (Fin 4)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [Ne.symm hlk, Ne.symm hmk]),
            Finset.card_pair hlm]
        have c2 : ({l, m, k'} : Finset (Fin 4)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hlm, hlk']), Finset.card_pair hmk']
        have := Finset.card_le_card e1; have := Finset.card_le_card e2
        omega
      · -- `Wc k - Wc k' = 1`: only `p₀` has `ψ ≥ 1`
        have hU : ∀ q ∈ U0 ∪ U1, q = ⟨(k, k'), hkk⟩ := by
          intro q hq
          have hq1 : 1 ≤ ψ q := by
            rcases Finset.mem_union.1 hq with h | h
            exacts [h0 q h, h1 q h]
          obtain ⟨⟨a, b⟩, hab⟩ := q
          simp only [hψ, sabs_eq] at hq1
          rw [hsabs] at hq1
          -- `a, b ∈ {k, k', l, m}`
          have ha := fin4_cover k k' l m a hkk hlm hlk hlk' hmk hmk'
          have hb := fin4_cover k k' l m b hkk hlm hlk hlk' hmk hmk'
          have hab' : a ≠ b := hab
          rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
            first
            | exact absurd rfl hab'
            | rfl
            | (exfalso; rw [hl0, hm0] at hq1; simp only [abs_zero, sub_zero, zero_sub] at hq1;
               rw [ak, ak'] at hq1; linarith)
        have hp0U0 : ∀ q ∈ U0, q = ⟨(k, k'), hkk⟩ := fun q hq => hU q (Finset.mem_union_left _ hq)
        have hp0U1 : ∀ q ∈ U1, q = ⟨(k, k'), hkk⟩ := fun q hq => hU q (Finset.mem_union_right _ hq)
        have hs0 : U0 ⊆ {⟨(k, k'), hkk⟩} := fun q hq => Finset.mem_singleton.2 (hp0U0 q hq)
        have hs1 : U1 ⊆ {⟨(k, k'), hkk⟩} := fun q hq => Finset.mem_singleton.2 (hp0U1 q hq)
        have hcU0 := Finset.card_le_card hs0
        have hcU1 := Finset.card_le_card hs1
        rw [Finset.card_singleton] at hcU0 hcU1
        have hboth : (⟨(k, k'), hkk⟩ : Pr) ∈ U0 ∧ (⟨(k, k'), hkk⟩ : Pr) ∈ U1 := by
          constructor
          · obtain ⟨q, hq⟩ := Finset.card_pos.1 (by omega : 0 < U0.card)
            rw [← hp0U0 q hq]; exact hq
          · obtain ⟨q, hq⟩ := Finset.card_pos.1 (by omega : 0 < U1.card)
            rw [← hp0U1 q hq]; exact hq
        exfalso
        refine hdeg ⟨(k, k'), hkk⟩ ?_ hc.symm hkpos hk'neg hboth.1 hboth.2
        intro d hd
        rw [hrest] at hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        exacts [hl0, hm0]
    · -- `Wc l ≠ 0`, `Wc m = 0`
      have hla : 0 < |W l| := abs_pos.2 hl0
      have m2 : q2 ∈ L := hup q2 (by show 1 < W k - W m + (∑ j, |W j| - |W k| - |W m|); rw [hsabs, ak, ak', hm0]; simp only [abs_zero]; linarith)
      have m4 : q4 ∈ L := hup q4 (by show 1 < W m - W k' + (∑ j, |W j| - |W m| - |W k'|); rw [hsabs, ak, ak', hm0]; simp only [abs_zero]; linarith)
      apply hbig
      by_cases hls : W l < 0
      · have m1 : q1 ∈ L := hup q1 (by
          show 1 < W k - W l + (∑ j, |W j| - |W k| - |W l|); rw [hsabs, ak, ak', abs_of_neg hls, hm0]; simp only [abs_zero]; linarith)
        have e1 : ({k, m} : Finset (Fin 4)) ⊆ L.image fun p => p.1.1 := by
          intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl
          · exact hπ L _ q2 m2
          · exact hπ L _ q4 m4
        have e2 : ({l, m, k'} : Finset (Fin 4)) ⊆ L.image fun p => p.1.2 := by
          intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl | rfl
          · exact hπ L _ q1 m1
          · exact hπ L _ q2 m2
          · exact hπ L _ q4 m4
        have c1 : ({k, m} : Finset (Fin 4)).card = 2 := Finset.card_pair (Ne.symm hmk)
        have c2 : ({l, m, k'} : Finset (Fin 4)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hlm, hlk']), Finset.card_pair hmk']
        have := Finset.card_le_card e1; have := Finset.card_le_card e2
        omega
      · push_neg at hls
        have hlp : 0 < W l := lt_of_le_of_ne hls (Ne.symm hl0)
        have m3 : q3 ∈ L := hup q3 (by
          show 1 < W l - W k' + (∑ j, |W j| - |W l| - |W k'|); rw [hsabs, ak, ak', abs_of_pos hlp, hm0]; simp only [abs_zero]; linarith)
        have e1 : ({k, l, m} : Finset (Fin 4)) ⊆ L.image fun p => p.1.1 := by
          intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl | rfl
          · exact hπ L _ q2 m2
          · exact hπ L _ q3 m3
          · exact hπ L _ q4 m4
        have e2 : ({m, k'} : Finset (Fin 4)) ⊆ L.image fun p => p.1.2 := by
          intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl
          · exact hπ L _ q2 m2
          · exact hπ L _ q4 m4
        have c1 : ({k, l, m} : Finset (Fin 4)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [Ne.symm hlk, Ne.symm hmk]),
            Finset.card_pair hlm]
        have c2 : ({m, k'} : Finset (Fin 4)).card = 2 := Finset.card_pair hmk'
        have := Finset.card_le_card e1; have := Finset.card_le_card e2
        omega
  · -- `Wc m ≠ 0`
    have hma : 0 < |W m| := abs_pos.2 hm0
    have m1 : q1 ∈ L := hup q1 (by show 1 < W k - W l + (∑ j, |W j| - |W k| - |W l|); rw [hsabs, ak, ak']; linarith)
    have m3 : q3 ∈ L := hup q3 (by show 1 < W l - W k' + (∑ j, |W j| - |W l| - |W k'|); rw [hsabs, ak, ak']; linarith)
    apply hbig
    by_cases hms : W m < 0
    · have m2 : q2 ∈ L := hup q2 (by
        show 1 < W k - W m + (∑ j, |W j| - |W k| - |W m|); rw [hsabs, ak, ak', abs_of_neg hms]; linarith)
      have e1 : ({k, l} : Finset (Fin 4)) ⊆ L.image fun p => p.1.1 := by
        intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact hπ L _ q1 m1
        · exact hπ L _ q3 m3
      have e2 : ({l, m, k'} : Finset (Fin 4)) ⊆ L.image fun p => p.1.2 := by
        intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl
        · exact hπ L _ q1 m1
        · exact hπ L _ q2 m2
        · exact hπ L _ q3 m3
      have c1 : ({k, l} : Finset (Fin 4)).card = 2 := Finset.card_pair (Ne.symm hlk)
      have c2 : ({l, m, k'} : Finset (Fin 4)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hlm, hlk']), Finset.card_pair hmk']
      have := Finset.card_le_card e1; have := Finset.card_le_card e2
      omega
    · push_neg at hms
      have hmp : 0 < W m := lt_of_le_of_ne hms (Ne.symm hm0)
      have m4 : q4 ∈ L := hup q4 (by
        show 1 < W m - W k' + (∑ j, |W j| - |W m| - |W k'|); rw [hsabs, ak, ak', abs_of_pos hmp]; linarith)
      have e1 : ({k, l, m} : Finset (Fin 4)) ⊆ L.image fun p => p.1.1 := by
        intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl
        · exact hπ L _ q1 m1
        · exact hπ L _ q3 m3
        · exact hπ L _ q4 m4
      have e2 : ({l, k'} : Finset (Fin 4)) ⊆ L.image fun p => p.1.2 := by
        intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact hπ L _ q1 m1
        · exact hπ L _ q3 m3
      have c1 : ({k, l, m} : Finset (Fin 4)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hlk, Ne.symm hmk]),
          Finset.card_pair hlm]
      have c2 : ({l, k'} : Finset (Fin 4)).card = 2 := Finset.card_pair hlk'
      have := Finset.card_le_card e1; have := Finset.card_le_card e2
      omega


lemma bip2 : ∀ A1 A2 : Finset (Fin 4),
    (Finset.univ.filter (fun p : Pr => p.1.1 ∈ A1 ∧ p.1.2 ∈ A2)).card ≤ A1.card + A2.card + 2 ∨
      (A1 = Finset.univ ∧ A2 = Finset.univ) := by
  decide

/-- Every `|W d|` over the rest vanishes when their sum does. -/
lemma rest_zero (W : Fin 4 → ℝ) (p : Pr) (h : ∑ j ∈ p.rest, |W j| ≤ 0) : ∀ d ∈ p.rest, W d = 0 := by
  intro d hd
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (W j))).1
    (le_antisymm h (Finset.sum_nonneg fun j _ => abs_nonneg (W j))) d hd
  exact abs_eq_zero.1 h0

/-- Two distinct pairs of a column cover the other indices by their rests. -/
lemma col_cover {q1 q2 : Pr} (h2 : q1.1.2 = q2.1.2) (hne : q1 ≠ q2) (d : Fin 4) (hd : d ≠ q1.1.2) :
    d ∈ q1.rest ∨ d ∈ q2.rest := by
  have h1 : q1.1.1 ≠ q2.1.1 := fun h => hne (Subtype.ext (Prod.ext h h2))
  simp only [Pr.rest, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hd1 : d = q1.1.1
  · right; refine ⟨?_, ?_⟩
    · rw [hd1]; exact h1
    · rw [← h2]; exact hd
  · left; exact ⟨hd1, hd⟩

lemma row_cover {q1 q2 : Pr} (h1 : q1.1.1 = q2.1.1) (hne : q1 ≠ q2) (d : Fin 4) (hd : d ≠ q1.1.1) :
    d ∈ q1.rest ∨ d ∈ q2.rest := by
  have h2 : q1.1.2 ≠ q2.1.2 := fun h => hne (Subtype.ext (Prod.ext h1 h))
  simp only [Pr.rest, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hd2 : d = q1.1.2
  · right; refine ⟨?_, ?_⟩
    · rw [← h1]; exact hd
    · rw [hd2]; exact h2
  · left; exact ⟨hd, hd2⟩

/-- Two distinct elements of a large set in a column (at most one pair is missing). -/
lemma two_in_col (U : Finset Pr) (hU : (Finset.univ \ U).card ≤ 1) (k : Fin 4) :
    ∃ q1 ∈ U, ∃ q2 ∈ U, q1 ≠ q2 ∧ q1.1.2 = k ∧ q2.1.2 = k := by
  have hc : 2 ≤ (colF k ∩ U).card := by
    have h1 := Finset.card_le_card (show colF k \ U ⊆ Finset.univ \ U from
      Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl)
    have h2 := Finset.card_sdiff_add_card_inter (colF k) U
    have h3 := card_colF k
    omega
  obtain ⟨q1, hq1, q2, hq2, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < (colF k ∩ U).card)
  rw [Finset.mem_inter] at hq1 hq2
  simp only [colF, Finset.mem_filter, Finset.mem_univ, true_and] at hq1 hq2
  exact ⟨q1, hq1.2, q2, hq2.2, hne, hq1.1, hq2.1⟩

lemma two_in_row (U : Finset Pr) (hU : (Finset.univ \ U).card ≤ 1) (k : Fin 4) :
    ∃ q1 ∈ U, ∃ q2 ∈ U, q1 ≠ q2 ∧ q1.1.1 = k ∧ q2.1.1 = k := by
  have hc : 2 ≤ (rowF k ∩ U).card := by
    have h1 := Finset.card_le_card (show rowF k \ U ⊆ Finset.univ \ U from
      Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl)
    have h2 := Finset.card_sdiff_add_card_inter (rowF k) U
    have h3 := card_rowF k
    omega
  obtain ⟨q1, hq1, q2, hq2, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < (rowF k ∩ U).card)
  rw [Finset.mem_inter] at hq1 hq2
  simp only [rowF, Finset.mem_filter, Finset.mem_univ, true_and] at hq1 hq2
  exact ⟨q1, hq1.2, q2, hq2.2, hne, hq1.1, hq2.1⟩

/-- `W` vanishes everywhere if it vanishes off `k1` and off `k2 ≠ k1`. -/
lemma W_zero_of_two {W : Fin 4 → ℝ} {k1 k2 : Fin 4} (hk : k1 ≠ k2) (h1 : ∀ d, d ≠ k1 → W d = 0)
    (h2 : ∀ d, d ≠ k2 → W d = 0) (d : Fin 4) : W d = 0 := by
  by_cases hd : d = k1
  · exact h2 d (by rw [hd]; exact hk)
  · exact h1 d hd

/-- **Concurrent case with loose adjacency.** -/
lemma comb_concurrent_loose (W : Fin 4 → ℝ) (ξ : ℝ) (hz1 : -1 < ξ + ∑ j, W j)
    (hz2 : ξ + ∑ j, W j < 1) (U0 U1 US : Finset Pr)
    (h0 : ∀ p ∈ U0, 1 ≤ W p.1.1 - W p.1.2 - ∑ j ∈ p.rest, |W j| - ξ)
    (h1 : ∀ p ∈ U1, 1 ≤ W p.1.1 - W p.1.2 - ∑ j ∈ p.rest, |W j| + ξ)
    (hS : ∀ p ∈ US, 1 ≤ W p.1.1 - W p.1.2 - ∑ j ∈ p.rest, |W j| - |ξ|)
    (LS : Finset Pr) (hLS : ∀ p : Pr, 1 < W p.1.1 - W p.1.2 + |ξ| + ∑ j ∈ p.rest, |W j| → p ∈ LS)
    (E : ℕ)
    (hE1 : ((U0 ∪ US).image fun p => p.1.1).card + (U1.image fun p => p.1.1).card +
      (U0.image fun p => p.1.2).card + ((U1 ∪ US).image fun p => p.1.2).card ≤ E)
    (hE2 : (U0.image fun p => p.1.1).card + (U0.image fun p => p.1.2).card +
      ((U0.filter (· ∈ LS)).image fun p => p.1.2).card ≤ E)
    (hE3 : (U1.image fun p => p.1.1).card + ((U1.filter (· ∈ LS)).image fun p => p.1.1).card +
      (U1.image fun p => p.1.2).card ≤ E) :
    U0.card + U1.card + US.card ≤ max 5 E + 2 := by
  classical
  set ψ : Pr → ℝ := fun p => W p.1.1 - W p.1.2 - ∑ j ∈ p.rest, |W j| with hψ
  have hconf : ∀ p q : Pr, p.1.1 ≠ q.1.1 → p.1.2 ≠ q.1.2 → ψ p + ψ q ≤ 0 :=
    fun p q a b => psi_conflict W p q a b
  have hm5 := le_max_left 5 E
  have hmE := le_max_right 5 E
  by_cases hsmall : U0.card + U1.card + US.card ≤ 7
  · omega
  push_neg at hsmall
  have hrowc : ∀ (k : Fin 4) (S : Finset Pr), S ⊆ rowF k → S.card ≤ 3 := fun k S hS =>
    (Finset.card_le_card hS).trans (card_rowF k).le
  have hcolc : ∀ (k : Fin 4) (S : Finset Pr), S ⊆ colF k → S.card ≤ 3 := fun k S hS =>
    (Finset.card_le_card hS).trans (card_colF k).le
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
    have hU0 : U0 ⊆ Ψ1 := fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, by
      have := h0 p hp; have := neg_abs_le ξ; simp only [hψ]; linarith⟩
    have hU1 : U1 ⊆ Ψ1 := fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, by
      have := h1 p hp; have := le_abs_self ξ; simp only [hψ]; linarith⟩
    have hUS : US ⊆ Ψ1 := fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, by
      have := hS p hp; have := abs_nonneg ξ; simp only [hψ]; linarith⟩
    have hUS3 : US ⊆ Ψ3 := fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, by
      have := hS p hp; simp only [hψ]; linarith⟩
    -- a second element of `Ψ3`
    have hΨ1C : Ψ1 ⊆ Finset.univ.filter (Pr.compat p0) := fun q hq =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hcompat p0 hp0Ψ3 q hq⟩
    have hΨ1c5 : Ψ1.card ≤ 5 := (Finset.card_le_card hΨ1C).trans (card_compat p0).le
    obtain ⟨p1, hp1, hp10⟩ : ∃ p1 ∈ Ψ3, p1 ≠ p0 := by
      by_contra hcon
      push_neg at hcon
      have hsub : Ψ3 ⊆ {p0} := fun q hq => Finset.mem_singleton.2 (hcon q hq)
      have hΨ3c := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hΨ3c
      have h31 : US.card ≤ 1 := (Finset.card_le_card hUS3).trans hΨ3c
      rcases le_total ξ 0 with hξ | hξ
      · have hU13 : U1 ⊆ Ψ3 := fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, by
          have := h1 p hp; rw [abs_of_nonpos hξ]; simp only [hψ]; linarith⟩
        have := (Finset.card_le_card hU13).trans hΨ3c
        have := (Finset.card_le_card hU0).trans hΨ1c5
        omega
      · have hU03 : U0 ⊆ Ψ3 := fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, by
          have := h0 p hp; rw [abs_of_nonneg hξ]; simp only [hψ]; linarith⟩
        have := (Finset.card_le_card hU03).trans hΨ3c
        have := (Finset.card_le_card hU1).trans hΨ1c5
        omega
    have h01 := hcompat p0 hp0Ψ3 p1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, by
      have := (Finset.mem_filter.1 hp1).2; have := abs_nonneg ξ; linarith⟩)
    have hboth : ∀ q ∈ Ψ1, Pr.compat p0 q ∧ Pr.compat p1 q := fun q hq =>
      ⟨hcompat p0 hp0Ψ3 q hq, hcompat p1 hp1 q hq⟩
    rcases h01 with hrow | hcol
    · -- everything in the row of `p0`
      have hin : ∀ q ∈ Ψ1, q.1.1 = p0.1.1 := by
        intro q hq
        rcases hboth q hq with ⟨e0 | e0, e1 | e1⟩
        · exact e0.symm
        · exact e0.symm
        · rw [← hrow] at e1; exact e1.symm
        · exfalso; apply hp10; exact Subtype.ext (Prod.ext hrow.symm (e1.trans e0.symm))
      have hsub : ∀ S ⊆ Ψ1, S ⊆ rowF p0.1.1 := fun S hS q hq => by
        simp only [rowF, Finset.mem_filter, Finset.mem_univ, true_and]; exact hin q (hS hq)
      have c0 := hrowc _ U0 (hsub U0 hU0)
      have c1 := hrowc _ U1 (hsub U1 hU1)
      have cS := hrowc _ US (hsub US hUS)
      have hinj2 : ∀ S ⊆ Ψ1, (S.image fun p => p.1.2).card = S.card := fun S hS =>
        Finset.card_image_of_injOn fun a ha b hb h =>
          Subtype.ext (Prod.ext ((hin a (hS ha)).trans (hin b (hS hb)).symm) h)
      have hone : ∀ S ⊆ Ψ1, S.Nonempty → (S.image fun p => p.1.1).card = 1 := by
        intro S hS hne
        rw [Finset.card_eq_one]
        refine ⟨p0.1.1, ?_⟩
        ext d
        simp only [Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨q, hq, rfl⟩; exact hin q (hS hq)
        · rintro rfl; obtain ⟨q, hq⟩ := hne; exact ⟨q, hq, hin q (hS hq)⟩
      have hne1 : U1.Nonempty := Finset.card_pos.1 (by omega)
      have hne0S : (U0 ∪ US).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro he
        have := Finset.card_le_card (show U0 ⊆ U0 ∪ US from Finset.subset_union_left)
        have := Finset.card_le_card (show US ⊆ U0 ∪ US from Finset.subset_union_right)
        rw [he, Finset.card_empty] at *; omega
      have e1 := hone (U0 ∪ US) (Finset.union_subset hU0 hUS) hne0S
      have e2 := hone U1 hU1 hne1
      have e3 := hinj2 U0 hU0
      have e4 := hinj2 (U1 ∪ US) (Finset.union_subset hU1 hUS)
      have e5 := Finset.card_union_add_card_inter U1 US
      have e6 := Finset.card_le_card (show U1 ∩ US ⊆ US from Finset.inter_subset_right)
      omega
    · -- everything in the column of `p0`
      have hin : ∀ q ∈ Ψ1, q.1.2 = p0.1.2 := by
        intro q hq
        rcases hboth q hq with ⟨e0 | e0, e1 | e1⟩
        · exfalso; apply hp10; exact Subtype.ext (Prod.ext (e1.trans e0.symm) hcol.symm)
        · rw [← hcol] at e1; exact e1.symm
        · exact e0.symm
        · exact e0.symm
      have hsub : ∀ S ⊆ Ψ1, S ⊆ colF p0.1.2 := fun S hS q hq => by
        simp only [colF, Finset.mem_filter, Finset.mem_univ, true_and]; exact hin q (hS hq)
      have c0 := hcolc _ U0 (hsub U0 hU0)
      have c1 := hcolc _ U1 (hsub U1 hU1)
      have cS := hcolc _ US (hsub US hUS)
      have hinj1 : ∀ S ⊆ Ψ1, (S.image fun p => p.1.1).card = S.card := fun S hS =>
        Finset.card_image_of_injOn fun a ha b hb h =>
          Subtype.ext (Prod.ext h ((hin a (hS ha)).trans (hin b (hS hb)).symm))
      have hone : ∀ S ⊆ Ψ1, S.Nonempty → (S.image fun p => p.1.2).card = 1 := by
        intro S hS hne
        rw [Finset.card_eq_one]
        refine ⟨p0.1.2, ?_⟩
        ext d
        simp only [Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨q, hq, rfl⟩; exact hin q (hS hq)
        · rintro rfl; obtain ⟨q, hq⟩ := hne; exact ⟨q, hq, hin q (hS hq)⟩
      have hne0 : U0.Nonempty := Finset.card_pos.1 (by omega)
      have hne1S : (U1 ∪ US).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro he
        have := Finset.card_le_card (show U1 ⊆ U1 ∪ US from Finset.subset_union_left)
        have := Finset.card_le_card (show US ⊆ U1 ∪ US from Finset.subset_union_right)
        rw [he, Finset.card_empty] at *; omega
      have e1 := hinj1 (U0 ∪ US) (Finset.union_subset hU0 hUS)
      have e2 := hinj1 U1 hU1
      have e3 := hone U0 hU0 hne0
      have e4 := hone (U1 ∪ US) (Finset.union_subset hU1 hUS) hne1S
      have e5 := Finset.card_union_add_card_inter U0 US
      have e6 := Finset.card_le_card (show U0 ∩ US ⊆ US from Finset.inter_subset_right)
      omega
  · push_neg at hB
    have hUS : US = ∅ := Finset.eq_empty_of_forall_notMem fun p hp => by
      have := hS p hp; have := hB p; simp only [hψ] at this; linarith
    rw [hUS, Finset.card_empty, add_zero] at hsmall ⊢
    rcases lt_trichotomy ξ 0 with hξ | hξ | hξ
    · -- only the `s0`-candidates can be up
      have hU1 : U1 = ∅ := Finset.eq_empty_of_forall_notMem fun p hp => by
        have := h1 p hp; have := hB p; rw [abs_of_neg hξ] at this; simp only [hψ] at this
        linarith
      rw [hU1, Finset.card_empty, add_zero] at hsmall ⊢
      set A1 := U0.image fun p => p.1.1 with hA1
      set A2 := U0.image fun p => p.1.2 with hA2
      have hsub : U0 ⊆ Finset.univ.filter (fun p : Pr => p.1.1 ∈ A1 ∧ p.1.2 ∈ A2) := fun p hp =>
        Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ hp,
          Finset.mem_image_of_mem _ hp⟩
      rcases bip2 A1 A2 with hb | ⟨hu1, hu2⟩
      · have := Finset.card_le_card hsub; omega
      · have c1 : A1.card = 4 := by rw [hu1]; rfl
        have c2 : A2.card = 4 := by rw [hu2]; rfl
        by_cases h10 : U0.card ≤ 10
        · omega
        push_neg at h10
        -- at least three new endpoints from the loose same-sign candidates
        have hcompl : (Finset.univ \ U0).card ≤ 1 := by
          have := Finset.card_sdiff_add_card_inter Finset.univ U0
          have h12 : (Finset.univ : Finset Pr).card = 12 := by rfl
          rw [Finset.univ_inter, h12] at this; omega
        have hzero : ∀ q ∈ U0, q ∉ LS → ∀ d ∈ q.rest, W d = 0 := by
          intro q hq hqL
          apply rest_zero W q
          have e1 := h0 q hq
          have e2 : ¬ (1 < W q.1.1 - W q.1.2 + |ξ| + ∑ j ∈ q.rest, |W j|) := fun h => hqL (hLS q h)
          push_neg at e2
          rw [abs_of_neg hξ] at e2
          linarith
        set N := (U0.filter (· ∈ LS)).image fun p => p.1.2 with hN
        have hN3 : 3 ≤ N.card := by
          by_contra hlt
          push_neg at hlt
          obtain ⟨k1, hk1, k2, hk2, hk12⟩ : ∃ k1 ∉ N, ∃ k2 ∉ N, k1 ≠ k2 := by
            have hc : 2 ≤ (Finset.univ \ N).card := by
              have := Finset.card_sdiff_add_card_inter Finset.univ N
              rw [Finset.univ_inter] at this
              have h4 : (Finset.univ : Finset (Fin 4)).card = 4 := by rfl
              omega
            obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < (Finset.univ \ N).card)
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at ha hb
            exact ⟨a, ha, b, hb, hab⟩
          have hsupp : ∀ k ∉ N, ∀ d, d ≠ k → W d = 0 := by
            intro k hk d hd
            obtain ⟨q1, hq1, q2, hq2, hne, e1, e2⟩ := two_in_col U0 hcompl k
            have hq1L : q1 ∉ LS := fun h => hk (Finset.mem_image.2
              ⟨q1, Finset.mem_filter.2 ⟨hq1, h⟩, e1⟩)
            have hq2L : q2 ∉ LS := fun h => hk (Finset.mem_image.2
              ⟨q2, Finset.mem_filter.2 ⟨hq2, h⟩, e2⟩)
            rcases col_cover (e1.trans e2.symm) hne d (by rw [e1]; exact hd) with h | h
            · exact hzero q1 hq1 hq1L d h
            · exact hzero q2 hq2 hq2L d h
          have hW0 := W_zero_of_two hk12 (hsupp k1 hk1) (hsupp k2 hk2)
          obtain ⟨q, hq⟩ := Finset.card_pos.1 (by omega : 0 < U0.card)
          have e1 := h0 q hq
          simp only [hW0, abs_zero, Finset.sum_const_zero, sub_zero] at e1
          simp only [hW0, Finset.sum_const_zero, add_zero] at hz1
          linarith
        have h12 : U0.card ≤ 12 := by
          have := Finset.card_le_card (Finset.subset_univ U0)
          rwa [show (Finset.univ : Finset Pr).card = 12 from rfl] at this
        omega
    · -- `ξ = 0`: nothing is up
      have hU0 : U0 = ∅ := Finset.eq_empty_of_forall_notMem fun p hp => by
        have := h0 p hp; have := hB p; rw [hξ, abs_zero] at this; simp only [hψ] at this
        rw [hξ] at *; linarith
      have hU1 : U1 = ∅ := Finset.eq_empty_of_forall_notMem fun p hp => by
        have := h1 p hp; have := hB p; rw [hξ, abs_zero] at this; simp only [hψ] at this
        rw [hξ] at *; linarith
      rw [hU0, hU1] at hsmall; simp at hsmall
    · -- only the `oth s0`-candidates can be up
      have hU0 : U0 = ∅ := Finset.eq_empty_of_forall_notMem fun p hp => by
        have := h0 p hp; have := hB p; rw [abs_of_pos hξ] at this; simp only [hψ] at this
        linarith
      rw [hU0, Finset.card_empty, zero_add] at hsmall ⊢
      set A1 := U1.image fun p => p.1.1 with hA1
      set A2 := U1.image fun p => p.1.2 with hA2
      have hsub : U1 ⊆ Finset.univ.filter (fun p : Pr => p.1.1 ∈ A1 ∧ p.1.2 ∈ A2) := fun p hp =>
        Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ hp,
          Finset.mem_image_of_mem _ hp⟩
      rcases bip2 A1 A2 with hb | ⟨hu1, hu2⟩
      · have := Finset.card_le_card hsub; omega
      · have c1 : A1.card = 4 := by rw [hu1]; rfl
        have c2 : A2.card = 4 := by rw [hu2]; rfl
        by_cases h10 : U1.card ≤ 10
        · omega
        push_neg at h10
        have hcompl : (Finset.univ \ U1).card ≤ 1 := by
          have := Finset.card_sdiff_add_card_inter Finset.univ U1
          have h12 : (Finset.univ : Finset Pr).card = 12 := by rfl
          rw [Finset.univ_inter, h12] at this; omega
        have hzero : ∀ q ∈ U1, q ∉ LS → ∀ d ∈ q.rest, W d = 0 := by
          intro q hq hqL
          apply rest_zero W q
          have e1 := h1 q hq
          have e2 : ¬ (1 < W q.1.1 - W q.1.2 + |ξ| + ∑ j ∈ q.rest, |W j|) := fun h => hqL (hLS q h)
          push_neg at e2
          rw [abs_of_pos hξ] at e2
          linarith
        set N := (U1.filter (· ∈ LS)).image fun p => p.1.1 with hN
        have hN3 : 3 ≤ N.card := by
          by_contra hlt
          push_neg at hlt
          obtain ⟨k1, hk1, k2, hk2, hk12⟩ : ∃ k1 ∉ N, ∃ k2 ∉ N, k1 ≠ k2 := by
            have hc : 2 ≤ (Finset.univ \ N).card := by
              have := Finset.card_sdiff_add_card_inter Finset.univ N
              rw [Finset.univ_inter] at this
              have h4 : (Finset.univ : Finset (Fin 4)).card = 4 := by rfl
              omega
            obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < (Finset.univ \ N).card)
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at ha hb
            exact ⟨a, ha, b, hb, hab⟩
          have hsupp : ∀ k ∉ N, ∀ d, d ≠ k → W d = 0 := by
            intro k hk d hd
            obtain ⟨q1, hq1, q2, hq2, hne, e1, e2⟩ := two_in_row U1 hcompl k
            have hq1L : q1 ∉ LS := fun h => hk (Finset.mem_image.2
              ⟨q1, Finset.mem_filter.2 ⟨hq1, h⟩, e1⟩)
            have hq2L : q2 ∉ LS := fun h => hk (Finset.mem_image.2
              ⟨q2, Finset.mem_filter.2 ⟨hq2, h⟩, e2⟩)
            rcases row_cover (e1.trans e2.symm) hne d (by rw [e1]; exact hd) with h | h
            · exact hzero q1 hq1 hq1L d h
            · exact hzero q2 hq2 hq2L d h
          have hW0 := W_zero_of_two hk12 (hsupp k1 hk1) (hsupp k2 hk2)
          obtain ⟨q, hq⟩ := Finset.card_pos.1 (by omega : 0 < U1.card)
          have e1 := h1 q hq
          simp only [hW0, abs_zero, Finset.sum_const_zero, sub_zero] at e1
          simp only [hW0, Finset.sum_const_zero, add_zero] at hz2
          linarith
        have h12 : U1.card ≤ 12 := by
          have := Finset.card_le_card (Finset.subset_univ U1)
          rwa [show (Finset.univ : Finset Pr).card = 12 from rfl] at this
        omega

end Kalai5
