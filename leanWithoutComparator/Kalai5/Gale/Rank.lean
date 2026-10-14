import Kalai5.Gale.Signs

/-!
# Rank of a subconfiguration from the sign codes

`finrank_span_image`: the vectors `g '' A` span a space of dimension `0` (all zero), `1` (all
nonzero vectors on one line) or `2`; and `nlines (List.ofFn c) = m`.
-/

namespace Kalai5.Gale

open Module

variable {n : ℕ}

open Classical in
/-- Combinatorial rank of the codes indexed by `A`. -/
noncomputable def crank (c : Fin n → ℕ) (A : Finset (Fin n)) : ℕ :=
  if ∀ j ∈ A, c j = 0 then 0
  else if ∃ i, ∀ j ∈ A, c j ≠ 0 → cline (c j) = i then 1 else 2

namespace CodeFor

variable {g : Fin n → Fin 2 → ℝ} {c : Fin n → ℕ} {m : ℕ} (hc : CodeFor g c m)
include hc

lemma smul_of_same_line {j j0 : Fin n} (hj : c j ≠ 0) (hj0 : c j0 ≠ 0)
    (h : cline (c j) = cline (c j0)) : g j = (g j 0 / g j0 0) • g j0 := by
  have h0 := hc.fst_ne j0 hj0
  have h1 := hc.fst_ne j hj
  have hs := (hc.eq_iff hj hj0).1 h
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]; field_simp
  · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
    rw [snd_eq_mul_slope (g j) h1, snd_eq_mul_slope (g j0) h0, hs]
    field_simp

lemma linearIndependent_of_line_ne {j1 j2 : Fin n} (h1 : c j1 ≠ 0) (h2 : c j2 ≠ 0)
    (h : cline (c j1) ≠ cline (c j2)) : LinearIndependent ℝ ![g j1, g j2] := by
  have hs : slope (g j1) ≠ slope (g j2) := fun e => h ((hc.eq_iff h1 h2).2 e)
  have hw : wedge (g j1) (g j2) ≠ 0 := by
    rw [wedge_eq _ _ (hc.fst_ne j1 h1) (hc.fst_ne j2 h2)]
    exact mul_ne_zero (mul_ne_zero (hc.fst_ne j1 h1) (hc.fst_ne j2 h2)) (sub_ne_zero.2 hs.symm)
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have e0 := congrFun hst 0
  have e1 := congrFun hst 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e0 e1
  unfold wedge at hw
  constructor
  · have : s * (g j1 0 * g j2 1 - g j1 1 * g j2 0) = 0 := by linear_combination g j2 1 * e0 - g j2 0 * e1
    exact (mul_eq_zero.1 this).resolve_right hw
  · have : t * (g j1 0 * g j2 1 - g j1 1 * g j2 0) = 0 := by linear_combination g j1 0 * e1 - g j1 1 * e0
    exact (mul_eq_zero.1 this).resolve_right hw

/-- **The rank of a subconfiguration is read off the codes.** -/
theorem finrank_span_image (A : Finset (Fin n)) :
    finrank ℝ (Submodule.span ℝ (g '' ↑A)) = crank c A := by
  classical
  unfold crank
  by_cases h0 : ∀ j ∈ A, c j = 0
  · rw [if_pos h0]
    have : Submodule.span ℝ (g '' ↑A) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨j, hj, rfl⟩
      exact hc.zero_of_code (h0 j hj)
    rw [this, finrank_bot]
  rw [if_neg h0]
  push_neg at h0
  obtain ⟨j0, hj0A, hj0⟩ := h0
  by_cases h1 : ∃ i, ∀ j ∈ A, c j ≠ 0 → cline (c j) = i
  · rw [if_pos h1]
    obtain ⟨i, hi⟩ := h1
    have hspan : Submodule.span ℝ (g '' ↑A) = ℝ ∙ g j0 := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨j, hj, rfl⟩
        by_cases hcj : c j = 0
        · rw [hc.zero_of_code hcj]; exact Submodule.zero_mem _
        · rw [hc.smul_of_same_line hcj hj0 ((hi j hj hcj).trans (hi j0 hj0A hj0).symm)]
          exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · rw [Submodule.span_singleton_le_iff_mem]
        exact Submodule.subset_span ⟨j0, hj0A, rfl⟩
    rw [hspan, finrank_span_singleton]
    exact fun h => hj0 ((hc.zero_iff j0).2 h)
  · rw [if_neg h1]
    push_neg at h1
    obtain ⟨j, hjA, hj, hne⟩ := h1 (cline (c j0))
    have hli := hc.linearIndependent_of_line_ne hj0 hj (Ne.symm hne)
    apply le_antisymm
    · have := Submodule.finrank_le (Submodule.span ℝ (g '' ↑A))
      rwa [Module.finrank_fin_fun] at this
    · have h2 : finrank ℝ (Submodule.span ℝ (Set.range ![g j0, g j])) = 2 := by
        rw [finrank_span_eq_card hli, Fintype.card_fin]
      have hsub : Set.range ![g j0, g j] ⊆ g '' ↑A := by
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact ⟨j0, hj0A, rfl⟩
        · exact ⟨j, hjA, rfl⟩
      calc (2 : ℕ) = finrank ℝ (Submodule.span ℝ (Set.range ![g j0, g j])) := h2.symm
        _ ≤ finrank ℝ (Submodule.span ℝ (g '' ↑A)) :=
          Submodule.finrank_mono (Submodule.span_mono hsub)

end CodeFor

/-! ### The number of lines -/

lemma nlines_spec_aux (cs : List ℕ) (acc : ℕ) :
    let r := cs.foldl (fun acc c => if c == 0 then acc else max acc (cline c + 1)) acc
    acc ≤ r ∧ (∀ x ∈ cs, x ≠ 0 → cline x < r) ∧
      ∀ N, acc ≤ N → (∀ x ∈ cs, x ≠ 0 → cline x < N) → r ≤ N := by
  induction cs generalizing acc with
  | nil => simp
  | cons x cs ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih (if x == 0 then acc else max acc (cline x + 1))
    refine ⟨?_, ?_, ?_⟩
    · refine le_trans ?_ h1
      split <;> simp
    · intro y hy hy0
      rcases List.mem_cons.1 hy with rfl | hy
      · have : cline y + 1 ≤ if y == 0 then acc else max acc (cline y + 1) := by
          simp [hy0]
        omega
      · exact h2 y hy hy0
    · intro N hN hall
      apply h3 N
      · split
        · exact hN
        · exact max_le hN (hall x List.mem_cons_self (by simpa using ‹¬(x == 0) = true›))
      · exact fun y hy hy0 => hall y (List.mem_cons_of_mem _ hy) hy0

lemma lt_nlines {cs : List ℕ} {x : ℕ} (hx : x ∈ cs) (h0 : x ≠ 0) : cline x < nlines cs :=
  (nlines_spec_aux cs 0).2.1 x hx h0

lemma nlines_le {cs : List ℕ} {N : ℕ} (h : ∀ x ∈ cs, x ≠ 0 → cline x < N) : nlines cs ≤ N :=
  (nlines_spec_aux cs 0).2.2 N (Nat.zero_le _) h

lemma CodeFor.nlines_eq {g : Fin n → Fin 2 → ℝ} {c : Fin n → ℕ} {m : ℕ} (hc : CodeFor g c m) :
    nlines (List.ofFn c) = m := by
  apply le_antisymm
  · apply nlines_le
    intro x hx h0
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    exact hc.line_lt j h0
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Nat.zero_le _
    · obtain ⟨j, hj, hl⟩ := hc.used (m - 1) (by omega)
      have := lt_nlines (List.mem_ofFn.2 ⟨j, rfl⟩) hj
      omega

end Kalai5.Gale
