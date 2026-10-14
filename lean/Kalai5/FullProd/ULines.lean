import Kalai5.FullProd.UStructure

/-!
# Pairwise coplanar lines

Lines `ℓᵢ = aᵢ + ℝ dᵢ` (`dᵢ = bᵢ - aᵢ ≠ 0`) that are pairwise coplanar (the relevant difference
vectors of each pair lie in a subspace of dimension at most two) but not all coplanar (the
differences span at least three dimensions):

* `lines_meet`: two coplanar lines with independent directions meet;
* `lines_concurrent`: if `ℓ₀, ℓ₁` meet at `p`, then `p ∈ ℓ₂`;
* `lines_parallel`: if `ℓ₀ ∥ ℓ₁`, then `ℓ₂ ∥ ℓ₀`.
-/

namespace Kalai5

open Module Submodule

/-- The span of two vectors has dimension at most two. -/
lemma finrank_span_pair_le (u v : E5) : finrank ℝ (span ℝ ({u, v} : Set E5)) ≤ 2 := by
  classical
  have h := finrank_span_finset_le_card (R := ℝ) ({u, v} : Finset E5)
  have hc : ({u, v} : Finset E5).card ≤ 2 := Finset.card_le_two
  have e : ((({u, v} : Finset E5)) : Set E5) = {u, v} := by ext; simp
  unfold Set.finrank at h
  rw [e] at h
  omega

/-- Two independent vectors of a subspace of dimension at most two span it. -/
lemma mem_span_pair_of_finrank_le {S : Submodule ℝ E5} (hS : finrank ℝ S ≤ 2) {u v w : E5}
    (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S) (huv : LinearIndependent ℝ ![u, v]) :
    ∃ α β : ℝ, w = α • u + β • v := by
  have hle : span ℝ {u, v} ≤ S := by
    rw [span_le]; intro z hz
    rcases hz with rfl | rfl
    · exact hu
    · exact hv
  have hr : Set.range ![u, v] = ({u, v} : Set E5) := by
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
    · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
  have h2 : finrank ℝ (span ℝ ({u, v} : Set E5)) = 2 := by
    rw [← hr, finrank_span_eq_card huv]; simp
  have heq : span ℝ {u, v} = S := eq_of_le_of_finrank_le hle (by omega)
  rw [← heq] at hw
  obtain ⟨α, β, h⟩ := mem_span_pair.1 hw
  exact ⟨α, β, h.symm⟩

/-- **Two coplanar lines with independent directions meet.** -/
lemma lines_meet {a0 b0 a1 b1 : E5} {S : Submodule ℝ E5} (hS : finrank ℝ S ≤ 2)
    (h0 : b0 - a0 ∈ S) (h1 : b1 - a1 ∈ S) (h01 : a1 - a0 ∈ S)
    (hind : LinearIndependent ℝ ![b0 - a0, b1 - a1]) :
    ∃ s0 s1 : ℝ, a0 + s0 • (b0 - a0) = a1 + s1 • (b1 - a1) := by
  obtain ⟨α, β, h⟩ := mem_span_pair_of_finrank_le hS h0 h1 h01 hind
  refine ⟨α, -β, ?_⟩
  rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, add_assoc, ← h]
  abel

/-- If two vectors lie in a subspace of dimension at most two together with two independent
vectors of it, everything lies in the span of the first two. -/
lemma span_le_of_indep {S : Submodule ℝ E5} (hS : finrank ℝ S ≤ 2) {u v : E5}
    (hu : u ∈ S) (hv : v ∈ S) (huv : LinearIndependent ℝ ![u, v]) :
    S ≤ span ℝ {u, v} := by
  have hle : span ℝ {u, v} ≤ S := by
    rw [span_le]; intro z hz
    rcases hz with rfl | rfl
    · exact hu
    · exact hv
  have hr : Set.range ![u, v] = ({u, v} : Set E5) := by
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
    · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
  have h2 : finrank ℝ (span ℝ ({u, v} : Set E5)) = 2 := by
    rw [← hr, finrank_span_eq_card huv]; simp
  exact (eq_of_le_of_finrank_le hle (by omega)).symm.le

/-- **Concurrency**: if `ℓ₀, ℓ₁` meet at `p`, the third line passes through `p`. -/
lemma lines_concurrent {p d0 d1 a2 d2 : E5} {S02 S12 : Submodule ℝ E5}
    (h02 : finrank ℝ S02 ≤ 2) (h12 : finrank ℝ S12 ≤ 2)
    (m02 : d0 ∈ S02 ∧ a2 - p ∈ S02 ∧ d2 ∈ S02) (m12 : d1 ∈ S12 ∧ a2 - p ∈ S12 ∧ d2 ∈ S12)
    (hT : 3 ≤ finrank ℝ (span ℝ ({d0, d1, a2 - p, d2} : Set E5))) (hd2 : d2 ≠ 0) :
    ∃ s : ℝ, p = a2 + s • d2 := by
  by_cases hind : LinearIndependent ℝ ![a2 - p, d2]
  · exfalso
    have hS02 := span_le_of_indep h02 m02.2.1 m02.2.2 hind
    have hS12 := span_le_of_indep h12 m12.2.1 m12.2.2 hind
    have hle : span ℝ ({d0, d1, a2 - p, d2} : Set E5) ≤ span ℝ {a2 - p, d2} := by
      rw [span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact hS02 m02.1
      · exact hS12 m12.1
      · exact subset_span (by simp)
      · exact subset_span (by simp)
    have h2 : finrank ℝ (span ℝ ({a2 - p, d2} : Set E5)) ≤ 2 := finrank_span_pair_le _ _
    have := Submodule.finrank_mono hle
    omega
  · -- `a2 - p` is a multiple of `d2`
    rw [LinearIndependent.pair_iff] at hind
    push_neg at hind
    obtain ⟨s, t, hst, hne⟩ := hind
    have hs : s ≠ 0 := by
      intro hs0
      have ht := hne hs0
      rw [hs0, zero_smul, zero_add] at hst
      exact hd2 ((smul_eq_zero.1 hst).resolve_left ht)
    refine ⟨t / s, ?_⟩
    have : a2 - p = -(t / s) • d2 := by
      have h' : s • (a2 - p) = -(t • d2) := eq_neg_of_add_eq_zero_left hst
      have := congrArg (fun z => s⁻¹ • z) h'
      simp only [smul_smul, inv_mul_cancel₀ hs, one_smul] at this
      rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
    rw [neg_smul] at this
    rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, sub_eq_zero] at this
    exact this.symm

/-- **Parallelism**: if `ℓ₁ ∥ ℓ₀`, then `ℓ₂ ∥ ℓ₀`. -/
lemma lines_parallel {a0 d0 a1 a2 d2 : E5} {S02 S12 : Submodule ℝ E5}
    (h02 : finrank ℝ S02 ≤ 2) (h12 : finrank ℝ S12 ≤ 2)
    (m02 : d0 ∈ S02 ∧ a2 - a0 ∈ S02 ∧ d2 ∈ S02) (m12 : d0 ∈ S12 ∧ a2 - a1 ∈ S12 ∧ d2 ∈ S12)
    (hT : 3 ≤ finrank ℝ (span ℝ ({d0, a1 - a0, a2 - a0, d2} : Set E5))) (hd0 : d0 ≠ 0) :
    ∃ μ : ℝ, d2 = μ • d0 := by
  by_cases hind : LinearIndependent ℝ ![d0, d2]
  · exfalso
    have hS02 := span_le_of_indep h02 m02.1 m02.2.2 hind
    have hS12 := span_le_of_indep h12 m12.1 m12.2.2 hind
    have hle : span ℝ ({d0, a1 - a0, a2 - a0, d2} : Set E5) ≤ span ℝ {d0, d2} := by
      rw [span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact subset_span (by simp)
      · have h1 : a2 - a0 ∈ span ℝ ({d0, d2} : Set E5) := hS02 m02.2.1
        have h2 : a2 - a1 ∈ span ℝ ({d0, d2} : Set E5) := hS12 m12.2.1
        have := sub_mem h1 h2
        rwa [sub_sub_sub_cancel_left] at this
      · exact hS02 m02.2.1
      · exact subset_span (by simp)
    have h2 : finrank ℝ (span ℝ ({d0, d2} : Set E5)) ≤ 2 := finrank_span_pair_le _ _
    have := Submodule.finrank_mono hle
    omega
  · rw [LinearIndependent.pair_iff] at hind
    push_neg at hind
    obtain ⟨s, t, hst, hne⟩ := hind
    have ht : t ≠ 0 := by
      intro ht0
      rw [ht0, zero_smul, add_zero] at hst
      have hs : s ≠ 0 := fun hs0 => hne hs0 ht0
      exact hd0 ((smul_eq_zero.1 hst).resolve_left hs)
    refine ⟨-(s / t), ?_⟩
    have h' : t • d2 = -(s • d0) := eq_neg_of_add_eq_zero_right hst
    have := congrArg (fun z => t⁻¹ • z) h'
    simp only [smul_smul, inv_mul_cancel₀ ht, one_smul] at this
    rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

end Kalai5
