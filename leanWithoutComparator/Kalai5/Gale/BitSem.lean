import Kalai5.Gale.Bits

/-!
# Meaning of the bit-sliced vectors

For the tables `tab n`, bit `S` of each bit-sliced vector is the value of the corresponding
predicate at the subset with mask `S` (`S < 2 ^ n`).
-/

namespace Kalai5.Gale

variable {n : ℕ}

@[simp] lemma tab_n : (tab n).n = n := rfl

lemma testBit_one' (S : ℕ) : (1 : ℕ).testBit S = decide (S = 0) := by
  have h : (2 ^ 0 : ℕ).testBit S = decide (0 = S) := Nat.testBit_two_pow
  rw [pow_zero] at h
  rw [h]; simp [eq_comm]

lemma tab_full_testBit (S : ℕ) : (tab n).full.testBit S = decide (S < 2 ^ n) := by
  simp [tab, Nat.testBit_two_pow_sub_one]

lemma tab_bv_testBit {j : ℕ} (hj : j < n) (S : ℕ) :
    ((tab n).bv j).testBit S = (decide (S < 2 ^ n) && S.testBit j) := by
  simp [Tab.bv, tab, hj, testBit_maskOf]

lemma tab_nbv_testBit {j : ℕ} (hj : j < n) (S : ℕ) :
    ((tab n).nbv j).testBit S = (decide (S < 2 ^ n) && !S.testBit j) := by
  rw [Tab.nbv, Nat.testBit_xor, tab_full_testBit, tab_bv_testBit hj]
  cases decide (S < 2 ^ n) <;> cases S.testBit j <;> rfl

lemma tab_supV_testBit (x S : ℕ) :
    ((tab n).supV x).testBit S = true ↔
      S < 2 ^ n ∧ ∀ j < n, x.testBit j = true → S.testBit j = true := by
  unfold Tab.supV
  rw [testBit_andL, tab_full_testBit]
  simp only [tab_n, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_filterMap,
    List.mem_range]
  constructor
  · rintro ⟨hS, h⟩
    refine ⟨hS, fun j hj hx => ?_⟩
    have := h ((tab n).bv j) ⟨j, hj, by simp [hx]⟩
    rw [tab_bv_testBit hj] at this
    simpa [hS] using this
  · rintro ⟨hS, h⟩
    refine ⟨hS, ?_⟩
    rintro v ⟨j, hj, hv⟩
    by_cases hx : x.testBit j = true
    · rw [if_pos hx] at hv
      cases hv
      rw [tab_bv_testBit hj]
      simp [hS, h j hj hx]
    · rw [if_neg hx] at hv; cases hv

lemma tab_disjV_testBit (x S : ℕ) :
    ((tab n).disjV x).testBit S = true ↔
      S < 2 ^ n ∧ ∀ j < n, x.testBit j = true → S.testBit j = false := by
  unfold Tab.disjV
  rw [testBit_andL, tab_full_testBit]
  simp only [tab_n, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_filterMap,
    List.mem_range]
  constructor
  · rintro ⟨hS, h⟩
    refine ⟨hS, fun j hj hx => ?_⟩
    have := h ((tab n).nbv j) ⟨j, hj, by simp [hx]⟩
    rw [tab_nbv_testBit hj] at this
    simpa [hS] using this
  · rintro ⟨hS, h⟩
    refine ⟨hS, ?_⟩
    rintro v ⟨j, hj, hv⟩
    by_cases hx : x.testBit j = true
    · rw [if_pos hx] at hv
      cases hv
      rw [tab_nbv_testBit hj]
      simp [hS, h j hj hx]
    · rw [if_neg hx] at hv; cases hv

/-- Subsets that are unions of circuits. -/
lemma tab_covV_testBit (circ : List ℕ) (S : ℕ) :
    ((tab n).covV circ).testBit S = true ↔ S < 2 ^ n ∧ ∀ k < n, S.testBit k = true →
      ∃ x ∈ circ, x.testBit k = true ∧ ∀ j < n, x.testBit j = true → S.testBit j = true := by
  unfold Tab.covV
  rw [testBit_andL, tab_full_testBit]
  simp only [tab_n, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_map,
    List.mem_range]
  constructor
  · rintro ⟨hS, h⟩
    refine ⟨hS, fun k hk hSk => ?_⟩
    have := h _ ⟨k, hk, rfl⟩
    rw [Nat.testBit_lor, tab_nbv_testBit hk, testBit_orL] at this
    simp only [hS, decide_true, hSk, Bool.not_true, Bool.and_false, Bool.false_or,
      List.any_eq_true, List.mem_map, List.mem_filter] at this
    obtain ⟨v, ⟨x, ⟨hx, hxk⟩, rfl⟩, hv⟩ := this
    exact ⟨x, hx, hxk, ((tab_supV_testBit x S).1 hv).2⟩
  · rintro ⟨hS, h⟩
    refine ⟨hS, ?_⟩
    rintro v ⟨k, hk, rfl⟩
    rw [Nat.testBit_lor, tab_nbv_testBit hk, testBit_orL]
    by_cases hSk : S.testBit k = true
    · obtain ⟨x, hx, hxk, hxS⟩ := h k hk hSk
      simp only [Bool.or_eq_true, List.any_eq_true, List.mem_map, List.mem_filter]
      right
      exact ⟨_, ⟨x, ⟨hx, hxk⟩, rfl⟩, (tab_supV_testBit x S).2 ⟨hS, hxS⟩⟩
    · simp [hS, hSk]

/-- Subsets whose complement is a union of circuits (and nonempty). -/
lemma tab_faceV_testBit (circ : List ℕ) (S : ℕ) :
    ((tab n).faceV circ).testBit S = true ↔ S < 2 ^ n ∧ S ≠ 0 ∧ ∀ k < n, S.testBit k = false →
      ∃ x ∈ circ, x.testBit k = true ∧ ∀ j < n, x.testBit j = true → S.testBit j = false := by
  unfold Tab.faceV
  rw [Nat.testBit_land, testBit_andL, Nat.testBit_xor, tab_full_testBit, testBit_one']
  simp only [tab_n, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_map,
    List.mem_range]
  constructor
  · rintro ⟨⟨hS, h⟩, h1⟩
    have hS0 : S ≠ 0 := by
      rintro rfl; simp at h1
    refine ⟨hS, hS0, fun k hk hSk => ?_⟩
    have := h _ ⟨k, hk, rfl⟩
    rw [Nat.testBit_lor, tab_bv_testBit hk, testBit_orL] at this
    simp only [hS, decide_true, hSk, Bool.and_false, Bool.false_or,
      List.any_eq_true, List.mem_map, List.mem_filter] at this
    obtain ⟨v, ⟨x, ⟨hx, hxk⟩, rfl⟩, hv⟩ := this
    exact ⟨x, hx, hxk, ((tab_disjV_testBit x S).1 hv).2⟩
  · rintro ⟨hS, hS0, h⟩
    refine ⟨⟨hS, ?_⟩, ?_⟩
    · rintro v ⟨k, hk, rfl⟩
      rw [Nat.testBit_lor, tab_bv_testBit hk, testBit_orL]
      by_cases hSk : S.testBit k = true
      · simp [hS, hSk]
      · have hSk' : S.testBit k = false := by simpa using hSk
        obtain ⟨x, hx, hxk, hxS⟩ := h k hk hSk'
        simp only [Bool.or_eq_true, List.any_eq_true, List.mem_map, List.mem_filter]
        right
        exact ⟨_, ⟨x, ⟨hx, hxk⟩, rfl⟩, (tab_disjV_testBit x S).2 ⟨hS, hxS⟩⟩
    · simp [hS, hS0]

/-- Subsets certified by some candidate functional. -/
lemma tab_farV_testBit (cands : List (ℕ × ℕ)) (S : ℕ) :
    ((tab n).farV cands).testBit S = true ↔ S < 2 ^ n ∧ ∃ pn ∈ cands,
      (∀ j < n, pn.2.testBit j = true → S.testBit j = false) ∧
      ∃ j < n, pn.1.testBit j = true ∧ S.testBit j = true := by
  unfold Tab.farV
  rw [testBit_orL]
  simp only [List.any_eq_true, List.mem_map]
  constructor
  · rintro ⟨v, ⟨pn, hpn, rfl⟩, hv⟩
    rw [Nat.testBit_land, Nat.testBit_xor, tab_full_testBit, Bool.and_eq_true] at hv
    obtain ⟨h1, h2⟩ := hv
    obtain ⟨hS, hN⟩ := (tab_disjV_testBit pn.2 S).1 h1
    refine ⟨hS, pn, hpn, hN, ?_⟩
    by_contra hP
    push_neg at hP
    have : ((tab n).disjV pn.1).testBit S = true :=
      (tab_disjV_testBit pn.1 S).2 ⟨hS, fun j hj hx => by simpa using hP j hj hx⟩
    simp [hS, this] at h2
  · rintro ⟨hS, pn, hpn, hN, j, hj, hP, hSj⟩
    refine ⟨_, ⟨pn, hpn, rfl⟩, ?_⟩
    rw [Nat.testBit_land, Nat.testBit_xor, tab_full_testBit, Bool.and_eq_true]
    refine ⟨(tab_disjV_testBit pn.2 S).2 ⟨hS, hN⟩, ?_⟩
    have : ((tab n).disjV pn.1).testBit S = false := by
      by_contra h
      have h' := (tab_disjV_testBit pn.1 S).1 (by simpa using h)
      rw [h'.2 j hj hP] at hSj; exact absurd hSj (by simp)
    simp [hS, this]

/-- Subsets of size `q`. -/
lemma tab_popv_testBit (q : ℤ) (S : ℕ) :
    ((tab n).popv q).testBit S = true ↔ S < 2 ^ n ∧ (popc n S : ℤ) = q := by
  unfold Tab.popv
  by_cases hq : q < 0
  · rw [if_pos hq]; simp only [Nat.zero_testBit, Bool.false_eq_true, false_iff, not_and]
    intro _ h; omega
  · rw [if_neg hq]
    have hpop : popc n S ≤ n := by
      unfold popc
      exact (List.length_filter_le _ _).trans (List.length_range).le
    by_cases hqn : q.toNat ≤ n
    · simp only [tab, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range,
        Nat.lt_succ_iff.2 hqn, if_true, Option.map_some, Option.getD_some, testBit_maskOf,
        Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      constructor
      · rintro ⟨hS, h⟩; exact ⟨hS, by omega⟩
      · rintro ⟨hS, h⟩; exact ⟨hS, by omega⟩
    · have hnone : ((tab n).pop)[q.toNat]? = none := by
        apply List.getElem?_eq_none
        simp [tab]; omega
      have : (tab n).pop.getD q.toNat 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, hnone]; rfl
      rw [this]
      simp only [Nat.zero_testBit, Bool.false_eq_true, false_iff, not_and]
      intro _ h; omega

end Kalai5.Gale
