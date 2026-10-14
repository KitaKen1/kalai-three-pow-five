import Kalai5.Gale.Comb
import Mathlib.Data.Nat.Bitwise

/-!
# Bit lemmas for the Gale checker

`testBit` characterisations of the bitmask constructions of `Kalai5.Gale.Comb`.
-/

namespace Kalai5.Gale

lemma testBit_foldl_mask (p : ℕ → Bool) (l : List ℕ) (acc S : ℕ) :
    (l.foldl (fun acc j => if p j then acc ||| 2 ^ j else acc) acc).testBit S =
      (acc.testBit S || l.any fun j => p j && j == S) := by
  induction l generalizing acc with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, ih]
    by_cases hp : p j
    · simp only [hp, if_true, Nat.testBit_lor, Nat.testBit_two_pow, List.any_cons, Bool.true_and]
      cases acc.testBit S <;> by_cases hjS : j = S <;> simp [hjS]
    · simp [hp]

lemma testBit_maskOf (n : ℕ) (p : ℕ → Bool) (S : ℕ) :
    (maskOf n p).testBit S = (decide (S < n) && p S) := by
  unfold maskOf
  rw [testBit_foldl_mask]
  simp only [Nat.zero_testBit, Bool.false_or]
  by_cases hS : S < n
  · simp only [hS, decide_true, Bool.true_and]
    cases hpS : p S
    · simp only [List.any_eq_false, List.mem_range, Bool.and_eq_true, beq_iff_eq, not_and]
      rintro j - hj rfl; simp_all
    · simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
      exact ⟨S, hS, hpS, rfl⟩
  · simp only [hS, decide_false, Bool.false_and, List.any_eq_false, List.mem_range,
      Bool.and_eq_true, beq_iff_eq, not_and]
    rintro j hj - rfl; exact hS hj

lemma testBit_andL (full : ℕ) (vs : List ℕ) (S : ℕ) :
    (andL full vs).testBit S = (full.testBit S && vs.all fun v => v.testBit S) := by
  unfold andL
  induction vs generalizing full with
  | nil => simp
  | cons v vs ih =>
    rw [List.foldl_cons, ih, Nat.testBit_land, List.all_cons, Bool.and_assoc]

lemma testBit_orL (vs : List ℕ) (S : ℕ) : (orL vs).testBit S = vs.any fun v => v.testBit S := by
  unfold orL
  suffices h : ∀ acc, (vs.foldl (· ||| ·) acc).testBit S = (acc.testBit S || vs.any fun v => v.testBit S) by
    rw [h]; simp
  induction vs with
  | nil => simp
  | cons v vs ih =>
    intro acc
    rw [List.foldl_cons, ih, Nat.testBit_lor, List.any_cons, Bool.or_assoc]

lemma testBit_two_pow_sub_one' (N S : ℕ) : (2 ^ N - 1).testBit S = decide (S < N) :=
  Nat.testBit_two_pow_sub_one N S

lemma testBit_pow_or_pow (j k S : ℕ) : (2 ^ j ||| 2 ^ k).testBit S = (decide (j = S) || decide (k = S)) := by
  rw [Nat.testBit_lor, Nat.testBit_two_pow, Nat.testBit_two_pow]

lemma testBit_pow_or_pow_or_pow (j k l S : ℕ) :
    (2 ^ j ||| 2 ^ k ||| 2 ^ l).testBit S = (decide (j = S) || decide (k = S) || decide (l = S)) := by
  rw [Nat.testBit_lor, testBit_pow_or_pow, Nat.testBit_two_pow]

/-- Membership in the circuit list. -/
lemma mem_circuits {cs : List ℕ} {x : ℕ} (hx : x ∈ circuits cs) :
    (∃ j < cs.length, cd cs j = 0 ∧ x = 2 ^ j) ∨
    (∃ j k, j < k ∧ k < cs.length ∧ isPair (cd cs j) (cd cs k) = true ∧ x = 2 ^ j ||| 2 ^ k) ∨
    (∃ j k l, j < k ∧ k < l ∧ l < cs.length ∧ isTriple (cd cs j) (cd cs k) (cd cs l) = true ∧
      x = 2 ^ j ||| 2 ^ k ||| 2 ^ l) := by
  unfold circuits at hx
  simp only [List.mem_append, List.mem_filterMap, List.mem_range, List.mem_flatMap,
    List.mem_range'_1] at hx
  rcases hx with (⟨j, hj, h⟩ | ⟨j, hj, k, ⟨hk1, hk2⟩, h⟩) |
      ⟨j, hj, k, ⟨hk1, hk2⟩, l, ⟨hl1, hl2⟩, h⟩
  · left
    split at h
    · rename_i h0
      exact ⟨j, hj, by simpa using h0, (Option.some.inj h).symm⟩
    · simp at h
  · right; left
    split at h
    · rename_i h0
      exact ⟨j, k, by omega, by omega, h0, (Option.some.inj h).symm⟩
    · simp at h
  · right; right
    split at h
    · rename_i h0
      exact ⟨j, k, l, by omega, by omega, by omega, h0, (Option.some.inj h).symm⟩
    · simp at h

/-- A single-subset certificate check unpacks into its sign conditions. -/
lemma farkas_spec {cands : List (ℕ × ℕ)} {S : ℕ} (h : farkas cands S = true) :
    ∃ pn ∈ cands, (∀ i, pn.2.testBit i = true → S.testBit i = false) ∧
      ∃ i, pn.1.testBit i = true ∧ S.testBit i = true := by
  unfold farkas at h
  rw [List.any_eq_true] at h
  obtain ⟨pn, hpn, h⟩ := h
  rw [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
  refine ⟨pn, hpn, fun i hi => ?_, ?_⟩
  · have := congrArg (fun x => x.testBit i) h.1
    simp only [Nat.testBit_land, Nat.zero_testBit, hi, Bool.and_true] at this
    exact this
  · by_contra hne
    push_neg at hne
    apply h.2
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land, Nat.zero_testBit]
    cases hS : S.testBit i
    · simp
    · cases hP : pn.1.testBit i
      · simp
      · exact absurd hS (by simp [hne i hP])

/-- Membership in the candidate list. -/
lemma mem_candidates {cs : List ℕ} {pn : ℕ × ℕ} (h : pn ∈ candidates cs) :
    ∃ i < nlines cs, ∃ σ : Bool,
      pn = (maskOf cs.length fun j => posA i σ (cd cs j), maskOf cs.length fun j => negA i σ (cd cs j)) ∨
      pn = (maskOf cs.length fun j => posB i σ (cd cs j), maskOf cs.length fun j => negB i σ (cd cs j)) := by
  unfold candidates at h
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨i, hi, σ, -, h⟩ := h
  exact ⟨i, hi, σ, h⟩

lemma cd_ofFn {n : ℕ} (c : Fin n → ℕ) (j : Fin n) : cd (List.ofFn c) j = c j := by
  simp [cd]

end Kalai5.Gale
