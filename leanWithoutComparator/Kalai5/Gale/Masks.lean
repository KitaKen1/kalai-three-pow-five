import Kalai5.Gale.BitSem

/-!
# Masks as subsets of `Fin n`

`ofMask n S = {j | bit j of S}` is a bijection from `{S < 2 ^ n}` onto `Finset (Fin n)`;
counts and sums over subsets become `cntB` and `sizeSum` of bit vectors.
-/

namespace Kalai5.Gale

variable {n : ℕ}

/-- The subset of `Fin n` with mask `S`. -/
def ofMask (n S : ℕ) : Finset (Fin n) := Finset.univ.filter fun j => S.testBit j = true

lemma mem_ofMask {S : ℕ} {j : Fin n} : j ∈ ofMask n S ↔ S.testBit j = true := by
  simp [ofMask]

lemma testBit_eq_false_of_lt {S i : ℕ} (hS : S < 2 ^ n) (hi : n ≤ i) : S.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hS (Nat.pow_le_pow_right (by norm_num) hi))

lemma ofMask_injOn : Set.InjOn (ofMask n) ↑(Finset.range (2 ^ n)) := by
  intro S hS S' hS' h
  simp only [Finset.coe_range, Set.mem_Iio] at hS hS'
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have := congrArg (fun F => (⟨i, hi⟩ : Fin n) ∈ F) h
    simp only [mem_ofMask, eq_iff_iff] at this
    cases h1 : S.testBit i <;> cases h2 : S'.testBit i <;> simp_all
  · rw [testBit_eq_false_of_lt hS (by omega), testBit_eq_false_of_lt hS' (by omega)]

lemma image_ofMask : (Finset.range (2 ^ n)).image (ofMask n) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn ofMask_injOn, Finset.card_range, Fintype.card_finset,
    Fintype.card_fin]

lemma exists_ofMask (F : Finset (Fin n)) : ∃ S < 2 ^ n, ofMask n S = F := by
  have : F ∈ (Finset.range (2 ^ n)).image (ofMask n) := by rw [image_ofMask]; exact Finset.mem_univ F
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 this
  exact ⟨S, Finset.mem_range.1 hS, rfl⟩

lemma ofMask_nonempty_iff {S : ℕ} (hS : S < 2 ^ n) : (ofMask n S).Nonempty ↔ S ≠ 0 := by
  constructor
  · rintro ⟨j, hj⟩ rfl
    simp [mem_ofMask] at hj
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
    have hin : i < n := by
      by_contra hn
      rw [testBit_eq_false_of_lt hS (by omega)] at hi
      exact absurd hi (by simp)
    exact ⟨⟨i, hin⟩, mem_ofMask.2 hi⟩

/-- Complement within `{0, …, n-1}`. -/
def cmask (n S : ℕ) : ℕ := (2 ^ n - 1) ^^^ S

lemma cmask_testBit {S j : ℕ} (hj : j < n) : (cmask n S).testBit j = !S.testBit j := by
  rw [cmask, Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
  simp [hj]

lemma cmask_lt {S : ℕ} (hS : S < 2 ^ n) : cmask n S < 2 ^ n :=
  Nat.xor_lt_two_pow (Nat.sub_lt (Nat.two_pow_pos n) (by norm_num)) hS

lemma ofMask_cmask (S : ℕ) : ofMask n (cmask n S) = (ofMask n S)ᶜ := by
  ext j
  rw [Finset.mem_compl, mem_ofMask, mem_ofMask, cmask_testBit j.2]
  cases S.testBit j <;> simp

lemma card_ofMask (S : ℕ) : (ofMask n S).card = popc n S := by
  unfold popc ofMask
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    List.mem_toFinset, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j.2, hj⟩
  · rintro ⟨hi, h⟩; exact ⟨⟨i, hi⟩, h, rfl⟩

lemma length_filter_range (N : ℕ) (p : ℕ → Bool) :
    ((List.range N).filter p).length = ((Finset.range N).filter fun S => p S = true).card := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  congr 1
  ext S; simp

lemma sum_filter_range (N : ℕ) (p : ℕ → Bool) (f : ℕ → ℕ) :
    (((List.range N).filter p).map f).sum = ∑ S ∈ (Finset.range N).filter (fun S => p S = true), f S := by
  rw [← List.sum_toFinset f (List.nodup_range.filter _)]
  congr 1
  ext S; simp

/-- Counting subsets through a bit vector. -/
lemma card_filter_eq_cntB (P : Finset (Fin n) → Prop) [DecidablePred P] (v : ℕ)
    (hv : ∀ S < 2 ^ n, v.testBit S = true ↔ P (ofMask n S)) :
    (Finset.univ.filter P).card = cntB (2 ^ n) v := by
  classical
  unfold cntB
  rw [length_filter_range]
  have h1 : (Finset.range (2 ^ n)).filter (fun S => v.testBit S = true) =
      (Finset.range (2 ^ n)).filter (fun S => P (ofMask n S)) := by
    apply Finset.filter_congr
    intro S hS; exact hv S (Finset.mem_range.1 hS)
  rw [h1]
  have h2 : Finset.univ.filter P = ((Finset.range (2 ^ n)).filter fun S => P (ofMask n S)).image
      (ofMask n) := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hF
      obtain ⟨S, hS, rfl⟩ := exists_ofMask F
      exact ⟨S, ⟨hS, hF⟩, rfl⟩
    · rintro ⟨S, ⟨-, hS⟩, rfl⟩; exact hS
  rw [h2, Finset.card_image_of_injOn (ofMask_injOn.mono (by
    intro S hS; simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hS
    simpa using hS.1))]

/-- Summing subset sizes through a bit vector. -/
lemma sum_card_filter_eq_sizeSum (P : Finset (Fin n) → Prop) [DecidablePred P] (v : ℕ)
    (hv : ∀ S < 2 ^ n, v.testBit S = true ↔ P (ofMask n S)) :
    ∑ F ∈ Finset.univ.filter P, F.card = sizeSum n v := by
  classical
  unfold sizeSum
  rw [sum_filter_range]
  have h1 : (Finset.range (2 ^ n)).filter (fun S => v.testBit S = true) =
      (Finset.range (2 ^ n)).filter (fun S => P (ofMask n S)) := by
    apply Finset.filter_congr
    intro S hS; exact hv S (Finset.mem_range.1 hS)
  rw [h1]
  have h2 : Finset.univ.filter P = ((Finset.range (2 ^ n)).filter fun S => P (ofMask n S)).image
      (ofMask n) := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hF
      obtain ⟨S, hS, rfl⟩ := exists_ofMask F
      exact ⟨S, ⟨hS, hF⟩, rfl⟩
    · rintro ⟨S, ⟨-, hS⟩, rfl⟩; exact hS
  have hinj : Set.InjOn (ofMask n) ↑((Finset.range (2 ^ n)).filter fun S => P (ofMask n S)) :=
    ofMask_injOn.mono (by
      intro S hS
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hS
      simpa using hS.1)
  rw [h2, Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun S _ => card_ofMask S

end Kalai5.Gale
