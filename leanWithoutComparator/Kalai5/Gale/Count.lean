import Kalai5.Gale.Masks
import Kalai5.Gale.Normal

/-!
# The row of `conv W` from the bit-sliced face vectors

Given a Gale diagram `g` of `W` with codes `c`, and the completeness certificate (every subset
is covered by circuits or certified by a candidate functional), bit `S` of `faceV` says that
`ofMask n S` is a face index, and bit `S` of `dimV d` that this face has dimension `d`.
Hence `rowOf (conv W) = (tab n).row …` (`rowOf_eq`).
-/

namespace Kalai5.Gale

open Set Module

variable {n : ℕ}

/-! ### Codes and their masks -/

lemma nzMask_testBit (c : Fin n → ℕ) (j : Fin n) :
    (nzMask (List.ofFn c)).testBit j = true ↔ c j ≠ 0 := by
  simp [nzMask, testBit_maskOf, cd_ofFn, j.2]

lemma nzMask_testBit_ge (c : Fin n → ℕ) {j : ℕ} (hj : n ≤ j) :
    (nzMask (List.ofFn c)).testBit j = false := by
  simp [nzMask, testBit_maskOf]; omega

lemma lineMask_testBit (c : Fin n → ℕ) (i : ℕ) (j : Fin n) :
    (lineMask (List.ofFn c) i).testBit j = true ↔ c j ≠ 0 ∧ cline (c j) = i := by
  simp [lineMask, testBit_maskOf, cd_ofFn, j.2]

/-- `r₁`: subsets whose complement has its nonzero vectors on at most one line. -/
noncomputable def r1v (c : Fin n → ℕ) : ℕ :=
  (tab n).supV (nzMask (List.ofFn c)) |||
    orL (((List.range (nlines (List.ofFn c))).map (lineMask (List.ofFn c))).map fun l =>
      (tab n).supV (nzMask (List.ofFn c) &&& ((2 ^ (tab n).n - 1) ^^^ l)))

/-- Rank vectors of the codes. -/
noncomputable def rkOf (c : Fin n → ℕ) : ℕ × ℕ × ℕ :=
  (tab n).rk (nzMask (List.ofFn c)) ((List.range (nlines (List.ofFn c))).map (lineMask (List.ofFn c)))

lemma rkOf_eq (c : Fin n → ℕ) : rkOf c = ((tab n).supV (nzMask (List.ofFn c)),
    r1v c ^^^ (tab n).supV (nzMask (List.ofFn c)), (tab n).full ^^^ r1v c) := rfl

lemma rk0_testBit (c : Fin n → ℕ) {S : ℕ} (hS : S < 2 ^ n) :
    ((tab n).supV (nzMask (List.ofFn c))).testBit S = true ↔
      ∀ j : Fin n, c j ≠ 0 → S.testBit j = true := by
  rw [tab_supV_testBit]
  constructor
  · rintro ⟨-, h⟩ j hj
    exact h j j.2 ((nzMask_testBit c j).2 hj)
  · intro h
    refine ⟨hS, fun j hj hx => ?_⟩
    exact h ⟨j, hj⟩ ((nzMask_testBit c ⟨j, hj⟩).1 hx)

lemma r1v_testBit (c : Fin n → ℕ) {S : ℕ} (hS : S < 2 ^ n) :
    (r1v c).testBit S = true ↔ (∀ j : Fin n, c j ≠ 0 → S.testBit j = true) ∨
      ∃ i < nlines (List.ofFn c), ∀ j : Fin n, c j ≠ 0 → cline (c j) ≠ i → S.testBit j = true := by
  unfold r1v
  rw [Nat.testBit_lor, Bool.or_eq_true, rk0_testBit c hS, testBit_orL]
  apply or_congr Iff.rfl
  simp only [List.map_map, List.any_eq_true, List.mem_map, List.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨v, ⟨i, hi, rfl⟩, hv⟩
    refine ⟨i, hi, fun j hj hji => ?_⟩
    rw [tab_supV_testBit] at hv
    apply hv.2 j j.2
    rw [Nat.testBit_land, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Bool.and_eq_true,
      (nzMask_testBit c j).2 hj]
    refine ⟨rfl, ?_⟩
    have : (lineMask (List.ofFn c) i).testBit j = false := by
      by_contra h; exact hji ((lineMask_testBit c i j).1 (by simpa using h)).2
    simp [this, j.2]
  · rintro ⟨i, hi, h⟩
    refine ⟨_, ⟨i, hi, rfl⟩, ?_⟩
    rw [tab_supV_testBit]
    refine ⟨hS, fun j hj hx => ?_⟩
    rw [Nat.testBit_land, Bool.and_eq_true] at hx
    have hjn : j < n := by
      by_contra hn; rw [nzMask_testBit_ge c (by omega)] at hx; exact absurd hx.1 (by simp)
    have h1 := (nzMask_testBit c ⟨j, hjn⟩).1 hx.1
    have h2 : cline (c ⟨j, hjn⟩) ≠ i := by
      intro he
      have := (lineMask_testBit c i ⟨j, hjn⟩).2 ⟨h1, he⟩
      rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one] at hx
      simp only at this
      simp [this, hjn] at hx
    exact h ⟨j, hjn⟩ h1 h2

lemma card_ofMask_cmask (S : ℕ) : (ofMask n (cmask n S)).card = n - popc n S := by
  rw [ofMask_cmask, Finset.card_compl, card_ofMask, Fintype.card_fin]

lemma popc_le (S : ℕ) : popc n S ≤ n := by
  rw [← card_ofMask]; exact (Finset.card_le_univ _).trans (by simp)

/-- The combinatorial rank of the complement, through the rank vectors. -/
lemma crank_cases {g : Fin n → Fin 2 → ℝ} {c : Fin n → ℕ} {m : ℕ} (hc : CodeFor g c m) {S : ℕ}
    (hS : S < 2 ^ n) :
    (crank c (ofMask n (cmask n S)) = 0 ↔
        ((tab n).supV (nzMask (List.ofFn c))).testBit S = true) ∧
    (crank c (ofMask n (cmask n S)) ≤ 1 ↔ (r1v c).testBit S = true) ∧
    crank c (ofMask n (cmask n S)) ≤ 2 := by
  classical
  rw [rk0_testBit c hS, r1v_testBit c hS, hc.nlines_eq]
  have hmem : ∀ j : Fin n, j ∈ ofMask n (cmask n S) ↔ S.testBit j = false := by
    intro j; rw [mem_ofMask, cmask_testBit j.2]; cases S.testBit j <;> simp
  have e0 : (∀ j ∈ ofMask n (cmask n S), c j = 0) ↔ ∀ j : Fin n, c j ≠ 0 → S.testBit j = true := by
    constructor
    · intro h j hj
      by_contra hS'
      exact hj (h j ((hmem j).2 (by simpa using hS')))
    · intro h j hj
      by_contra hc0
      have := h j hc0
      rw [(hmem j).1 hj] at this
      exact absurd this (by simp)
  have e1 : (∃ i, ∀ j ∈ ofMask n (cmask n S), c j ≠ 0 → cline (c j) = i) ↔
      ∃ i, ∀ j : Fin n, c j ≠ 0 → cline (c j) ≠ i → S.testBit j = true := by
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, fun j hj hji => ?_⟩
      by_contra hS'
      exact hji (hi j ((hmem j).2 (by simpa using hS')) hj)
    · rintro ⟨i, hi⟩
      refine ⟨i, fun j hj hcj => ?_⟩
      by_contra hji
      have := hi j hcj hji
      rw [(hmem j).1 hj] at this
      exact absurd this (by simp)
  unfold crank
  refine ⟨?_, ?_, by split_ifs <;> omega⟩
  · rw [← e0]; split_ifs with h1 h2 <;> simp_all
  · constructor
    · intro hle
      by_cases h1 : ∀ j ∈ ofMask n (cmask n S), c j = 0
      · left; exact e0.1 h1
      · right
        rw [if_neg h1] at hle
        by_cases h2 : ∃ i, ∀ j ∈ ofMask n (cmask n S), c j ≠ 0 → cline (c j) = i
        · obtain ⟨i, hi⟩ := h2
          push_neg at h1
          obtain ⟨j0, hj0, hc0⟩ := h1
          refine ⟨i, ?_, ?_⟩
          · rw [← hi j0 hj0 hc0]; exact hc.line_lt j0 hc0
          · intro j hj hji
            by_contra hS'
            exact hji (hi j ((hmem j).2 (by simpa using hS')) hj)
        · rw [if_neg h2] at hle; omega
    · rintro (h | ⟨i, -, h⟩)
      · rw [if_pos (e0.2 h)]; omega
      · split_ifs with h1 h2
        · omega
        · omega
        · exact absurd (e1.2 ⟨i, h⟩) h2

/-- Bit `S` of `dimV d`: a face with `#S = d + n - 4 - rank(complement)`. -/
lemma dimV_testBit {g : Fin n → Fin 2 → ℝ} {c : Fin n → ℕ} {m : ℕ} (hc : CodeFor g c m)
    (fv d : ℕ) {S : ℕ} (hS : S < 2 ^ n) :
    ((tab n).dimV fv (rkOf c) d).testBit S = true ↔ fv.testBit S = true ∧
      (popc n S : ℤ) = d + n - 4 - crank c (ofMask n (cmask n S)) := by
  obtain ⟨h0, h1, h2⟩ := crank_cases hc hS
  unfold Tab.dimV
  rw [rkOf_eq]
  simp only [Nat.testBit_land, Nat.testBit_lor, Nat.testBit_xor, tab_full_testBit, hS,
    decide_true, Bool.and_eq_true, Bool.or_eq_true, tab_n]
  rw [tab_popv_testBit, tab_popv_testBit, tab_popv_testBit]
  apply and_congr Iff.rfl
  set r := crank c (ofMask n (cmask n S))
  rcases Nat.lt_or_ge r 1 with hr | hr
  · have hR0 := h0.1 (by omega)
    have hR1 := h1.1 (by omega)
    rw [hR0, hR1]
    simp only [Bool.true_xor, Bool.not_true, Bool.false_eq_true, and_false, or_false, and_true]
    constructor
    · rintro ⟨-, h⟩; omega
    · intro h; exact ⟨hS, by omega⟩
  · rcases Nat.lt_or_ge r 2 with hr2 | hr2
    · have hR0 : ((tab n).supV (nzMask (List.ofFn c))).testBit S = false := by
        by_contra h; exact absurd (h0.2 (by simpa using h)) (by omega)
      have hR1 := h1.1 (by omega)
      rw [hR0, hR1]
      simp only [Bool.false_eq_true, and_false, false_or, Bool.true_xor, Bool.not_true,
        or_false, Bool.xor_false, and_true]
      constructor
      · rintro ⟨-, h⟩; omega
      · intro h; exact ⟨hS, by omega⟩
    · have hR0 : ((tab n).supV (nzMask (List.ofFn c))).testBit S = false := by
        by_contra h; exact absurd (h0.2 (by simpa using h)) (by omega)
      have hR1 : (r1v c).testBit S = false := by
        by_contra h; exact absurd (h1.2 (by simpa using h)) (by omega)
      rw [hR0, hR1]
      simp only [Bool.false_eq_true, and_false, false_or, Bool.xor_false, Bool.true_xor,
        Bool.not_false, and_true]
      constructor
      · rintro ⟨-, h⟩; omega
      · intro h; exact ⟨hS, by omega⟩

/-! ### Faces and dimensions -/

variable {W : Fin n → E 4} {g : Fin n → Fin 2 → ℝ} {c : Fin n → ℕ} {m : ℕ}

lemma isFaceIdx_ofMask_iff (hg : IsGale W g) (S : ℕ) :
    IsFaceIdx W (ofMask n S) ↔ ∃ a : Fin n → ℝ,
      (∀ j : Fin n, (cmask n S).testBit j = true → 0 < a j) ∧
      (∀ j : Fin n, (cmask n S).testBit j = false → a j = 0) ∧ ∑ j, a j • g j = 0 := by
  unfold IsFaceIdx
  constructor
  · rintro ⟨a, ha, h0, hpos⟩
    refine ⟨a, fun j hj => hpos j ?_, fun j hj => h0 j ?_, (hg.mem_iff a).1 ha⟩
    · rw [mem_ofMask]; rw [cmask_testBit j.2] at hj; simpa using hj
    · rw [mem_ofMask]; rw [cmask_testBit j.2] at hj; simpa using hj
  · rintro ⟨a, hpos, h0, hsum⟩
    refine ⟨a, (hg.mem_iff a).2 hsum, fun j hj => h0 j ?_, fun j hj => hpos j ?_⟩
    · rw [cmask_testBit j.2]; rw [mem_ofMask] at hj; simp [hj]
    · rw [cmask_testBit j.2]; rw [mem_ofMask] at hj; simpa using hj

/-- **Bit `S` of `faceV` detects the face indices.** -/
lemma faceV_iff (hg : IsGale W g) (hc : CodeFor g c m)
    (hcomp : ∀ S < 2 ^ n, ((tab n).covV (circuits (List.ofFn c))).testBit S = true ∨
      ((tab n).farV (candidates (List.ofFn c))).testBit S = true) {S : ℕ} (hS : S < 2 ^ n) :
    ((tab n).faceV (circuits (List.ofFn c))).testBit S = true ↔
      S ≠ 0 ∧ IsFaceIdx W (ofMask n S) := by
  rw [tab_faceV_testBit, isFaceIdx_ofMask_iff hg]
  set C := cmask n S
  have hC : C < 2 ^ n := cmask_lt hS
  have hCbit : ∀ j : Fin n, C.testBit j = !S.testBit j := fun j => cmask_testBit j.2
  constructor
  · rintro ⟨-, hS0, hcov⟩
    refine ⟨hS0, hc.posDep_of_covered fun k hk => ?_⟩
    rw [hCbit] at hk
    obtain ⟨x, hx, hxk, hxS⟩ := hcov k k.2 (by simpa using hk)
    exact ⟨x, hx, hxk, fun j hj => by rw [hCbit, hxS j j.2 hj]; rfl⟩
  · rintro ⟨hS0, hpd⟩
    refine ⟨hS, hS0, fun k hk hSk => ?_⟩
    rcases hcomp C hC with hcov | hfar
    · obtain ⟨-, h⟩ := (tab_covV_testBit _ C).1 hcov
      have hCk : C.testBit k = true := by
        have := hCbit ⟨k, hk⟩; simp only at this; rw [this, hSk]; rfl
      obtain ⟨x, hx, hxk, hxC⟩ := h k hk hCk
      refine ⟨x, hx, hxk, fun j hj hxj => ?_⟩
      have := hxC j hj hxj
      have h' := hCbit ⟨j, hj⟩; simp only at h'
      rw [h'] at this; simpa using this
    · exfalso
      obtain ⟨-, pn, hpn, hN, j, hj, hP, hCj⟩ := (tab_farV_testBit _ C).1 hfar
      exact hc.not_posDep_of_farkas hc.nlines_eq
        ⟨pn, hpn, fun i hi => hN i i.2 hi, ⟨j, hj⟩, hP, hCj⟩ hpd

/-- **Dimension formula for faces**: `dim + #complement = 4 + rank(complement)`. -/
lemma dim_add_card_compl (hspan : affineSpan ℝ (range W) = ⊤) (hg : IsGale W g)
    (hc : CodeFor g c m) {F : Finset (Fin n)} (hF : F.Nonempty) :
    finrank ℝ (vectorSpan ℝ (W '' ↑F)) + Fᶜ.card = 4 + crank c Fᶜ := by
  have h1 := finrank_inf_supp_compl_add hspan hF
  have h2 := finrank_inf_supp_add hg Fᶜ
  rw [hc.finrank_span_image] at h2
  omega

/-- **Bit `S` of `dimV d` detects the `d`-dimensional faces.** -/
lemma dimV_iff (hspan : affineSpan ℝ (range W) = ⊤) (hg : IsGale W g) (hc : CodeFor g c m)
    (hcomp : ∀ S < 2 ^ n, ((tab n).covV (circuits (List.ofFn c))).testBit S = true ∨
      ((tab n).farV (candidates (List.ofFn c))).testBit S = true) (d : ℕ) {S : ℕ}
    (hS : S < 2 ^ n) :
    ((tab n).dimV ((tab n).faceV (circuits (List.ofFn c))) (rkOf c) d).testBit S = true ↔
      (ofMask n S).Nonempty ∧ IsFaceIdx W (ofMask n S) ∧
        finrank ℝ (vectorSpan ℝ (W '' ↑(ofMask n S))) = d := by
  rw [dimV_testBit hc _ d hS, faceV_iff hg hc hcomp hS, ofMask_nonempty_iff hS]
  have hpop := popc_le (n := n) S
  constructor
  · rintro ⟨⟨hS0, hfi⟩, hd⟩
    refine ⟨hS0, hfi, ?_⟩
    have hdim := dim_add_card_compl hspan hg hc ((ofMask_nonempty_iff hS).2 hS0)
    rw [← ofMask_cmask, card_ofMask_cmask] at hdim
    omega
  · rintro ⟨hS0, hfi, hd⟩
    refine ⟨⟨hS0, hfi⟩, ?_⟩
    have hdim := dim_add_card_compl hspan hg hc ((ofMask_nonempty_iff hS).2 hS0)
    rw [← ofMask_cmask, card_ofMask_cmask] at hdim
    omega

/-- **The row of `conv W` is the row of the bit-sliced face vectors.** -/
theorem rowOf_eq (hspan : affineSpan ℝ (range W) = ⊤) (hinj : Function.Injective W)
    (hvert : ∀ j, IsFaceIdx W {j}) (hg : IsGale W g) (hc : CodeFor g c m)
    (hcomp : ∀ S < 2 ^ n, ((tab n).covV (circuits (List.ofFn c))).testBit S = true ∨
      ((tab n).farV (candidates (List.ofFn c))).testBit S = true) :
    rowOf (convexHull ℝ (range W)) =
      (tab n).row ((tab n).faceV (circuits (List.ofFn c))) (rkOf c) := by
  classical
  have hf : ∀ d, fvec (convexHull ℝ (range W)) d =
      cntB (2 ^ n) ((tab n).dimV ((tab n).faceV (circuits (List.ofFn c))) (rkOf c) d) := by
    intro d
    rw [fvec_eq_card]
    exact card_filter_eq_cntB _ _ fun S hS => dimV_iff hspan hg hc hcomp d hS
  have hJ : flag2 (convexHull ℝ (range W)) 0 3 =
      sizeSum n ((tab n).dimV ((tab n).faceV (circuits (List.ofFn c))) (rkOf c) 3) := by
    rw [flag2_zero_three_eq hinj hvert]
    exact sum_card_filter_eq_sizeSum _ _ fun S hS => dimV_iff hspan hg hc hcomp 3 hS
  simp only [rowOf, Tab.row, tab_n, hf, hJ]

end Kalai5.Gale
