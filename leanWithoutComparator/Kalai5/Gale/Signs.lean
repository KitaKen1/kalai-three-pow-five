import Kalai5.Gale.Bits
import Kalai5.Gale.Affine

/-!
# Sign codes of planar vector configurations

`CodeFor g c m`: the codes `c` describe the vectors `g : Fin n → ℝ²` — zero vectors get code `0`;
every nonzero vector has nonzero first coordinate `t`, orientation `cpos ↔ t > 0`, and line
indices `< m`, all used, ordered like the slopes.

* **Circuits are positive dependencies** (`posDep_of_covered`): each circuit of
  `Kalai5.Gale.circuits` carries an explicit nonnegative relation (zero vector; `|t'| g + |t| g'`
  for opposite vectors; the wedge coefficients for alternating triples).
* **Candidates are separating functionals** (`not_posDep_of_farkas`): each candidate sign pattern
  is realised by `x ↦ ± (x₁ - s x₀)` for a slope `s` (or by `± x₀`).
* **Rank** (`finrank_span_image`): read off zero vectors and lines.
-/

namespace Kalai5.Gale

open Module

variable {n : ℕ}

/-- `u₀ v₁ - u₁ v₀`. -/
def wedge (u v : Fin 2 → ℝ) : ℝ := u 0 * v 1 - u 1 * v 0

lemma wedge_identity (a b c : Fin 2 → ℝ) :
    wedge b c • a + wedge c a • b + wedge a b • c = 0 := by
  funext i; fin_cases i <;> simp [wedge] <;> ring

lemma wedge_anti (u v : Fin 2 → ℝ) : wedge u v = -wedge v u := by unfold wedge; ring

/-- Slope of a vector (meaningful for nonzero first coordinate). -/
noncomputable def slope (u : Fin 2 → ℝ) : ℝ := u 1 / u 0

lemma snd_eq_mul_slope (u : Fin 2 → ℝ) (h : u 0 ≠ 0) : u 1 = u 0 * slope u := by
  unfold slope; field_simp

lemma wedge_eq (u v : Fin 2 → ℝ) (hu : u 0 ≠ 0) (hv : v 0 ≠ 0) :
    wedge u v = u 0 * v 0 * (slope v - slope u) := by
  unfold wedge; rw [snd_eq_mul_slope v hv, snd_eq_mul_slope u hu]; ring

/-- `± 1`. -/
def sgn (σ : Bool) : ℝ := if σ then 1 else -1

/-- `x ↦ τ (x₁ - s x₀)`. -/
noncomputable def linA (τ s : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  τ • (LinearMap.proj 1 - s • LinearMap.proj 0)

lemma linA_apply (τ s : ℝ) (x : Fin 2 → ℝ) : linA τ s x = τ * (x 1 - s * x 0) := by
  simp [linA]

/-- `x ↦ τ x₀`. -/
noncomputable def linB (τ : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := τ • LinearMap.proj 0

lemma linB_apply (τ : ℝ) (x : Fin 2 → ℝ) : linB τ x = τ * x 0 := by simp [linB]

lemma mul_sign_pos {x d : ℝ} (hd : 0 < d) : (0 < x * d ↔ 0 < x) ∧ (x * d < 0 ↔ x < 0) :=
  ⟨⟨fun h => by nlinarith, fun h => by nlinarith⟩, ⟨fun h => by nlinarith, fun h => by nlinarith⟩⟩

lemma mul_sign_neg {x d : ℝ} (hd : d < 0) : (0 < x * d ↔ x < 0) ∧ (x * d < 0 ↔ 0 < x) :=
  ⟨⟨fun h => by nlinarith, fun h => by nlinarith⟩, ⟨fun h => by nlinarith, fun h => by nlinarith⟩⟩

/-- The codes `c` (with `m` lines) describe the vectors `g`. -/
structure CodeFor (g : Fin n → Fin 2 → ℝ) (c : Fin n → ℕ) (m : ℕ) : Prop where
  zero_iff : ∀ j, c j = 0 ↔ g j = 0
  fst_ne : ∀ j, c j ≠ 0 → g j 0 ≠ 0
  pos_iff : ∀ j, c j ≠ 0 → (cpos (c j) = true ↔ 0 < g j 0)
  lt_iff : ∀ i j, c i ≠ 0 → c j ≠ 0 → (cline (c i) < cline (c j) ↔ slope (g i) < slope (g j))
  line_lt : ∀ j, c j ≠ 0 → cline (c j) < m
  used : ∀ i < m, ∃ j, c j ≠ 0 ∧ cline (c j) = i

namespace CodeFor

variable {g : Fin n → Fin 2 → ℝ} {c : Fin n → ℕ} {m : ℕ} (hc : CodeFor g c m)
include hc

lemma eq_iff {i j : Fin n} (hi : c i ≠ 0) (hj : c j ≠ 0) :
    cline (c i) = cline (c j) ↔ slope (g i) = slope (g j) := by
  have h1 := hc.lt_iff i j hi hj
  have h2 := hc.lt_iff j i hj hi
  constructor
  · intro h; by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := h1.2 hlt; omega
    · have := h2.2 hlt; omega
  · intro h; by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := h1.1 hlt; linarith
    · have := h2.1 hlt; linarith

lemma zero_of_code {j : Fin n} (h : c j = 0) : g j = 0 := (hc.zero_iff j).1 h

/-- Same orientation means positive product of first coordinates. -/
lemma mul_pos_of_cpos_eq {i j : Fin n} (hi : c i ≠ 0) (hj : c j ≠ 0) (h : cpos (c i) = cpos (c j)) :
    0 < g i 0 * g j 0 := by
  have hi0 := hc.fst_ne i hi
  have hj0 := hc.fst_ne j hj
  have pi := hc.pos_iff i hi
  have pj := hc.pos_iff j hj
  rcases lt_or_gt_of_ne hi0 with h1 | h1
  · have : ¬ cpos (c i) = true := fun h' => by linarith [pi.1 h']
    have h2 : ¬ 0 < g j 0 := fun h' => this (h ▸ pj.2 h')
    have h3 : g j 0 < 0 := lt_of_le_of_ne (not_lt.1 h2) hj0
    nlinarith
  · have h2 : 0 < g j 0 := pj.1 (h ▸ pi.2 h1)
    positivity

/-- Opposite orientation means negative product of first coordinates. -/
lemma mul_neg_of_cpos_ne {i j : Fin n} (hi : c i ≠ 0) (hj : c j ≠ 0) (h : cpos (c i) ≠ cpos (c j)) :
    g i 0 * g j 0 < 0 := by
  have hi0 := hc.fst_ne i hi
  have hj0 := hc.fst_ne j hj
  have pi := hc.pos_iff i hi
  have pj := hc.pos_iff j hj
  rcases lt_or_gt_of_ne hi0 with h1 | h1
  · have hci : cpos (c i) = false := by
      cases h' : cpos (c i)
      · rfl
      · linarith [pi.1 h']
    have hcj : cpos (c j) = true := by
      cases h' : cpos (c j)
      · exact absurd (hci.trans h'.symm) h
      · rfl
    have := pj.1 hcj
    nlinarith
  · have hci : cpos (c i) = true := pi.2 h1
    have hcj : cpos (c j) = false := by
      cases h' : cpos (c j)
      · rfl
      · exact absurd (hci.trans h'.symm) h
    have h2 : ¬ 0 < g j 0 := fun h' => by rw [pj.2 h'] at hcj; exact Bool.noConfusion hcj
    have h3 : g j 0 < 0 := lt_of_le_of_ne (not_lt.1 h2) hj0
    nlinarith

/-- Three vectors on increasing lines with alternating orientations: all wedges negative. -/
lemma wedges_neg_of_triS {a b d : Fin n} (h : isTriS (c a) (c b) (c d) = true) :
    wedge (g b) (g d) < 0 ∧ wedge (g d) (g a) < 0 ∧ wedge (g a) (g b) < 0 := by
  simp only [isTriS, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hd⟩, hab⟩, hbd⟩, had⟩, hab'⟩ := h
  have sab := (hc.lt_iff a b ha hb).1 hab
  have sbd := (hc.lt_iff b d hb hd).1 hbd
  have ha0 := hc.fst_ne a ha
  have hb0 := hc.fst_ne b hb
  have hd0 := hc.fst_ne d hd
  have pbd : g b 0 * g d 0 < 0 := hc.mul_neg_of_cpos_ne hb hd (fun h' => hab' (had.trans h'.symm))
  have pda : 0 < g d 0 * g a 0 := hc.mul_pos_of_cpos_eq hd ha had.symm
  have pab : g a 0 * g b 0 < 0 := hc.mul_neg_of_cpos_ne ha hb hab'
  rw [wedge_eq _ _ hb0 hd0, wedge_eq _ _ hd0 ha0, wedge_eq _ _ ha0 hb0]
  refine ⟨?_, ?_, ?_⟩
  · exact mul_neg_of_neg_of_pos pbd (by linarith)
  · exact mul_neg_of_pos_of_neg pda (by linarith)
  · exact mul_neg_of_neg_of_pos pab (by linarith)

/-- All three wedge coefficients of a positive triple have the same strict sign. -/
lemma wedges_sameSign_of_triple {j k l : Fin n} (h : isTriple (c j) (c k) (c l) = true) :
    (wedge (g k) (g l) < 0 ∧ wedge (g l) (g j) < 0 ∧ wedge (g j) (g k) < 0) ∨
    (0 < wedge (g k) (g l) ∧ 0 < wedge (g l) (g j) ∧ 0 < wedge (g j) (g k)) := by
  have a1 := wedge_anti (g j) (g k)
  have a2 := wedge_anti (g k) (g l)
  have a3 := wedge_anti (g l) (g j)
  simp only [isTriple, Bool.or_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · left; exact hc.wedges_neg_of_triS h
  · obtain ⟨h1, h2, h3⟩ := hc.wedges_neg_of_triS h
    right; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · obtain ⟨h1, h2, h3⟩ := hc.wedges_neg_of_triS h
    right; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · obtain ⟨h1, h2, h3⟩ := hc.wedges_neg_of_triS h
    left; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · obtain ⟨h1, h2, h3⟩ := hc.wedges_neg_of_triS h
    left; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · obtain ⟨h1, h2, h3⟩ := hc.wedges_neg_of_triS h
    right; refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- **Every circuit carries a nonnegative relation**, positive exactly on the circuit. -/
lemma circuit_dep {x : ℕ} (hx : x ∈ circuits (List.ofFn c)) :
    ∃ d : Fin n → ℝ, (∀ j, 0 ≤ d j) ∧ (∀ j : Fin n, x.testBit j = true → 0 < d j) ∧
      (∀ j : Fin n, x.testBit j = false → d j = 0) ∧ ∑ j, d j • g j = 0 := by
  classical
  rcases mem_circuits hx with ⟨j, hj, h0, rfl⟩ | ⟨j, k, hjk, hk, hp, rfl⟩ |
      ⟨j, k, l, hjk, hkl, hl, ht, rfl⟩
  · rw [List.length_ofFn] at hj
    set J : Fin n := ⟨j, hj⟩
    have hJ : c J = 0 := by rw [← cd_ofFn c J]; exact h0
    refine ⟨Pi.single J 1, fun i => ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
    · by_cases h : i = J <;> simp [h]
    · rw [Nat.testBit_two_pow, decide_eq_true_eq] at hi
      have : i = J := Fin.ext hi.symm
      simp [this]
    · rw [Nat.testBit_two_pow, decide_eq_false_iff_not] at hi
      have : i ≠ J := fun h => hi (by rw [h])
      simp [this]
    · rw [Finset.sum_eq_single J (fun i _ hi => by simp [hi]) (by simp)]
      simp [hc.zero_of_code hJ]
  · rw [List.length_ofFn] at hk
    set J : Fin n := ⟨j, by omega⟩
    set K : Fin n := ⟨k, hk⟩
    have hJK : J ≠ K := fun h => by have := congrArg Fin.val h; simp [J, K] at this; omega
    rw [show j = (J : ℕ) from rfl, show k = (K : ℕ) from rfl, cd_ofFn, cd_ofFn] at hp
    simp only [isPair, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hp
    obtain ⟨⟨⟨hJ0, hK0⟩, hl⟩, hs⟩ := hp
    have hslope := (hc.eq_iff hJ0 hK0).1 hl
    have hJ := hc.fst_ne J hJ0
    have hK := hc.fst_ne K hK0
    have hneg := hc.mul_neg_of_cpos_ne hJ0 hK0 hs
    let d : Fin n → ℝ := fun i => if i = J then |g K 0| else if i = K then |g J 0| else 0
    refine ⟨d, fun i => ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
    · simp only [d]; split_ifs <;> positivity
    · rw [testBit_pow_or_pow] at hi
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hi
      rcases hi with hi | hi
      · have : i = J := Fin.ext hi.symm
        simp [d, this, abs_pos.2 hK]
      · have : i = K := Fin.ext hi.symm
        simp [d, this, hJK.symm, abs_pos.2 hJ]
    · rw [testBit_pow_or_pow] at hi
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hi
      have h1 : i ≠ J := fun h => hi.1 (by rw [h])
      have h2 : i ≠ K := fun h => hi.2 (by rw [h])
      simp [d, h1, h2]
    · rw [Fintype.sum_eq_add J K hJK (fun i hi => by simp [d, hi.1, hi.2])]
      have hdJ : d J = |g K 0| := by simp [d]
      have hdK : d K = |g J 0| := by simp [d, hJK.symm]
      rw [hdJ, hdK]
      have e1 := snd_eq_mul_slope (g J) hJ
      have e2 := snd_eq_mul_slope (g K) hK
      funext i
      fin_cases i
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.zero_eta]
        rcases lt_or_gt_of_ne hJ with h1 | h1
        · have h2 : 0 < g K 0 := by nlinarith
          rw [abs_of_pos h2, abs_of_neg h1]; ring
        · have h2 : g K 0 < 0 := by nlinarith
          rw [abs_of_neg h2, abs_of_pos h1]; ring
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.mk_one]
        rw [e1, e2, hslope]
        rcases lt_or_gt_of_ne hJ with h1 | h1
        · have h2 : 0 < g K 0 := by nlinarith
          rw [abs_of_pos h2, abs_of_neg h1]; ring
        · have h2 : g K 0 < 0 := by nlinarith
          rw [abs_of_neg h2, abs_of_pos h1]; ring
  · rw [List.length_ofFn] at hl
    set J : Fin n := ⟨j, by omega⟩
    set K : Fin n := ⟨k, by omega⟩
    set L : Fin n := ⟨l, hl⟩
    have hJK : J ≠ K := fun h => by have := congrArg Fin.val h; simp [J, K] at this; omega
    have hKL : K ≠ L := fun h => by have := congrArg Fin.val h; simp [K, L] at this; omega
    have hJL : J ≠ L := fun h => by have := congrArg Fin.val h; simp [J, L] at this; omega
    rw [show j = (J : ℕ) from rfl, show k = (K : ℕ) from rfl, show l = (L : ℕ) from rfl,
      cd_ofFn, cd_ofFn, cd_ofFn] at ht
    have hs := hc.wedges_sameSign_of_triple ht
    set w1 := wedge (g K) (g L)
    set w2 := wedge (g L) (g J)
    set w3 := wedge (g J) (g K)
    let d : Fin n → ℝ := fun i => if i = J then |w1| else if i = K then |w2| else if i = L then |w3| else 0
    have hw : w1 ≠ 0 ∧ w2 ≠ 0 ∧ w3 ≠ 0 := by
      rcases hs with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact ⟨h1.ne, h2.ne, h3.ne⟩
      · exact ⟨h1.ne', h2.ne', h3.ne'⟩
    refine ⟨d, fun i => ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
    · simp only [d]; split_ifs <;> positivity
    · rw [testBit_pow_or_pow_or_pow] at hi
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hi
      rcases hi with (hi | hi) | hi
      · have : i = J := Fin.ext hi.symm
        simp [d, this, abs_pos.2 hw.1]
      · have : i = K := Fin.ext hi.symm
        simp [d, this, hJK.symm, abs_pos.2 hw.2.1]
      · have : i = L := Fin.ext hi.symm
        simp [d, this, hJL.symm, hKL.symm, abs_pos.2 hw.2.2]
    · rw [testBit_pow_or_pow_or_pow] at hi
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hi
      have h1 : i ≠ J := fun h => hi.1.1 (by rw [h])
      have h2 : i ≠ K := fun h => hi.1.2 (by rw [h])
      have h3 : i ≠ L := fun h => hi.2 (by rw [h])
      simp [d, h1, h2, h3]
    · have hsum : ∑ i, d i • g i = |w1| • g J + |w2| • g K + |w3| • g L := by
        rw [← Finset.sum_subset (Finset.subset_univ {J, K, L}) (fun i _ hi => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
          simp [d, hi.1, hi.2.1, hi.2.2])]
        rw [Finset.sum_insert (by simp [hJK, hJL]), Finset.sum_insert (by simp [hKL]),
          Finset.sum_singleton]
        have hdJ : d J = |w1| := by simp [d]
        have hdK : d K = |w2| := by simp [d, hJK.symm]
        have hdL : d L = |w3| := by simp [d, hJL.symm, hKL.symm]
        rw [hdJ, hdK, hdL, add_assoc]
      rw [hsum]
      have hid := wedge_identity (g J) (g K) (g L)
      rcases hs with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · rw [abs_of_neg h1, abs_of_neg h2, abs_of_neg h3, neg_smul, neg_smul, neg_smul,
          ← neg_add, ← neg_add, hid, neg_zero]
      · rw [abs_of_pos h1, abs_of_pos h2, abs_of_pos h3]; exact hid

/-- **Covered subsets have positive dependencies.** -/
theorem posDep_of_covered {S : ℕ}
    (hcov : ∀ k : Fin n, S.testBit k = true → ∃ x ∈ circuits (List.ofFn c), x.testBit k = true ∧
      ∀ j : Fin n, x.testBit j = true → S.testBit j = true) :
    ∃ a : Fin n → ℝ, (∀ j : Fin n, S.testBit j = true → 0 < a j) ∧
      (∀ j : Fin n, S.testBit j = false → a j = 0) ∧ ∑ j, a j • g j = 0 := by
  classical
  have hdep : ∀ k : Fin n, S.testBit k = true → ∃ d : Fin n → ℝ, (∀ j, 0 ≤ d j) ∧ 0 < d k ∧
      (∀ j : Fin n, S.testBit j = false → d j = 0) ∧ ∑ j, d j • g j = 0 := by
    intro k hk
    obtain ⟨x, hx, hxk, hxS⟩ := hcov k hk
    obtain ⟨d, hd0, hdpos, hdzero, hdsum⟩ := hc.circuit_dep hx
    refine ⟨d, hd0, hdpos k hxk, fun j hj => hdzero j ?_, hdsum⟩
    cases h : x.testBit j
    · rfl
    · rw [hxS j h] at hj; exact absurd hj (by simp)
  choose! D hD0 hDpos hDzero hDsum using hdep
  let T := Finset.univ.filter fun k : Fin n => S.testBit k = true
  refine ⟨fun j => ∑ k ∈ T, D k j, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · have hjT : j ∈ T := by simp [T, hj]
    calc 0 < D j j := hDpos j hj
      _ ≤ ∑ k ∈ T, D k j :=
        Finset.single_le_sum (f := fun k => D k j) (fun k hk => hD0 k (by simpa [T] using hk) j) hjT
  · exact Finset.sum_eq_zero fun k hk => hDzero k (by simpa [T] using hk) j hj
  · simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun k hk => hDsum k (by simpa [T] using hk)


/-! ### Separating functionals -/

lemma sgn_mul_pos_iff {j : Fin n} (hj : c j ≠ 0) (σ : Bool) :
    0 < sgn σ * g j 0 ↔ cpos (c j) = σ := by
  have h0 := hc.fst_ne j hj
  have hp := hc.pos_iff j hj
  cases σ <;> simp only [sgn, Bool.false_eq_true, if_false, if_true, neg_mul, one_mul,
    Left.neg_pos_iff]
  · constructor
    · intro h; cases h' : cpos (c j)
      · rfl
      · linarith [hp.1 h']
    · intro h; rcases lt_or_gt_of_ne h0 with h1 | h1
      · exact h1
      · rw [hp.2 h1] at h; exact absurd h (by simp)
  · exact hp.symm

lemma sgn_mul_neg_iff {j : Fin n} (hj : c j ≠ 0) (σ : Bool) :
    sgn σ * g j 0 < 0 ↔ cpos (c j) ≠ σ := by
  have h0 := hc.fst_ne j hj
  have hσ : sgn σ ≠ 0 := by cases σ <;> simp [sgn]
  have hne : sgn σ * g j 0 ≠ 0 := mul_ne_zero hσ h0
  rw [ne_eq, ← hc.sgn_mul_pos_iff hj σ]
  constructor
  · intro h h'; linarith
  · intro h; exact lt_of_le_of_ne (not_lt.1 h) hne

lemma slope_lt_of_cline_lt {i j : Fin n} (hi : c i ≠ 0) (hj : c j ≠ 0)
    (h : cline (c i) < cline (c j)) : slope (g i) < slope (g j) := (hc.lt_iff i j hi hj).1 h

lemma slope_le_of_cline_le {i j : Fin n} (hi : c i ≠ 0) (hj : c j ≠ 0)
    (h : cline (c i) ≤ cline (c j)) : slope (g i) ≤ slope (g j) := by
  rcases lt_or_eq_of_le h with h | h
  · exact (hc.slope_lt_of_cline_lt hi hj h).le
  · exact ((hc.eq_iff hi hj).1 h).le

lemma linA_eq {j : Fin n} (hj : c j ≠ 0) (τ s : ℝ) :
    linA τ s (g j) = τ * g j 0 * (slope (g j) - s) := by
  rw [linA_apply, snd_eq_mul_slope (g j) (hc.fst_ne j hj)]; ring

/-- **Each candidate is realised by a linear functional.** -/
lemma exists_functional_of_candidate (hm : nlines (List.ofFn c) = m) {pn : ℕ × ℕ}
    (h : pn ∈ candidates (List.ofFn c)) :
    ∃ f : (Fin 2 → ℝ) →ₗ[ℝ] ℝ, ∀ j : Fin n, (pn.1.testBit j = true → 0 < f (g j)) ∧
      (pn.2.testBit j = false → 0 ≤ f (g j)) := by
  obtain ⟨i, hi, σ, hA | hB⟩ := mem_candidates h
  · -- the functional vanishing on line `i`
    rw [hm] at hi
    obtain ⟨j1, hj1, hl1⟩ := hc.used i hi
    refine ⟨linA (sgn σ) (slope (g j1)), fun j => ⟨fun hp => ?_, fun hn => ?_⟩⟩
    · rw [hA] at hp
      simp only [testBit_maskOf, List.length_ofFn, cd_ofFn, Bool.and_eq_true, decide_eq_true_eq,
        j.2, true_and] at hp
      simp only [posA, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hp
      obtain ⟨⟨hj, hli⟩, hs⟩ := hp
      rw [hc.linA_eq hj]
      by_cases hlt : i < cline (c j)
      · have h1 : cpos (c j) = σ := by simpa [hlt] using hs
        have h2 := (hc.sgn_mul_pos_iff hj σ).2 h1
        have h3 := hc.slope_lt_of_cline_lt hj1 hj (by omega)
        exact mul_pos h2 (by linarith)
      · have h1 : cpos (c j) ≠ σ := by simpa [hlt] using hs
        have h2 := (hc.sgn_mul_neg_iff hj σ).2 h1
        have h3 := hc.slope_lt_of_cline_lt hj hj1 (by omega)
        exact mul_pos_of_neg_of_neg h2 (by linarith)
    · rw [hA] at hn
      simp only [testBit_maskOf, List.length_ofFn, cd_ofFn, decide_eq_true_eq, j.2,
        Bool.true_and] at hn
      by_cases hj : c j = 0
      · rw [hc.zero_of_code hj, map_zero]
      rw [hc.linA_eq hj]
      by_cases hli : cline (c j) = i
      · rw [(hc.eq_iff hj hj1).1 (hli.trans hl1.symm)]; simp
      simp only [negA, Bool.and_eq_false_iff, bne_iff_ne, ne_eq, hj, not_false_eq_true,
        hli, Bool.not_eq_true, bne_eq_false_iff_eq, false_or, decide_eq_false_iff_not] at hn
      by_cases hlt : i < cline (c j)
      · have h1 : cpos (c j) = σ := by simpa [hlt] using hn
        have h2 := (hc.sgn_mul_pos_iff hj σ).2 h1
        have h3 := hc.slope_lt_of_cline_lt hj1 hj (by omega)
        exact (mul_pos h2 (by linarith)).le
      · have h1 : cpos (c j) ≠ σ := by simpa [hlt] using hn
        have h2 := (hc.sgn_mul_neg_iff hj σ).2 h1
        have h3 := hc.slope_lt_of_cline_lt hj hj1 (by omega)
        exact (mul_pos_of_neg_of_neg h2 (by linarith)).le
  · -- the functional separating lines `< i` from lines `≥ i`
    rw [hm] at hi
    have key : ∃ f : (Fin 2 → ℝ) →ₗ[ℝ] ℝ, ∀ j : Fin n, c j ≠ 0 →
        (0 < f (g j) ↔ (cpos (c j) == σ) = decide (i ≤ cline (c j))) ∧
        (f (g j) < 0 ↔ (cpos (c j) == σ) ≠ decide (i ≤ cline (c j))) := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · refine ⟨linB (sgn σ), fun j hj => ?_⟩
        rw [linB_apply, hc.sgn_mul_pos_iff hj, hc.sgn_mul_neg_iff hj]
        cases cpos (c j) <;> cases σ <;> simp
      · obtain ⟨j1, hj1, hl1⟩ := hc.used (i - 1) (by omega)
        obtain ⟨j2, hj2, hl2⟩ := hc.used i hi
        have h12 := hc.slope_lt_of_cline_lt hj1 hj2 (by omega)
        refine ⟨linA (sgn σ) ((slope (g j1) + slope (g j2)) / 2), fun j hj => ?_⟩
        rw [hc.linA_eq hj]
        by_cases hle : i ≤ cline (c j)
        · have h3 := hc.slope_le_of_cline_le hj2 hj (by omega)
          have hd : 0 < slope (g j) - (slope (g j1) + slope (g j2)) / 2 := by linarith
          rw [(mul_sign_pos hd).1, (mul_sign_pos hd).2,
            hc.sgn_mul_pos_iff hj, hc.sgn_mul_neg_iff hj]
          cases cpos (c j) <;> cases σ <;> simp [hle]
        · have h3 := hc.slope_le_of_cline_le hj hj1 (by omega)
          have hd : slope (g j) - (slope (g j1) + slope (g j2)) / 2 < 0 := by linarith
          rw [(mul_sign_neg hd).1, (mul_sign_neg hd).2,
            hc.sgn_mul_neg_iff hj, hc.sgn_mul_pos_iff hj]
          cases cpos (c j) <;> cases σ <;> simp [hle]
    obtain ⟨f, hf⟩ := key
    refine ⟨f, fun j => ⟨fun hp => ?_, fun hn => ?_⟩⟩
    · rw [hB] at hp
      simp only [testBit_maskOf, List.length_ofFn, cd_ofFn, Bool.and_eq_true, decide_eq_true_eq,
        j.2, true_and] at hp
      simp only [posB, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hp
      exact (hf j hp.1).1.2 hp.2
    · rw [hB] at hn
      simp only [testBit_maskOf, List.length_ofFn, cd_ofFn, decide_eq_true_eq, j.2,
        Bool.true_and] at hn
      by_cases hj : c j = 0
      · rw [hc.zero_of_code hj, map_zero]
      have hn' : (cpos (c j) == σ) = decide (i ≤ cline (c j)) := by
        simp only [negB, Bool.and_eq_false_iff, bne_iff_ne, ne_eq, hj, not_false_eq_true,
          Bool.not_eq_true, false_or, bne_eq_false_iff_eq] at hn
        simpa using hn
      exact ((hf j hj).1.2 hn').le

/-- **Certified subsets have no positive dependency.** -/
theorem not_posDep_of_farkas (hm : nlines (List.ofFn c) = m) {S : ℕ}
    (hfar : ∃ pn ∈ candidates (List.ofFn c),
      (∀ j : Fin n, pn.2.testBit j = true → S.testBit j = false) ∧
      ∃ j : Fin n, pn.1.testBit j = true ∧ S.testBit j = true) :
    ¬ ∃ a : Fin n → ℝ, (∀ j : Fin n, S.testBit j = true → 0 < a j) ∧
      (∀ j : Fin n, S.testBit j = false → a j = 0) ∧ ∑ j, a j • g j = 0 := by
  obtain ⟨pn, hpn, hN, j0, hj0P, hj0S⟩ := hfar
  obtain ⟨f, hf⟩ := hc.exists_functional_of_candidate hm hpn
  rintro ⟨a, ha, ha0, hsum⟩
  have hfs : ∑ j, a j * f (g j) = 0 := by
    have := congrArg f hsum
    rw [map_sum, map_zero] at this
    simpa [map_smul, smul_eq_mul] using this
  have hterm : ∀ j, 0 ≤ a j * f (g j) := by
    intro j
    cases hS : S.testBit j
    · rw [ha0 j hS, zero_mul]
    · have hN' : pn.2.testBit j = false := by
        cases h' : pn.2.testBit j
        · rfl
        · rw [hN j h'] at hS; exact absurd hS (by simp)
      exact mul_nonneg (ha j hS).le ((hf j).2 hN')
  have hpos : 0 < a j0 * f (g j0) := mul_pos (ha j0 hj0S) ((hf j0).1 hj0P)
  have : 0 < ∑ j, a j * f (g j) :=
    lt_of_lt_of_le hpos (Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ j0))
  linarith

end CodeFor

end Kalai5.Gale
