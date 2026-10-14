import Kalai5.A16.Cert
import Kalai5.LemmaA.Sound

/-!
# A16: semantics of the facts

`Z4.ev u a = u · a`; the sixteen points `pt a w = (q_w, ζ_w · a)`; `Holds a facts`: every fact
`(p, s)` is the sign of `ℓ_p(a)`.  Soundness of the arithmetic steps of the checker: Motzkin
refutations, implied signs, forced coincidences, and forced `a = 0`.
-/

namespace Kalai5.A16

open Set Kalai5.LemmaA

/-- `u · a`. -/
def Z4.ev (u : Z4) (a : Fin 4 → ℝ) : ℝ :=
  (u.x0 : ℝ) * a 0 + (u.x1 : ℝ) * a 1 + (u.x2 : ℝ) * a 2 + (u.x3 : ℝ) * a 3

@[simp] lemma Z4.ev_add (u v : Z4) (a : Fin 4 → ℝ) : (Z4.add u v).ev a = u.ev a + v.ev a := by
  simp only [Z4.add, Z4.ev]; push_cast; ring

@[simp] lemma Z4.ev_smul (c : ℤ) (u : Z4) (a : Fin 4 → ℝ) : (Z4.smul c u).ev a = c * u.ev a := by
  simp only [Z4.smul, Z4.ev]; push_cast; ring

@[simp] lemma Z4.ev_neg (u : Z4) (a : Fin 4 → ℝ) : u.neg.ev a = -u.ev a := by
  simp only [Z4.neg, Z4.ev]; push_cast; ring

@[simp] lemma Z4.ev_zero (a : Fin 4 → ℝ) : Z4.zero.ev a = 0 := by simp [Z4.zero, Z4.ev]

lemma Z4.ev_of_isZero {u : Z4} (h : u.isZero = true) (a : Fin 4 → ℝ) : u.ev a = 0 := by
  simp only [Z4.isZero, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  simp [Z4.ev, h0, h1, h2, h3]

lemma Z4.eq_of_ev {u v : Z4} (h : u = v) (a : Fin 4 → ℝ) : u.ev a = v.ev a := by rw [h]

lemma foldl_ev {α : Type*} (g : α → Z4) (a : Fin 4 → ℝ) (l : List α) (acc : Z4) :
    (l.foldl (fun acc t => Z4.add acc (g t)) acc).ev a = acc.ev a + (l.map fun t => (g t).ev a).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons t l ih => rw [List.foldl_cons, ih, Z4.ev_add, List.map_cons, List.sum_cons]; ring

namespace Family

variable (F : Family)

/-- The facts hold at `a`. -/
def Holds (a : Fin 4 → ℝ) (facts : Facts) : Prop := ∀ t ∈ facts, SignIs ((F.plane t.1).ev a) t.2

lemma holds_append {a : Fin 4 → ℝ} {facts : Facts} (h : F.Holds a facts) {p : ℕ} {s : ℤ}
    (hs : SignIs ((F.plane p).ev a) s) : F.Holds a (facts ++ [(p, s)]) := by
  intro t ht
  rcases List.mem_append.1 ht with ht | ht
  · exact h t ht
  · rw [List.mem_singleton] at ht; subst ht; exact hs

lemma holds_of_factOf {a : Fin 4 → ℝ} {facts : Facts} (h : F.Holds a facts) {p : ℕ}
    {s : ℤ} (hp : factOf facts p = some s) : SignIs ((F.plane p).ev a) s := by
  unfold factOf at hp
  rw [Option.map_eq_some_iff] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  have hmem := List.mem_of_find?_eq_some ht
  have hp' := List.find?_some ht
  simp only [beq_iff_eq] at hp'
  rw [← hp']
  exact h t hmem

lemma holds_getD {a : Fin 4 → ℝ} {facts : Facts} (h : F.Holds a facts) {k : ℕ}
    (hk : k < facts.length) :
    SignIs ((F.plane (facts.getD k (0, 0)).1).ev a) (facts.getD k (0, 0)).2 := by
  rw [List.getD_eq_getElem _ _ hk]
  exact h _ (List.getElem_mem hk)

/-- The value of a combination of facts. -/
lemma comb_ev (facts : Facts) (cert : List (ℕ × ℤ)) (a : Fin 4 → ℝ) :
    (F.comb facts cert).ev a = (cert.map fun t =>
      ((t.2 * (if (facts.getD t.1 (0, 0)).2 == 0 then 1 else (facts.getD t.1 (0, 0)).2) : ℤ) : ℝ) *
        (F.plane (facts.getD t.1 (0, 0)).1).ev a).sum := by
  unfold comb
  rw [foldl_ev, Z4.ev_zero, zero_add]
  congr 1
  apply List.map_congr_left
  intro t _
  simp

/-- Each term of a combination with a nonnegative coefficient on a strict fact is nonnegative,
and positive if the coefficient is positive. -/
lemma term_nonneg {a : Fin 4 → ℝ} {facts : Facts} (h : F.Holds a facts) {t : ℕ × ℤ}
    (hk : t.1 < facts.length) (hc : (facts.getD t.1 (0, 0)).2 = 0 ∨ 0 ≤ t.2) :
    0 ≤ ((t.2 * (if (facts.getD t.1 (0, 0)).2 == 0 then 1 else (facts.getD t.1 (0, 0)).2) : ℤ) : ℝ) *
        (F.plane (facts.getD t.1 (0, 0)).1).ev a ∧
      ((facts.getD t.1 (0, 0)).2 ≠ 0 → 0 < t.2 →
        0 < ((t.2 * (if (facts.getD t.1 (0, 0)).2 == 0 then 1 else
          (facts.getD t.1 (0, 0)).2) : ℤ) : ℝ) * (F.plane (facts.getD t.1 (0, 0)).1).ev a) := by
  have hsg := F.holds_getD h hk
  set f := facts.getD t.1 (0, 0)
  by_cases hs : f.2 = 0
  · rw [hs] at hsg
    rw [hsg.eq_zero]
    simp [hs]
  · have hpos := hsg.mul_pos hs
    have hnn : (0 : ℝ) ≤ t.2 := by exact_mod_cast hc.resolve_left hs
    have hsb : (f.2 == 0) = false := by simpa using hs
    rw [hsb]
    simp only [Bool.false_eq_true, if_false]
    push_cast
    refine ⟨by nlinarith, fun _ hc0 => ?_⟩
    have : (0 : ℝ) < t.2 := by exact_mod_cast hc0
    nlinarith

/-- **Motzkin refutations are sound.** -/
lemma refutes_sound {a : Fin 4 → ℝ} {facts : Facts} {cert : List (ℕ × ℤ)}
    (hc : F.refutes facts cert = true) (h : F.Holds a facts) : False := by
  unfold refutes at hc
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq, Bool.or_eq_true,
    decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hall, ⟨t0, ht0, hs0, hc0⟩⟩, hsum⟩ := hc
  have hdot := Z4.ev_of_isZero hsum a
  rw [comb_ev] at hdot
  have key : 0 < (cert.map fun t =>
      ((t.2 * (if (facts.getD t.1 (0, 0)).2 == 0 then 1 else (facts.getD t.1 (0, 0)).2) : ℤ) : ℝ) *
        (F.plane (facts.getD t.1 (0, 0)).1).ev a).sum := by
    obtain ⟨hk0, hnn0⟩ := hall t0 ht0
    refine lt_of_lt_of_le ((F.term_nonneg h hk0 hnn0).2 hs0 hc0)
      (List.single_le_sum (fun x hx => ?_) _ (List.mem_map_of_mem ht0))
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hk, hnn⟩ := hall t ht
    exact (F.term_nonneg h hk hnn).1
  linarith

/-- **Implied signs are sound.** -/
lemma impliesSign_sound {a : Fin 4 → ℝ} {facts : Facts} {p : ℕ} {s : ℤ} {cert : List (ℕ × ℤ)}
    {den : ℤ} (hc : F.impliesSign facts p s cert den = true) (h : F.Holds a facts) :
    SignIs ((F.plane p).ev a) s := by
  unfold impliesSign at hc
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hlen, hc⟩ := hc
  split_ifs at hc with hs
  · -- vanishing
    simp only [beq_iff_eq] at hs
    subst hs
    simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
    obtain ⟨⟨hden, hz⟩, hcomb⟩ := hc
    have hv := Z4.eq_of_ev hcomb a
    rw [comb_ev, Z4.ev_smul] at hv
    have hzero : (cert.map fun t =>
        ((t.2 * (if (facts.getD t.1 (0, 0)).2 == 0 then 1 else (facts.getD t.1 (0, 0)).2) : ℤ) : ℝ) *
          (F.plane (facts.getD t.1 (0, 0)).1).ev a).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      have hsg := F.holds_getD h (hlen t ht)
      rw [hz t ht] at hsg
      rw [hsg.eq_zero, mul_zero]
    rw [hzero] at hv
    have hd : (den : ℝ) ≠ 0 := by exact_mod_cast hden
    have : (F.plane p).ev a = 0 := by
      rcases mul_eq_zero.1 hv.symm with h1 | h1
      · exact absurd h1 hd
      · exact h1
    exact Or.inr (Or.inl ⟨rfl, this⟩)
  · simp only [beq_iff_eq] at hs
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
      List.any_eq_true, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨⟨hs1, hden⟩, hall⟩, ⟨t0, ht0, hs0, hc0⟩⟩, hcomb⟩ := hc
    have hv := Z4.eq_of_ev hcomb a
    rw [comb_ev, Z4.ev_smul] at hv
    have hpos : 0 < (cert.map fun t =>
        ((t.2 * (if (facts.getD t.1 (0, 0)).2 == 0 then 1 else (facts.getD t.1 (0, 0)).2) : ℤ) : ℝ) *
          (F.plane (facts.getD t.1 (0, 0)).1).ev a).sum := by
      refine lt_of_lt_of_le ((F.term_nonneg h (hlen t0 ht0) (hall t0 ht0)).2 hs0 hc0)
        (List.single_le_sum (fun x hx => ?_) _ (List.mem_map_of_mem ht0))
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      exact (F.term_nonneg h (hlen t ht) (hall t ht)).1
    rw [hv] at hpos
    have hd : (0 : ℝ) < den := by exact_mod_cast hden
    rcases hs1 with rfl | rfl
    · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
      push_cast at hpos
      nlinarith
    · refine Or.inl ⟨rfl, ?_⟩
      push_cast at hpos
      nlinarith

/-- The real dot product of an integer list of length four with `x`. -/
def dotR (u : List ℤ) (x : Fin 4 → ℝ) : ℝ :=
  (u.getD 0 0 : ℝ) * x 0 + (u.getD 1 0 : ℝ) * x 1 + (u.getD 2 0 : ℝ) * x 2 + (u.getD 3 0 : ℝ) * x 3

/-- **A spanning certificate**: a vector orthogonal to the four vectors is zero. -/
lemma spanCert_sound {us C : List (List ℤ)} {D : ℤ} (hc : spanCert us C D = true)
    {x : Fin 4 → ℝ} (hx : ∀ k < 4, dotR (us.getD k []) x = 0) : x = 0 := by
  unfold spanCert at hc
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true, List.mem_range]
    at hc
  obtain ⟨⟨⟨hD, -⟩, -⟩, hC⟩ := hc
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  have e : ∀ j < 4, ∀ i < 4, ((C.getD j []).getD 0 0 * (us.getD 0 []).getD i 0 +
      (C.getD j []).getD 1 0 * (us.getD 1 []).getD i 0 + (C.getD j []).getD 2 0 * (us.getD 2 []).getD i 0 +
      (C.getD j []).getD 3 0 * (us.getD 3 []).getD i 0 : ℝ) = if i = j then (D : ℝ) else 0 := by
    intro j hj i hi
    have h := hC j hj i hi
    simp only [hr, List.foldl_cons, List.foldl_nil, zero_add] at h
    split_ifs at h with hij
    · subst hij; simp only [if_true]; exact_mod_cast h
    · simp only [hij, if_false]; exact_mod_cast h
  have hx0 := hx 0 (by norm_num); have hx1 := hx 1 (by norm_num)
  have hx2 := hx 2 (by norm_num); have hx3 := hx 3 (by norm_num)
  simp only [dotR] at hx0 hx1 hx2 hx3
  have key : ∀ j : Fin 4, (D : ℝ) * x j = 0 := by
    intro j
    have e0 := e j j.2 0 (by norm_num); have e1 := e j j.2 1 (by norm_num)
    have e2 := e j j.2 2 (by norm_num); have e3 := e j j.2 3 (by norm_num)
    have hsum : (D : ℝ) * x j =
        (if 0 = (j : ℕ) then (D : ℝ) else 0) * x 0 + (if 1 = (j : ℕ) then (D : ℝ) else 0) * x 1 +
          (if 2 = (j : ℕ) then (D : ℝ) else 0) * x 2 + (if 3 = (j : ℕ) then (D : ℝ) else 0) * x 3 := by
      fin_cases j <;> simp
    rw [hsum, ← e0, ← e1, ← e2, ← e3]
    linear_combination ((C.getD j []).getD 0 0 : ℝ) * hx0 + ((C.getD j []).getD 1 0 : ℝ) * hx1 +
      ((C.getD j []).getD 2 0 : ℝ) * hx2 + ((C.getD j []).getD 3 0 : ℝ) * hx3
  funext i
  have := key i
  simpa [hD'] using this

lemma dotR_toList (u : Z4) (a : Fin 4 → ℝ) : dotR u.toList a = u.ev a := by
  simp [dotR, Z4.toList, Z4.ev]

/-- **Four vanishing planes of full rank force `a = 0`.** -/
lemma eq_zero_of_zero_node {a : Fin 4 → ℝ} {facts : Facts} (h : F.Holds a facts) {top : Bool}
    {p0 p1 p2 p3 : ℕ} {C : List (List ℤ)} {D : ℤ}
    (hw : F.walk top facts (.zero p0 p1 p2 p3 C D) = true) : a = 0 := by
  simp only [walk, Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, hc⟩ := hw
  refine spanCert_sound hc fun k hk => ?_
  interval_cases k <;> simp only [List.getD_cons_zero, List.getD_cons_succ, dotR_toList]
  · exact (F.holds_of_factOf h h0).eq_zero
  · exact (F.holds_of_factOf h h1).eq_zero
  · exact (F.holds_of_factOf h h2).eq_zero
  · exact (F.holds_of_factOf h h3).eq_zero

end Family

end Kalai5.A16
