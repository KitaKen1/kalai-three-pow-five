import Kalai5.FullPrism.Pattern

/-!
# Counting the exposed faces of the prism configuration

Oriented data: `A_k > 0 > B_k`, `A_k + B_k = κ ≥ 0`, and every value assignment
`(ξ⁺_k, ξ⁻_k)` with `A_k ξ⁺_k + B_k ξ⁻_k = x` (the same `x` for all `k`) is realized by a linear form
(this is what the common line gives).  We exhibit the faces of `conv {±v⁺_k, ±v⁻_k}` level by level
(design note `cayley_report.md` §2):

* **parallel** (`κ = 0`): levels `0, ±m` with three cells per factor, and one pattern at each of the
  levels `±2m` (`m = min A_k`): `3 · 80 + 2` nonempty faces, plus `P`, `243` in all;
* **concurrent** (`κ > 0`): levels `0, ±κ, κ + ε`: `80 + 3 · 65` nonempty faces, plus `P`.
-/

namespace Kalai5.FullPrism

open Set Module Kalai5.Gale

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {v : Fin 8 → E5}

/-! ### From realizable patterns to faces -/

/-- A pattern realized by a linear form with all values in `[-1, 1]`. -/
def Realizable (v : Fin 8 → E5) (s : Fin 4 → ℤ × ℤ) : Prop :=
  ∃ z : E5, ∃ ξp ξm : Fin 4 → ℝ, (∀ k, ⟪z, vp v k⟫ = ξp k ∧ ⟪z, vm v k⟫ = ξm k) ∧
    (∀ k, |ξp k| ≤ 1 ∧ |ξm k| ≤ 1) ∧ s = fun k => (sgnOf (ξp k), sgnOf (ξm k))

/-- **Each realizable nonzero pattern is a face**, and `P` itself is one more. -/
theorem card_add_one_le (T : Finset (Fin 4 → ℤ × ℤ)) (hT : ∀ s ∈ T, s ≠ 0 ∧ Realizable v s) :
    T.card + 1 ≤ (faces (convexHull ℝ (range (pm16 v)))).ncard := by
  classical
  have hpat : ∀ s ∈ T, IsPat s := by
    intro s hs
    obtain ⟨-, z, ξp, ξm, -, -, rfl⟩ := hT s hs
    exact isPat_sgnOf ξp ξm
  have hnot : Finset.univ ∉ T.image patIdx := by
    intro h
    obtain ⟨s, -, hs⟩ := Finset.mem_image.1 h
    exact patIdx_ne_univ s hs
  have hcard : (insert Finset.univ (T.image patIdx)).card = T.card + 1 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn]
    intro s hs s' hs' h
    exact patIdx_injOn (hpat s hs) (hpat s' hs') h
  rw [← hcard]
  apply le_ncard_faces
  intro F hF
  rcases Finset.mem_insert.1 hF with rfl | hF
  · exact ⟨Finset.univ_nonempty, isFaceIdx_univ⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hF
    obtain ⟨hs0, z, ξp, ξm, hz, hb, rfl⟩ := hT s hs
    refine ⟨?_, ?_⟩
    · obtain ⟨k, hk⟩ : ∃ k, (sgnOf (ξp k), sgnOf (ξm k)) ≠ (0, 0) := by
        by_contra h
        push_neg at h
        exact hs0 (funext fun k => h k)
      exact patIdx_nonempty hk (isPat_sgnOf ξp ξm)
    · rw [← idxOf_eq_patIdx hz]
      apply isFaceIdx_idxOf
      intro j
      rw [inner_v_eq hz j]
      split_ifs
      · exact (hb _).1
      · exact (hb _).2

lemma sgnOf_one : sgnOf 1 = 1 := by simp [sgnOf]

lemma sgnOf_neg_one : sgnOf (-1) = -1 := by norm_num [sgnOf]

lemma sgnOf_of_abs_lt {x : ℝ} (h : |x| < 1) : sgnOf x = 0 := by
  have h1 : x ≠ 1 := fun e => by rw [e] at h; norm_num at h
  have h2 : x ≠ -1 := fun e => by rw [e] at h; norm_num at h
  simp [sgnOf, h1, h2]

/-! ### The parallel case -/

/-- Cells of the levels `0, m, -m`. -/
def cellPar : Fin 3 → Fin 3 → ℤ × ℤ :=
  ![![(0, 0), (1, 1), (-1, -1)], ![(0, 0), (1, 0), (0, -1)], ![(0, 0), (-1, 0), (0, 1)]]

/-- Values realizing the cells (`a = A_k`, `m = min A`). -/
noncomputable def valsPar (m a : ℝ) : Fin 3 → Fin 3 → ℝ × ℝ :=
  ![![(0, 0), (1, 1), (-1, -1)],
    ![(m / a / 2, -(m / a / 2)), (1, 1 - m / a), (m / a - 1, -1)],
    ![(-(m / a / 2), m / a / 2), (-1, m / a - 1), (1 - m / a, 1)]]

noncomputable def levPar (m : ℝ) : Fin 3 → ℝ := ![0, m, -m]

lemma valsPar_level {m a : ℝ} (ha : a ≠ 0) (ℓ c : Fin 3) :
    a * (valsPar m a ℓ c).1 + (-a) * (valsPar m a ℓ c).2 = levPar m ℓ := by
  fin_cases ℓ <;> fin_cases c <;> simp [valsPar, levPar] <;> field_simp <;> ring

lemma valsPar_spec {m a : ℝ} (hm : 0 < m) (hma : m ≤ a) (ℓ c : Fin 3) :
    (|(valsPar m a ℓ c).1| ≤ 1 ∧ |(valsPar m a ℓ c).2| ≤ 1) ∧
      (sgnOf (valsPar m a ℓ c).1, sgnOf (valsPar m a ℓ c).2) = cellPar ℓ c := by
  have ha : 0 < a := lt_of_lt_of_le hm hma
  have h1 : 0 < m / a := div_pos hm ha
  have h2 : m / a ≤ 1 := (div_le_one ha).2 hma
  have e1 : |m / a / 2| < 1 := by rw [abs_lt]; constructor <;> linarith
  have e2 : |-(m / a / 2)| < 1 := by rw [abs_neg]; exact e1
  have e3 : |1 - m / a| < 1 := by rw [abs_lt]; constructor <;> linarith
  have e4 : |m / a - 1| < 1 := by rw [abs_lt]; constructor <;> linarith
  fin_cases ℓ <;> fin_cases c <;>
    simp [valsPar, cellPar, sgnOf_one, sgnOf_neg_one, sgnOf_of_abs_lt, e1, e2, e3, e4,
      e1.le, e2.le, e3.le, e4.le]

/-- The pattern of level `ℓ` and cells `c`. -/
def patPar (lc : Fin 3 × (Fin 4 → Fin 3)) : Fin 4 → ℤ × ℤ := fun k => cellPar lc.1 (lc.2 k)

lemma cellPar_inj : ∀ ℓ ℓ' x y : Fin 3, x ≠ 0 → cellPar ℓ x = cellPar ℓ' y → ℓ = ℓ' ∧ x = y := by
  decide

lemma cellPar_zero : ∀ ℓ : Fin 3, cellPar ℓ 0 = (0, 0) := by decide

lemma cellPar_eq_zero : ∀ ℓ y : Fin 3, cellPar ℓ y = (0, 0) → y = 0 := by decide

lemma cellPar_ne : ∀ ℓ x : Fin 3, cellPar ℓ x ≠ (1, -1) ∧ cellPar ℓ x ≠ (-1, 1) := by decide

lemma patPar_injOn : Set.InjOn patPar {lc | lc.2 ≠ 0} := by
  rintro ⟨ℓ, c⟩ hc ⟨ℓ', c'⟩ - h
  simp only [Set.mem_setOf_eq] at hc
  obtain ⟨k, hk⟩ : ∃ k, c k ≠ 0 := by
    by_contra h'; push_neg at h'; exact hc (funext h')
  have hk' := congrFun h k
  simp only [patPar] at hk'
  obtain ⟨rfl, -⟩ := cellPar_inj ℓ ℓ' (c k) (c' k) hk hk'
  refine Prod.ext rfl (funext fun j => ?_)
  have hj := congrFun h j
  simp only [patPar] at hj
  show c j = c' j
  by_cases hcj : c j = 0
  · rw [hcj, cellPar_zero] at hj
    rw [hcj, cellPar_eq_zero ℓ (c' j) hj.symm]
  · exact (cellPar_inj ℓ ℓ (c j) (c' j) hcj hj).2

lemma card_dom_par : (Finset.univ.filter fun lc : Fin 3 × (Fin 4 → Fin 3) => lc.2 ≠ 0).card = 240 := by
  have : (Finset.univ.filter fun lc : Fin 3 × (Fin 4 → Fin 3) => lc.2 ≠ 0) =
      (Finset.univ : Finset (Fin 3)) ×ˢ (Finset.univ.erase 0) := by
    ext ⟨ℓ, c⟩; simp
  rw [this, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

/-- **Parallel edges** (`κ = 0`): at least 243 faces. -/
theorem faces_parallel {A : Fin 4 → ℝ} (hA : ∀ k, 0 < A k)
    (hreal : ∀ (x : ℝ) (Xp Xm : Fin 4 → ℝ), (∀ k, A k * Xp k + (-A k) * Xm k = x) →
      ∃ z : E5, ∀ k, ⟪z, vp v k⟫ = Xp k ∧ ⟪z, vm v k⟫ = Xm k) :
    243 ≤ (faces (convexHull ℝ (range (pm16 v)))).ncard := by
  classical
  obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image Finset.univ A ⟨0, Finset.mem_univ _⟩
  set m := A k0 with hmdef
  have hm : 0 < m := hA k0
  have hmle : ∀ k, m ≤ A k := fun k => hk0 k (Finset.mem_univ _)
  -- the patterns of the levels `0, ±m`
  have hrealPar : ∀ lc : Fin 3 × (Fin 4 → Fin 3), Realizable v (patPar lc) := by
    rintro ⟨ℓ, c⟩
    obtain ⟨z, hz⟩ := hreal (levPar m ℓ) (fun k => (valsPar m (A k) ℓ (c k)).1)
      (fun k => (valsPar m (A k) ℓ (c k)).2) (fun k => valsPar_level (hA k).ne' ℓ (c k))
    refine ⟨z, _, _, hz, fun k => (valsPar_spec hm (hmle k) ℓ (c k)).1, ?_⟩
    funext k
    exact ((valsPar_spec hm (hmle k) ℓ (c k)).2).symm
  -- the two patterns of the levels `±2m`
  set ePos : Fin 4 → ℤ × ℤ := fun k => if A k = m then (1, -1) else (0, 0) with hePos
  set eNeg : Fin 4 → ℤ × ℤ := fun k => if A k = m then (-1, 1) else (0, 0) with heNeg
  have hfrac : ∀ k, A k ≠ m → |m / A k| < 1 := by
    intro k hk
    have hlt : m < A k := lt_of_le_of_ne (hmle k) (Ne.symm hk)
    rw [abs_lt]; constructor
    · have := div_pos hm (hA k); linarith
    · exact (div_lt_one (hA k)).2 hlt
  have hbound : ∀ k, |m / A k| ≤ 1 := by
    intro k
    rw [abs_le]; constructor
    · have := div_pos hm (hA k); linarith
    · exact (div_le_one (hA k)).2 (hmle k)
  have hePos' : Realizable v ePos := by
    obtain ⟨z, hz⟩ := hreal (2 * m) (fun k => m / A k) (fun k => -(m / A k))
      (fun k => by field_simp [(hA k).ne']; ring)
    refine ⟨z, _, _, hz, fun k => ⟨hbound k, by rw [abs_neg]; exact hbound k⟩, ?_⟩
    funext k
    show (if A k = m then ((1 : ℤ), (-1 : ℤ)) else (0, 0)) = (sgnOf (m / A k), sgnOf (-(m / A k)))
    by_cases hk : A k = m
    · rw [if_pos hk, hk, div_self hm.ne', sgnOf_one, sgnOf_neg_one]
    · rw [if_neg hk, sgnOf_of_abs_lt (hfrac k hk),
        sgnOf_of_abs_lt (by rw [abs_neg]; exact hfrac k hk)]
  have heNeg' : Realizable v eNeg := by
    obtain ⟨z, hz⟩ := hreal (-(2 * m)) (fun k => -(m / A k)) (fun k => m / A k)
      (fun k => by field_simp [(hA k).ne']; ring)
    refine ⟨z, _, _, hz, fun k => ⟨by rw [abs_neg]; exact hbound k, hbound k⟩, ?_⟩
    funext k
    show (if A k = m then ((-1 : ℤ), (1 : ℤ)) else (0, 0)) = (sgnOf (-(m / A k)), sgnOf (m / A k))
    by_cases hk : A k = m
    · rw [if_pos hk, hk, div_self hm.ne', sgnOf_one, sgnOf_neg_one]
    · rw [if_neg hk, sgnOf_of_abs_lt (hfrac k hk),
        sgnOf_of_abs_lt (by rw [abs_neg]; exact hfrac k hk)]
  -- the family
  set TPar := (Finset.univ.filter fun lc : Fin 3 × (Fin 4 → Fin 3) => lc.2 ≠ 0).image patPar
  have hTPar : TPar.card = 240 := by
    rw [Finset.card_image_of_injOn, card_dom_par]
    intro x hx y hy h
    exact patPar_injOn (by simpa using hx) (by simpa using hy) h
  have hk0m : A k0 = m := rfl
  have heNeg_notin : eNeg ∉ TPar := by
    intro h
    obtain ⟨lc, -, hlc⟩ := Finset.mem_image.1 h
    have := congrFun hlc k0
    simp only [patPar, heNeg, if_pos hk0m] at this
    exact (cellPar_ne _ _).2 this
  have hePos_notin : ePos ∉ insert eNeg TPar := by
    intro h
    rcases Finset.mem_insert.1 h with h | h
    · have := congrFun h k0
      simp only [hePos, heNeg, if_pos hk0m] at this
      norm_num at this
    · obtain ⟨lc, -, hlc⟩ := Finset.mem_image.1 h
      have := congrFun hlc k0
      simp only [patPar, hePos, if_pos hk0m] at this
      exact (cellPar_ne _ _).1 this
  have hcard : (insert ePos (insert eNeg TPar)).card = 242 := by
    rw [Finset.card_insert_of_notMem hePos_notin, Finset.card_insert_of_notMem heNeg_notin, hTPar]
  have h := card_add_one_le (v := v) (insert ePos (insert eNeg TPar)) (by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · refine ⟨fun h0 => ?_, hePos'⟩
      have := congrFun h0 k0
      simp only [hePos, if_pos hk0m, Pi.zero_apply] at this
      norm_num [Prod.ext_iff] at this
    rcases Finset.mem_insert.1 hs with rfl | hs
    · refine ⟨fun h0 => ?_, heNeg'⟩
      have := congrFun h0 k0
      simp only [heNeg, if_pos hk0m, Pi.zero_apply] at this
      norm_num [Prod.ext_iff] at this
    · obtain ⟨⟨ℓ, c⟩, hlc, rfl⟩ := Finset.mem_image.1 hs
      refine ⟨fun h0 => ?_, hrealPar _⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlc
      apply hlc
      funext k
      exact cellPar_eq_zero ℓ (c k) (congrFun h0 k))
  rw [hcard] at h
  exact h

/-! ### The concurrent case -/

/-- Cells of the levels `0, κ, -κ, κ + ε`. -/
def cellCon : Fin 4 → Fin 3 → ℤ × ℤ :=
  ![![(0, 0), (0, 1), (0, -1)], ![(0, 0), (1, 1), (0, -1)], ![(0, 0), (-1, -1), (0, 1)],
    ![(0, 0), (1, 0), (0, -1)]]

/-- Values realizing the cells (`a = A_k > 0 > b = B_k`, `a + b = κ > 0`, `0 < ε ≤ -b/2`). -/
noncomputable def valsCon (κ ε a b : ℝ) : Fin 4 → Fin 3 → ℝ × ℝ :=
  ![![(0, 0), (-b / a, 1), (b / a, -1)],
    ![(κ / a, 0), (1, 1), ((κ + b) / a, -1)],
    ![(-(κ / a), 0), (-1, -1), (-((κ + b) / a), 1)],
    ![((κ + ε) / a, 0), (1, 1 + ε / b), ((κ + ε + b) / a, -1)]]

noncomputable def levCon (κ ε : ℝ) : Fin 4 → ℝ := ![0, κ, -κ, κ + ε]

lemma valsCon_level {κ ε a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b = κ) (ℓ : Fin 4)
    (c : Fin 3) : a * (valsCon κ ε a b ℓ c).1 + b * (valsCon κ ε a b ℓ c).2 = levCon κ ε ℓ := by
  subst hab
  fin_cases ℓ <;> fin_cases c <;> simp [valsCon, levCon] <;> field_simp <;> ring

lemma valsCon_spec {κ ε a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : b < 0) (hab : a + b = κ)
    (hε : 0 < ε) (hεb : ε ≤ -b / 2) (ℓ : Fin 4) (c : Fin 3) :
    (|(valsCon κ ε a b ℓ c).1| ≤ 1 ∧ |(valsCon κ ε a b ℓ c).2| ≤ 1) ∧
      (sgnOf (valsCon κ ε a b ℓ c).1, sgnOf (valsCon κ ε a b ℓ c).2) = cellCon ℓ c := by
  have hd : ∀ x : ℝ, -a < x → x < a → |x / a| < 1 := by
    intro x h1 h2
    rw [abs_div, abs_of_pos ha, div_lt_one ha, abs_lt]
    exact ⟨h1, h2⟩
  have f1 : |-b / a| < 1 := hd _ (by linarith) (by linarith)
  have f2 : |b / a| < 1 := hd _ (by linarith) (by linarith)
  have f3 : |κ / a| < 1 := hd _ (by linarith) (by linarith)
  have f4 : |-(κ / a)| < 1 := by rw [abs_neg]; exact f3
  have f5 : |(κ + b) / a| < 1 := hd _ (by linarith) (by linarith)
  have f6 : |-((κ + b) / a)| < 1 := by rw [abs_neg]; exact f5
  have f7 : |(κ + ε) / a| < 1 := hd _ (by linarith) (by linarith)
  have f8 : |1 + ε / b| < 1 := by
    have g1 : ε / b < 0 := div_neg_of_pos_of_neg hε hb
    have g2 : -1 / 2 ≤ ε / b := by rw [le_div_iff_of_neg hb]; linarith
    rw [abs_lt]; constructor <;> linarith
  have f9 : |(κ + ε + b) / a| < 1 := hd _ (by linarith) (by linarith)
  fin_cases ℓ <;> fin_cases c <;>
    simp [valsCon, cellCon, sgnOf_one, sgnOf_neg_one, sgnOf_of_abs_lt, f1, f2, f3, f4, f5, f6, f7,
      f8, f9, f1.le, f2.le, f3.le, f4.le, f5.le, f6.le, f7.le, f8.le, f9.le]

/-- The pattern of level `ℓ` and cells `c`. -/
def patCon (lc : Fin 4 × (Fin 4 → Fin 3)) : Fin 4 → ℤ × ℤ := fun k => cellCon lc.1 (lc.2 k)

lemma cellCon_inj : ∀ (ℓ : Fin 4) (x y : Fin 3), cellCon ℓ x = cellCon ℓ y → x = y := by decide

lemma cellCon_one : ∀ ℓ ℓ' : Fin 4, ∀ y : Fin 3, ℓ ≠ 0 → cellCon ℓ 1 = cellCon ℓ' y → ℓ' = ℓ := by
  decide

lemma cellCon_eq_zero : ∀ (ℓ : Fin 4) (y : Fin 3), cellCon ℓ y = (0, 0) → y = 0 := by decide

/-- The index set: level `0` with some nonzero cell, or another level with some cell `1`. -/
def domCon : Finset (Fin 4 × (Fin 4 → Fin 3)) :=
  Finset.univ.filter fun lc => (lc.1 = 0 ∧ lc.2 ≠ 0) ∨ (lc.1 ≠ 0 ∧ ∃ k, lc.2 k = 1)

lemma card_domCon : domCon.card = 275 := by decide +kernel

lemma patCon_injOn : Set.InjOn patCon domCon := by
  rintro ⟨ℓ, c⟩ hc ⟨ℓ', c'⟩ hc' h
  simp only [domCon, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hc hc'
  have hlev : ℓ = ℓ' := by
    by_cases hℓ : ℓ = 0
    · by_cases hℓ' : ℓ' = 0
      · rw [hℓ, hℓ']
      · obtain ⟨k, hk⟩ := (hc'.resolve_left fun h' => hℓ' h'.1).2
        have := congrFun h k
        simp only [patCon, hk] at this
        exact absurd (cellCon_one ℓ' ℓ (c k) hℓ' this.symm) (fun e => hℓ' (e ▸ hℓ))
    · obtain ⟨k, hk⟩ := (hc.resolve_left fun h' => hℓ h'.1).2
      have := congrFun h k
      simp only [patCon, hk] at this
      exact (cellCon_one ℓ ℓ' (c' k) hℓ this).symm
  subst hlev
  refine Prod.ext rfl (funext fun j => ?_)
  have := congrFun h j
  exact cellCon_inj ℓ (c j) (c' j) this

/-- **Concurrent edge lines** (`κ > 0`): at least 243 faces (in fact 276). -/
theorem faces_concurrent {A B : Fin 4 → ℝ} {κ : ℝ} (hκ : 0 < κ) (hA : ∀ k, 0 < A k)
    (hB : ∀ k, B k < 0) (hAB : ∀ k, A k + B k = κ)
    (hreal : ∀ (x : ℝ) (Xp Xm : Fin 4 → ℝ), (∀ k, A k * Xp k + B k * Xm k = x) →
      ∃ z : E5, ∀ k, ⟪z, vp v k⟫ = Xp k ∧ ⟪z, vm v k⟫ = Xm k) :
    243 ≤ (faces (convexHull ℝ (range (pm16 v)))).ncard := by
  classical
  obtain ⟨k1, -, hk1⟩ := Finset.exists_min_image Finset.univ (fun k => -B k) ⟨0, Finset.mem_univ _⟩
  set ε := -B k1 / 2 with hεdef
  have hε : 0 < ε := by have := hB k1; rw [hεdef]; linarith
  have hεb : ∀ k, ε ≤ -B k / 2 := fun k => by
    have := hk1 k (Finset.mem_univ _); rw [hεdef]; linarith
  have hrealCon : ∀ lc : Fin 4 × (Fin 4 → Fin 3), Realizable v (patCon lc) := by
    rintro ⟨ℓ, c⟩
    obtain ⟨z, hz⟩ := hreal (levCon κ ε ℓ) (fun k => (valsCon κ ε (A k) (B k) ℓ (c k)).1)
      (fun k => (valsCon κ ε (A k) (B k) ℓ (c k)).2)
      (fun k => valsCon_level (hA k).ne' (hB k).ne (hAB k) ℓ (c k))
    refine ⟨z, _, _, hz, fun k =>
      (valsCon_spec hκ (hA k) (hB k) (hAB k) hε (hεb k) ℓ (c k)).1, ?_⟩
    funext k
    exact ((valsCon_spec hκ (hA k) (hB k) (hAB k) hε (hεb k) ℓ (c k)).2).symm
  have hcard : (domCon.image patCon).card = 275 := by
    rw [Finset.card_image_of_injOn patCon_injOn, card_domCon]
  have h := card_add_one_le (v := v) (domCon.image patCon) (by
    intro s hs
    obtain ⟨⟨ℓ, c⟩, hlc, rfl⟩ := Finset.mem_image.1 hs
    refine ⟨fun h0 => ?_, hrealCon _⟩
    simp only [domCon, Finset.mem_filter, Finset.mem_univ, true_and] at hlc
    rcases hlc with ⟨-, hc⟩ | ⟨-, k, hk⟩
    · apply hc
      funext k
      exact cellCon_eq_zero ℓ (c k) (congrFun h0 k)
    · have := cellCon_eq_zero ℓ (c k) (congrFun h0 k)
      rw [hk] at this
      exact absurd this (by decide))
  rw [hcard] at h
  omega

end Kalai5.FullPrism
