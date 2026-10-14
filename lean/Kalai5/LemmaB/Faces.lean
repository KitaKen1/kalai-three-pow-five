import Kalai5.LemmaB.Config

/-!
# Lemma B: faces of a rank-three configuration as sign patterns

For a direction `b ∈ ℝ²` let `H_j(b)`, `L_j(b)` be the maximum and minimum of `⟪b, ·⟫` on the
fibre `K_j`.

* **Octahedral patterns** (`octPat`): `S : Fin 3 → Option Bool` uses class `j` with sign `+`
  (`some true`), `-` (`some false`) or not at all.  The pattern takes `1` at the points of `K_j`
  maximizing `⟪b, ·⟫` for `S j = +`, `-1` at the minimizers for `S j = -`, and `0` elsewhere.
  It is realized with `a_j = M - H_j`, `-M - L_j`, `-(H_j + L_j)/2`, scaled by `M = 1 + Σ widths`.
* **Equatorial patterns** (`equPat`): some classes carry both signs; these must be exactly the
  classes of maximal width `W(b) = 2M > 0`.
-/

namespace Kalai5.LemmaB

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {x : Fin 7 → E5} (C : Config x)

namespace Config

/-- Points of class `j`. -/
def cls (j : Fin 3) : Finset (Fin 7) := Finset.univ.filter fun v => C.c v = j

lemma cls_nonempty (j : Fin 3) : (C.cls j).Nonempty := by
  obtain ⟨v, hv⟩ := C.surj j
  exact ⟨v, by simp [cls, hv]⟩

/-- Maximum of `⟪b, ·⟫` on the fibre `j`. -/
noncomputable def hi (j : Fin 3) (b : E 2) : ℝ := (C.cls j).sup' (C.cls_nonempty j) fun v => ⟪b, C.k v⟫

/-- Minimum of `⟪b, ·⟫` on the fibre `j`. -/
noncomputable def lo (j : Fin 3) (b : E 2) : ℝ := (C.cls j).inf' (C.cls_nonempty j) fun v => ⟪b, C.k v⟫

lemma le_hi {v : Fin 7} (b : E 2) : ⟪b, C.k v⟫ ≤ C.hi (C.c v) b :=
  Finset.le_sup' (fun v => ⟪b, C.k v⟫) (by simp [cls])

lemma lo_le {v : Fin 7} (b : E 2) : C.lo (C.c v) b ≤ ⟪b, C.k v⟫ :=
  Finset.inf'_le (fun v => ⟪b, C.k v⟫) (by simp [cls])

lemma exists_hi (j : Fin 3) (b : E 2) : ∃ v, C.c v = j ∧ ⟪b, C.k v⟫ = C.hi j b := by
  obtain ⟨v, hv, h⟩ := Finset.exists_mem_eq_sup' (C.cls_nonempty j) fun v => ⟪b, C.k v⟫
  exact ⟨v, by simpa [cls] using hv, h.symm⟩

lemma exists_lo (j : Fin 3) (b : E 2) : ∃ v, C.c v = j ∧ ⟪b, C.k v⟫ = C.lo j b := by
  obtain ⟨v, hv, h⟩ := Finset.exists_mem_eq_inf' (C.cls_nonempty j) fun v => ⟪b, C.k v⟫
  exact ⟨v, by simpa [cls] using hv, h.symm⟩

/-- Width of the fibre `j` in direction `b`. -/
noncomputable def wd (j : Fin 3) (b : E 2) : ℝ := C.hi j b - C.lo j b

lemma wd_nonneg (j : Fin 3) (b : E 2) : 0 ≤ C.wd j b := by
  obtain ⟨v, hv, -⟩ := C.exists_hi j b
  have h1 := C.le_hi (v := v) b
  have h2 := C.lo_le (v := v) b
  rw [hv] at h1 h2
  simp only [wd]; linarith

/-- The octahedral pattern of `S` in direction `b`. -/
noncomputable def octPat (S : Fin 3 → Option Bool) (b : E 2) (v : Fin 7) : ℤ :=
  if S (C.c v) = some true ∧ ⟪b, C.k v⟫ = C.hi (C.c v) b then 1
  else if S (C.c v) = some false ∧ ⟪b, C.k v⟫ = C.lo (C.c v) b then -1 else 0

/-- The coefficient realizing the octahedral pattern. -/
noncomputable def octA (S : Fin 3 → Option Bool) (b : E 2) (M : ℝ) (j : Fin 3) : ℝ :=
  match S j with
  | some true => M - C.hi j b
  | some false => -M - C.lo j b
  | none => -(C.hi j b + C.lo j b) / 2

lemma sgnOf_div {t M : ℝ} (hM : 0 < M) (h1 : t ≤ M) (h2 : -M ≤ t) :
    FullPrism.sgnOf (t / M) = if t = M then 1 else if t = -M then -1 else 0 := by
  unfold FullPrism.sgnOf
  have hM' : M ≠ 0 := hM.ne'
  by_cases ht : t = M
  · subst ht; simp [div_self hM']
  · by_cases ht' : t = -M
    · subst ht'; simp [neg_div, div_self hM', ht]; norm_num
    · have e1 : t / M ≠ 1 := fun h => ht (by field_simp at h; linarith)
      have e2 : t / M ≠ -1 := fun h => ht' (by field_simp at h; linarith)
      simp [e1, e2, ht, ht']

/-- **Octahedral patterns are realizable.** -/
theorem octPat_realizable (S : Fin 3 → Option Bool) (b : E 2) :
    LemmaB.Realizable7 x (C.octPat S b) := by
  set M := 1 + ∑ j, C.wd j b with hMdef
  have hwM : ∀ j, C.wd j b < M := by
    intro j
    have : C.wd j b ≤ ∑ j, C.wd j b :=
      Finset.single_le_sum (fun j _ => C.wd_nonneg j b) (Finset.mem_univ j)
    rw [hMdef]; linarith
  have hM : 0 < M := by have := hwM 0; have := C.wd_nonneg 0 b; linarith
  obtain ⟨z, hz⟩ := C.real (fun j => C.octA S b M j / M) (M⁻¹ • b)
  have hval : ∀ v, ⟪z, x v⟫ = (C.octA S b M (C.c v) + ⟪b, C.k v⟫) / M := by
    intro v; rw [hz, real_inner_smul_left]; field_simp
  refine ⟨z, fun v => (C.octA S b M (C.c v) + ⟪b, C.k v⟫) / M, hval, fun v => ?_, ?_⟩
  · have h1 := C.le_hi (v := v) b
    have h2 := C.lo_le (v := v) b
    have hw := hwM (C.c v)
    simp only [wd] at hw
    rw [abs_div, abs_of_pos hM, div_le_one hM, abs_le]
    unfold octA
    split <;> constructor <;> linarith
  · funext v
    have h1 := C.le_hi (v := v) b
    have h2 := C.lo_le (v := v) b
    have hw := hwM (C.c v)
    simp only [wd] at hw
    show C.octPat S b v = FullPrism.sgnOf ((C.octA S b M (C.c v) + ⟪b, C.k v⟫) / M)
    unfold octPat octA
    rcases hS : S (C.c v) with _ | _ | _
    · simp only [hS, reduceCtorEq, false_and, if_false]
      rw [sgnOf_div hM (by linarith) (by linarith)]
      have e1 : -(C.hi (C.c v) b + C.lo (C.c v) b) / 2 + ⟪b, C.k v⟫ ≠ M := fun h' => by linarith
      have e2 : -(C.hi (C.c v) b + C.lo (C.c v) b) / 2 + ⟪b, C.k v⟫ ≠ -M := fun h' => by linarith
      rw [if_neg e1, if_neg e2]
    · simp only [hS, reduceCtorEq, false_and, if_false, Option.some.injEq, Bool.false_eq_true,
        true_and]
      rw [sgnOf_div hM (by linarith) (by linarith)]
      have e1 : -M - C.lo (C.c v) b + ⟪b, C.k v⟫ ≠ M := fun h' => by linarith
      rw [if_neg e1]
      by_cases he : ⟪b, C.k v⟫ = C.lo (C.c v) b
      · rw [if_pos he, if_pos (by linarith)]
      · rw [if_neg he, if_neg (fun h' => he (by linarith))]
    · simp only [hS, Option.some.injEq, true_and, Bool.true_eq_false, false_and, if_false]
      rw [sgnOf_div hM (by linarith) (by linarith)]
      by_cases he : ⟪b, C.k v⟫ = C.hi (C.c v) b
      · rw [if_pos he, if_pos (by linarith)]
      · have e2 : M - C.hi (C.c v) b + ⟪b, C.k v⟫ ≠ -M := fun h' => by linarith
        rw [if_neg he, if_neg (fun h' => he (by linarith)), if_neg e2]

/-- Maximal width in direction `b`. -/
noncomputable def wmax (b : E 2) : ℝ := Finset.univ.sup' Finset.univ_nonempty fun j => C.wd j b

lemma wd_le_wmax (j : Fin 3) (b : E 2) : C.wd j b ≤ C.wmax b :=
  Finset.le_sup' (fun j => C.wd j b) (Finset.mem_univ j)

/-- Equatorial labels: `none` (unused), `some (some σ)` (sign `σ`), `some none` (both signs). -/
abbrev ELab := Option (Option Bool)

/-- The equatorial pattern of `S` in direction `b`. -/
noncomputable def equPat (S : Fin 3 → ELab) (b : E 2) (v : Fin 7) : ℤ :=
  if (S (C.c v) = some (some true) ∨ S (C.c v) = some none) ∧ ⟪b, C.k v⟫ = C.hi (C.c v) b then 1
  else if (S (C.c v) = some (some false) ∨ S (C.c v) = some none) ∧
    ⟪b, C.k v⟫ = C.lo (C.c v) b then -1 else 0

/-- The coefficient realizing the equatorial pattern. -/
noncomputable def equA (S : Fin 3 → ELab) (b : E 2) (M : ℝ) (j : Fin 3) : ℝ :=
  match S j with
  | some (some true) => M - C.hi j b
  | some (some false) => -M - C.lo j b
  | some none => M - C.hi j b
  | none => -(C.hi j b + C.lo j b) / 2

/-- **Equatorial patterns are realizable** when the classes with both signs are exactly the
widest ones (in a direction with positive width). -/
theorem equPat_realizable (S : Fin 3 → ELab) (b : E 2) (hpos : 0 < C.wmax b)
    (hJ : ∀ j, S j = some none ↔ C.wd j b = C.wmax b) :
    LemmaB.Realizable7 x (C.equPat S b) := by
  set M := C.wmax b / 2 with hMdef
  have hM : 0 < M := by rw [hMdef]; linarith
  have hwle : ∀ j, C.wd j b ≤ 2 * M := fun j => by rw [hMdef]; linarith [C.wd_le_wmax j b]
  have hwlt : ∀ j, S j ≠ some none → C.wd j b < 2 * M := by
    intro j hj
    have := C.wd_le_wmax j b
    have hne : C.wd j b ≠ C.wmax b := fun h => hj ((hJ j).2 h)
    rw [hMdef]; exact lt_of_le_of_ne (by linarith) (by intro h; apply hne; linarith)
  have hweq : ∀ j, S j = some none → C.wd j b = 2 * M := fun j hj => by
    rw [hMdef, (hJ j).1 hj]; ring
  obtain ⟨z, hz⟩ := C.real (fun j => C.equA S b M j / M) (M⁻¹ • b)
  have hval : ∀ v, ⟪z, x v⟫ = (C.equA S b M (C.c v) + ⟪b, C.k v⟫) / M := by
    intro v; rw [hz, real_inner_smul_left]; field_simp
  have hbounds : ∀ v, C.equA S b M (C.c v) + ⟪b, C.k v⟫ ≤ M ∧
      -M ≤ C.equA S b M (C.c v) + ⟪b, C.k v⟫ := by
    intro v
    have h1 := C.le_hi (v := v) b
    have h2 := C.lo_le (v := v) b
    have hw := hwle (C.c v)
    simp only [wd] at hw
    unfold equA
    split <;> constructor <;> linarith
  refine ⟨z, fun v => (C.equA S b M (C.c v) + ⟪b, C.k v⟫) / M, hval, fun v => ?_, ?_⟩
  · rw [abs_div, abs_of_pos hM, div_le_one hM, abs_le]
    exact ⟨(hbounds v).2, (hbounds v).1⟩
  · funext v
    have h1 := C.le_hi (v := v) b
    have h2 := C.lo_le (v := v) b
    show C.equPat S b v = FullPrism.sgnOf ((C.equA S b M (C.c v) + ⟪b, C.k v⟫) / M)
    rw [sgnOf_div hM (hbounds v).1 (hbounds v).2]
    unfold equPat equA
    rcases hS : S (C.c v) with _ | (_ | (_ | _))
    · -- unused class
      have hw := hwlt (C.c v) (by rw [hS]; simp)
      simp only [wd] at hw
      simp only [hS, reduceCtorEq, false_or, false_and, if_false]
      have e1 : -(C.hi (C.c v) b + C.lo (C.c v) b) / 2 + ⟪b, C.k v⟫ ≠ M := fun h' => by linarith
      have e2 : -(C.hi (C.c v) b + C.lo (C.c v) b) / 2 + ⟪b, C.k v⟫ ≠ -M := fun h' => by linarith
      rw [if_neg e1, if_neg e2]
    · -- both signs
      have hw := hweq (C.c v) hS
      simp only [wd] at hw
      simp only [hS, reduceCtorEq, or_true, true_and]
      by_cases he : ⟪b, C.k v⟫ = C.hi (C.c v) b
      · rw [if_pos he, if_pos (show M - C.hi (C.c v) b + ⟪b, C.k v⟫ = M by linarith)]
      · have e1 : M - C.hi (C.c v) b + ⟪b, C.k v⟫ ≠ M := fun h' => he (by linarith)
        rw [if_neg he, if_neg e1]
        by_cases he' : ⟪b, C.k v⟫ = C.lo (C.c v) b
        · rw [if_pos he', if_pos (show M - C.hi (C.c v) b + ⟪b, C.k v⟫ = -M by linarith)]
        · have e2 : M - C.hi (C.c v) b + ⟪b, C.k v⟫ ≠ -M := fun h' => he' (by linarith)
          rw [if_neg he', if_neg e2]
    · -- sign `-`
      have hw := hwlt (C.c v) (by rw [hS]; simp)
      simp only [wd] at hw
      simp only [hS, reduceCtorEq, Option.some.injEq, Bool.false_eq_true, false_or, or_false,
        false_and, if_false, true_and]
      have e1 : -M - C.lo (C.c v) b + ⟪b, C.k v⟫ ≠ M := fun h' => by linarith
      rw [if_neg e1]
      by_cases he : ⟪b, C.k v⟫ = C.lo (C.c v) b
      · rw [if_pos he, if_pos (show -M - C.lo (C.c v) b + ⟪b, C.k v⟫ = -M by linarith)]
      · have e2 : -M - C.lo (C.c v) b + ⟪b, C.k v⟫ ≠ -M := fun h' => he (by linarith)
        rw [if_neg he, if_neg e2]
    · -- sign `+`
      have hw := hwlt (C.c v) (by rw [hS]; simp)
      simp only [wd] at hw
      simp only [hS, reduceCtorEq, Option.some.injEq, Bool.true_eq_false, false_or, or_false,
        true_and, false_and, if_false]
      by_cases he : ⟪b, C.k v⟫ = C.hi (C.c v) b
      · rw [if_pos he, if_pos (show M - C.hi (C.c v) b + ⟪b, C.k v⟫ = M by linarith)]
      · have e1 : M - C.hi (C.c v) b + ⟪b, C.k v⟫ ≠ M := fun h' => he (by linarith)
        have e2 : M - C.hi (C.c v) b + ⟪b, C.k v⟫ ≠ -M := fun h' => by linarith
        rw [if_neg he, if_neg e1, if_neg e2]

end Config

end Kalai5.LemmaB
