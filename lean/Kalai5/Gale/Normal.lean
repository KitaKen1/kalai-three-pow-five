import Kalai5.Gale.Rank
import Kalai5.Gale.Faces

/-!
# Normal form of a planar Gale diagram

* A shear `(x₀, x₁) ↦ (x₀ + t x₁, x₁)` makes every nonzero vector have nonzero first coordinate
  and keeps the Gale property (`exists_normal`).
* Sign codes by slope rank (`codeOf`) then satisfy `CodeFor` (`codeFor_codeOf`).
* Gale diagrams and codes are compatible with relabelling the points (`IsGale.perm`,
  `CodeFor.perm`).
-/

namespace Kalai5.Gale

open Module

variable {k n : ℕ}

/-- The shear `(x₀, x₁) ↦ (x₀ + t x₁, x₁)`. -/
noncomputable def shear (t : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearMap.pi fun i : Fin 2 => if i = 0 then LinearMap.proj 0 + t • LinearMap.proj 1
    else LinearMap.proj i

lemma shear_apply_zero (t : ℝ) (x : Fin 2 → ℝ) : shear t x 0 = x 0 + t * x 1 := by
  simp [shear]

lemma shear_apply_one (t : ℝ) (x : Fin 2 → ℝ) : shear t x 1 = x 1 := by
  simp [shear]

lemma shear_injective (t : ℝ) : Function.Injective (shear t) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  rw [shear_apply_zero, shear_apply_zero] at h0
  rw [shear_apply_one, shear_apply_one] at h1
  funext i; fin_cases i
  · simp only [Fin.zero_eta]; rw [h1] at h0; linarith
  · exact h1

lemma IsGale.comp {W : Fin n → E k} {g : Fin n → Fin 2 → ℝ} (hg : IsGale W g)
    (L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (hL : Function.Injective L) :
    IsGale W (fun j => L (g j)) := by
  unfold IsGale at *
  ext a
  rw [LinearMap.mem_ker, ← hg, LinearMap.mem_ker, galeMap_apply, galeMap_apply]
  have : ∑ j, a j • L (g j) = L (∑ j, a j • g j) := by simp [map_sum, map_smul]
  rw [this]
  exact ⟨fun h => hL (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

/-- Some shear makes all nonzero first coordinates nonzero. -/
lemma exists_shear (g : Fin n → Fin 2 → ℝ) : ∃ t : ℝ, ∀ j, g j ≠ 0 → g j 0 + t * g j 1 ≠ 0 := by
  classical
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
    ((Finset.univ.filter fun j => g j 1 ≠ 0).image fun j => -g j 0 / g j 1)
  refine ⟨t, fun j hj => ?_⟩
  by_cases h1 : g j 1 = 0
  · have : g j 0 ≠ 0 := by
      intro h0; apply hj; funext i; fin_cases i
      · exact h0
      · exact h1
    simpa [h1] using this
  · intro h
    apply ht
    refine Finset.mem_image.2 ⟨j, by simp [h1], ?_⟩
    field_simp
    linarith

/-- **Normal form**: a Gale diagram whose nonzero vectors have nonzero first coordinate. -/
theorem exists_normal {W : Fin n → E k} {g : Fin n → Fin 2 → ℝ} (hg : IsGale W g) :
    ∃ g' : Fin n → Fin 2 → ℝ, IsGale W g' ∧ ∀ j, g' j ≠ 0 → g' j 0 ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_shear g
  refine ⟨fun j => shear t (g j), hg.comp _ (shear_injective t), fun j hj => ?_⟩
  change shear t (g j) ≠ 0 at hj
  show shear t (g j) 0 ≠ 0
  rw [shear_apply_zero]
  apply ht
  intro h0; apply hj; rw [h0, map_zero]

/-! ### Codes by slope rank -/

open Classical in
/-- The slopes of the nonzero vectors. -/
noncomputable def slopes (g : Fin n → Fin 2 → ℝ) : Finset ℝ :=
  (Finset.univ.filter fun j => g j ≠ 0).image fun j => slope (g j)

open Classical in
/-- Rank of the slope of `g j` among all slopes. -/
noncomputable def lineIdx (g : Fin n → Fin 2 → ℝ) (j : Fin n) : ℕ :=
  ((slopes g).filter fun s => s < slope (g j)).card

open Classical in
/-- Sign code of `g j`. -/
noncomputable def codeOf (g : Fin n → Fin 2 → ℝ) (j : Fin n) : ℕ :=
  if g j = 0 then 0 else if 0 < g j 0 then 2 * lineIdx g j + 1 else 2 * lineIdx g j + 2

lemma slope_mem_slopes {g : Fin n → Fin 2 → ℝ} {j : Fin n} (hj : g j ≠ 0) :
    slope (g j) ∈ slopes g := by
  classical
  exact Finset.mem_image.2 ⟨j, by simp [hj], rfl⟩

lemma lineIdx_lt_lineIdx_iff {g : Fin n → Fin 2 → ℝ} {i j : Fin n} (hi : g i ≠ 0) :
    lineIdx g i < lineIdx g j ↔ slope (g i) < slope (g j) := by
  classical
  unfold lineIdx
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    have : ((slopes g).filter fun s => s < slope (g j)) ⊆
        ((slopes g).filter fun s => s < slope (g i)) := by
      intro s hs
      simp only [Finset.mem_filter] at hs ⊢
      exact ⟨hs.1, lt_of_lt_of_le hs.2 hle⟩
    have := Finset.card_le_card this
    omega
  · intro h
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨slope (g i), ?_, ?_⟩
      · simp [slope_mem_slopes hi, h]
      · simp
    · intro s hs
      simp only [Finset.mem_filter] at hs ⊢
      exact ⟨hs.1, hs.2.trans h⟩

lemma lineIdx_lt_card {g : Fin n → Fin 2 → ℝ} {j : Fin n} (hj : g j ≠ 0) :
    lineIdx g j < (slopes g).card := by
  classical
  unfold lineIdx
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨slope (g j), slope_mem_slopes hj, by simp⟩

lemma cline_codeOf {g : Fin n → Fin 2 → ℝ} {j : Fin n} (hj : g j ≠ 0) :
    cline (codeOf g j) = lineIdx g j := by
  unfold codeOf cline
  rw [if_neg hj]
  split <;> omega

/-- **The slope-rank codes describe a normal Gale diagram.** -/
theorem codeFor_codeOf {g : Fin n → Fin 2 → ℝ} (hg : ∀ j, g j ≠ 0 → g j 0 ≠ 0) :
    CodeFor g (codeOf g) (slopes g).card := by
  classical
  have hne : ∀ j, codeOf g j ≠ 0 → g j ≠ 0 := fun j h h0 => h (by simp [codeOf, h0])
  refine ⟨fun j => ?_, fun j h => hg j (hne j h), fun j h => ?_, fun i j hi hj => ?_,
    fun j h => ?_, fun i hi => ?_⟩
  · constructor
    · intro h; by_contra h0; unfold codeOf at h; rw [if_neg h0] at h; split at h <;> omega
    · intro h0; simp [codeOf, h0]
  · have h0 := hne j h
    unfold codeOf cpos
    rw [if_neg h0]
    by_cases hp : 0 < g j 0
    · rw [if_pos hp]; simp [hp]
    · rw [if_neg hp]; simp [hp]
  · rw [cline_codeOf (hne i hi), cline_codeOf (hne j hj)]
    exact lineIdx_lt_lineIdx_iff (hne i hi)
  · rw [cline_codeOf (hne j h)]; exact lineIdx_lt_card (hne j h)
  · -- surjectivity of the slope rank
    have hsurj := Finset.surj_on_of_inj_on_of_card_le
      (s := slopes g) (t := Finset.range (slopes g).card)
      (fun s _ => ((slopes g).filter fun x => x < s).card)
      (fun s hs => by
        rw [Finset.mem_range]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
        exact ⟨s, hs, by simp⟩)
      (fun s1 s2 hs1 hs2 h => by
        by_contra hne'
        rcases lt_or_gt_of_ne hne' with hlt | hlt
        · have : ((slopes g).filter fun x => x < s1).card < ((slopes g).filter fun x => x < s2).card := by
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_of_subset]
            · exact ⟨s1, by simp [hs1, hlt], by simp⟩
            · intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans hlt⟩
          omega
        · have : ((slopes g).filter fun x => x < s2).card < ((slopes g).filter fun x => x < s1).card := by
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_of_subset]
            · exact ⟨s2, by simp [hs2, hlt], by simp⟩
            · intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans hlt⟩
          omega)
      (by simp)
    obtain ⟨s, hs, hi'⟩ := hsurj i (Finset.mem_range.2 hi)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨j, fun h => hj ((codeFor_zero_iff hg j).1 h), ?_⟩
    rw [cline_codeOf hj]
    exact hi'.symm
where
  codeFor_zero_iff (hg : ∀ j, g j ≠ 0 → g j 0 ≠ 0) (j : Fin n) : codeOf g j = 0 ↔ g j = 0 := by
    classical
    constructor
    · intro h; by_contra h0; unfold codeOf at h; rw [if_neg h0] at h; split at h <;> omega
    · intro h0; simp [codeOf, h0]

/-! ### Relabelling -/

lemma IsGale.perm {W : Fin n → E k} {g : Fin n → Fin 2 → ℝ} (hg : IsGale W g)
    (σ : Equiv.Perm (Fin n)) : IsGale (W ∘ σ) (g ∘ σ) := by
  have key := hg.mem_iff
  show LinearMap.ker (galeMap (g ∘ σ)) = affVals (W ∘ σ)
  ext a
  rw [LinearMap.mem_ker, galeMap_apply]
  have hsum : ∑ j, a j • (g ∘ σ) j = ∑ i, a (σ.symm i) • g i := by
    rw [← Equiv.sum_comp σ (fun i => a (σ.symm i) • g i)]; simp
  rw [hsum, ← key (fun i => a (σ.symm i))]
  constructor
  · rintro ⟨uc, huc⟩
    refine ⟨uc, ?_⟩
    funext j
    have := congrFun huc (σ j)
    simpa using this
  · rintro ⟨uc, huc⟩
    refine ⟨uc, ?_⟩
    funext i
    have := congrFun huc (σ.symm i)
    simpa using this

lemma CodeFor.perm {g : Fin n → Fin 2 → ℝ} {c : Fin n → ℕ} {m : ℕ} (hc : CodeFor g c m)
    (σ : Equiv.Perm (Fin n)) : CodeFor (g ∘ σ) (c ∘ σ) m :=
  ⟨fun j => hc.zero_iff (σ j), fun j => hc.fst_ne (σ j), fun j => hc.pos_iff (σ j),
    fun i j => hc.lt_iff (σ i) (σ j), fun j => hc.line_lt (σ j),
    fun i hi => by
      obtain ⟨j, hj, hl⟩ := hc.used i hi
      exact ⟨σ.symm j, by simpa using hj, by simpa using hl⟩⟩

/-- The total rank of the codes is `min m 2`. -/
lemma CodeFor.crank_univ {g : Fin n → Fin 2 → ℝ} {c : Fin n → ℕ} {m : ℕ} (hc : CodeFor g c m) :
    crank c Finset.univ = min m 2 := by
  classical
  unfold crank
  rcases Nat.lt_or_ge m 1 with hm | hm
  · have hm0 : m = 0 := by omega
    have h0 : ∀ j ∈ (Finset.univ : Finset (Fin n)), c j = 0 := by
      intro j _; by_contra h; have := hc.line_lt j h; omega
    rw [if_pos h0, hm0]; rfl
  · obtain ⟨j0, hj0, hl0⟩ := hc.used 0 hm
    have h0 : ¬ ∀ j ∈ (Finset.univ : Finset (Fin n)), c j = 0 := fun h => hj0 (h j0 (by simp))
    rw [if_neg h0]
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have h1 : ∃ i, ∀ j ∈ (Finset.univ : Finset (Fin n)), c j ≠ 0 → cline (c j) = i :=
        ⟨0, fun j _ hj => by have := hc.line_lt j hj; omega⟩
      rw [if_pos h1]; omega
    · obtain ⟨j1, hj1, hl1⟩ := hc.used 1 (by omega)
      have h1 : ¬ ∃ i, ∀ j ∈ (Finset.univ : Finset (Fin n)), c j ≠ 0 → cline (c j) = i := by
        rintro ⟨i, hi⟩
        have a := hi j0 (by simp) hj0
        have b := hi j1 (by simp) hj1
        omega
      rw [if_neg h1]; omega

end Kalai5.Gale
