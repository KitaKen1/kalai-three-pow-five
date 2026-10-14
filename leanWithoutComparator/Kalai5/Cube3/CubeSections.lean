import Kalai5.Cube3.FibreLift

/-!
# Explicit vertices in sections of a cube

Two saturated coordinates and the sum constraint force a section vertex.
Three cyclic witnesses suffice at every height strictly between -3 and 3,
including the degenerate transition heights -1 and 1.
-/

namespace Kalai5.Cube3

open Set

def cubeSection (m : ℕ) (s : ℝ) : Set (E m) :=
  {p | (∀ i, |p i| ≤ 1) ∧ ∑ i, p i = s}

lemma endpoint_combination {a b p t u : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (ht : 0 < t) (hu : 0 < u) (htu : t + u = 1)
    (he : t * a + u * b = p) (hp : p = 1 ∨ p = -1) : a = p ∧ b = p := by
  rcases abs_le.1 ha with ⟨ha0, ha1⟩
  rcases abs_le.1 hb with ⟨hb0, hb1⟩
  rcases hp with rfl | rfl
  · have hta := mul_nonneg ht.le (sub_nonneg.2 ha1)
    have hub := mul_nonneg hu.le (sub_nonneg.2 hb1)
    have h0 : t * (1 - a) = 0 := by nlinarith
    have h1 : u * (1 - b) = 0 := by nlinarith
    have h0' := (mul_eq_zero.1 h0).resolve_left ht.ne'
    have h1' := (mul_eq_zero.1 h1).resolve_left hu.ne'
    constructor <;> linarith
  · have hta := mul_nonneg ht.le (by linarith : 0 ≤ a + 1)
    have hub := mul_nonneg hu.le (by linarith : 0 ≤ b + 1)
    have h0 : t * (a + 1) = 0 := by nlinarith
    have h1 : u * (b + 1) = 0 := by nlinarith
    have h0' := (mul_eq_zero.1 h0).resolve_left ht.ne'
    have h1' := (mul_eq_zero.1 h1).resolve_left hu.ne'
    constructor <;> linarith

/-- All but one coordinate are fixed by box endpoints; the sum fixes the last. -/
theorem extreme_cubeSection {m : ℕ} {s : ℝ} {p : E m}
    (hp : p ∈ cubeSection m s) (j : Fin m)
    (htight : ∀ i, i ≠ j → p i = 1 ∨ p i = -1) :
    p ∈ (cubeSection m s).extremePoints ℝ := by
  classical
  refine mem_extremePoints.2 ⟨hp, ?_⟩
  intro a ha b hb hseg
  obtain ⟨t, u, ht, hu, htu, he⟩ := hseg
  have hfixed : ∀ i, i ≠ j → a i = p i ∧ b i = p i := by
    intro i hij
    apply endpoint_combination (ha.1 i) (hb.1 i) ht hu htu _ (htight i hij)
    have hi := congrArg (fun q : E m => q i) he
    simpa using hi
  have key : ∀ q : E m, (∑ i, q i = s) → (∀ i, i ≠ j → q i = p i) → q = p := by
    intro q hq hfix
    have hsum : ∑ i, (q i - p i) = 0 := by
      rw [Finset.sum_sub_distrib, hq, hp.2, sub_self]
    have heq : ∑ i, (q i - p i) = q j - p j := by
      apply Finset.sum_eq_single j
      · intro i _ hij; rw [hfix i hij, sub_self]
      · simp
    rw [heq] at hsum
    ext i
    by_cases hij : i = j
    · subst i; exact sub_eq_zero.1 hsum
    · exact hfix i hij
  exact ⟨key a ha.2 (fun i hi => (hfixed i hi).1),
    key b hb.2 (fun i hi => (hfixed i hi).2)⟩

noncomputable def cycle3 (a b c : ℝ) (i : Fin 3) : E 3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (![![a,b,c], ![c,a,b], ![b,c,a]] i)

lemma cycle3_extreme (a b c s : ℝ) (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) (hc : |c| ≤ 1) (hs : a + b + c = s) (i : Fin 3) :
    cycle3 a b c i ∈ (cubeSection 3 s).extremePoints ℝ := by
  have haa : |a| ≤ 1 := by rcases ha with rfl | rfl <;> norm_num
  have hbb : |b| ≤ 1 := by rcases hb with rfl | rfl <;> norm_num
  have hmem : cycle3 a b c i ∈ cubeSection 3 s := by
    constructor
    · intro j; fin_cases i <;> fin_cases j <;> simp_all [cycle3]
    · fin_cases i <;> simp [cycle3, Fin.sum_univ_three] <;> linarith
  fin_cases i
  · apply extreme_cubeSection hmem 2
    intro j hj; fin_cases j <;> simp_all [cycle3]
  · apply extreme_cubeSection hmem 0
    intro j hj; fin_cases j <;> simp_all [cycle3]
  · apply extreme_cubeSection hmem 1
    intro j hj; fin_cases j <;> simp_all [cycle3]

lemma cycle3_injective {a b c : ℝ} (h : a ≠ b ∨ b ≠ c) :
    Function.Injective (cycle3 a b c) := by
  intro i j he
  have h0 := congrArg (fun q : E 3 => q 0) he
  have h1 := congrArg (fun q : E 3 => q 1) he
  have h2 := congrArg (fun q : E 3 => q 2) he
  fin_cases i <;> fin_cases j <;> simp [cycle3] at h0 h1 h2 ⊢ <;> aesop

/-- A constructive lower bound valid also at the transition heights ±1. -/
theorem cubeSection_three_vertices {s : ℝ} (hs : |s| < 3) :
    ∃ f : Fin 3 → E 3, Function.Injective f ∧
      ∀ i, f i ∈ (cubeSection 3 s).extremePoints ℝ := by
  have hsl := (abs_lt.1 hs).1
  have hsu := (abs_lt.1 hs).2
  by_cases hl : s < -1
  · refine ⟨cycle3 (-1) (-1) (s + 2), cycle3_injective (Or.inr (by linarith)), ?_⟩
    intro i
    apply cycle3_extreme (-1) (-1) (s + 2) s (Or.inr rfl) (Or.inr rfl)
    · exact abs_le.2 ⟨by linarith, by linarith⟩
    · ring
  · by_cases hu : s ≤ 1
    · refine ⟨cycle3 1 (-1) s, cycle3_injective (Or.inl (by norm_num)), ?_⟩
      intro i
      apply cycle3_extreme 1 (-1) s s (Or.inl rfl) (Or.inr rfl)
      · exact abs_le.2 ⟨by linarith, hu⟩
      · ring
    · refine ⟨cycle3 1 1 (s - 2), cycle3_injective (Or.inr (by linarith)), ?_⟩
      intro i
      apply cycle3_extreme 1 1 (s - 2) s (Or.inl rfl) (Or.inl rfl)
      · exact abs_le.2 ⟨by linarith, by linarith⟩
      · ring

end Kalai5.Cube3
