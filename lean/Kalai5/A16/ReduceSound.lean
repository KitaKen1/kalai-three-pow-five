import Kalai5.A16.Reduce
import Kalai5.A16.Walk
import Kalai5.A16.Transfer
import Kalai5.LemmaA.ReduceSound
import Kalai5.FullPrism.Assemble

/-!
# A16: soundness of the reduction table

`core16`: eight points `y_v ∈ ℝ⁵` whose first four coordinates are `±1`, such that the sixteen points
`±y_v` are distinct, no three of them agree in the first four coordinates, and they span `ℝ⁵`: either
at least `N` polar points of `{±y_v}` have spanning tight sets, or there is a fifth full normal
(`±1` at every point, nonzero last coordinate), or there are `242` distinct nonempty tight sets —
provided the table and the families pass their kernel checks (`checkN N`).  As for Lemma A (`Kalai5.LemmaA.core`): normalize, sort the classes, look up the table
entry, and map the points onto the family's points by `phi` (the shear zeroes the base heights; the
free heights are the parameter `a`).
-/

namespace Kalai5.A16

open Set Module Kalai5.LemmaA Kalai5.FullPrism

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The conclusion of A16 for a set of points: `N` polar points with spanning tight sets, a fifth
full normal, or `242` tight sets. -/
def GoalN (N : ℕ) (X : Set E5) : Prop :=
  (∃ S : Finset E5, N ≤ S.card ∧ ∀ y ∈ S, IsPVs X y) ∨
    (∃ y : E5, (∀ x ∈ X, ⟪x, y⟫ = 1 ∨ ⟪x, y⟫ = -1) ∧ y 4 ≠ 0) ∨ CountGoal X

/-! ### Sorted class sequences -/

lemma mem_allSeqs8 {c : Fin 8 → ℕ} (hmono : Monotone c) (h8 : ∀ i, c i < 8)
    (hnt : ∀ (i : ℕ) (h : i + 2 < 8), c ⟨i, by omega⟩ ≠ c ⟨i + 2, h⟩) :
    List.ofFn c ∈ allSeqs8 := by
  unfold allSeqs8
  rw [List.mem_filter]
  refine ⟨mem_monoSeqs 8 0 _ (by simp) ?_ ?_, noTriple_of _ ?_⟩
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact hmono hij.le
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact ⟨Nat.zero_le _, h8 i⟩
  · intro i hi
    simp only [List.length_ofFn] at hi
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact hnt i hi

/-! ### Signed points -/

lemma pm16_inj_iff {y : Fin 8 → E5} :
    Function.Injective (pm16 y) ↔ Function.Injective y ∧ ∀ u v, y u ≠ -y v := by
  constructor
  · intro h
    refine ⟨fun u v huv => ?_, fun u v huv => ?_⟩
    · have := h (show pm16 y ⟨u, by omega⟩ = pm16 y ⟨v, by omega⟩ by rw [pm16_lo, pm16_lo, huv])
      exact Fin.ext (by simpa using this)
    · have := h (show pm16 y ⟨u, by omega⟩ = pm16 y ⟨v + 8, by omega⟩ by
        rw [pm16_lo, pm16_hi, huv])
      simp [Fin.ext_iff] at this
      omega
  · rintro ⟨hy, hneg⟩ i j hij
    unfold pm16 at hij
    split_ifs at hij with hi hj hj
    · exact Fin.ext (by simpa using hy hij)
    · exact absurd hij (hneg _ _)
    · exact absurd hij.symm (hneg _ _)
    · have := hy (neg_injective hij)
      simp [Fin.ext_iff] at this
      exact Fin.ext (by omega)

lemma range_pm16_signed {y : Fin 8 → E5} (t : Fin 8 → ℝ) (ht : ∀ v, t v = 1 ∨ t v = -1)
    (ρ : Equiv.Perm (Fin 8)) : range (pm16 fun v => t v • y (ρ v)) = range (pm16 y) := by
  ext x
  simp only [mem_range_pm16]
  constructor
  · rintro ⟨v, hx⟩
    refine ⟨ρ v, ?_⟩
    rcases ht v with h | h <;> rcases hx with hx | hx <;> simp [hx, h]
  · rintro ⟨u, hx⟩
    refine ⟨ρ.symm u, ?_⟩
    rcases ht (ρ.symm u) with h | h <;> rcases hx with hx | hx <;> simp [hx, h]

lemma pm16_signed_injective {y : Fin 8 → E5} (hy : Function.Injective (pm16 y)) (t : Fin 8 → ℝ)
    (ht : ∀ v, t v = 1 ∨ t v = -1) (ρ : Equiv.Perm (Fin 8)) :
    Function.Injective (pm16 fun v => t v • y (ρ v)) := by
  rw [pm16_inj_iff] at hy ⊢
  obtain ⟨hy, hneg⟩ := hy
  refine ⟨fun u v huv => ?_, fun u v huv => ?_⟩
  · rcases ht u with hu | hu <;> rcases ht v with hv | hv <;> simp only [hu, hv, one_smul,
      neg_smul] at huv
    · exact ρ.injective (hy huv)
    · exact absurd huv (hneg _ _)
    · exact absurd huv.symm (hneg _ _)
    · exact ρ.injective (hy (neg_injective huv))
  · rcases ht u with hu | hu <;> rcases ht v with hv | hv <;> simp only [hu, hv, one_smul,
      neg_smul, neg_neg, neg_inj] at huv
    · exact hneg _ _ huv
    · have := ρ.injective (hy huv); subst this; rw [hu] at hv; norm_num at hv
    · have := ρ.injective (hy huv); subst this; rw [hu] at hv; norm_num at hv
    · exact hneg _ _ huv.symm

/-! ### The points of a family -/

namespace Family

variable (F : Family)

lemma pt_ext {a : Fin 4 → ℝ} {w : Fin 16} {x : E5}
    (h : ∀ j : Fin 4, x j.castSucc = ((F.q w).getD j 0 : ℝ)) (h4 : x 4 = (F.z w).ev a) :
    F.pt a w = x := by
  ext k
  fin_cases k
  · exact (h 0).symm
  · exact (h 1).symm
  · exact (h 2).symm
  · exact (h 3).symm
  · exact h4.symm

end Family

lemma Z4.unit_ev (a : Fin 4 → ℝ) {k : ℕ} (hk : k < 4) : (Z4.unit k).ev a = a ⟨k, hk⟩ := by
  interval_cases k <;> simp [Z4.unit, Z4.ev] <;> rfl

/-- Point `k` of `z`, or `0`. -/
noncomputable def zz8 (z : Fin 8 → E5) (k : ℕ) : E5 := if h : k < 8 then z ⟨k, h⟩ else 0

lemma zz8_of_lt (z : Fin 8 → E5) {k : ℕ} (h : k < 8) : zz8 z k = z ⟨k, h⟩ := by simp [zz8, h]

/-- The image of the last unit vector under `phi`. -/
lemma phi_e4 (A : List (List ℤ)) (d : ℤ) (μ : Fin 4 → ℝ) :
    phi A d μ (EuclideanSpace.single 4 1) = EuclideanSpace.single 4 1 := by
  have hne : ∀ x : Fin 4, (x.castSucc : Fin 5) ≠ 4 := by decide
  have huq : ∀ i, uq A d (EuclideanSpace.single 4 1) i = 0 := by
    intro i; simp [uq, EuclideanSpace.single_apply, hne]
  ext k
  fin_cases k
  · show phi A d μ _ (Fin.castSucc 0) = _
    rw [phi_lt, huq]; simp [EuclideanSpace.single_apply]
  · show phi A d μ _ (Fin.castSucc 1) = _
    rw [phi_lt, huq]; simp [EuclideanSpace.single_apply]
  · show phi A d μ _ (Fin.castSucc 2) = _
    rw [phi_lt, huq]; simp [EuclideanSpace.single_apply]
  · show phi A d μ _ (Fin.castSucc 3) = _
    rw [phi_lt, huq]; simp [EuclideanSpace.single_apply]
  · show phi A d μ _ 4 = _
    rw [phi_four]; simp [huq, EuclideanSpace.single_apply]

lemma inner_single4 (v : E5) : ⟪(EuclideanSpace.single 4 1 : E5), v⟫ = v 4 := by
  rw [EuclideanSpace.inner_single_left]; simp

/-- `IsPV` for a family is `IsPVs` for its point set. -/
lemma Family.isPVs_of_isPV (F : Family) {a : Fin 4 → ℝ} {y : E5} (h : F.IsPV a y) :
    IsPVs (range (F.pt a)) y := by
  refine ⟨fun x hx => ?_, fun v hv => h.2 v fun w hw => hv _ ⟨w, rfl⟩ hw⟩
  obtain ⟨w, rfl⟩ := hx
  exact h.1 w

/-- Tight sets of a family. -/
lemma Family.countGoal_of_F (F : Family) {a : Fin 4 → ℝ} (h : F.CountGoalF a) :
    CountGoal (range (F.pt a)) := by
  obtain ⟨M, hM, hMm⟩ := h
  refine ⟨M, hM, fun m hm => ?_⟩
  obtain ⟨hne, Z, hZ, hZpv, hm'⟩ := hMm m hm
  refine ⟨hne, Z, hZ, fun y hy x hx => ?_, hm'⟩
  obtain ⟨w, rfl⟩ := hx
  exact (hZpv y hy).1 w

/-- **The reduction for one table entry**: `phi` sends `±z` onto the points of the family, and the
conclusion of the family's certificate pulls back. -/
theorem map_case16 {N : ℕ} (X : FamX) (hX : X.ok = true) (hcheck : X.F.checkN N = true)
    (hrecs : ∀ r ∈ X.F.recs, X.F.recOK r = true)
    (hsubs : ∀ k < X.F.subs.length, X.F.subOK k = true)
    {z : Fin 8 → E5} (hzinj : Function.Injective (pm16 z))
    (hspan : ∀ φ : E5 →ₗ[ℝ] ℝ, (∀ x ∈ range (pm16 z), φ x = 0) → φ = 0)
    {cz : List ℕ} (hzq : ∀ (v : Fin 8) (j : Fin 4), z v j.castSucc = (rep (cz.getD v 0) j : ℝ))
    {A B : List (List ℤ)} {d e : ℤ} {tau : List ℕ} {eps : List ℤ}
    (hd : d ≠ 0) (he : e ≠ 0)
    (hBA : ∀ i < 4, ∀ k < 4, sum4 (fun j => mat B i j * mat A j k) = if i = k then e else 0)
    (htau : tau.length = 8) (htnd : tau.Nodup) (htlt : ∀ x ∈ tau, x < 8)
    (heps : ∀ w < 8, eps.getD w 0 = 1 ∨ eps.getD w 0 = -1)
    (hmatch : ∀ w < 8, ∀ i < 4,
      sum4 (fun j => mat A i j * (eps.getD w 0 * rep (cz.getD (tau.getD w 0) 0) j)) =
        d * (X.F.q w).getD i 0) :
    GoalN N (range (pm16 z)) := by
  classical
  -- the shear data of the family
  unfold FamX.ok at hX
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    List.contains_iff_mem, bne_iff_ne, ne_eq, List.mem_range] at hX
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hbl, hfl⟩, hblt⟩, hflt⟩, hcov⟩, hD⟩, hMN⟩, hzb⟩, hzf⟩ := hX
  have hτlt : ∀ w < 8, tau.getD w 0 < 8 := fun w hw => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact htlt _ (List.getElem_mem _)
  -- heights, shear and parameter
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ w, g w = (eps.getD w 0 : ℝ) * zz8 z (tau.getD w 0) 4 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Fin 4 → ℝ, ∀ i : Fin 4,
      ∑ j : Fin 4, ((X.F.q (X.basis.getD i 0)).getD j 0 : ℝ) * μ j = g (X.basis.getD i 0) := by
    refine ⟨fun j => (∑ k : Fin 4, (mat X.N j k : ℝ) * g (X.basis.getD k 0)) / X.D,
      solve_of_right_inv (M := fun i j => ((X.F.q (X.basis.getD i 0)).getD j 0 : ℝ))
        (N := fun j k => (mat X.N j k : ℝ)) (by exact_mod_cast hD) (fun i k => ?_) _⟩
    have := congrArg (fun t : ℤ => (t : ℝ)) (hMN i i.2 k k.2)
    simp only [sum4_eq, Int.cast_mul] at this
    rw [this]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (Fin.ext h1) h2
    · exact absurd (congrArg Fin.val h2) h1
    · simp
  obtain ⟨a, ha⟩ : ∃ a : Fin 4 → ℝ, ∀ k : Fin 4,
      a k = g (X.free.getD k 0) - ∑ j : Fin 4, ((X.F.q (X.free.getD k 0)).getD j 0 : ℝ) * μ j :=
    ⟨_, fun _ => rfl⟩
  -- the family's points are the images of `±z`
  have hpt : ∀ w (hw : w < 8),
      X.F.pt a ⟨w, by omega⟩ = phi A d μ ((eps.getD w 0 : ℝ) • zz8 z (tau.getD w 0)) := by
    intro w hw
    have hzw : ∀ j : Fin 4,
        zz8 z (tau.getD w 0) j.castSucc = (rep (cz.getD (tau.getD w 0) 0) j : ℝ) := by
      intro j; rw [zz8_of_lt z (hτlt w hw)]; exact hzq ⟨_, hτlt w hw⟩ j
    have huq : ∀ i : Fin 4,
        uq A d ((eps.getD w 0 : ℝ) • zz8 z (tau.getD w 0)) i = ((X.F.q w).getD i 0 : ℝ) := by
      intro i
      have := congrArg (fun t : ℤ => (t : ℝ)) (hmatch w hw i i.2)
      simp only [sum4_eq, Int.cast_mul] at this
      simp only [uq, PiLp.smul_apply, smul_eq_mul, hzw]
      rw [this]
      field_simp
    refine X.F.pt_ext (fun j => ?_) ?_
    · rw [phi_lt, huq]
    · rw [phi_four, Finset.sum_congr rfl fun i _ => by rw [huq i]]
      simp only [PiLp.smul_apply, smul_eq_mul]
      rw [← hg w]
      rcases hcov w hw with hb | hf
      · obtain ⟨i0, hi0, rfl⟩ := List.mem_iff_getElem.1 hb
        have h0 := hμ ⟨i0, by omega⟩
        simp only [List.getD_eq_getElem _ _ hi0] at h0
        have hz0 : X.F.z (X.basis[i0]) = Z4.zero := hzb _ hb
        rw [hz0, Z4.ev_zero, ← h0]
        simp only [mul_comm (μ _)]
        ring
      · obtain ⟨k0, hk0, rfl⟩ := List.mem_iff_getElem.1 hf
        have h0 := hzf k0 (by omega)
        have ha0 := ha ⟨k0, by omega⟩
        simp only [List.getD_eq_getElem _ _ hk0] at h0 ha0
        rw [h0, Z4.unit_ev a (by omega), ha0]
        simp only [mul_comm (μ _)]
  have hpt8 : ∀ w (hw : w < 8), X.F.pt a ⟨w + 8, by omega⟩ =
      phi A d μ (-((eps.getD w 0 : ℝ) • zz8 z (tau.getD w 0))) := by
    intro w hw
    rw [show (⟨w + 8, by omega⟩ : Fin 16) = ⟨(⟨w, hw⟩ : Fin 8) + 8, by omega⟩ from rfl,
      X.F.pt_add8 a ⟨w, hw⟩]
    rw [show (⟨((⟨w, hw⟩ : Fin 8) : ℕ), by omega⟩ : Fin 16) = ⟨w, by omega⟩ from rfl, hpt w hw,
      map_neg]
  -- `tau` is onto
  have hsurj : ∀ u : Fin 8, ∃ w < 8, tau.getD w 0 = u := by
    intro u
    have hsub : tau.toFinset ⊆ Finset.range 8 := fun x hx =>
      Finset.mem_range.2 (htlt x (List.mem_toFinset.1 hx))
    have hcard : tau.toFinset.card = 8 := by rw [List.toFinset_card_of_nodup htnd, htau]
    have heq : tau.toFinset = Finset.range 8 :=
      Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
    have hu : (u : ℕ) ∈ tau := List.mem_toFinset.1 (heq ▸ Finset.mem_range.2 u.2)
    obtain ⟨w, hw, hw'⟩ := List.mem_iff_getElem.1 hu
    exact ⟨w, by omega, by rw [List.getD_eq_getElem _ _ hw]; exact hw'⟩
  have hrange : range (X.F.pt a) = phi A d μ '' range (pm16 z) := by
    ext x
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      by_cases h8 : i < 8
      · refine ⟨_, ?_, (hpt i h8).symm⟩
        rw [mem_range_pm16]
        refine ⟨⟨_, hτlt i h8⟩, ?_⟩
        rw [zz8_of_lt z (hτlt i h8)]
        rcases heps i h8 with h1 | h1
        · left; rw [h1]; simp
        · right; rw [h1]; simp
      · obtain ⟨w, rfl⟩ : ∃ w, i = w + 8 := ⟨i - 8, by omega⟩
        refine ⟨_, ?_, (hpt8 w (by omega)).symm⟩
        rw [mem_range_pm16]
        refine ⟨⟨_, hτlt w (by omega)⟩, ?_⟩
        rw [zz8_of_lt z (hτlt w (by omega))]
        rcases heps w (by omega) with h1 | h1
        · right; rw [h1]; simp
        · left; rw [h1]; simp
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, hu⟩ := mem_range_pm16.1 hy
      obtain ⟨w, hw, hτw⟩ := hsurj u
      have hzu : zz8 z (tau.getD w 0) = z u := by
        rw [zz8_of_lt z (hτlt w hw)]; congr 1; exact Fin.ext hτw
      rcases heps w hw with h1 | h1 <;> rcases hu with rfl | rfl
      · exact ⟨⟨w, by omega⟩, by rw [hpt w hw, h1, hzu]; simp⟩
      · exact ⟨⟨w + 8, by omega⟩, by rw [hpt8 w hw, h1, hzu]; simp⟩
      · exact ⟨⟨w + 8, by omega⟩, by rw [hpt8 w hw, h1, hzu]; simp⟩
      · exact ⟨⟨w, by omega⟩, by rw [hpt w hw, h1, hzu]; simp⟩
  have hΦ := phi_injective hd he hBA μ
  -- the sixteen points are distinct
  have hinj : Function.Injective (X.F.pt a) := by
    have h16 : (range (X.F.pt a)).ncard = 16 := by
      rw [hrange, Set.ncard_image_of_injective _ hΦ, Set.ncard_range_of_injective hzinj]
      simp
    have hc : (Finset.univ.image (X.F.pt a)).card = (Finset.univ : Finset (Fin 16)).card := by
      rw [← Set.ncard_coe_finset, Finset.coe_image, Finset.coe_univ, Set.image_univ, h16]
      simp
    have := Finset.card_image_iff.1 hc
    exact fun x y hxy => this (Finset.mem_coe.2 (Finset.mem_univ x))
      (Finset.mem_coe.2 (Finset.mem_univ y)) hxy
  -- they span
  have hspan' : ∀ u : E5, (∀ w, ⟪X.F.pt a w, u⟫ = 0) → u = 0 := by
    intro u hu
    set v := LinearMap.adjoint (phi A d μ) u with hv
    have hφ : linF (fun j => v j) = 0 := by
      apply hspan
      intro x hx
      rw [linF_apply]
      have : ∑ j, v j * x j = ⟪x, v⟫ := by rw [inner_eq_sum]; simp only [mul_comm]
      rw [this, hv, LinearMap.adjoint_inner_right]
      obtain ⟨w, hw⟩ : phi A d μ x ∈ range (X.F.pt a) := by rw [hrange]; exact ⟨x, hx, rfl⟩
      rw [← hw]
      exact hu w
    have hv0 : v = 0 := by
      ext j
      have := congrArg (fun f : E5 →ₗ[ℝ] ℝ => f (EuclideanSpace.single j 1)) hφ
      simpa [linF_apply, EuclideanSpace.single_apply] using this
    exact adjoint_injective hΦ (by rw [← hv, hv0, map_zero])
  -- the certificate of the family
  rcases X.F.sound_pvN hcheck hrecs hsubs hinj hspan' with ⟨S, hS, hSpv⟩ | ⟨y, hy, hy4⟩ | hcount
  · left
    refine ⟨S.image (LinearMap.adjoint (phi A d μ)), ?_, fun y' hy' => ?_⟩
    · rw [Finset.card_image_of_injective _ (adjoint_injective hΦ)]; exact hS
    · obtain ⟨y, hyS, rfl⟩ := Finset.mem_image.1 hy'
      have h1 := X.F.isPVs_of_isPV (hSpv y hyS)
      rw [hrange] at h1
      exact h1.adjoint hΦ
  · right; left
    refine ⟨LinearMap.adjoint (phi A d μ) y, fun x hx => ?_, ?_⟩
    · rw [LinearMap.adjoint_inner_right]
      obtain ⟨w, hw⟩ : phi A d μ x ∈ range (X.F.pt a) := by rw [hrange]; exact ⟨x, hx, rfl⟩
      rw [← hw]
      exact hy w
    · rw [← inner_single4, LinearMap.adjoint_inner_right, phi_e4, inner_single4]
      exact hy4
  · right; right
    have h1 := X.F.countGoal_of_F hcount
    rw [hrange] at h1
    exact h1.of_image

/-- **The reduction of A16**, given the kernel checks of the table and the families. -/
theorem core16 {N : ℕ} (fams : List FamX) (table : List (List ℕ × TEntry))
    (hfams : ∀ X ∈ fams, X.ok = true ∧ X.F.checkN N = true ∧ (∀ r ∈ X.F.recs, X.F.recOK r = true) ∧
      ∀ k < X.F.subs.length, X.F.subOK k = true)
    (hseqs : seqsOK table = true) (hents : entriesOK fams table = true)
    {y : Fin 8 → E5}
    (hq : ∀ v (j : Fin 4), y v j.castSucc = 1 ∨ y v j.castSucc = -1)
    (hinj : Function.Injective (pm16 y))
    (hfib : ∀ x₁ ∈ range (pm16 y), ∀ x₂ ∈ range (pm16 y), ∀ x₃ ∈ range (pm16 y), x₁ ≠ x₂ →
      x₁ ≠ x₃ → x₂ ≠ x₃ →
        (∀ j : Fin 4, x₁ j.castSucc = x₂ j.castSucc ∧ x₁ j.castSucc = x₃ j.castSucc) → False)
    (hspan : ∀ φ : E5 →ₗ[ℝ] ℝ, (∀ x ∈ range (pm16 y), φ x = 0) → φ = 0) :
    GoalN N (range (pm16 y)) := by
  classical
  -- normalize the first coordinate to `+1`
  obtain ⟨s, hs⟩ : ∃ s : Fin 8 → ℝ, ∀ v, s v = y v 0 := ⟨_, fun _ => rfl⟩
  have hq0 : ∀ v, y v 0 = 1 ∨ y v 0 = -1 := fun v => hq v 0
  have hs1 : ∀ v, s v = 1 ∨ s v = -1 := fun v => by rw [hs]; exact hq0 v
  have hy1 : ∀ v (j : Fin 4), (s v • y v) j.castSucc = 1 ∨ (s v • y v) j.castSucc = -1 := by
    intro v j
    simp only [PiLp.smul_apply, smul_eq_mul]
    rcases hs1 v with h | h <;> rcases hq v j with h' | h' <;> simp [h, h']
  have hy10 : ∀ v, (s v • y v) 0 = 1 := by
    intro v
    simp only [PiLp.smul_apply, smul_eq_mul, hs]
    rcases hq0 v with h | h <;> rw [h] <;> norm_num
  -- classes, sorted
  obtain ⟨c, hc⟩ : ∃ c : Fin 8 → ℕ, ∀ v, c v = cls (s v • y v) := ⟨_, fun _ => rfl⟩
  have hrep : ∀ v (j : Fin 4), (s v • y v) j.castSucc = (rep (c v) j : ℝ) := fun v j => by
    rw [hc]; exact rep_cls (hy10 v) (hy1 v 1) (hy1 v 2) (hy1 v 3) j
  set σ := Tuple.sort c
  have hmono : Monotone (c ∘ σ) := Tuple.monotone_sort c
  obtain ⟨z, hz⟩ : ∃ z : Fin 8 → E5, z = fun v => s (σ v) • y (σ v) := ⟨_, rfl⟩
  have hzrange : range (pm16 z) = range (pm16 y) := by
    rw [hz]; exact range_pm16_signed (fun v => s (σ v)) (fun v => hs1 _) σ
  have hzinj : Function.Injective (pm16 z) := by
    rw [hz]; exact pm16_signed_injective hinj (fun v => s (σ v)) (fun v => hs1 _) σ
  have hzq : ∀ v (j : Fin 4), z v j.castSucc = (rep ((c ∘ σ) v) j : ℝ) := fun v j => by
    rw [hz]; exact hrep (σ v) j
  -- no class three times: fibres have at most two points
  have hnt : ∀ (i : ℕ) (h : i + 2 < 8), (c ∘ σ) ⟨i, by omega⟩ ≠ (c ∘ σ) ⟨i + 2, h⟩ := by
    intro i h heq
    have h01 : (c ∘ σ) ⟨i, by omega⟩ ≤ (c ∘ σ) ⟨i + 1, by omega⟩ :=
      hmono (Fin.mk_le_mk.2 (by omega))
    have h12 : (c ∘ σ) ⟨i + 1, by omega⟩ ≤ (c ∘ σ) ⟨i + 2, h⟩ :=
      hmono (Fin.mk_le_mk.2 (by omega))
    have e1 : (c ∘ σ) ⟨i + 1, by omega⟩ = (c ∘ σ) ⟨i, by omega⟩ := by omega
    have hzi := (pm16_inj_iff.1 hzinj).1
    have hmem : ∀ v, z v ∈ range (pm16 y) := fun v => by rw [← hzrange]; exact ⟨_, pm16_lo z v⟩
    refine hfib _ (hmem ⟨i, by omega⟩) _ (hmem ⟨i + 1, by omega⟩) _ (hmem ⟨i + 2, h⟩)
      (fun hh => by simpa [Fin.ext_iff] using hzi hh) (fun hh => by simpa [Fin.ext_iff] using hzi hh)
      (fun hh => by simpa [Fin.ext_iff] using hzi hh) fun j => ?_
    rw [hzq, hzq, hzq, e1, ← heq]
    exact ⟨rfl, rfl⟩
  -- the table entry of the sorted sequence
  have hmem := mem_allSeqs8 hmono (fun i => by rw [Function.comp_apply, hc]; exact cls_lt _) hnt
  unfold seqsOK at hseqs
  rw [beq_iff_eq] at hseqs
  rw [← hseqs, List.mem_map] at hmem
  obtain ⟨⟨cl, t⟩, hct, hcl⟩ := hmem
  simp only at hcl
  subst hcl
  unfold entriesOK at hents
  rw [List.all_eq_true] at hents
  have hok := hents _ hct
  simp only at hok
  have hgetD : ∀ v : Fin 8, (List.ofFn (c ∘ σ)).getD v 0 = (c ∘ σ) v := by
    intro v; rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have hzq' : ∀ (v : Fin 8) (j : Fin 4),
      z v j.castSucc = (rep ((List.ofFn (c ∘ σ)).getD v 0) j : ℝ) := by
    intro v j; rw [hgetD]; exact hzq v j
  have hspan' : ∀ φ : E5 →ₗ[ℝ] ℝ, (∀ x ∈ range (pm16 z), φ x = 0) → φ = 0 :=
    fun φ hφ => hspan φ fun x hx => hφ x (by rw [hzrange]; exact hx)
  cases t with
  | nonspan n =>
    simp only [TEntry.ok, Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range,
      bne_iff_ne, ne_eq, beq_iff_eq] at hok
    obtain ⟨⟨j0, hj0, hn0⟩, hperp⟩ := hok
    have hφ : linF (fun j => if j.val < 4 then (n.getD j 0 : ℝ) else 0) = 0 := by
      apply hspan'
      intro x hx
      have hzero : ∀ v : Fin 8, ∑ j : Fin 4, (n.getD j 0 : ℝ) * z v j.castSucc = 0 := by
        intro v
        have := congrArg (fun t : ℤ => (t : ℝ)) (hperp v v.2)
        simp only [sum4_eq, Int.cast_mul, Int.cast_zero] at this
        simp only [hzq']
        exact this
      obtain ⟨v, rfl | rfl⟩ := mem_range_pm16.1 hx
      · rw [linF_low]; exact hzero v
      · rw [map_neg, linF_low, hzero v, neg_zero]
    have := congrArg (fun f : E5 →ₗ[ℝ] ℝ => f (EuclideanSpace.single (⟨j0, by omega⟩ : Fin 5) 1)) hφ
    simp only [linF_low, LinearMap.zero_apply, Fin.sum_univ_four] at this
    exfalso
    apply hn0
    interval_cases j0 <;> simpa [EuclideanSpace.single_apply] using this
  | map fam A d B e tau eps =>
    simp only [TEntry.ok, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
      List.all_eq_true, List.mem_range, beq_iff_eq, Bool.or_eq_true] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨hfam, hd⟩, he⟩, hBA⟩, htau⟩, htnd⟩, htlt⟩, hrest⟩ := hok
    have hX : fams.getD fam default ∈ fams := by
      rw [List.getD_eq_getElem _ _ hfam]; exact List.getElem_mem _
    obtain ⟨hXok, hXc, hXr, hXs⟩ := hfams _ hX
    have h := map_case16 (fams.getD fam default) hXok hXc hXr hXs hzinj hspan' hzq'
      hd he hBA htau htnd htlt (fun w hw => (hrest w hw).1) (fun w hw => (hrest w hw).2)
    rwa [hzrange] at h

end Kalai5.A16
