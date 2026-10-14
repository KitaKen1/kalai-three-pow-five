import Kalai5.LemmaA.Sound
import Kalai5.LemmaA.Reduce
import Kalai5.Small.Model

/-!
# Lemma A: soundness of the reduction table

`core`: seven points `y_v ∈ ℝ⁵` whose first four coordinates are `±1`, such that the fourteen
points `±y_v` are distinct, no three of them agree in the first four coordinates, and they span
`ℝ⁵`, have at least 243 faces in their convex hull — provided the table and the families pass
their kernel checks.

Proof: normalize each `y_v` to first coordinate `+1` and read off its class, sort the classes
(`Tuple.sort`), look up the table entry of the sorted sequence, and map the points onto the
family's points by the linear map `x ↦ ((1/d) A q, x₄ - μ · ((1/d) A q))` (the shear `μ` zeroes
the base heights; the free heights are the parameter `a`).
-/

namespace Kalai5.LemmaA

open Set Module

/-! ### Sorted class sequences -/

lemma mem_monoSeqs : ∀ (k lo : ℕ) (l : List ℕ), l.length = k → l.Pairwise (· ≤ ·) →
    (∀ x ∈ l, lo ≤ x ∧ x < 8) → l ∈ monoSeqs k lo
  | 0, _, [], _, _, _ => by simp [monoSeqs]
  | k + 1, lo, v :: l, hlen, hpw, hb => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    rw [List.pairwise_cons] at hpw
    have hv := hb v List.mem_cons_self
    simp only [monoSeqs, List.mem_flatMap, List.mem_range', List.mem_map]
    refine ⟨v, ⟨v - lo, by omega, by omega⟩, l, ?_, rfl⟩
    exact mem_monoSeqs k v l hlen hpw.2 fun x hx =>
      ⟨hpw.1 x hx, (hb x (List.mem_cons_of_mem _ hx)).2⟩

lemma noTriple_of : ∀ l : List ℕ, (∀ i (h : i + 2 < l.length), l[i] ≠ l[i + 2]) → noTriple l = true
  | a :: b :: c :: l, h => by
    simp only [noTriple, Bool.and_eq_true, bne_iff_ne, ne_eq]
    refine ⟨h 0 (by simp), noTriple_of (b :: c :: l) fun i hi => ?_⟩
    have := h (i + 1) (by simp at hi ⊢; omega)
    simpa using this
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl

lemma mem_allSeqs {c : Fin 7 → ℕ} (hmono : Monotone c) (h8 : ∀ i, c i < 8)
    (hnt : ∀ (i : ℕ) (h : i + 2 < 7), c ⟨i, by omega⟩ ≠ c ⟨i + 2, h⟩) : List.ofFn c ∈ allSeqs := by
  unfold allSeqs
  rw [List.mem_filter]
  refine ⟨mem_monoSeqs 7 0 _ (by simp) ?_ ?_, noTriple_of _ ?_⟩
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

/-! ### Classes -/

/-- The class of a point whose first four coordinates are `(1, ±1, ±1, ±1)`. -/
noncomputable def cls (x : E5) : ℕ :=
  (if x 1 < 0 then 1 else 0) + (if x 2 < 0 then 2 else 0) + (if x 3 < 0 then 4 else 0)

lemma cls_lt (x : E5) : cls x < 8 := by
  unfold cls; split_ifs <;> norm_num

lemma rep_cls {x : E5} (h0 : x 0 = 1) (h1 : x 1 = 1 ∨ x 1 = -1) (h2 : x 2 = 1 ∨ x 2 = -1)
    (h3 : x 3 = 1 ∨ x 3 = -1) (j : Fin 4) : x j.castSucc = (rep (cls x) j : ℝ) := by
  have key : x 0 = rep (cls x) 0 ∧ x 1 = rep (cls x) 1 ∧ x 2 = rep (cls x) 2 ∧
      x 3 = rep (cls x) 3 := by
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      norm_num [cls, rep, repTable, h0, h1, h2, h3]
  obtain ⟨j, hj⟩ := j
  interval_cases j
  · exact key.1
  · exact key.2.1
  · exact key.2.2.1
  · exact key.2.2.2

/-! ### Signed points -/

/-- The fourteen points `±y_v`. -/
noncomputable def pm (y : Fin 7 → E5) (i : Fin 14) : E5 :=
  if h : i.val < 7 then y ⟨i, h⟩ else -y ⟨i.val - 7, by omega⟩

lemma pm_lo (y : Fin 7 → E5) (v : Fin 7) : pm y ⟨v, by omega⟩ = y v := by
  simp [pm, v.2]

lemma pm_hi (y : Fin 7 → E5) (v : Fin 7) : pm y ⟨v + 7, by omega⟩ = -y v := by
  simp [pm]

lemma mem_range_pm {y : Fin 7 → E5} {x : E5} : x ∈ range (pm y) ↔ ∃ v, x = y v ∨ x = -y v := by
  constructor
  · rintro ⟨i, rfl⟩
    by_cases h : i.val < 7
    · exact ⟨⟨i, h⟩, Or.inl (by simp [pm, h])⟩
    · exact ⟨⟨i.val - 7, by omega⟩, Or.inr (by simp [pm, h])⟩
  · rintro ⟨v, rfl | rfl⟩
    · exact ⟨_, pm_lo y v⟩
    · exact ⟨_, pm_hi y v⟩

lemma pm_injective_iff {y : Fin 7 → E5} :
    Function.Injective (pm y) ↔ Function.Injective y ∧ ∀ u v, y u ≠ -y v := by
  constructor
  · intro h
    refine ⟨fun u v huv => ?_, fun u v huv => ?_⟩
    · have := h (show pm y ⟨u, by omega⟩ = pm y ⟨v, by omega⟩ by rw [pm_lo, pm_lo, huv])
      exact Fin.ext (by simpa using this)
    · have := h (show pm y ⟨u, by omega⟩ = pm y ⟨v + 7, by omega⟩ by rw [pm_lo, pm_hi, huv])
      simp [Fin.ext_iff] at this
      omega
  · rintro ⟨hy, hneg⟩ i j hij
    unfold pm at hij
    split_ifs at hij with hi hj hj
    · exact Fin.ext (by simpa using hy hij)
    · exact absurd hij (hneg _ _)
    · exact absurd hij.symm (hneg _ _)
    · have := hy (neg_injective hij)
      simp [Fin.ext_iff] at this
      exact Fin.ext (by omega)

/-- Signs and permutations do not change the set `{±y_v}`. -/
lemma range_pm_signed {y : Fin 7 → E5} (t : Fin 7 → ℝ) (ht : ∀ v, t v = 1 ∨ t v = -1)
    (ρ : Equiv.Perm (Fin 7)) : range (pm fun v => t v • y (ρ v)) = range (pm y) := by
  ext x
  simp only [mem_range_pm]
  constructor
  · rintro ⟨v, hx⟩
    refine ⟨ρ v, ?_⟩
    rcases ht v with h | h <;> rcases hx with hx | hx <;> simp [hx, h]
  · rintro ⟨u, hx⟩
    refine ⟨ρ.symm u, ?_⟩
    rcases ht (ρ.symm u) with h | h <;> rcases hx with hx | hx <;> simp [hx, h]

lemma pm_signed_injective {y : Fin 7 → E5} (hy : Function.Injective (pm y)) (t : Fin 7 → ℝ)
    (ht : ∀ v, t v = 1 ∨ t v = -1) (ρ : Equiv.Perm (Fin 7)) :
    Function.Injective (pm fun v => t v • y (ρ v)) := by
  rw [pm_injective_iff] at hy ⊢
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

/-! ### Linear algebra over `Fin 4` -/

lemma sum4_eq (f : ℕ → ℤ) : (sum4 f : ℝ) = ∑ j : Fin 4, (f j : ℝ) := by
  simp [sum4, Fin.sum_univ_four]

/-- A left inverse up to the scalar `e` makes the matrix injective. -/
lemma eq_zero_of_left_inv {Am Bm : Fin 4 → Fin 4 → ℝ} {e : ℝ} (he : e ≠ 0)
    (hBA : ∀ i k, ∑ j, Bm i j * Am j k = if i = k then e else 0) {x : Fin 4 → ℝ}
    (hx : ∀ i, ∑ j, Am i j * x j = 0) (k : Fin 4) : x k = 0 := by
  have h1 : ∑ i, Bm k i * ∑ j, Am i j * x j = 0 := by simp [hx]
  have h2 : ∑ i, Bm k i * ∑ j, Am i j * x j = e * x k := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hBA]
    simp
  rw [h2] at h1
  exact (mul_eq_zero.1 h1).resolve_left he

/-- An inverse up to the scalar `D` solves every system. -/
lemma solve_of_right_inv {M N : Fin 4 → Fin 4 → ℝ} {D : ℝ} (hD : D ≠ 0)
    (hMN : ∀ i k, ∑ j, M i j * N j k = if i = k then D else 0) (g : Fin 4 → ℝ) (i : Fin 4) :
    ∑ j, M i j * ((∑ k, N j k * g k) / D) = g i := by
  have : ∑ j, M i j * ∑ k, N j k * g k = D * g i := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hMN]
    simp
  simp_rw [mul_div_assoc', ← Finset.sum_div, this]
  field_simp

/-! ### The linear map `x ↦ ((1/d) A q, x₄ - μ · (1/d) A q)` -/

/-- `((1/d) A q(x))_i`. -/
noncomputable def uq (A : List (List ℤ)) (d : ℤ) (x : E5) (i : ℕ) : ℝ :=
  (∑ j : Fin 4, (mat A i j : ℝ) * x j.castSucc) / d

/-- The reduction map. -/
noncomputable def phi (A : List (List ℤ)) (d : ℤ) (μ : Fin 4 → ℝ) : E5 →ₗ[ℝ] E5 where
  toFun x := (WithLp.equiv 2 (Fin 5 → ℝ)).symm
    ![uq A d x 0, uq A d x 1, uq A d x 2, uq A d x 3, x 4 - ∑ i : Fin 4, μ i * uq A d x i]
  map_add' x y := by
    ext i; fin_cases i <;> simp [uq, Fin.sum_univ_four] <;> ring
  map_smul' r x := by
    ext i; fin_cases i <;> simp [uq, Fin.sum_univ_four] <;> ring

lemma phi_lt (A : List (List ℤ)) (d : ℤ) (μ : Fin 4 → ℝ) (x : E5) (i : Fin 4) :
    phi A d μ x i.castSucc = uq A d x i := by
  fin_cases i <;> rfl

lemma phi_four (A : List (List ℤ)) (d : ℤ) (μ : Fin 4 → ℝ) (x : E5) :
    phi A d μ x 4 = x 4 - ∑ i : Fin 4, μ i * uq A d x i := rfl

lemma phi_injective {A B : List (List ℤ)} {d e : ℤ} (hd : d ≠ 0) (he : e ≠ 0)
    (hBA : ∀ i < 4, ∀ k < 4, sum4 (fun j => mat B i j * mat A j k) = if i = k then e else 0)
    (μ : Fin 4 → ℝ) : Function.Injective (phi A d μ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hq : ∀ i : Fin 4, ∑ j : Fin 4, (mat A i j : ℝ) * x j.castSucc = 0 := by
    intro i
    have := congrArg (fun y : E5 => y i.castSucc) hx
    simp only [phi_lt, PiLp.zero_apply, uq] at this
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    exact (div_eq_zero_iff.1 this).resolve_right hd'
  have hBA' : ∀ i k : Fin 4, ∑ j : Fin 4, (mat B i j : ℝ) * (mat A j k : ℝ) =
      if i = k then (e : ℝ) else 0 := by
    intro i k
    have := congrArg (fun t : ℤ => (t : ℝ)) (hBA i i.2 k k.2)
    simp only [sum4_eq, Int.cast_mul] at this
    rw [this]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (Fin.ext h1) h2
    · exact absurd (congrArg Fin.val h2) h1
    · simp
  have hx4 : ∀ k : Fin 4, x k.castSucc = 0 :=
    eq_zero_of_left_inv (by exact_mod_cast he) hBA' hq
  have h4 := congrArg (fun y : E5 => y 4) hx
  simp only [phi_four, PiLp.zero_apply] at h4
  have huq : ∀ i, uq A d x i = 0 := by
    intro i; simp [uq, hx4]
  simp only [huq, mul_zero, Finset.sum_const_zero, sub_zero] at h4
  ext k
  fin_cases k
  · exact hx4 0
  · exact hx4 1
  · exact hx4 2
  · exact hx4 3
  · exact h4

/-! ### Antipodal points of a family -/

namespace Family

variable (F : Family)

lemma pt_ext {a : Fin 3 → ℝ} {w : Fin 14} {x : E5} (h : ∀ j : Fin 4, x j.castSucc = F.qc w j)
    (h4 : x 4 = (F.zt w).dot a) : F.pt a w = x := by
  ext k
  fin_cases k
  · exact (h 0).symm
  · exact (h 1).symm
  · exact (h 2).symm
  · exact (h 3).symm
  · exact h4.symm

lemma qc_add7 {w : ℕ} (hw : w < 7) (j : ℕ) : F.qc (w + 7) j = -F.qc w j := by
  simp [qc, hw]

lemma zt_add7 {w : ℕ} (hw : w < 7) : F.zt (w + 7) = Z3.smul (-1) (F.zt w) := by
  simp [zt, hw]

lemma pt_add7 (a : Fin 3 → ℝ) {w : ℕ} (hw : w < 7) :
    F.pt a ⟨w + 7, by omega⟩ = -F.pt a ⟨w, by omega⟩ := by
  refine F.pt_ext (fun j => ?_) ?_
  · fin_cases j <;> simp [pt, qc_add7 F hw]
  · simp [pt, zt_add7 F hw]

end Family

/-! ### One table entry -/

/-- `x ↦ Σ_j c_j x_j`. -/
noncomputable def linF (c : Fin 5 → ℝ) : E5 →ₗ[ℝ] ℝ where
  toFun x := ∑ j, c j * x j
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

lemma Z3.unit_dot (a : Fin 3 → ℝ) {k : ℕ} (hk : k < 3) : (Z3.unit k).dot a = a ⟨k, hk⟩ := by
  interval_cases k <;> simp [Z3.unit, Z3.dot] <;> rfl

lemma linF_apply (c : Fin 5 → ℝ) (x : E5) : linF c x = ∑ j, c j * x j := rfl

/-- Point `k` of `z`, or `0`. -/
noncomputable def zz (z : Fin 7 → E5) (k : ℕ) : E5 := if h : k < 7 then z ⟨k, h⟩ else 0

lemma zz_of_lt (z : Fin 7 → E5) {k : ℕ} (h : k < 7) : zz z k = z ⟨k, h⟩ := by simp [zz, h]

/-- **The reduction for one table entry**: the linear map `phi` sends `±z` onto the points of
the family, so the certificate of the family applies. -/
theorem map_case (X : FamX) (hX : X.ok = true) (hcheck : X.F.check = true)
    {z : Fin 7 → E5} (hzinj : Function.Injective (pm z))
    (hspan : ∀ φ : E5 →ₗ[ℝ] ℝ, (∀ x ∈ range (pm z), φ x = 0) → φ = 0)
    {cz : List ℕ} (hzq : ∀ (v : Fin 7) (j : Fin 4), z v j.castSucc = (rep (cz.getD v 0) j : ℝ))
    {A B : List (List ℤ)} {d e : ℤ} {tau : List ℕ} {eps : List ℤ}
    (hd : d ≠ 0) (he : e ≠ 0)
    (hBA : ∀ i < 4, ∀ k < 4, sum4 (fun j => mat B i j * mat A j k) = if i = k then e else 0)
    (htau : tau.length = 7) (htnd : tau.Nodup) (htlt : ∀ x ∈ tau, x < 7)
    (heps : ∀ w < 7, eps.getD w 0 = 1 ∨ eps.getD w 0 = -1)
    (hmatch : ∀ w < 7, ∀ i < 4,
      sum4 (fun j => mat A i j * (eps.getD w 0 * rep (cz.getD (tau.getD w 0) 0) j)) =
        d * X.F.qc w i) :
    243 ≤ (faces (convexHull ℝ (range (pm z)))).ncard := by
  classical
  -- the shear data of the family
  unfold FamX.ok at hX
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    List.contains_iff_mem, bne_iff_ne, ne_eq, List.mem_range] at hX
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hbl, hfl⟩, hblt⟩, hflt⟩, hcov⟩, hD⟩, hMN⟩, hzb⟩, hzf⟩ := hX
  have hτlt : ∀ w < 7, tau.getD w 0 < 7 := fun w hw => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact htlt _ (List.getElem_mem _)
  -- heights, shear and parameter
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ w, g w = (eps.getD w 0 : ℝ) * zz z (tau.getD w 0) 4 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Fin 4 → ℝ, ∀ i : Fin 4,
      ∑ j : Fin 4, (X.F.qc (X.basis.getD i 0) j : ℝ) * μ j = g (X.basis.getD i 0) := by
    refine ⟨fun j => (∑ k : Fin 4, (mat X.N j k : ℝ) * g (X.basis.getD k 0)) / X.D,
      solve_of_right_inv (M := fun i j => (X.F.qc (X.basis.getD i 0) j : ℝ))
        (N := fun j k => (mat X.N j k : ℝ)) (by exact_mod_cast hD) (fun i k => ?_) _⟩
    have := congrArg (fun t : ℤ => (t : ℝ)) (hMN i i.2 k k.2)
    simp only [sum4_eq, Int.cast_mul] at this
    rw [this]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (Fin.ext h1) h2
    · exact absurd (congrArg Fin.val h2) h1
    · simp
  obtain ⟨a, ha⟩ : ∃ a : Fin 3 → ℝ, ∀ k : Fin 3,
      a k = g (X.free.getD k 0) - ∑ j : Fin 4, (X.F.qc (X.free.getD k 0) j : ℝ) * μ j :=
    ⟨_, fun _ => rfl⟩
  -- the family's points are the images of `±z`
  have hpt : ∀ w (hw : w < 7),
      X.F.pt a ⟨w, by omega⟩ = phi A d μ ((eps.getD w 0 : ℝ) • zz z (tau.getD w 0)) := by
    intro w hw
    have hzw : ∀ j : Fin 4, zz z (tau.getD w 0) j.castSucc = (rep (cz.getD (tau.getD w 0) 0) j : ℝ) := by
      intro j; rw [zz_of_lt z (hτlt w hw)]; exact hzq ⟨_, hτlt w hw⟩ j
    have huq : ∀ i : Fin 4, uq A d ((eps.getD w 0 : ℝ) • zz z (tau.getD w 0)) i = X.F.qc w i := by
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
        rw [hzb _ hb, Z3.dot_zero, ← h0]
        simp only [mul_comm (μ _)]
        ring
      · obtain ⟨k0, hk0, rfl⟩ := List.mem_iff_getElem.1 hf
        have h0 := hzf k0 (by omega)
        have ha0 := ha ⟨k0, by omega⟩
        simp only [List.getD_eq_getElem _ _ hk0] at h0 ha0
        rw [h0, Z3.unit_dot a (by omega), ha0]
        simp only [mul_comm (μ _)]
  have hpt7 : ∀ w (hw : w < 7), X.F.pt a ⟨w + 7, by omega⟩ =
      phi A d μ (-((eps.getD w 0 : ℝ) • zz z (tau.getD w 0))) := by
    intro w hw; rw [X.F.pt_add7 a hw, hpt w hw, map_neg]
  -- `tau` is onto
  have hsurj : ∀ u : Fin 7, ∃ w < 7, tau.getD w 0 = u := by
    intro u
    have hsub : tau.toFinset ⊆ Finset.range 7 := fun x hx =>
      Finset.mem_range.2 (htlt x (List.mem_toFinset.1 hx))
    have hcard : tau.toFinset.card = 7 := by rw [List.toFinset_card_of_nodup htnd, htau]
    have heq : tau.toFinset = Finset.range 7 :=
      Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
    have hu : (u : ℕ) ∈ tau := List.mem_toFinset.1 (heq ▸ Finset.mem_range.2 u.2)
    obtain ⟨w, hw, hw'⟩ := List.mem_iff_getElem.1 hu
    exact ⟨w, by omega, by rw [List.getD_eq_getElem _ _ hw]; exact hw'⟩
  have hrange : range (X.F.pt a) = phi A d μ '' range (pm z) := by
    ext x
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      by_cases h7 : i < 7
      · refine ⟨_, ?_, (hpt i h7).symm⟩
        rw [mem_range_pm]
        refine ⟨⟨_, hτlt i h7⟩, ?_⟩
        rw [zz_of_lt z (hτlt i h7)]
        rcases heps i h7 with h1 | h1
        · left; rw [h1]; simp
        · right; rw [h1]; simp
      · obtain ⟨w, rfl⟩ : ∃ w, i = w + 7 := ⟨i - 7, by omega⟩
        refine ⟨_, ?_, (hpt7 w (by omega)).symm⟩
        rw [mem_range_pm]
        refine ⟨⟨_, hτlt w (by omega)⟩, ?_⟩
        rw [zz_of_lt z (hτlt w (by omega))]
        rcases heps w (by omega) with h1 | h1
        · right; rw [h1]; simp
        · left; rw [h1]; simp
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, hu⟩ := mem_range_pm.1 hy
      obtain ⟨w, hw, hτw⟩ := hsurj u
      have hzu : zz z (tau.getD w 0) = z u := by rw [zz_of_lt z (hτlt w hw)]; congr 1; exact Fin.ext hτw
      rcases heps w hw with h1 | h1 <;> rcases hu with rfl | rfl
      · exact ⟨⟨w, by omega⟩, by rw [hpt w hw, h1, hzu]; simp⟩
      · exact ⟨⟨w + 7, by omega⟩, by rw [hpt7 w hw, h1, hzu]; simp⟩
      · exact ⟨⟨w + 7, by omega⟩, by rw [hpt7 w hw, h1, hzu]; simp⟩
      · exact ⟨⟨w, by omega⟩, by rw [hpt w hw, h1, hzu]; simp⟩
  have hΦ := phi_injective hd he hBA μ
  -- the fourteen points are distinct
  have hinj : Function.Injective (X.F.pt a) := by
    have h14 : (range (X.F.pt a)).ncard = 14 := by
      rw [hrange, Set.ncard_image_of_injective _ hΦ, Set.ncard_range_of_injective hzinj]
      simp
    have hc : (Finset.univ.image (X.F.pt a)).card = (Finset.univ : Finset (Fin 14)).card := by
      rw [← Set.ncard_coe_finset, Finset.coe_image, Finset.coe_univ, Set.image_univ, h14]
      simp
    have := Finset.card_image_iff.1 hc
    exact fun x y hxy => this (Finset.mem_coe.2 (Finset.mem_univ x))
      (Finset.mem_coe.2 (Finset.mem_univ y)) hxy
  -- the parameter is not zero: otherwise every point lies in `x₄ = 0`
  have ha : a ≠ 0 := by
    intro ha0
    have hψ : (linF fun j => if j = 4 then 1 else 0).comp (phi A d μ) = 0 := by
      apply hspan
      intro x hx
      obtain ⟨i, hi⟩ : phi A d μ x ∈ range (X.F.pt a) := by rw [hrange]; exact ⟨x, hx, rfl⟩
      simp only [LinearMap.comp_apply, linF_apply, ← hi]
      simp [Fin.sum_univ_five, Family.pt, ha0, Z3.dot]
    have h1 := congrArg (fun f : E5 →ₗ[ℝ] ℝ => f (EuclideanSpace.single 4 1)) hψ
    simp only [LinearMap.comp_apply, linF_apply, LinearMap.zero_apply] at h1
    simp [Fin.sum_univ_five, phi_four, uq, Fin.sum_univ_four] at h1
  -- the certificate of the family
  have h243 := X.F.check_sound hcheck ha hinj
  rwa [hrange, ← LinearMap.image_convexHull, ncard_faces_image_of_injective _ hΦ] at h243

/-! ### The core statement -/

lemma linF_low (n : List ℤ) (x : E5) :
    linF (fun j => if j.val < 4 then (n.getD j 0 : ℝ) else 0) x =
      ∑ j : Fin 4, (n.getD j 0 : ℝ) * x j.castSucc := by
  rw [linF_apply, Fin.sum_univ_castSucc]
  simp

/-- **The reduction of Lemma A**, given the kernel checks of the table and the families. -/
theorem core (fams : List FamX) (table : List (List ℕ × TEntry))
    (hfams : ∀ X ∈ fams, X.ok = true ∧ X.F.check = true)
    (hseqs : seqsOK table = true) (hents : entriesOK fams table = true)
    {y : Fin 7 → E5}
    (hq : ∀ v (j : Fin 4), y v j.castSucc = 1 ∨ y v j.castSucc = -1)
    (hinj : Function.Injective (pm y))
    (hfib : ∀ x₁ ∈ range (pm y), ∀ x₂ ∈ range (pm y), ∀ x₃ ∈ range (pm y), x₁ ≠ x₂ → x₁ ≠ x₃ →
      x₂ ≠ x₃ → (∀ j : Fin 4, x₁ j.castSucc = x₂ j.castSucc ∧ x₁ j.castSucc = x₃ j.castSucc) →
        False)
    (hspan : ∀ φ : E5 →ₗ[ℝ] ℝ, (∀ x ∈ range (pm y), φ x = 0) → φ = 0) :
    243 ≤ (faces (convexHull ℝ (range (pm y)))).ncard := by
  classical
  -- normalize the first coordinate to `+1`
  obtain ⟨s, hs⟩ : ∃ s : Fin 7 → ℝ, ∀ v, s v = y v 0 := ⟨_, fun _ => rfl⟩
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
  obtain ⟨c, hc⟩ : ∃ c : Fin 7 → ℕ, ∀ v, c v = cls (s v • y v) := ⟨_, fun _ => rfl⟩
  have hrep : ∀ v (j : Fin 4), (s v • y v) j.castSucc = (rep (c v) j : ℝ) := fun v j => by
    rw [hc]; exact rep_cls (hy10 v) (hy1 v 1) (hy1 v 2) (hy1 v 3) j
  set σ := Tuple.sort c
  have hmono : Monotone (c ∘ σ) := Tuple.monotone_sort c
  obtain ⟨z, hz⟩ : ∃ z : Fin 7 → E5, z = fun v => s (σ v) • y (σ v) := ⟨_, rfl⟩
  have hzrange : range (pm z) = range (pm y) := by
    rw [hz]; exact range_pm_signed (fun v => s (σ v)) (fun v => hs1 _) σ
  have hzinj : Function.Injective (pm z) := by
    rw [hz]; exact pm_signed_injective hinj (fun v => s (σ v)) (fun v => hs1 _) σ
  have hzq : ∀ v (j : Fin 4), z v j.castSucc = (rep ((c ∘ σ) v) j : ℝ) := fun v j => by
    rw [hz]; exact hrep (σ v) j
  -- no class three times: fibres have at most two points
  have hnt : ∀ (i : ℕ) (h : i + 2 < 7), (c ∘ σ) ⟨i, by omega⟩ ≠ (c ∘ σ) ⟨i + 2, h⟩ := by
    intro i h heq
    have h01 : (c ∘ σ) ⟨i, by omega⟩ ≤ (c ∘ σ) ⟨i + 1, by omega⟩ :=
      hmono (Fin.mk_le_mk.2 (by omega))
    have h12 : (c ∘ σ) ⟨i + 1, by omega⟩ ≤ (c ∘ σ) ⟨i + 2, h⟩ :=
      hmono (Fin.mk_le_mk.2 (by omega))
    have e1 : (c ∘ σ) ⟨i + 1, by omega⟩ = (c ∘ σ) ⟨i, by omega⟩ := by omega
    have hzi := (pm_injective_iff.1 hzinj).1
    have hmem : ∀ v, z v ∈ range (pm y) := fun v => by rw [← hzrange]; exact ⟨_, pm_lo z v⟩
    refine hfib _ (hmem ⟨i, by omega⟩) _ (hmem ⟨i + 1, by omega⟩) _ (hmem ⟨i + 2, h⟩)
      (fun hh => by simpa [Fin.ext_iff] using hzi hh) (fun hh => by simpa [Fin.ext_iff] using hzi hh)
      (fun hh => by simpa [Fin.ext_iff] using hzi hh) fun j => ?_
    rw [hzq, hzq, hzq, e1, ← heq]
    exact ⟨rfl, rfl⟩
  -- the table entry of the sorted sequence
  have hmem := mem_allSeqs hmono (fun i => by rw [Function.comp_apply, hc]; exact cls_lt _) hnt
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
  have hgetD : ∀ v : Fin 7, (List.ofFn (c ∘ σ)).getD v 0 = (c ∘ σ) v := by
    intro v; rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have hzq' : ∀ (v : Fin 7) (j : Fin 4),
      z v j.castSucc = (rep ((List.ofFn (c ∘ σ)).getD v 0) j : ℝ) := by
    intro v j; rw [hgetD]; exact hzq v j
  have hspan' : ∀ φ : E5 →ₗ[ℝ] ℝ, (∀ x ∈ range (pm z), φ x = 0) → φ = 0 :=
    fun φ hφ => hspan φ fun x hx => hφ x (by rw [hzrange]; exact hx)
  cases t with
  | nonspan n =>
    simp only [TEntry.ok, Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range,
      bne_iff_ne, ne_eq, beq_iff_eq] at hok
    obtain ⟨⟨j0, hj0, hn0⟩, hperp⟩ := hok
    have hφ : linF (fun j => if j.val < 4 then (n.getD j 0 : ℝ) else 0) = 0 := by
      apply hspan'
      intro x hx
      have hzero : ∀ v : Fin 7, ∑ j : Fin 4, (n.getD j 0 : ℝ) * z v j.castSucc = 0 := by
        intro v
        have := congrArg (fun t : ℤ => (t : ℝ)) (hperp v v.2)
        simp only [sum4_eq, Int.cast_mul, Int.cast_zero] at this
        simp only [hzq']
        exact this
      obtain ⟨v, rfl | rfl⟩ := mem_range_pm.1 hx
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
    have h := map_case (fams.getD fam default) (hfams _ hX).1 (hfams _ hX).2 hzinj hspan' hzq'
      hd he hBA htau htnd htlt (fun w hw => (hrest w hw).1) (fun w hw => (hrest w hw).2)
    rwa [hzrange] at h

end Kalai5.LemmaA
