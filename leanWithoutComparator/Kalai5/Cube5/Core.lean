import Kalai5.Cube5.Sound
import Kalai5.FullPrism.Assemble

/-!
# Cube polytopes: the reduction to the representatives

`core`: eight points `y_v ∈ {±1}⁵` such that the sixteen points `±y_v` are distinct and span `ℝ⁵`
have at least `243` nonempty faces in their convex hull — provided the table and the
representatives pass their kernel checks.

Proof: normalize each point to first coordinate `+1` and read off its class; the classes are
distinct, so they are the set bits of a mask with eight bits; the table carries that set by a
signed permutation `G` onto the classes of a representative, and `G` maps `±y_v` onto the
representative's points.  Spanning excludes the representative without a face certificate.
-/

namespace Kalai5.Cube5

open Set Module Kalai5.Gale Kalai5.FullPrism

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-! ### Signs -/

/-- `-1` for `true`, `1` for `false`. -/
noncomputable def sgnB (b : Bool) : ℝ := if b then -1 else 1

lemma sgnB_xor (a b : Bool) : sgnB (xor a b) = sgnB a * sgnB b := by
  cases a <;> cases b <;> norm_num [sgnB]

lemma sgnB_mul_xor (a b : Bool) : sgnB a * sgnB (xor a b) = sgnB b := by
  cases a <;> cases b <;> norm_num [sgnB]

lemma sgnB_sq (a : Bool) : sgnB a * sgnB a = 1 := by
  cases a <;> norm_num [sgnB]

lemma sgnB_ne_zero (a : Bool) : sgnB a ≠ 0 := by
  cases a <;> norm_num [sgnB]

lemma sgnB_decide {t : ℝ} (h : t = 1 ∨ t = -1) : sgnB (decide (t < 0)) = t := by
  rcases h with rfl | rfl <;> norm_num [sgnB]

lemma rep_cast (c k : ℕ) : (rep c k : ℝ) = sgnB (nb c k) := by
  unfold rep nb sgnB
  by_cases hk : k = 0
  · simp [hk]
  · cases h : c.testBit (k - 1) <;> simp [hk, h]

/-! ### Classes of sign vectors -/

/-- The class of a point whose coordinates are `±1` (first coordinate `1`). -/
noncomputable def cls (x : E5) : ℕ :=
  (if x 1 < 0 then 1 else 0) + (if x 2 < 0 then 2 else 0) + (if x 3 < 0 then 4 else 0) +
    (if x 4 < 0 then 8 else 0)

lemma cls_lt (x : E5) : cls x < 16 := by
  unfold cls; split_ifs <;> norm_num

lemma testBit_sum4 (b1 b2 b3 b4 : Bool) :
    (((if b1 then 1 else 0) + (if b2 then 2 else 0) + (if b3 then 4 else 0) +
      (if b4 then 8 else 0) : ℕ).testBit 0 = b1) ∧
    (((if b1 then 1 else 0) + (if b2 then 2 else 0) + (if b3 then 4 else 0) +
      (if b4 then 8 else 0) : ℕ).testBit 1 = b2) ∧
    (((if b1 then 1 else 0) + (if b2 then 2 else 0) + (if b3 then 4 else 0) +
      (if b4 then 8 else 0) : ℕ).testBit 2 = b3) ∧
    (((if b1 then 1 else 0) + (if b2 then 2 else 0) + (if b3 then 4 else 0) +
      (if b4 then 8 else 0) : ℕ).testBit 3 = b4) := by
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

lemma testBit_cls (x : E5) :
    (cls x).testBit 0 = decide (x 1 < 0) ∧ (cls x).testBit 1 = decide (x 2 < 0) ∧
      (cls x).testBit 2 = decide (x 3 < 0) ∧ (cls x).testBit 3 = decide (x 4 < 0) := by
  have hcls : cls x = (if decide (x 1 < 0) then 1 else 0) + (if decide (x 2 < 0) then 2 else 0) +
      (if decide (x 3 < 0) then 4 else 0) + (if decide (x 4 < 0) then 8 else 0) := by
    simp only [cls, decide_eq_true_eq]
  rw [hcls]
  exact testBit_sum4 _ _ _ _

lemma repPt_cls {x : E5} (h0 : x 0 = 1) (h : ∀ j : Fin 5, x j = 1 ∨ x j = -1) :
    repPt (cls x) = x := by
  obtain ⟨t0, t1, t2, t3⟩ := testBit_cls x
  ext j
  rw [repPt, vecZ_apply, rep_cast]
  fin_cases j
  · change sgnB (nb (cls x) 0) = x 0
    rw [show nb (cls x) 0 = false from rfl, h0]; rfl
  · change sgnB (nb (cls x) 1) = x 1
    rw [show nb (cls x) 1 = (cls x).testBit 0 from rfl, t0]; exact sgnB_decide (h 1)
  · change sgnB (nb (cls x) 2) = x 2
    rw [show nb (cls x) 2 = (cls x).testBit 1 from rfl, t1]; exact sgnB_decide (h 2)
  · change sgnB (nb (cls x) 3) = x 3
    rw [show nb (cls x) 3 = (cls x).testBit 2 from rfl, t2]; exact sgnB_decide (h 3)
  · change sgnB (nb (cls x) 4) = x 4
    rw [show nb (cls x) 4 = (cls x).testBit 3 from rfl, t3]; exact sgnB_decide (h 4)

/-! ### Signed permutations -/

/-- `Fin 5` from a natural number. -/
def f5 (k : ℕ) : Fin 5 := ⟨k % 5, Nat.mod_lt _ (by norm_num)⟩

lemma f5_of_lt {k : ℕ} (hk : k < 5) : f5 k = ⟨k, hk⟩ := Fin.ext (Nat.mod_eq_of_lt hk)

/-- The signed permutation `(G x)_j = ε_j x_{p j}`. -/
noncomputable def gmap (p : List ℕ) (ε : ℕ) : E5 →ₗ[ℝ] E5 where
  toFun x := (WithLp.equiv 2 (Fin 5 → ℝ)).symm fun j => sgnB (ε.testBit j) * x (f5 (p.getD j 0))
  map_add' x y := by ext j; simp [mul_add]
  map_smul' r x := by
    ext j; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; simp; ring

lemma gmap_apply (p : List ℕ) (ε : ℕ) (x : E5) (j : Fin 5) :
    gmap p ε x j = sgnB (ε.testBit j) * x (f5 (p.getD j 0)) := rfl

/-- A permutation of `[0, 5)`. -/
def IsPerm5 (p : List ℕ) : Prop := p.length = 5 ∧ p.Nodup ∧ ∀ x ∈ p, x < 5

lemma getD_lt5 {p : List ℕ} (hp : IsPerm5 p) (j : Fin 5) : p.getD j 0 < 5 := by
  obtain ⟨hl, -, hlt⟩ := hp
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact hlt _ (List.getElem_mem _)

lemma f5_getD_inj {p : List ℕ} (hp : IsPerm5 p) :
    Function.Injective fun j : Fin 5 => f5 (p.getD j 0) := by
  intro i j hij
  have hl := hp.1
  simp only [f5_of_lt (getD_lt5 hp i), f5_of_lt (getD_lt5 hp j), Fin.mk.injEq] at hij
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hij
  exact Fin.ext ((List.Nodup.getElem_inj_iff hp.2.1).1 hij)

lemma gmap_injective {p : List ℕ} (hp : IsPerm5 p) (ε : ℕ) : Function.Injective (gmap p ε) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hsurj : Function.Surjective fun j : Fin 5 => f5 (p.getD j 0) :=
    Finite.injective_iff_surjective.1 (f5_getD_inj hp)
  ext i
  obtain ⟨j, rfl⟩ := hsurj i
  have := congrArg (fun y : E5 => y j) hx
  simp only [gmap_apply, PiLp.zero_apply] at this
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (sgnB_ne_zero _)
  · simpa using h

lemma gmap_surjective {p : List ℕ} (hp : IsPerm5 p) (ε : ℕ) : Function.Surjective (gmap p ε) :=
  LinearMap.injective_iff_surjective.1 (gmap_injective hp ε)

lemma testBit_gcls (p : List ℕ) (ε c : ℕ) :
    (gcls p ε c).testBit 0 = xor (gb p ε c 0) (gb p ε c 1) ∧
      (gcls p ε c).testBit 1 = xor (gb p ε c 0) (gb p ε c 2) ∧
      (gcls p ε c).testBit 2 = xor (gb p ε c 0) (gb p ε c 3) ∧
      (gcls p ε c).testBit 3 = xor (gb p ε c 0) (gb p ε c 4) := by
  unfold gcls
  exact testBit_sum4 _ _ _ _

lemma gmap_repPt {p : List ℕ} (hp : IsPerm5 p) (ε c : ℕ) :
    gmap p ε (repPt c) = sgnB (gb p ε c 0) • repPt (gcls p ε c) := by
  have hcoord : ∀ j : Fin 5, gmap p ε (repPt c) j = sgnB (gb p ε c j) := by
    intro j
    rw [gmap_apply, repPt, vecZ_apply, f5_of_lt (getD_lt5 hp j), rep_cast, gb, sgnB_xor]
  obtain ⟨t0, t1, t2, t3⟩ := testBit_gcls p ε c
  ext j
  rw [hcoord, PiLp.smul_apply, smul_eq_mul, repPt, vecZ_apply, rep_cast]
  fin_cases j
  · change sgnB (gb p ε c 0) = sgnB (gb p ε c 0) * sgnB (nb (gcls p ε c) 0)
    rw [show nb (gcls p ε c) 0 = false from rfl]; simp [sgnB]
  · change sgnB (gb p ε c 1) = sgnB (gb p ε c 0) * sgnB (nb (gcls p ε c) 1)
    rw [show nb (gcls p ε c) 1 = (gcls p ε c).testBit 0 from rfl, t0, sgnB_mul_xor]
  · change sgnB (gb p ε c 2) = sgnB (gb p ε c 0) * sgnB (nb (gcls p ε c) 2)
    rw [show nb (gcls p ε c) 2 = (gcls p ε c).testBit 1 from rfl, t1, sgnB_mul_xor]
  · change sgnB (gb p ε c 3) = sgnB (gb p ε c 0) * sgnB (nb (gcls p ε c) 3)
    rw [show nb (gcls p ε c) 3 = (gcls p ε c).testBit 2 from rfl, t2, sgnB_mul_xor]
  · change sgnB (gb p ε c 4) = sgnB (gb p ε c 0) * sgnB (nb (gcls p ε c) 4)
    rw [show nb (gcls p ε c) 4 = (gcls p ε c).testBit 3 from rfl, t3, sgnB_mul_xor]

/-! ### The table and the classes of a mask -/

lemma mem_clsOf {M k : ℕ} : k ∈ clsOf M ↔ k < 16 ∧ M.testBit k = true := by
  simp [clsOf]

lemma nodup_clsOf (M : ℕ) : (clsOf M).Nodup := List.Nodup.filter _ List.nodup_range

lemma entry_ok_spec {reps : List (List ℕ)} {e : Entry} (h : e.ok reps = true) :
    e.r < reps.length ∧ IsPerm5 e.p ∧
      ((clsOf e.M).map (gcls e.p e.ε)).insertionSort (· ≤ ·) = reps.getD e.r [] := by
  simp only [Entry.ok, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h3, ⟨h4, h5, h6⟩, h7⟩

/-- The functional `x ↦ Σ n_j x_j`. -/
noncomputable def linZ (n : ℕ → ℤ) : E5 →ₗ[ℝ] ℝ where
  toFun x := ∑ j : Fin 5, (n j : ℝ) * x j
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

lemma linZ_repPt (n : ℕ → ℤ) (c : ℕ) :
    linZ n (repPt c) = ((sum5 fun j => n j * rep c j : ℤ) : ℝ) := by
  simp only [linZ, LinearMap.coe_mk, AddHom.coe_mk, repPt, vecZ_apply, sum5_cast]
  push_cast
  rfl

/-! ### The scan covers every mask with eight classes -/

lemma scan_sound {reps : List (List ℕ)} : ∀ {n M : ℕ} {es : List Entry}, scan reps M n es = true →
    ∀ M', M ≤ M' → M' < M + n → (clsOf M').length = 8 → ∃ e ∈ es, e.M = M' ∧ e.ok reps = true
  | 0, _, _, _, _, h1, h2, _ => by omega
  | n + 1, M, es, h, M', h1, h2, h8 => by
    unfold scan at h
    by_cases hc : (clsOf M).length = 8
    · rw [if_pos (by simpa using hc)] at h
      cases es with
      | nil => simp at h
      | cons e es =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨heM, he⟩, hrest⟩ := h
        by_cases hM : M' = M
        · exact ⟨e, List.mem_cons_self .., by rw [heM, hM], he⟩
        · obtain ⟨e', he', h'⟩ := scan_sound hrest M' (by omega) (by omega) h8
          exact ⟨e', List.mem_cons_of_mem _ he', h'⟩
    · rw [if_neg (by simpa using hc)] at h
      have hM : M' ≠ M := fun h => hc (h ▸ h8)
      exact scan_sound h M' (by omega) (by omega) h8

/-- Thirty-two scans of width `2048` cover all masks below `2¹⁶`. -/
lemma cover_of_scans {reps : List (List ℕ)} {tabs : List (List Entry)}
    (h : ∀ k < 32, scan reps (2048 * k) 2048 (tabs.getD k []) = true) :
    ∀ M < 2 ^ 16, (clsOf M).length = 8 → ∃ e : Entry, e.M = M ∧ e.ok reps = true := by
  intro M hM h8
  have hM' : M < 65536 := by simpa using hM
  obtain ⟨e, -, he⟩ := scan_sound (h (M / 2048) (by omega)) M (by omega) (by omega) h8
  exact ⟨e, he⟩

/-! ### The reduction -/

/-- **Cube polytopes.**  Eight points `y_v ∈ {±1}⁵` with `±y_v` distinct and spanning: at least
`243` nonempty faces — given a table carrying every mask with eight classes onto a
representative, and a certificate for every representative. -/
theorem core (reps : List (List ℕ)) (certs : List RepCert)
    (hcerts : ∀ k < reps.length, (certs.getD k (.nonspan [])).ok (reps.getD k []) = true)
    (htab : ∀ M < 2 ^ 16, (clsOf M).length = 8 → ∃ e : Entry, e.M = M ∧ e.ok reps = true)
    {y : Fin 8 → E5} (hq : ∀ v (j : Fin 5), y v j = 1 ∨ y v j = -1)
    (hinj : Function.Injective (pm16 y))
    (hspan : ∀ φ : E5 →ₗ[ℝ] ℝ, (∀ x ∈ range (pm16 y), φ x = 0) → φ = 0) :
    243 ≤ (faces (convexHull ℝ (range (pm16 y)))).ncard := by
  classical
  -- normalize the first coordinate
  set x : Fin 8 → E5 := fun v => y v 0 • y v with hx
  have hx0 : ∀ v, x v 0 = 1 := by
    intro v; simp only [hx, PiLp.smul_apply, smul_eq_mul]
    rcases hq v 0 with h | h <;> rw [h] <;> norm_num
  have hxq : ∀ v j, x v j = 1 ∨ x v j = -1 := by
    intro v j; simp only [hx, PiLp.smul_apply, smul_eq_mul]
    rcases hq v 0 with h | h <;> rcases hq v j with h' | h' <;> rw [h, h'] <;> norm_num
  have hyx : ∀ v, y v = y v 0 • x v := by
    intro v; simp only [hx, smul_smul]
    rcases hq v 0 with h | h <;> rw [h] <;> norm_num
  set c : Fin 8 → ℕ := fun v => cls (x v) with hc
  have hrep : ∀ v, repPt (c v) = x v := fun v => repPt_cls (hx0 v) (hxq v)
  -- the classes are distinct
  have hcinj : Function.Injective c := by
    intro v w hvw
    have hxx : x v = x w := by rw [← hrep v, ← hrep w]; exact congrArg repPt hvw
    rcases hq v 0 with hv | hv <;> rcases hq w 0 with hw | hw
    · have h := hinj (show pm16 y ⟨v, by omega⟩ = pm16 y ⟨w, by omega⟩ by
        rw [pm16_lo, pm16_lo, hyx v, hyx w, hv, hw, hxx])
      exact Fin.ext (by simpa using congrArg Fin.val h)
    · have h := hinj (show pm16 y ⟨v, by omega⟩ = pm16 y ⟨w + 8, by omega⟩ by
        rw [pm16_lo, pm16_hi, hyx v, hyx w, hv, hw, hxx]; simp)
      have := congrArg Fin.val h; simp at this; omega
    · have h := hinj (show pm16 y ⟨v + 8, by omega⟩ = pm16 y ⟨w, by omega⟩ by
        rw [pm16_hi, pm16_lo, hyx v, hyx w, hv, hw, hxx]; simp)
      have := congrArg Fin.val h; simp at this; omega
    · have h := hinj (show pm16 y ⟨v, by omega⟩ = pm16 y ⟨w, by omega⟩ by
        rw [pm16_lo, pm16_lo, hyx v, hyx w, hv, hw, hxx])
      exact Fin.ext (by simpa using congrArg Fin.val h)
  -- the mask of the classes
  set M := maskOf 16 (fun k => decide (∃ v, c v = k)) with hM
  have hmemM : ∀ k, k ∈ clsOf M ↔ ∃ v, c v = k := by
    intro k
    rw [mem_clsOf, hM, testBit_maskOf]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨-, -, h⟩; exact h
    · rintro ⟨v, rfl⟩; exact ⟨cls_lt _, cls_lt _, v, rfl⟩
  have hlen : (clsOf M).length = 8 := by
    have hfs : (clsOf M).toFinset = Finset.univ.image c := by
      ext k; simp [hmemM]
    rw [← List.toFinset_card_of_nodup (nodup_clsOf M), hfs, Finset.card_image_of_injective _ hcinj]
    simp
  -- the table entry
  obtain ⟨e, heM, he⟩ := htab M (maskOf_lt _) hlen
  obtain ⟨hr, hp, hsort⟩ := entry_ok_spec he
  rw [heM] at hsort
  set R := reps.getD e.r [] with hR
  have hperm : ((clsOf M).map (gcls e.p e.ε)).Perm R := by
    rw [← hsort]; exact (List.perm_insertionSort _ _).symm
  have hRlen : R.length = 8 := by rw [← hperm.length_eq, List.length_map, hlen]
  have hRmem : ∀ v, ∃ u : Fin 8, R.getD u 0 = gcls e.p e.ε (c v) := by
    intro v
    obtain ⟨i, hi, hi'⟩ := List.mem_iff_getElem.1
      (hperm.subset (List.mem_map.2 ⟨c v, (hmemM _).2 ⟨v, rfl⟩, rfl⟩))
    exact ⟨⟨i, by omega⟩, by rw [List.getD_eq_getElem _ _ hi]; exact hi'⟩
  -- the signed permutation carries the points onto the representative's
  set G := gmap e.p e.ε with hG
  have hGinj : Function.Injective G := gmap_injective hp e.ε
  have hGy : ∀ v, ∃ u, G (y v) = pts R u ∨ G (y v) = -pts R u := by
    intro v
    obtain ⟨u, hu⟩ := hRmem v
    refine ⟨u, ?_⟩
    rw [hyx v, map_smul, ← hrep v, hG, gmap_repPt hp, smul_smul, pts, hu]
    rcases hq v 0 with h | h <;> cases gb e.p e.ε (c v) 0 <;> simp [h, sgnB]
  have hsub : G '' range (pm16 y) ⊆ range (pm16 (pts R)) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨v, rfl | rfl⟩ := mem_range_pm16.1 hz
    · exact mem_range_pm16.2 (hGy v)
    · obtain ⟨u, h | h⟩ := hGy v
      · exact mem_range_pm16.2 ⟨u, Or.inr (by rw [map_neg, h])⟩
      · exact mem_range_pm16.2 ⟨u, Or.inl (by rw [map_neg, h, neg_neg])⟩
  have hcard1 : (G '' range (pm16 y)).ncard = 16 := by
    rw [Set.ncard_image_of_injective _ hGinj, Set.ncard_range_of_injective hinj]; simp
  have hcard2 : (range (pm16 (pts R))).ncard ≤ 16 := by
    rw [← Set.image_univ]
    refine (Set.ncard_image_le Set.finite_univ).trans ?_
    simp [Set.ncard_univ]
  have hrange : G '' range (pm16 y) = range (pm16 (pts R)) :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.finite_range _)
  have htransfer : (faces (convexHull ℝ (range (pm16 (pts R))))).ncard =
      (faces (convexHull ℝ (range (pm16 y)))).ncard := by
    rw [← hrange, ← LinearMap.image_convexHull, ncard_faces_image_of_injective _ hGinj]
  -- the certificate of the representative
  have hck := hcerts e.r hr
  rw [← hR] at hck
  rcases hcert : certs.getD e.r (.nonspan []) with n | ws
  · -- a non-spanning representative contradicts spanning
    rw [hcert] at hck
    exfalso
    simp only [RepCert.ok, Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range,
      bne_iff_ne, ne_eq, beq_iff_eq] at hck
    obtain ⟨⟨j, hj, hnj⟩, hperp⟩ := hck
    have hz : ∀ u : Fin 8, linZ (fun j => n.getD j 0) (pts R u) = 0 := by
      intro u
      rw [pts, linZ_repPt, hperp u u.2]
      simp
    have hφ := hspan ((linZ fun j => n.getD j 0).comp G) fun z hz' => by
      obtain ⟨i, hi⟩ := hsub ⟨z, hz', rfl⟩
      rw [LinearMap.comp_apply, ← hi]
      obtain ⟨u, h | h⟩ := mem_range_pm16.1 ⟨i, rfl⟩
      · rw [h, hz]
      · rw [h, map_neg, hz, neg_zero]
    obtain ⟨w, hw⟩ := gmap_surjective hp e.ε (EuclideanSpace.single ⟨j, hj⟩ 1)
    have h1 := congrArg (fun f : E5 →ₗ[ℝ] ℝ => f w) hφ
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h1
    have hw' : G w = EuclideanSpace.single ⟨j, hj⟩ 1 := hw
    rw [hw'] at h1
    simp only [linZ, LinearMap.coe_mk, AddHom.coe_mk, EuclideanSpace.single_apply] at h1
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    exact hnj (by exact_mod_cast h1)
  · rw [hcert] at hck
    have := faces_of_cert hck
    omega

end Kalai5.Cube5
