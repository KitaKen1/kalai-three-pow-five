import Kalai5.Gale.ClassifyQ
import Kalai5.Polar.Intervals
import Kalai5.Rows.Dual

/-!
# The product of two triangles is recognized by its row

**Theorem** (`prodTri_structure`): a 4-polytope with row `qRow = (9,18,15,6; 36)` is combinatorially
`Δ2 × Δ2`: its vertices are `x a b` (`a, b : Fin 3`) and it has facets `R i`, `C j` with
`x a b ∈ R i ↔ a ≠ i` and `x a b ∈ C j ↔ b ≠ j`.

Proof: its polar has row `qDualRow`, so its facets are the `2 + 2` sets for a 3-set `U` of its
six vertices (`Gale.qDual_facets_labelled`); dual faces reverse inclusion.
-/

namespace Kalai5

open Set

/-- Row of the product of two triangles. -/
def qRow : Row := ⟨9, 18, 15, 6, 36⟩

variable {d : ℕ}

/-! ### Dual faces reverse inclusion -/

section dualInc

variable {V : Finset (E d)} (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d))))
include h0

lemma dualFace_subset_iff {F G : Set (E d)} (hF : F ∈ faces (convexHull ℝ (V : Set (E d))))
    (hFne : F ≠ convexHull ℝ (V : Set (E d))) (hG : G ∈ faces (convexHull ℝ (V : Set (E d))))
    (hGne : G ≠ convexHull ℝ (V : Set (E d))) :
    dualFace (convexHull ℝ (V : Set (E d))) G ⊆ dualFace (convexHull ℝ (V : Set (E d))) F ↔
      F ⊆ G := by
  constructor
  · intro h
    have := dualFace_antitone (K := polarSet (convexHull ℝ (V : Set (E d)))) h
    rwa [dualFace_dualFace h0 hF hFne, dualFace_dualFace h0 hG hGne] at this
  · exact fun h => dualFace_antitone h

lemma dualFace_inj {F G : Set (E d)} (hF : F ∈ faces (convexHull ℝ (V : Set (E d))))
    (hFne : F ≠ convexHull ℝ (V : Set (E d))) (hG : G ∈ faces (convexHull ℝ (V : Set (E d))))
    (hGne : G ≠ convexHull ℝ (V : Set (E d)))
    (h : dualFace (convexHull ℝ (V : Set (E d))) F = dualFace (convexHull ℝ (V : Set (E d))) G) :
    F = G := by
  rw [← dualFace_dualFace h0 hF hFne, ← dualFace_dualFace h0 hG hGne, h]

end dualInc

/-- A singleton face is a vertex. -/
lemma mem_extremePoints_of_singleton_face {K : Set (E d)} {z : E d} (h : ({z} : Set (E d)) ∈ faces K) :
    z ∈ K.extremePoints ℝ :=
  isExtreme_singleton.1 h.2.isExtreme

/-! ### The `2 + 2` index sets -/

section sets

variable {U : Finset (Fin 6)} (hU : U.card = 3)
include hU

lemma card_compl_three : Uᶜ.card = 3 := by
  rw [Finset.card_compl, hU, Fintype.card_fin]

/-- Enumeration of `U`. -/
noncomputable def enumU : Fin 3 → Fin 6 := fun a => U.orderEmbOfFin hU a

/-- Enumeration of the complement of `U`. -/
noncomputable def enumW : Fin 3 → Fin 6 := fun b => Uᶜ.orderEmbOfFin (card_compl_three hU) b

lemma enumU_mem (a : Fin 3) : enumU hU a ∈ U := Finset.orderEmbOfFin_mem U hU a

lemma enumW_mem (b : Fin 3) : enumW hU b ∈ Uᶜ := Finset.orderEmbOfFin_mem Uᶜ _ b

lemma enumU_inj : Function.Injective (enumU hU) := (U.orderEmbOfFin hU).injective

lemma enumW_inj : Function.Injective (enumW hU) := (Uᶜ.orderEmbOfFin _).injective

lemma exists_enumU {p : Fin 6} (hp : p ∈ U) : ∃ a, enumU hU a = p := by
  have : p ∈ Set.range (U.orderEmbOfFin hU) := by
    rw [Finset.range_orderEmbOfFin]; exact hp
  obtain ⟨a, ha⟩ := this
  exact ⟨a, ha⟩

lemma exists_enumW {q : Fin 6} (hq : q ∈ Uᶜ) : ∃ b, enumW hU b = q := by
  have : q ∈ Set.range (Uᶜ.orderEmbOfFin (card_compl_three hU)) := by
    rw [Finset.range_orderEmbOfFin]; exact hq
  obtain ⟨b, hb⟩ := this
  exact ⟨b, hb⟩

/-- The `2 + 2` set omitting `enumU a` and `enumW b`. -/
noncomputable def setS (a b : Fin 3) : Finset (Fin 6) := U.erase (enumU hU a) ∪ Uᶜ.erase (enumW hU b)

lemma mem_setS_U (a b i : Fin 3) : enumU hU i ∈ setS hU a b ↔ i ≠ a := by
  unfold setS
  rw [Finset.mem_union, Finset.mem_erase, Finset.mem_erase]
  have hi := enumU_mem hU i
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact fun hia => h (by rw [hia])
    · exact absurd hi (Finset.mem_compl.1 h)
  · intro h
    exact Or.inl ⟨fun he => h (enumU_inj hU he), hi⟩

lemma mem_setS_W (a b j : Fin 3) : enumW hU j ∈ setS hU a b ↔ j ≠ b := by
  unfold setS
  rw [Finset.mem_union, Finset.mem_erase, Finset.mem_erase]
  have hj := enumW_mem hU j
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd h (Finset.mem_compl.1 hj)
    · exact fun hjb => h (by rw [hjb])
  · intro h
    exact Or.inr ⟨fun he => h (enumW_inj hU he), hj⟩

lemma setS_inter (a b : Fin 3) : setS hU a b ∩ U = U.erase (enumU hU a) := by
  unfold setS
  ext i
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_erase, Finset.mem_compl]
  tauto

lemma setS_sdiff (a b : Fin 3) : setS hU a b \ U = Uᶜ.erase (enumW hU b) := by
  unfold setS
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_erase, Finset.mem_compl]
  tauto

lemma setS_card (a b : Fin 3) : (setS hU a b ∩ U).card = 2 ∧ (setS hU a b \ U).card = 2 := by
  rw [setS_inter, setS_sdiff, Finset.card_erase_of_mem (enumU_mem hU a),
    Finset.card_erase_of_mem (enumW_mem hU b), hU, card_compl_three hU]
  exact ⟨rfl, rfl⟩

lemma setS_inj {a b a' b' : Fin 3} (h : setS hU a b = setS hU a' b') : a = a' ∧ b = b' := by
  constructor
  · by_contra hne
    have h1 := (mem_setS_U hU a b a').2 (Ne.symm hne)
    rw [h] at h1
    exact (mem_setS_U hU a' b' a').1 h1 rfl
  · by_contra hne
    have h1 := (mem_setS_W hU a b b').2 (Ne.symm hne)
    rw [h] at h1
    exact (mem_setS_W hU a' b' b').1 h1 rfl

lemma exists_setS {S : Finset (Fin 6)} (h1 : (S ∩ U).card = 2) (h2 : (S \ U).card = 2) :
    ∃ a b, S = setS hU a b := by
  -- the point of `U` missing from `S`
  have hc1 : (U \ S).card = 1 := by
    have := Finset.card_sdiff_add_card_inter U S
    rw [Finset.inter_comm] at h1
    omega
  have hc2 : (Uᶜ \ S).card = 1 := by
    have e : S \ U = S ∩ Uᶜ := by ext i; simp
    have := Finset.card_sdiff_add_card_inter Uᶜ S
    rw [Finset.inter_comm, ← e, h2, card_compl_three hU] at this
    omega
  obtain ⟨p, hp⟩ := Finset.card_eq_one.1 hc1
  obtain ⟨q, hq⟩ := Finset.card_eq_one.1 hc2
  have hpU : p ∈ U := (Finset.mem_sdiff.1 (hp ▸ Finset.mem_singleton_self p)).1
  have hqU : q ∈ Uᶜ := (Finset.mem_sdiff.1 (hq ▸ Finset.mem_singleton_self q)).1
  obtain ⟨a, ha⟩ := exists_enumU hU hpU
  obtain ⟨b, hb⟩ := exists_enumW hU hqU
  refine ⟨a, b, ?_⟩
  ext i
  unfold setS
  rw [ha, hb, Finset.mem_union, Finset.mem_erase, Finset.mem_erase]
  by_cases hi : i ∈ U
  · have : i ∈ U \ S ↔ i = p := by rw [hp, Finset.mem_singleton]
    rw [Finset.mem_sdiff] at this
    have hiU' : i ∉ Uᶜ := by simpa using hi
    constructor
    · intro hiS
      exact Or.inl ⟨fun hip => (this.2 hip).2 hiS, hi⟩
    · rintro (⟨hip, -⟩ | ⟨-, h⟩)
      · by_contra hiS
        exact hip (this.1 ⟨hi, hiS⟩)
      · exact absurd h hiU'
  · have hiU' : i ∈ Uᶜ := by simpa using hi
    have : i ∈ Uᶜ \ S ↔ i = q := by rw [hq, Finset.mem_singleton]
    rw [Finset.mem_sdiff] at this
    constructor
    · intro hiS
      exact Or.inr ⟨fun hiq => (this.2 hiq).2 hiS, hiU'⟩
    · rintro (⟨-, h⟩ | ⟨hiq, -⟩)
      · exact absurd h hi
      · by_contra hiS
        exact hiq (this.1 ⟨hiU', hiS⟩)

end sets

/-! ### The structure theorem -/

set_option maxHeartbeats 1000000 in
/-- **A 4-polytope with row `(9,18,15,6; 36)` is combinatorially `Δ2 × Δ2`.** -/
theorem prodTri_structure {k : ℕ} (hk : k = 4) {V : Finset (E k)}
    (h0 : (0 : E k) ∈ interior (convexHull ℝ (V : Set (E k))))
    (hrow : rowOf (convexHull ℝ (V : Set (E k))) = qRow) :
    ∃ (x : Fin 3 → Fin 3 → E k) (R C : Fin 3 → Set (E k)),
      (∀ a b a' b', x a b = x a' b' → a = a' ∧ b = b') ∧
      (∀ a b, x a b ∈ (convexHull ℝ (V : Set (E k))).extremePoints ℝ) ∧
      (∀ z ∈ (convexHull ℝ (V : Set (E k))).extremePoints ℝ, ∃ a b, z = x a b) ∧
      (∀ i, R i ∈ faces (convexHull ℝ (V : Set (E k))) ∧ dim (R i) = 3) ∧
      (∀ j, C j ∈ faces (convexHull ℝ (V : Set (E k))) ∧ dim (C j) = 3) ∧
      (∀ a b i, x a b ∈ R i ↔ a ≠ i) ∧ (∀ a b j, x a b ∈ C j ↔ b ≠ j) := by
  subst hk
  classical
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have h0W : (0 : E 4) ∈ interior (convexHull ℝ (W : Set (E 4))) :=
    hW ▸ zero_mem_interior_polarSet V
  have hbip : polarSet (convexHull ℝ (W : Set (E 4))) = convexHull ℝ (V : Set (E 4)) := by
    rw [← hW]
    exact polarSet_polarSet (convex_convexHull ℝ _)
      (Set.Finite.isClosed_convexHull ℝ V.finite_toSet) (interior_subset h0)
  have hdimK : dim (convexHull ℝ (V : Set (E 4))) = 4 :=
    dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0⟩
  have hdimW : dim (convexHull ℝ (W : Set (E 4))) = 4 :=
    dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0W⟩
  -- the row of the polar
  have hrowW : rowOf (convexHull ℝ (W : Set (E 4))) = qDualRow := by
    have e0 := fvec_polarSet_eq h0 3 (by norm_num)
    have e1 := fvec_polarSet_eq h0 2 (by norm_num)
    have e2 := fvec_polarSet_eq h0 1 (by norm_num)
    have e3 := fvec_polarSet_eq h0 0 (by norm_num)
    have eJ := flag2_polarSet_eq h0 0 3 (by norm_num) (by norm_num)
    rw [hW] at e0 e1 e2 e3 eJ
    norm_num at e0 e1 e2 e3 eJ
    have hq := hrow
    simp only [rowOf, qRow, Row.mk.injEq] at hq
    simp only [rowOf, qDualRow, e0, e1, e2, e3, eJ, hq]
  -- label the vertices of the polar
  have hX := extremePoints_finite W
  set Xs := hX.toFinset with hXs
  have hcard : Xs.card = 6 := by
    have h1 : fvec (convexHull ℝ (W : Set (E 4))) 0 = 6 := congrArg Row.n hrowW
    rw [fvec_zero_eq, Set.ncard_eq_toFinset_card _ hX] at h1
    exact h1
  let Wl : Fin 6 → E 4 := fun i => (Xs.equivFin.symm ((finCongr hcard).symm i) : E 4)
  have hinj : Function.Injective Wl := fun i j h =>
    (finCongr hcard).symm.injective (Xs.equivFin.symm.injective (Subtype.ext h))
  have hrange : range Wl = (convexHull ℝ (W : Set (E 4))).extremePoints ℝ := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact hX.mem_toFinset.1 (Xs.equivFin.symm _).2
    · intro hz
      refine ⟨finCongr hcard (Xs.equivFin ⟨z, hX.mem_toFinset.2 hz⟩), ?_⟩
      simp [Wl]
  have hconvW : convexHull ℝ (range Wl) = convexHull ℝ (W : Set (E 4)) := by
    rw [hrange]; exact convexHull_extremePoints_eq W
  have hext : ∀ j, Wl j ∈ (convexHull ℝ (range Wl)).extremePoints ℝ := by
    intro j; rw [hconvW, ← hrange]; exact mem_range_self j
  have hspan : affineSpan ℝ (range Wl) = ⊤ := by
    rw [← affineSpan_convexHull, hconvW]
    exact (convex_convexHull ℝ _).interior_nonempty_iff_affineSpan_eq_top.1 ⟨0, h0W⟩
  obtain ⟨σ, U, hU3, hfac⟩ := Gale.qDual_facets_labelled (by norm_num) hinj hext hspan
    (by rw [hconvW]; exact hrowW)
  set Y := Wl ∘ σ with hY
  have hYrange : range Y = range Wl := EquivLike.range_comp Wl σ
  have hconvY : convexHull ℝ (range Y) = convexHull ℝ (W : Set (E 4)) := by rw [hYrange, hconvW]
  have hYext : ∀ i, Y i ∈ (convexHull ℝ (W : Set (E 4))).extremePoints ℝ := fun i => by
    rw [← hrange]; exact ⟨σ i, rfl⟩
  -- the facets of the polar, indexed by `Fin 3 × Fin 3`
  set Φ : Fin 3 → Fin 3 → Set (E 4) := fun a b => convexHull ℝ (Y '' ↑(setS hU3 a b)) with hΦ
  have hΦface : ∀ a b, Φ a b ∈ faces (convexHull ℝ (W : Set (E 4))) ∧ dim (Φ a b) = 3 ∧
      Gale.idx Y (Φ a b) = setS hU3 a b := by
    intro a b
    obtain ⟨hne, hfi, hd⟩ := (hfac (setS hU3 a b)).2 (setS_card hU3 a b)
    have hmem := Gale.conv_mem_faces hne hfi
    rw [hconvY] at hmem
    exact ⟨hmem.1, by rw [Gale.dim_convexHull]; exact hd, hmem.2⟩
  have hΦne : ∀ a b, Φ a b ≠ convexHull ℝ (W : Set (E 4)) := fun a b h => by
    have := (hΦface a b).2.1
    rw [h, hdimW] at this
    omega
  -- the vertices of `K` are the dual faces of the facets of the polar
  have hD : ∀ a b, ∃ p, dualFace (convexHull ℝ (W : Set (E 4))) (Φ a b) = {p} := by
    intro a b
    have hmem := dualFace_mem_faces h0W (hΦface a b).1 (hΦne a b)
    have hdd := dim_dualFace h0W (hΦface a b).1 (hΦne a b)
    rw [(hΦface a b).2.1] at hdd
    exact eq_singleton_of_dim_eq_zero hmem.1 (by omega)
  choose x hx using hD
  have hDface : ∀ a b, dualFace (convexHull ℝ (W : Set (E 4))) (Φ a b) ∈
      faces (convexHull ℝ (V : Set (E 4))) := fun a b => by
    rw [← hbip]; exact dualFace_mem_faces h0W (hΦface a b).1 (hΦne a b)
  -- the facets of `K` are the dual faces of the vertices of the polar
  have hvface : ∀ i, ({Y i} : Set (E 4)) ∈ faces (convexHull ℝ (W : Set (E 4))) := fun i =>
    singleton_mem_faces_of_extreme (hYext i)
  have hvne : ∀ i, ({Y i} : Set (E 4)) ≠ convexHull ℝ (W : Set (E 4)) := fun i h => by
    have := dim_singleton (Y i)
    rw [h, hdimW] at this
    omega
  have hRface : ∀ i, dualFace (convexHull ℝ (W : Set (E 4))) {Y i} ∈
      faces (convexHull ℝ (V : Set (E 4))) ∧
      dim (dualFace (convexHull ℝ (W : Set (E 4))) {Y i}) = 3 := by
    intro i
    have hmem := dualFace_mem_faces h0W (hvface i) (hvne i)
    have hdd := dim_dualFace h0W (hvface i) (hvne i)
    rw [dim_singleton] at hdd
    rw [hbip] at hmem
    exact ⟨hmem, by omega⟩
  -- incidences
  have hinc : ∀ a b i, x a b ∈ dualFace (convexHull ℝ (W : Set (E 4))) {Y i} ↔
      i ∈ setS hU3 a b := by
    intro a b i
    rw [← Set.singleton_subset_iff, ← hx a b,
      dualFace_subset_iff h0W (hvface i) (hvne i) (hΦface a b).1 (hΦne a b),
      Set.singleton_subset_iff, ← (hΦface a b).2.2, Gale.mem_idx]
  refine ⟨x, fun i => dualFace (convexHull ℝ (W : Set (E 4))) {Y (enumU hU3 i)},
    fun j => dualFace (convexHull ℝ (W : Set (E 4))) {Y (enumW hU3 j)}, ?_, ?_, ?_,
    fun i => hRface _, fun j => hRface _, ?_, ?_⟩
  · -- injectivity
    intro a b a' b' h
    have h1 : dualFace (convexHull ℝ (W : Set (E 4))) (Φ a b) =
        dualFace (convexHull ℝ (W : Set (E 4))) (Φ a' b') := by rw [hx, hx, h]
    have h2 := dualFace_inj h0W (hΦface a b).1 (hΦne a b) (hΦface a' b').1 (hΦne a' b') h1
    have h3 : setS hU3 a b = setS hU3 a' b' := by
      rw [← (hΦface a b).2.2, ← (hΦface a' b').2.2, h2]
    exact setS_inj hU3 h3
  · -- the points are vertices
    intro a b
    have := hDface a b
    rw [hx] at this
    exact mem_extremePoints_of_singleton_face this
  · -- every vertex is labelled
    intro z hz
    have hzf : ({z} : Set (E 4)) ∈ faces (convexHull ℝ (V : Set (E 4))) :=
      singleton_mem_faces_of_extreme hz
    have hzne : ({z} : Set (E 4)) ≠ convexHull ℝ (V : Set (E 4)) := fun h => by
      have := dim_singleton z
      rw [h, hdimK] at this
      omega
    have hG := dualFace_mem_faces h0 hzf hzne
    have hGd := dim_dualFace h0 hzf hzne
    rw [dim_singleton] at hGd
    rw [hW] at hG
    set G := dualFace (convexHull ℝ (V : Set (E 4))) {z} with hGdef
    have hG' : G ∈ faces (convexHull ℝ (range Y)) := by rw [hconvY]; exact hG
    have hGeq := Gale.face_eq_conv_idx hG'
    have hidx := (hfac (Gale.idx Y G)).1 ⟨Gale.idx_nonempty hG', Gale.isFaceIdx_idx hG', by
      rw [← Gale.dim_convexHull, ← hGeq]; omega⟩
    obtain ⟨a, b, hab⟩ := exists_setS hU3 hidx.1 hidx.2
    refine ⟨a, b, ?_⟩
    have hGΦ : G = Φ a b := by rw [hGeq, hab]
    have hzz := dualFace_dualFace h0 hzf hzne
    rw [← hGdef, hW, hGΦ, hx] at hzz
    exact (Set.singleton_eq_singleton_iff.1 hzz).symm
  · intro a b i
    rw [hinc, mem_setS_U, ne_comm]
  · intro a b j
    rw [hinc, mem_setS_W, ne_comm]

end Kalai5
