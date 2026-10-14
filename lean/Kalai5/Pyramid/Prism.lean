import Kalai5.Polar.General

/-!
# Faces of a prism `A × [-1,1]`

Write points of `E (n+1)` as `(y, t)` with `y = fstPart z ∈ E n`, `t = z (last)`.  A linear
functional splits as `⟪y, c'⟫ + γ t`, so its maximizers on `A × [-1,1]` form the product of the
maximizers on `A` and on `[-1,1]`.  Hence the faces of the prism are exactly the sets `F × G`,
`F` a face of `A`, `G ∈ {{1}, {-1}, [-1,1]}` (`ncard_faces_prism`: `s(prism) = 3 s(A)`).
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

/-- The first `n` coordinates. -/
def fstPart (z : E (n + 1)) : E n := WithLp.toLp 2 (fun i => z (Fin.castSucc i))

/-- The point with first coordinates `y` and last coordinate `t`. -/
def mkPt (y : E n) (t : ℝ) : E (n + 1) := WithLp.toLp 2 (Fin.snoc (fun i => y i) t)

@[simp] lemma fstPart_apply (z : E (n + 1)) (i : Fin n) : fstPart z i = z i.castSucc := rfl

@[simp] lemma mkPt_castSucc (y : E n) (t : ℝ) (i : Fin n) : mkPt y t i.castSucc = y i := by
  simp [mkPt]

@[simp] lemma mkPt_last (y : E n) (t : ℝ) : mkPt y t (Fin.last n) = t := by
  simp [mkPt]

@[simp] lemma fstPart_mkPt (y : E n) (t : ℝ) : fstPart (mkPt y t) = y := by
  refine PiLp.ext fun i => ?_
  simp

lemma inner_split (z c : E (n + 1)) :
    ⟪z, c⟫ = ⟪fstPart z, fstPart c⟫ + z (Fin.last n) * c (Fin.last n) := by
  simp [PiLp.inner_apply, Fin.sum_univ_castSucc, mul_comm]

/-- The prism `A × [-1,1]`. -/
def prism (A : Set (E n)) : Set (E (n + 1)) :=
  {z | fstPart z ∈ A ∧ -1 ≤ z (Fin.last n) ∧ z (Fin.last n) ≤ 1}

/-- The three nonempty faces of `[-1,1]`. -/
def segFace : Fin 3 → Set ℝ
  | 0 => {1}
  | 1 => {-1}
  | 2 => Icc (-1) 1

lemma segFace_nonempty (k : Fin 3) : (segFace k).Nonempty := by
  fin_cases k
  · exact ⟨1, rfl⟩
  · exact ⟨-1, rfl⟩
  · exact ⟨0, by norm_num [segFace]⟩

lemma segFace_subset (k : Fin 3) : segFace k ⊆ Icc (-1) 1 := by
  fin_cases k <;> intro t ht <;> simp_all [segFace] <;> norm_num

/-- The slope exposing `segFace k`. -/
def segSlope : Fin 3 → ℝ
  | 0 => 1
  | 1 => -1
  | 2 => 0

/-- `segFace k` is the set of maximizers of `t ↦ segSlope k * t` on `[-1,1]`. -/
lemma mem_segFace_iff (k : Fin 3) (t : ℝ) :
    t ∈ segFace k ↔ (-1 ≤ t ∧ t ≤ 1) ∧ ∀ s, -1 ≤ s → s ≤ 1 → segSlope k * s ≤ segSlope k * t := by
  fin_cases k
  · simp only [segFace, segSlope, mem_singleton_iff, one_mul]
    constructor
    · rintro rfl; exact ⟨⟨by norm_num, le_rfl⟩, fun s _ hs => hs⟩
    · rintro ⟨⟨-, h1⟩, h⟩; exact le_antisymm h1 (h 1 (by norm_num) le_rfl)
  · simp only [segFace, segSlope, mem_singleton_iff, neg_mul, one_mul, neg_le_neg_iff]
    constructor
    · rintro rfl; exact ⟨⟨le_rfl, by norm_num⟩, fun s hs _ => hs⟩
    · rintro ⟨⟨h1, -⟩, h⟩; exact le_antisymm (h (-1) le_rfl (by norm_num)) h1
  · simp only [segFace, segSlope, mem_Icc, zero_mul, le_refl, implies_true, and_true]

/-- Maximizers of a slope `γ` on `[-1,1]` form one of the three faces. -/
lemma exists_segFace (γ : ℝ) : ∃ k : Fin 3, ∀ t : ℝ,
    ((-1 ≤ t ∧ t ≤ 1) ∧ ∀ s, -1 ≤ s → s ≤ 1 → γ * s ≤ γ * t) ↔ t ∈ segFace k := by
  rcases lt_trichotomy γ 0 with hγ | hγ | hγ
  · refine ⟨1, fun t => ?_⟩
    rw [mem_segFace_iff]
    simp only [segSlope]
    constructor
    · rintro ⟨ht, h⟩
      refine ⟨ht, fun s hs1 hs2 => ?_⟩
      have := h (-1) le_rfl (by norm_num)
      have ht' : t = -1 := by nlinarith [ht.1]
      rw [ht']; linarith
    · rintro ⟨ht, h⟩
      refine ⟨ht, fun s hs1 hs2 => ?_⟩
      have := h (-1) le_rfl (by norm_num)
      have ht' : t = -1 := by linarith [ht.1]
      rw [ht']; nlinarith
  · refine ⟨2, fun t => ?_⟩
    rw [mem_segFace_iff]
    simp [segSlope, hγ]
  · refine ⟨0, fun t => ?_⟩
    rw [mem_segFace_iff]
    simp only [segSlope]
    constructor
    · rintro ⟨ht, h⟩
      refine ⟨ht, fun s hs1 hs2 => ?_⟩
      have := h 1 (by norm_num) le_rfl
      have ht' : t = 1 := by nlinarith [ht.2]
      rw [ht']; linarith
    · rintro ⟨ht, h⟩
      refine ⟨ht, fun s hs1 hs2 => ?_⟩
      have := h 1 (by norm_num) le_rfl
      have ht' : t = 1 := by linarith [ht.2]
      rw [ht']; nlinarith

/-- The face `F × segFace k` of the prism. -/
def prismFace (F : Set (E n)) (k : Fin 3) : Set (E (n + 1)) :=
  {z | fstPart z ∈ F ∧ z (Fin.last n) ∈ segFace k}

variable {A : Set (E n)}

/-- **Products of faces are faces of the prism.** -/
lemma prismFace_mem_faces {F : Set (E n)} (hF : F ∈ faces A) (k : Fin 3) :
    prismFace F k ∈ faces (prism A) := by
  obtain ⟨l, hl⟩ := exists_functional hF
  set c' := (InnerProductSpace.toDual ℝ (E n)).symm l
  have hc' : ∀ y, l y = ⟪y, c'⟫ := fun y => by
    rw [real_inner_comm]; exact (InnerProductSpace.toDual_symm_apply).symm
  set c := mkPt c' (segSlope k)
  have hL : ∀ z, ip c z = l (fstPart z) + segSlope k * z (Fin.last n) := fun z => by
    rw [ip_apply, inner_split, hc']
    simp [c, mul_comm]
  have hFA : F ⊆ A := face_subset hF
  have hmaxF : ∀ y, y ∈ F ↔ y ∈ A ∧ ∀ y' ∈ A, l y' ≤ l y := fun y => by
    rw [hl]; rfl
  obtain ⟨y0, hy0⟩ := hF.1
  obtain ⟨t0, ht0⟩ := segFace_nonempty k
  refine ⟨⟨mkPt y0 t0, by simp [prismFace, hy0, ht0]⟩, fun _ => ⟨ip c, ?_⟩⟩
  ext z
  simp only [prismFace, prism, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hz1, hz2⟩
    rw [mem_segFace_iff] at hz2
    rw [hmaxF] at hz1
    refine ⟨⟨hz1.1, hz2.1⟩, fun z' hz' => ?_⟩
    rw [hL, hL]
    have h1 := hz1.2 _ hz'.1
    have h2 := hz2.2 _ hz'.2.1 hz'.2.2
    linarith
  · rintro ⟨⟨hzA, hz1, hz2⟩, hmax⟩
    refine ⟨(hmaxF _).2 ⟨hzA, fun y' hy' => ?_⟩, (mem_segFace_iff k _).2 ⟨⟨hz1, hz2⟩,
      fun s hs1 hs2 => ?_⟩⟩
    · have := hmax (mkPt y' (z (Fin.last n))) ⟨by simpa using hy', by simpa using hz1,
        by simpa using hz2⟩
      rw [hL, hL] at this
      simp only [fstPart_mkPt, mkPt_last] at this
      linarith
    · have := hmax (mkPt (fstPart z) s) ⟨by simpa using hzA, by simpa using hs1,
        by simpa using hs2⟩
      rw [hL, hL] at this
      simp only [fstPart_mkPt, mkPt_last] at this
      linarith

/-- **Every face of the prism is a product of faces.** -/
lemma exists_prismFace {H : Set (E (n + 1))} (hH : H ∈ faces (prism A)) :
    ∃ F ∈ faces A, ∃ k, H = prismFace F k := by
  obtain ⟨L, hLH⟩ := exists_functional hH
  set c := (InnerProductSpace.toDual ℝ (E (n + 1))).symm L
  have hc : ∀ z, L z = ⟪z, c⟫ := fun z => by
    rw [real_inner_comm]; exact (InnerProductSpace.toDual_symm_apply).symm
  set c' := fstPart c
  set γ := c (Fin.last n)
  have hL : ∀ z, L z = ⟪fstPart z, c'⟫ + γ * z (Fin.last n) := fun z => by
    rw [hc, inner_split]; ring
  obtain ⟨k, hk⟩ := exists_segFace γ
  set F := {y | y ∈ A ∧ ∀ y' ∈ A, ⟪y', c'⟫ ≤ ⟪y, c'⟫} with hFdef
  have hmem : ∀ z, z ∈ H ↔ fstPart z ∈ F ∧ z (Fin.last n) ∈ segFace k := by
    intro z
    rw [hLH, ← hk]
    simp only [prism, Set.mem_ofPred_eq, hFdef]
    constructor
    · rintro ⟨⟨hzA, hz1, hz2⟩, hmax⟩
      refine ⟨⟨hzA, fun y' hy' => ?_⟩, ⟨hz1, hz2⟩, fun s hs1 hs2 => ?_⟩
      · have := hmax (mkPt y' (z (Fin.last n))) ⟨by simpa using hy', by simpa using hz1,
          by simpa using hz2⟩
        rw [hL, hL] at this
        simp only [fstPart_mkPt, mkPt_last] at this
        linarith
      · have := hmax (mkPt (fstPart z) s) ⟨by simpa using hzA, by simpa using hs1,
          by simpa using hs2⟩
        rw [hL, hL] at this
        simp only [fstPart_mkPt, mkPt_last] at this
        linarith
    · rintro ⟨⟨hzA, hF⟩, ⟨hz1, hz2⟩, hseg⟩
      refine ⟨⟨hzA, hz1, hz2⟩, fun z' hz' => ?_⟩
      rw [hL, hL]
      have h1 := hF _ hz'.1
      have h2 := hseg _ hz'.2.1 hz'.2.2
      linarith
  obtain ⟨z0, hz0⟩ := hH.1
  have hF : F ∈ faces A := by
    refine ⟨⟨fstPart z0, ((hmem z0).1 hz0).1⟩, fun _ => ⟨ip c', ?_⟩⟩
    ext y
    show y ∈ A ∧ (∀ y' ∈ A, ⟪y', c'⟫ ≤ ⟪y, c'⟫) ↔ y ∈ A ∧ ∀ y' ∈ A, ip c' y' ≤ ip c' y
    simp only [ip_apply]
  exact ⟨F, hF, k, Set.ext hmem⟩

lemma prismFace_inj {F F' : Set (E n)} (hF : F.Nonempty) (hF' : F'.Nonempty) {k k' : Fin 3}
    (h : prismFace F k = prismFace F' k') : F = F' ∧ k = k' := by
  have hproj : ∀ (G : Set (E n)) (j : Fin 3), fstPart '' prismFace G j = G := by
    intro G j
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz.1
    · intro hy
      obtain ⟨t, ht⟩ := segFace_nonempty j
      exact ⟨mkPt y t, ⟨by simpa using hy, by simpa using ht⟩, fstPart_mkPt y t⟩
  have hlast : ∀ (G : Set (E n)), G.Nonempty → ∀ j : Fin 3,
      (fun z : E (n + 1) => z (Fin.last n)) '' prismFace G j = segFace j := by
    intro G hG j
    ext t
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz.2
    · intro ht
      obtain ⟨y, hy⟩ := hG
      exact ⟨mkPt y t, ⟨by simpa using hy, by simpa using ht⟩, mkPt_last y t⟩
  refine ⟨by rw [← hproj F k, h, hproj], ?_⟩
  have hs : segFace k = segFace k' := by rw [← hlast F hF k, h, hlast F' hF' k']
  have key : ∀ j j' : Fin 3, segFace j = segFace j' → j = j' := by
    intro j j' hjj
    have m1 := congrArg (fun s : Set ℝ => (1 : ℝ) ∈ s) hjj
    have m0 := congrArg (fun s : Set ℝ => (0 : ℝ) ∈ s) hjj
    have mn := congrArg (fun s : Set ℝ => (-1 : ℝ) ∈ s) hjj
    fin_cases j <;> fin_cases j' <;>
      first
        | rfl
        | (norm_num [segFace] at m1; done)
        | (norm_num [segFace] at m0; done)
        | (norm_num [segFace] at mn; done)
  exact key k k' hs

/-- **A prism has three times as many nonempty faces as its base.** -/
theorem ncard_faces_prism (A : Set (E n)) : (faces (prism A)).ncard = 3 * (faces A).ncard := by
  have hprod : ((faces A) ×ˢ (Set.univ : Set (Fin 3))).ncard = (faces A).ncard * 3 := by
    rw [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [mul_comm, ← hprod]
  symm
  refine Set.ncard_congr (fun Fk _ => prismFace Fk.1 Fk.2) ?_ ?_ ?_
  · rintro ⟨F, k⟩ ⟨hF, -⟩
    exact prismFace_mem_faces hF k
  · rintro ⟨F, k⟩ ⟨F', k'⟩ ⟨hF, -⟩ ⟨hF', -⟩ h
    obtain ⟨h1, h2⟩ := prismFace_inj hF.1 hF'.1 h
    exact Prod.ext h1 h2
  · intro H hH
    obtain ⟨F, hF, k, rfl⟩ := exists_prismFace hH
    exact ⟨(F, k), ⟨hF, Set.mem_univ _⟩, rfl⟩

end Kalai5
