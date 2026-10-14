import Kalai5.Gale.TypeQ
import Kalai5.Gale.ClassifyX

/-!
# The free sum of two triangles is recognized by its row

**Theorem** (`qDual_facets`): a 4-polytope with row `qDualRow = (6,15,18,9; 36)` has a 3-set `U`
of vertices such that its facets are exactly the convex hulls of the vertex sets meeting `U` in
two points and the other three vertices in two points (the free sum `Δ2 ⊕ Δ2`).

The proof is the Gale classification with the type check `checkQ6`.
-/

namespace Kalai5

open Set

namespace Gale

open Module

variable {n : ℕ}

lemma ofMask_land (S U : ℕ) : ofMask n (S &&& U) = ofMask n S ∩ ofMask n U := by
  ext j
  simp [mem_ofMask, Nat.testBit_land]

lemma ofMask_land_cmask (S U : ℕ) : ofMask n (S &&& cmask n U) = ofMask n S \ ofMask n U := by
  ext j
  simp only [mem_ofMask, Nat.testBit_land, Finset.mem_sdiff, cmask_testBit j.2]
  cases S.testBit j <;> cases U.testBit j <;> simp

/-- **The type check, labelled**: for sorted codes, the facets are the `2 + 2` index sets. -/
theorem qDual_facets_labelled {W : Fin n → E 4} (hn : n ≤ 7) (hinj : Function.Injective W)
    (hext : ∀ j, W j ∈ (convexHull ℝ (range W)).extremePoints ℝ)
    (hspan : affineSpan ℝ (range W) = ⊤) (hrow : rowOf (convexHull ℝ (range W)) = qDualRow) :
    ∃ σ : Equiv.Perm (Fin n), ∃ U : Finset (Fin n), U.card = 3 ∧ ∀ F : Finset (Fin n),
      (F.Nonempty ∧ IsFaceIdx (W ∘ σ) F ∧ finrank ℝ (vectorSpan ℝ ((W ∘ σ) '' ↑F)) = 3) ↔
        ((F ∩ U).card = 2 ∧ (F \ U).card = 2) := by
  classical
  have h5 := five_le hspan
  have h6 : n = 6 := by
    have h1 : fvec (convexHull ℝ (range W)) 0 = 6 := congrArg Row.n hrow
    have h2 := fvec_zero_eq (Finset.univ.image W)
    rw [coe_image_univ] at h2
    have hext_eq : (convexHull ℝ (range W)).extremePoints ℝ = range W :=
      Subset.antisymm extremePoints_convexHull_subset (by rintro _ ⟨j, rfl⟩; exact hext j)
    rw [h1, hext_eq, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card,
      Fintype.card_fin] at h2
    exact h2.symm
  subst h6
  obtain ⟨g0, hg0⟩ := exists_isGale hspan (by omega)
  obtain ⟨g1, hg1, hnorm⟩ := exists_normal hg0
  have hc1 := codeFor_codeOf hnorm
  set m := (slopes g1).card
  set σ := Tuple.sort (codeOf g1)
  set W' := W ∘ σ
  set g := g1 ∘ σ
  set c := codeOf g1 ∘ σ
  have hg : IsGale W' g := hg1.perm σ
  have hc : CodeFor g c m := hc1.perm σ
  have hmono : Monotone c := Tuple.monotone_sort _
  have hrange : range W' = range W := EquivLike.range_comp W σ
  have hinj' : Function.Injective W' := hinj.comp σ.injective
  have hspan' : affineSpan ℝ (range W') = ⊤ := by rw [hrange]; exact hspan
  have hext' : ∀ j, W' j ∈ (convexHull ℝ (range W')).extremePoints ℝ := by
    intro j; rw [hrange]; exact hext (σ j)
  have hvert : ∀ j, IsFaceIdx W' {j} := isFaceIdx_singleton hinj' hext'
  have hmem := ofFn_mem_gen hc hmono
  have hck := checkQ6 _ hmem
  have hrank : min (nlines (List.ofFn c)) 2 = 6 - 5 := by
    rw [hc.nlines_eq, ← hc.crank_univ, ← hc.finrank_span_image]
    have := finrank_span_univ hspan' hg
    omega
  have hvpd : ∀ j : Fin 6, ∃ a : Fin 6 → ℝ,
      (∀ i : Fin 6, ((tab 6).co j).testBit i = true → 0 < a i) ∧
      (∀ i : Fin 6, ((tab 6).co j).testBit i = false → a i = 0) ∧ ∑ i, a i • g i = 0 := by
    intro j
    have h := (isFaceIdx_ofMask_iff hg (2 ^ (j : ℕ))).1 (by
      have hj : ofMask 6 (2 ^ (j : ℕ)) = {j} := by
        ext i; rw [mem_ofMask, Nat.testBit_two_pow, Finset.mem_singleton, decide_eq_true_eq]
        exact ⟨fun h => Fin.ext h.symm, fun h => by rw [h]⟩
      rw [hj]; exact hvert j)
    exact h
  unfold Tab.checkQ at hck
  dsimp only at hck
  split_ifs at hck with h1 hv
  · exfalso
    rw [show (tab 6).n = 6 from rfl, hrank] at h1
    simp at h1
  · rw [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hck
    obtain ⟨hfull, hq⟩ := hck
    have hcomp : ∀ S < 2 ^ 6, ((tab 6).covV (circuits (List.ofFn c))).testBit S = true ∨
        ((tab 6).farV (candidates (List.ofFn c))).testBit S = true := by
      intro S hS
      have := congrArg (fun x => x.testBit S) hfull
      simp only [Nat.testBit_lor, tab_full_testBit, hS, decide_true, Bool.or_eq_true] at this
      exact this
    have hrowEq := rowOf_eq hspan' hinj' hvert hg hc hcomp
    have hrowW' : rowOf (convexHull ℝ (range W')) = qDualRow := by rw [hrange]; exact hrow
    rcases hq with hne | hok
    · exact absurd (hrowEq.symm.trans hrowW') hne
    · unfold Tab.qOK at hok
      rw [List.any_eq_true] at hok
      obtain ⟨U, hU, hU2⟩ := hok
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hU2
      obtain ⟨hpop, hdim⟩ := hU2
      rw [List.mem_range] at hU
      refine ⟨σ, ofMask 6 U, by rw [card_ofMask]; exact hpop, fun F => ?_⟩
      obtain ⟨S, hS, rfl⟩ := exists_ofMask F
      rw [← dimV_iff hspan' hg hc hcomp 3 hS]
      change ((tab 6).dimV ((tab 6).faceV (circuits (List.ofFn c))) (rkOf c) 3).testBit S = true ↔ _
      rw [show rkOf c = (tab 6).rk (nzMask (List.ofFn c))
          ((List.range (nlines (List.ofFn c))).map (lineMask (List.ofFn c))) from rfl, hdim, famQ,
        testBit_maskOf, ← ofMask_land, ← ofMask_land_cmask, card_ofMask, card_ofMask]
      have hS' : S < 64 := by simpa using hS
      simp [hS']
  · exfalso
    rw [List.any_eq_true] at hck
    obtain ⟨j, hj, hjb⟩ := hck
    rw [List.mem_range] at hj
    rw [Bool.and_eq_true] at hjb
    obtain ⟨pn, hpn, hN, i, hP, hS⟩ := farkas_spec hjb.2
    have hi : i < 6 := by
      obtain ⟨i', -, σ', hA | hB⟩ := mem_candidates hpn
      · rw [hA, testBit_maskOf, List.length_ofFn, Bool.and_eq_true, decide_eq_true_eq] at hP
        exact hP.1
      · rw [hB, testBit_maskOf, List.length_ofFn, Bool.and_eq_true, decide_eq_true_eq] at hP
        exact hP.1
    exact hc.not_posDep_of_farkas hc.nlines_eq
      ⟨pn, hpn, fun i' hi' => hN i' hi', ⟨i, hi⟩, hP, hS⟩ (hvpd ⟨j, hj⟩)

end Gale

end Kalai5
