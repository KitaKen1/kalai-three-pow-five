import Kalai5.Gale.CheckAllX
import Kalai5.Gale.ProfileCount
import Kalai5.Gale.Classify

/-!
# Extended classification of 4-polytopes with at most seven vertices

**Theorem** (`smallX_classification`): every 4-polytope with at most seven vertices has one of
the 36 extended rows of `smallRowsX` — its row together with its facet profile and its vertex
profile (`Kalai5.Rows.Profile`).

The proof is that of `small_classification_proof`, with the extended kernel check
(`checkX_all`) and `rowXOf_eq` in place of `check_all` and `rowOf_eq`; the profiles are invariant
under the transport of a polytope to its own affine hull (`facetCnt_affEmb`, `vertCnt_affEmb`).
-/

namespace Kalai5

open Set

/-! ### Transport of the profiles to the affine hull -/

section transport

variable {d : ℕ} {K : Set (E d)} {p : E d}

lemma cnt_affEmb (hp : p ∈ K) (G' : Set (E (dim K))) (j : ℕ) :
    cnt K (affEmb K p '' G') j = cnt (affEmb K p ⁻¹' K) G' j := by
  unfold cnt
  symm
  refine Set.ncard_congr (fun F _ => affEmb K p '' F) ?_ ?_ ?_
  · rintro F ⟨hF, hFG, hd⟩
    exact ⟨image_mem_faces hp hF, Set.image_mono hFG, by rw [dim_image_affEmb]; exact hd⟩
  · intro F F' _ _ h
    exact (Set.image_injective.2 (affEmb_injective (K := K) p)) h
  · rintro F ⟨hF, hFG, hd⟩
    have hFr := subset_range_affEmb hp (face_subset hF)
    refine ⟨affEmb K p ⁻¹' F, ⟨preimage_mem_faces hp hF, fun z hz => ?_, ?_⟩,
      Set.image_preimage_eq_of_subset hFr⟩
    · obtain ⟨w, hw, hwz⟩ := hFG hz
      rw [← affEmb_injective (K := K) p hwz]
      exact hw
    · have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' F)
      rw [Set.image_preimage_eq_of_subset hFr] at this
      rw [← this]; exact hd

lemma facetCnt_affEmb (hp : p ∈ K) (t : ℕ × ℕ × ℕ) :
    facetCnt K t = facetCnt (affEmb K p ⁻¹' K) t := by
  unfold facetCnt
  symm
  refine Set.ncard_congr (fun F _ => affEmb K p '' F) ?_ ?_ ?_
  · rintro F ⟨hF, hd, ht⟩
    refine ⟨image_mem_faces hp hF, by rw [dim_image_affEmb]; exact hd, ?_⟩
    simp only [triBelow, cnt_affEmb hp]
    exact ht
  · intro F F' _ _ h
    exact (Set.image_injective.2 (affEmb_injective (K := K) p)) h
  · rintro F ⟨hF, hd, ht⟩
    have hFr := subset_range_affEmb hp (face_subset hF)
    have hFF : affEmb K p '' (affEmb K p ⁻¹' F) = F := Set.image_preimage_eq_of_subset hFr
    refine ⟨affEmb K p ⁻¹' F, ⟨preimage_mem_faces hp hF, ?_, ?_⟩, hFF⟩
    · have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' F)
      rw [hFF] at this
      rw [← this]; exact hd
    · rw [← hFF] at ht
      simp only [triBelow, cnt_affEmb hp] at ht
      exact ht

lemma vertCnt_affEmb (hp : p ∈ K) (t : ℕ × ℕ × ℕ) :
    vertCnt K t = vertCnt (affEmb K p ⁻¹' K) t := by
  unfold vertCnt
  symm
  refine Set.ncard_congr (fun F _ => affEmb K p '' F) ?_ ?_ ?_
  · rintro F ⟨hF, hd, ht⟩
    refine ⟨image_mem_faces hp hF, by rw [dim_image_affEmb]; exact hd, ?_⟩
    simp only [triAbove, upIn_affEmb hp]
    exact ht
  · intro F F' _ _ h
    exact (Set.image_injective.2 (affEmb_injective (K := K) p)) h
  · rintro F ⟨hF, hd, ht⟩
    have hFr := subset_range_affEmb hp (face_subset hF)
    have hFF : affEmb K p '' (affEmb K p ⁻¹' F) = F := Set.image_preimage_eq_of_subset hFr
    refine ⟨affEmb K p ⁻¹' F, ⟨preimage_mem_faces hp hF, ?_, ?_⟩, hFF⟩
    · have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' F)
      rw [hFF] at this
      rw [← this]; exact hd
    · rw [← hFF] at ht
      simp only [triAbove, upIn_affEmb hp] at ht
      exact ht

lemma rowXOf_affEmb (hp : p ∈ K) : rowXOf K = rowXOf (affEmb K p ⁻¹' K) := by
  have h1 : facetCnt K = facetCnt (affEmb K p ⁻¹' K) := funext (facetCnt_affEmb hp)
  have h2 : vertCnt K = vertCnt (affEmb K p ⁻¹' K) := funext (vertCnt_affEmb hp)
  simp only [rowXOf, rowOf, h1, h2, fvec_affEmb hp, flag2_affEmb hp]

end transport

namespace Gale

open Module

variable {n : ℕ}

/-- **Extended rows of labelled 4-polytopes with at most seven vertices.** -/
theorem rowXOf_mem_smallRowsX {W : Fin n → E 4} (hn : n ≤ 7) (hinj : Function.Injective W)
    (hext : ∀ j, W j ∈ (convexHull ℝ (range W)).extremePoints ℝ)
    (hspan : affineSpan ℝ (range W) = ⊤) :
    rowXOf (convexHull ℝ (range W)) ∈ smallRowsX := by
  classical
  have h5 := five_le hspan
  obtain ⟨g0, hg0⟩ := exists_isGale hspan (by omega)
  obtain ⟨g1, hg1, hnorm⟩ := exists_normal hg0
  have hc1 := codeFor_codeOf hnorm
  set m := (slopes g1).card
  -- sort the codes
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
  -- the kernel certificate
  have hmem := ofFn_mem_gen hc hmono
  have hck := checkX_all h5 hn _ hmem
  -- the rank condition holds
  have hrank : min (nlines (List.ofFn c)) 2 = n - 5 := by
    rw [hc.nlines_eq, ← hc.crank_univ, ← hc.finrank_span_image]
    have := finrank_span_univ hspan' hg
    omega
  -- vertices are certified
  have hvpd : ∀ j : Fin n, ∃ a : Fin n → ℝ,
      (∀ i : Fin n, ((tab n).co j).testBit i = true → 0 < a i) ∧
      (∀ i : Fin n, ((tab n).co j).testBit i = false → a i = 0) ∧ ∑ i, a i • g i = 0 := by
    intro j
    have h := (isFaceIdx_ofMask_iff hg (2 ^ (j : ℕ))).1 (by
      have hj : ofMask n (2 ^ (j : ℕ)) = {j} := by
        ext i; rw [mem_ofMask, Nat.testBit_two_pow, Finset.mem_singleton, decide_eq_true_eq]
        exact ⟨fun h => Fin.ext h.symm, fun h => by rw [h]⟩
      rw [hj]; exact hvert j)
    exact h
  unfold Tab.checkX at hck
  dsimp only at hck
  split_ifs at hck with h1 hv
  · -- the rank condition holds, so this branch is impossible
    exfalso
    rw [show (tab n).n = n from rfl, hrank] at h1
    simp at h1
  · -- valid branch: completeness and the extended row
    rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hck
    obtain ⟨hfull, hrow⟩ := hck
    have hcomp : ∀ S < 2 ^ n, ((tab n).covV (circuits (List.ofFn c))).testBit S = true ∨
        ((tab n).farV (candidates (List.ofFn c))).testBit S = true := by
      intro S hS
      have := congrArg (fun x => x.testBit S) hfull
      simp only [Nat.testBit_lor, tab_full_testBit, hS, decide_true, Bool.or_eq_true] at this
      exact this
    have hrowEq := rowXOf_eq hspan' hinj' hvert hg hc hcomp
    rw [show convexHull ℝ (range W) = convexHull ℝ (range W') by rw [hrange], hrowEq]
    exact hrow
  · -- invalid branch: impossible, a vertex would be refuted
    exfalso
    rw [List.any_eq_true] at hck
    obtain ⟨j, hj, hjb⟩ := hck
    rw [List.mem_range] at hj
    rw [Bool.and_eq_true] at hjb
    obtain ⟨pn, hpn, hN, i, hP, hS⟩ := farkas_spec hjb.2
    have hi : i < n := by
      obtain ⟨i', -, σ', hA | hB⟩ := mem_candidates hpn
      · rw [hA, testBit_maskOf, List.length_ofFn, Bool.and_eq_true, decide_eq_true_eq] at hP
        exact hP.1
      · rw [hB, testBit_maskOf, List.length_ofFn, Bool.and_eq_true, decide_eq_true_eq] at hP
        exact hP.1
    exact hc.not_posDep_of_farkas hc.nlines_eq
      ⟨pn, hpn, fun i' hi' => hN i' hi', ⟨i, hi⟩, hP, hS⟩ (hvpd ⟨j, hj⟩)

/-- Transport to the standard space of the right dimension. -/
theorem rowXOf_mem_smallRowsX_of_interior {k : ℕ} (hk : k = 4) {V : Finset (E k)}
    (h0 : (0 : E k) ∈ interior (convexHull ℝ (V : Set (E k))))
    (hn : fvec (convexHull ℝ (V : Set (E k))) 0 ≤ 7) :
    rowXOf (convexHull ℝ (V : Set (E k))) ∈ smallRowsX := by
  classical
  subst hk
  set K := convexHull ℝ (V : Set (E 4))
  have hX := extremePoints_finite V
  set XF := hX.toFinset
  let W : Fin XF.card → E 4 := fun i => (XF.equivFin.symm i : E 4)
  have hinj : Function.Injective W := fun i j h =>
    XF.equivFin.symm.injective (Subtype.ext h)
  have hrange : range W = K.extremePoints ℝ := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact hX.mem_toFinset.1 (XF.equivFin.symm i).2
    · intro hx
      exact ⟨XF.equivFin ⟨x, hX.mem_toFinset.2 hx⟩, by simp [W]⟩
  have hK : convexHull ℝ (range W) = K := by rw [hrange]; exact convexHull_extremePoints_eq V
  have hcard : XF.card ≤ 7 := by
    rw [fvec_zero_eq] at hn
    rwa [Set.ncard_eq_toFinset_card _ hX] at hn
  have hext : ∀ j, W j ∈ (convexHull ℝ (range W)).extremePoints ℝ := by
    intro j; rw [hK, ← hrange]; exact mem_range_self j
  have hspan : affineSpan ℝ (range W) = ⊤ := by
    rw [← affineSpan_convexHull, hK]
    exact (convex_convexHull ℝ _).interior_nonempty_iff_affineSpan_eq_top.1 ⟨0, h0⟩
  have := rowXOf_mem_smallRowsX hcard hinj hext hspan
  rwa [hK] at this

end Gale

/-- **Every 4-polytope with at most seven vertices has an extended row in `smallRowsX`.** -/
theorem smallX_classification : ∀ X, IsRealRowX X → X.1.n ≤ 7 → X ∈ smallRowsX := by
  rintro X ⟨d, Q, ⟨V, hQ⟩, hdim, rfl⟩ hn
  have hne : Q.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hdim
    unfold dim at hdim
    rw [vectorSpan_empty, finrank_bot] at hdim
    omega
  obtain ⟨p, hp, V', hV', h0⟩ := exists_good_affEmb hQ hne
  have hrow : rowXOf Q = rowXOf (convexHull ℝ (V' : Set (E (dim Q)))) := by
    rw [rowXOf_affEmb hp, hV']
  rw [hrow] at hn ⊢
  exact Gale.rowXOf_mem_smallRowsX_of_interior hdim h0 hn

end Kalai5
