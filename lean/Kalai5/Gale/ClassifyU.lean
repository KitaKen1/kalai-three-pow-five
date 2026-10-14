import Kalai5.Gale.CheckAllU
import Kalai5.Gale.Classify

/-!
# The combinatorial type of the dual of `U`

**Theorem** (`uStar_facets`): a labelled 4-polytope with seven vertices and row
`(7, 17, 19, 9; 38)` has, after relabelling its vertices, exactly the facet index sets `uSets`.

Proof: as `small_classification_proof`, with the kernel check `checkU7`: the sorted Gale code is
one of the ten codes of `uTable`, and its facet masks (read off `dimV`, `dimV_iff`) are
`uStarFacets` after the tabulated relabelling.
-/

namespace Kalai5.Gale

open Set Module

/-- The canonical facets of the dual of `U`, as index sets. -/
def uSets : List (Finset (Fin 7)) := uStarFacets.map (ofMask 7)

/-- Kernel facts on the tabulated relabellings. -/
theorem uTable_facts : ∀ e ∈ uTable,
    (∀ i < 7, e.2.getD i 0 < 7 ∧ e.2.idxOf (e.2.getD i 0) = i) ∧
    (∀ k < 7, e.2.idxOf k < 7 ∧ e.2.getD (e.2.idxOf k) 0 = k) ∧
    (∀ S < 128, permMask e.2 S < 128 ∧
      ∀ k < 7, (permMask e.2 S).testBit k = S.testBit (e.2.idxOf k)) := by
  decide +kernel

lemma uStarFacets_lt : ∀ M ∈ uStarFacets, M < 128 := by decide

lemma lookup_mem {cs b : List ℕ} {l : List (List ℕ × List ℕ)} (h : l.lookup cs = some b) :
    (cs, b) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons x xs ih =>
    obtain ⟨k, v⟩ := x
    by_cases hk : cs = k
    · subst hk
      have hv : v = b := by simpa [List.lookup] using h
      rw [hv]; exact List.mem_cons_self
    · have hb : (cs == k) = false := by simpa using hk
      simp only [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- **The facets of the dual of `U`.** -/
theorem uStar_facets {W : Fin 7 → E 4} (hinj : Function.Injective W)
    (hext : ∀ j, W j ∈ (convexHull ℝ (range W)).extremePoints ℝ)
    (hspan : affineSpan ℝ (range W) = ⊤) (hrow : rowOf (convexHull ℝ (range W)) = uStarRow) :
    ∃ τ : Fin 7 ≃ Fin 7,
      (∀ G ∈ faces (convexHull ℝ (range W)), dim G = 3 →
        (idx W G).map τ.toEmbedding ∈ uSets) ∧
      (∀ F ∈ uSets, ∃ G ∈ faces (convexHull ℝ (range W)), dim G = 3 ∧
        (idx W G).map τ.toEmbedding = F) := by
  classical
  have h5 := five_le hspan
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
  have hck := check_all h5 (le_refl 7) _ hmem
  have hckU := checkU7 _ hmem
  have hrank : min (nlines (List.ofFn c)) 2 = 7 - 5 := by
    rw [hc.nlines_eq, ← hc.crank_univ, ← hc.finrank_span_image]
    have := finrank_span_univ hspan' hg
    omega
  have hvpd : ∀ j : Fin 7, ∃ a : Fin 7 → ℝ,
      (∀ i : Fin 7, ((tab 7).co j).testBit i = true → 0 < a i) ∧
      (∀ i : Fin 7, ((tab 7).co j).testBit i = false → a i = 0) ∧ ∑ i, a i • g i = 0 := by
    intro j
    have h := (isFaceIdx_ofMask_iff hg (2 ^ (j : ℕ))).1 (by
      have hj : ofMask 7 (2 ^ (j : ℕ)) = {j} := by
        ext i; rw [mem_ofMask, Nat.testBit_two_pow, Finset.mem_singleton, decide_eq_true_eq]
        exact ⟨fun h => Fin.ext h.symm, fun h => by rw [h]⟩
      rw [hj]; exact hvert j)
    exact h
  -- validity and completeness from the base check
  have hvalid : (List.range (tab 7).n).all (fun j => covered (circuits (List.ofFn c)) ((tab 7).co j))
      = true ∧ ∀ S < 2 ^ 7, ((tab 7).covV (circuits (List.ofFn c))).testBit S = true ∨
        ((tab 7).farV (candidates (List.ofFn c))).testBit S = true := by
    unfold Tab.check at hck
    dsimp only at hck
    split_ifs at hck with h1 hv
    · exfalso
      rw [show (tab 7).n = 7 from rfl, hrank] at h1
      simp at h1
    · refine ⟨hv, ?_⟩
      rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hck
      obtain ⟨hfull, -⟩ := hck
      intro S hS
      have := congrArg (fun x => x.testBit S) hfull
      simp only [Nat.testBit_lor, tab_full_testBit, hS, decide_true, Bool.or_eq_true] at this
      exact this
    · exfalso
      rw [List.any_eq_true] at hck
      obtain ⟨j, hj, hjb⟩ := hck
      rw [List.mem_range] at hj
      rw [Bool.and_eq_true] at hjb
      obtain ⟨pn, hpn, hN, i, hP, hS⟩ := farkas_spec hjb.2
      have hi : i < 7 := by
        obtain ⟨i', -, σ', hA | hB⟩ := mem_candidates hpn
        · rw [hA, testBit_maskOf, List.length_ofFn, Bool.and_eq_true, decide_eq_true_eq] at hP
          exact hP.1
        · rw [hB, testBit_maskOf, List.length_ofFn, Bool.and_eq_true, decide_eq_true_eq] at hP
          exact hP.1
      exact hc.not_posDep_of_farkas hc.nlines_eq
        ⟨pn, hpn, fun i' hi' => hN i' hi', ⟨i, hi⟩, hP, hS⟩ (hvpd ⟨j, hj⟩)
  obtain ⟨hv, hcomp⟩ := hvalid
  -- the row of the code is `uStarRow`
  have hrowEq := rowOf_eq hspan' hinj' hvert hg hc hcomp
  have hrowc : (tab 7).row ((tab 7).faceV (circuits (List.ofFn c))) (rkOf c) = uStarRow := by
    rw [← hrowEq, show convexHull ℝ (range W') = convexHull ℝ (range W) by rw [hrange]]
    exact hrow
  -- the table entry
  obtain ⟨π, hlook, hperm⟩ : ∃ π, uTable.lookup (List.ofFn c) = some π ∧
      (((bitsList (2 ^ 7) ((tab 7).dimV ((tab 7).faceV (circuits (List.ofFn c))) (rkOf c) 3)).map
        (permMask π)).Perm uStarFacets) := by
    unfold Tab.checkU at hckU
    dsimp only at hckU
    rw [if_neg (by rw [show (tab 7).n = 7 from rfl, hrank]; simp), if_pos hv] at hckU
    have hrowc' : (tab 7).row ((tab 7).faceV (circuits (List.ofFn c)))
        ((tab 7).rk (nzMask (List.ofFn c)) ((List.range (nlines (List.ofFn c))).map
          (lineMask (List.ofFn c)))) = uStarRow := hrowc
    rw [if_pos hrowc'] at hckU
    cases hl : uTable.lookup (List.ofFn c) with
    | none => rw [hl] at hckU; exact absurd hckU (by simp)
    | some π =>
      rw [hl] at hckU
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hckU
      exact ⟨π, rfl, hckU.2⟩
  obtain ⟨hπ1, hπ2, hπ3⟩ := uTable_facts _ (lookup_mem hlook)
  simp only at hπ1 hπ2 hπ3
  -- the relabelling as an equivalence
  let τπ : Fin 7 ≃ Fin 7 :=
    { toFun := fun i => ⟨π.getD i 0, (hπ1 i i.2).1⟩
      invFun := fun k => ⟨π.idxOf (k : ℕ), (hπ2 k k.2).1⟩
      left_inv := fun i => Fin.ext (hπ1 i i.2).2
      right_inv := fun k => Fin.ext (hπ2 k k.2).2 }
  have hτπ : ∀ k : Fin 7, ((τπ.symm k : Fin 7) : ℕ) = π.idxOf (k : ℕ) := fun _ => rfl
  have hkey : ∀ S < 128, ofMask 7 (permMask π S) = (ofMask 7 S).map τπ.toEmbedding := by
    intro S hS
    ext k
    rw [mem_ofMask, Finset.mem_map_equiv, mem_ofMask, (hπ3 S hS).2 k k.2, hτπ]
  have hinjP : ∀ S < 128, ∀ S' < 128, permMask π S = permMask π S' → S = S' := by
    intro S hS S' hS' h
    have h1 := hkey S hS
    have h2 := hkey S' hS'
    rw [h] at h1
    have h3 : ofMask 7 S = ofMask 7 S' := by
      rw [h1] at h2
      exact Finset.map_injective _ h2
    exact ofMask_injOn (by simpa using hS) (by simpa using hS') h3
  -- faces of `conv W` and of `conv W'`
  have hface : ∀ G, G ∈ faces (convexHull ℝ (range W)) ↔ G ∈ faces (convexHull ℝ (range W')) := by
    intro G; rw [hrange]
  have hidx : ∀ G : Set (E 4), idx W' G = (idx W G).map σ.symm.toEmbedding := by
    intro G
    ext j
    rw [mem_idx, Finset.mem_map_equiv, Equiv.symm_symm, mem_idx]
    rfl
  refine ⟨σ.symm.trans τπ, ?_, ?_⟩
  · intro G hG hG3
    have hG' := (hface G).1 hG
    have hfi := isFaceIdx_idx hG'
    have hne := idx_nonempty hG'
    have hconv := face_eq_conv_idx hG'
    obtain ⟨S, hS, hSeq⟩ := exists_ofMask (idx W' G)
    have hdim : finrank ℝ (vectorSpan ℝ (W' '' ↑(ofMask 7 S))) = 3 := by
      rw [hSeq, ← dim_convexHull, ← hconv]; exact hG3
    have hbit := (dimV_iff hspan' hg hc hcomp 3 hS).2 ⟨by rw [hSeq]; exact hne,
      by rw [hSeq]; exact hfi, hdim⟩
    have hSmem : S ∈ bitsList (2 ^ 7) ((tab 7).dimV ((tab 7).faceV (circuits (List.ofFn c)))
        (rkOf c) 3) := by
      unfold bitsList
      rw [List.mem_filter, List.mem_range]
      exact ⟨hS, hbit⟩
    have hM : permMask π S ∈ uStarFacets := hperm.subset (List.mem_map_of_mem hSmem)
    have hF : ofMask 7 (permMask π S) ∈ uSets := List.mem_map_of_mem hM
    rw [hkey S hS, hSeq, hidx, Finset.map_map] at hF
    rw [Equiv.trans_toEmbedding]
    exact hF
  · intro F hF
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hF
    obtain ⟨S, hSmem, hSM⟩ := List.mem_map.1 (hperm.symm.subset hM)
    unfold bitsList at hSmem
    rw [List.mem_filter, List.mem_range] at hSmem
    obtain ⟨hS, hbit⟩ := hSmem
    obtain ⟨hne, hfi, hdim⟩ := (dimV_iff hspan' hg hc hcomp 3 hS).1 hbit
    obtain ⟨hG', hidxG⟩ := conv_mem_faces hne hfi
    refine ⟨convexHull ℝ (W' '' ↑(ofMask 7 S)), (hface _).2 hG', ?_, ?_⟩
    · rw [dim_convexHull]; exact hdim
    · rw [Equiv.trans_toEmbedding, ← Finset.map_map, ← hidx, hidxG, ← hkey S hS, hSM]

end Kalai5.Gale
