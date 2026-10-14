import Kalai5.Statement

/-!
# The rank of a family of full normals

* `card_pm_one_le`: a subspace `W ⊆ ℝ^ι` contains at most `2 ^ dim W` vectors with all entries
  `±1`.  (Take a minimal set `T` of coordinates on which restriction is injective on `W`; for each
  `i ∈ T` some `w_i ∈ W` vanishes on `T \ {i}` but not at `i`, and these are independent.)
* `exists_four_indep`: more than eight vectors whose inner products with a separating set of points
  are all `±1` contain four linearly independent ones.

Used for full normals: at `f₀ = 14` a full normal takes the values `±1` at every vertex, so six
full pairs (twelve normals) contain four independent normals (Lemma A applies).
-/

namespace Kalai5

open Module

/-- A linear functional vanishing on a set with `0` in its interior is zero. -/
lemma linMap_eq_zero_of_interior {K : Set E5} (h0 : (0 : E5) ∈ interior K) {φ : E5 →ₗ[ℝ] ℝ}
    (hφ : ∀ x ∈ K, φ x = 0) : φ = 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 h0)
  ext v
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have ht : 0 < r / (2 * ‖v‖) := by positivity
  have hmem : (r / (2 * ‖v‖)) • v ∈ K := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    field_simp
    linarith
  have := hφ _ hmem
  rw [map_smul, smul_eq_mul] at this
  simpa [ht.ne'] using this


/-- **`±1` vectors in a subspace**: at most `2 ^ dim W` of them. -/
theorem card_pm_one_le {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Submodule ℝ (ι → ℝ))
    (S : Finset (ι → ℝ)) (hS : ∀ v ∈ S, v ∈ W ∧ ∀ i, v i = 1 ∨ v i = -1) :
    S.card ≤ 2 ^ finrank ℝ W := by
  classical
  -- coordinate sets on which restriction is injective on `W`
  let good : Finset ι → Prop := fun T => ∀ w ∈ W, (∀ i ∈ T, w i = 0) → w = 0
  have huniv : good Finset.univ := fun w _ h => funext fun i => h i (Finset.mem_univ i)
  obtain ⟨T, hT, hmin⟩ : ∃ T, good T ∧ ∀ T', good T' → T.card ≤ T'.card := by
    have hne : (Finset.univ.filter fun T : Finset ι => good T).Nonempty :=
      ⟨Finset.univ, Finset.mem_filter.2 ⟨Finset.mem_univ _, huniv⟩⟩
    obtain ⟨T, hTmem, hTmin⟩ := Finset.exists_min_image _ Finset.card hne
    exact ⟨T, (Finset.mem_filter.1 hTmem).2,
      fun T' hT' => hTmin T' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hT'⟩)⟩
  -- for `i ∈ T`, a vector of `W` vanishing on `T \ {i}` but not at `i`
  have hwit : ∀ i ∈ T, ∃ w ∈ W, (∀ j ∈ T, j ≠ i → w j = 0) ∧ w i ≠ 0 := by
    intro i hi
    have hnot : ¬ good (T.erase i) := fun h => by
      have h1 := hmin _ h
      rw [Finset.card_erase_of_mem hi] at h1
      have h2 : 0 < T.card := Finset.card_pos.2 ⟨i, hi⟩
      omega
    simp only [good, not_forall] at hnot
    obtain ⟨w, hw, hz, hne⟩ := hnot
    refine ⟨w, hw, fun j hj hji => hz j (Finset.mem_erase.2 ⟨hji, hj⟩), fun hwi => hne ?_⟩
    refine hT w hw fun j hj => ?_
    by_cases hji : j = i
    · rw [hji]; exact hwi
    · exact hz j (Finset.mem_erase.2 ⟨hji, hj⟩)
  choose! w hwW hwz hwi using hwit
  -- these are independent, so `|T| ≤ dim W`
  have hind : LinearIndependent ℝ (fun i : T => (⟨w i, hwW i i.2⟩ : W)) := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    have h := congrArg (fun x : W => (x : ι → ℝ) i) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Submodule.coe_zero, Pi.zero_apply] at h
    rw [Finset.sum_eq_single i] at h
    · exact (mul_eq_zero.1 h).resolve_right (hwi i i.2)
    · intro j _ hji
      rw [hwz j j.2 i i.2 (fun h' => hji (Subtype.ext h'.symm)), mul_zero]
    · intro h'; exact absurd hi h'
  have hTcard : T.card ≤ finrank ℝ W := by
    have := hind.fintype_card_le_finrank
    simpa using this
  -- restriction to `T` is injective on `S`
  have hinj : Set.InjOn (fun v : ι → ℝ => fun i : T => decide (v i = 1)) S := by
    intro v hv v' hv' h
    have hvv' : v - v' = 0 := by
      refine hT (v - v') (W.sub_mem (hS v hv).1 (hS v' hv').1) fun i hi => ?_
      have h1 := congrFun h ⟨i, hi⟩
      simp only at h1
      rw [Pi.sub_apply, sub_eq_zero]
      rcases (hS v hv).2 i with h2 | h2 <;> rcases (hS v' hv').2 i with h3 | h3
      · rw [h2, h3]
      · rw [h2, h3] at h1; norm_num at h1
      · rw [h2, h3] at h1; norm_num at h1
      · rw [h2, h3]
    exact sub_eq_zero.1 hvv'
  calc S.card ≤ (Finset.univ : Finset (T → Bool)).card :=
        Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
    _ = 2 ^ T.card := by simp
    _ ≤ 2 ^ finrank ℝ W := Nat.pow_le_pow_right (by norm_num) hTcard

/-- **Four independent normals**: more than eight vectors whose inner products with a separating
set `X` are all `±1` contain four linearly independent ones. -/
theorem exists_four_indep {N X : Finset E5}
    (hX : ∀ u : E5, (∀ x ∈ X, inner ℝ u x = (0 : ℝ)) → u = 0)
    (hN : ∀ u ∈ N, ∀ x ∈ X, inner ℝ u x = (1 : ℝ) ∨ inner ℝ u x = (-1 : ℝ)) (h8 : 8 < N.card) :
    ∃ u : Fin 4 → E5, LinearIndependent ℝ u ∧ ∀ i, u i ∈ N := by
  classical
  obtain ⟨b, hbN, hspan, hb⟩ := exists_linearIndependent ℝ (N : Set E5)
  have hbfin : b.Finite := N.finite_toSet.subset hbN
  haveI : Fintype b := hbfin.fintype
  by_cases h4 : 4 ≤ Fintype.card b
  · obtain ⟨f⟩ : Nonempty (Fin 4 ↪ b) := Function.Embedding.nonempty_of_card_le (by simpa using h4)
    exact ⟨fun i => (f i : E5), hb.comp f f.injective, fun i => hbN (f i).2⟩
  · exfalso
    have hdim : finrank ℝ (Submodule.span ℝ (N : Set E5)) ≤ 3 := by
      rw [← hspan, finrank_span_set_eq_card hb, Set.toFinset_card]
      omega
    -- evaluation at the points of `X`
    let ev : E5 →ₗ[ℝ] (X → ℝ) :=
      { toFun := fun u x => inner ℝ u (x : E5)
        map_add' := fun u v => by ext x; simp [inner_add_left]
        map_smul' := fun r u => by ext x; simp [real_inner_smul_left] }
    have hev : Function.Injective ev := by
      intro u v huv
      have h0 : u - v = 0 := hX (u - v) fun x hx => by
        have := congrFun huv ⟨x, hx⟩
        simp only [ev, LinearMap.coe_mk, AddHom.coe_mk] at this
        rw [inner_sub_left, this, sub_self]
      exact sub_eq_zero.1 h0
    let W := (Submodule.span ℝ (N : Set E5)).map ev
    have hW : finrank ℝ W ≤ 3 := le_trans (Submodule.finrank_map_le _ _) hdim
    have hS := card_pm_one_le W (N.image ev) (by
      intro v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
      exact ⟨Submodule.mem_map_of_mem (Submodule.subset_span hu), fun x => hN u hu x x.2⟩)
    rw [Finset.card_image_of_injective _ hev] at hS
    have h2 : 2 ^ finrank ℝ W ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hW
    omega

end Kalai5
