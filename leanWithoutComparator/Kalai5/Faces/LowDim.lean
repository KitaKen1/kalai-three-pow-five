import Kalai5.Faces.Transitive

/-!
# Vertices of low-dimensional polytopes

For a polytope `Q = conv S`:
* the 0-dimensional faces are the singletons of extreme points (`fvec_zero_eq`);
* `dim Q + 1 ≤ #(extreme points)`;
* a 1-dimensional polytope (an edge) has exactly two extreme points.
Hence edges have exactly two vertices and 2-faces have at least three.
-/

namespace Kalai5

open Set

variable {d : ℕ}

lemma eq_singleton_of_dim_eq_zero {G : Set (E d)} (hne : G.Nonempty) (h : dim G = 0) :
    ∃ g, G = {g} := by
  have hbot : vectorSpan ℝ G = ⊥ := Submodule.finrank_eq_zero.1 h
  have hsub := (vectorSpan_eq_bot_iff_subsingleton ℝ).1 hbot
  obtain ⟨g, hg⟩ := hne
  exact ⟨g, hsub.eq_singleton_of_mem hg⟩

lemma dim_singleton (g : E d) : dim ({g} : Set (E d)) = 0 := by
  simp [dim, vectorSpan_singleton]

/-- An extreme point of a polytope is an exposed point. -/
lemma singleton_mem_faces_of_extreme {S : Finset (E d)} {x : E d}
    (hx : x ∈ (convexHull ℝ (S : Set (E d))).extremePoints ℝ) :
    ({x} : Set (E d)) ∈ faces (convexHull ℝ (S : Set (E d))) := by
  classical
  have hxS : x ∈ S := by exact_mod_cast extremePoints_convexHull_subset hx
  set S' := S.erase x
  have hxS' : x ∉ convexHull ℝ (S' : Set (E d)) := by
    intro hmem
    have hsub : convexHull ℝ (S' : Set (E d)) ⊆ convexHull ℝ (S : Set (E d)) :=
      convexHull_mono (by rw [Finset.coe_erase]; exact Set.sdiff_subset)
    have h1 := inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hmem, hx⟩
    have h2 := extremePoints_convexHull_subset h1
    simp [S'] at h2
  obtain ⟨f, u, hfx, hfS'⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
    (Set.Finite.isClosed_convexHull ℝ S'.finite_toSet) hxS'
  have hlt : ∀ v ∈ S, v ≠ x → (-f) v < (-f) x := by
    intro v hv hvx
    have := hfS' v (subset_convexHull ℝ _ (Finset.mem_erase.2 ⟨hvx, hv⟩))
    simp only [ContinuousLinearMap.neg_apply]; linarith
  have hv : ∀ v ∈ S, (-f) v ≤ (-f) x := fun v hv => by
    by_cases hvx : v = x
    · rw [hvx]
    · exact (hlt v hv hvx).le
  refine ⟨Set.singleton_nonempty x, fun _ => ⟨-f, ?_⟩⟩
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro rfl
    exact ⟨subset_convexHull ℝ _ hxS, fun y hy => (le_on_convexHull (-f) hv hy).1⟩
  · rintro ⟨hz, hmax⟩
    have heq : (-f) z = (-f) x :=
      le_antisymm (le_on_convexHull (-f) hv hz).1 (hmax x (subset_convexHull ℝ _ hxS))
    have hmem := (le_on_convexHull (-f) hv hz).2 heq
    have hfilt : (S.filter fun v => (-f) v = (-f) x) = {x} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hv', hfv⟩
        by_contra hvx
        exact absurd hfv (hlt v hv' hvx).ne
      · rintro rfl; exact ⟨hxS, rfl⟩
    rw [hfilt, Finset.coe_singleton, convexHull_singleton] at hmem
    exact hmem

lemma extremePoints_finite (S : Finset (E d)) :
    ((convexHull ℝ (S : Set (E d))).extremePoints ℝ).Finite :=
  S.finite_toSet.subset extremePoints_convexHull_subset

/-- **The vertices of a polytope are its extreme points.** -/
lemma fvec_zero_eq (S : Finset (E d)) :
    fvec (convexHull ℝ (S : Set (E d))) 0 =
      ((convexHull ℝ (S : Set (E d))).extremePoints ℝ).ncard := by
  set Q := convexHull ℝ (S : Set (E d))
  have h : {F | F ∈ faces Q ∧ dim F = 0} =
      (fun x => ({x} : Set (E d))) '' (Q.extremePoints ℝ) := by
    ext F; constructor
    · rintro ⟨hF, hd⟩
      obtain ⟨g, rfl⟩ := eq_singleton_of_dim_eq_zero hF.1 hd
      exact ⟨g, isExtreme_singleton.1 hF.2.isExtreme, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨singleton_mem_faces_of_extreme hx, dim_singleton x⟩
  rw [fvec, h, Set.ncard_image_of_injective _ fun a b hab => Set.singleton_injective hab]

/-- A polytope is the convex hull of its extreme points. -/
lemma convexHull_extremePoints_eq (S : Finset (E d)) :
    convexHull ℝ ((convexHull ℝ (S : Set (E d))).extremePoints ℝ) =
      convexHull ℝ (S : Set (E d)) := by
  have hc : IsClosed (convexHull ℝ ((convexHull ℝ (S : Set (E d))).extremePoints ℝ)) :=
    Set.Finite.isClosed_convexHull ℝ (extremePoints_finite S)
  have := closure_convexHull_extremePoints (S.finite_toSet.isCompact_convexHull ℝ)
    (convex_convexHull ℝ _)
  rwa [hc.closure_eq] at this

/-- `dim Q + 1 ≤ #(extreme points of Q)` for a nonempty polytope. -/
lemma dim_add_one_le_ncard_extremePoints (S : Finset (E d)) (hS : S.Nonempty) :
    dim (convexHull ℝ (S : Set (E d))) + 1 ≤
      ((convexHull ℝ (S : Set (E d))).extremePoints ℝ).ncard := by
  classical
  set Q := convexHull ℝ (S : Set (E d))
  set T := (extremePoints_finite S).toFinset
  have hT : (T : Set (E d)) = Q.extremePoints ℝ := Set.Finite.coe_toFinset _
  have hTne : T.Nonempty := by
    obtain ⟨s, hs⟩ := hS
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hQ := convexHull_extremePoints_eq S
    rw [← hT, h, Finset.coe_empty, convexHull_empty] at hQ
    have : s ∈ convexHull ℝ (S : Set (E d)) := subset_convexHull ℝ _ hs
    rw [← hQ] at this; exact this
  obtain ⟨n, hn⟩ : ∃ n, T.card = n + 1 := ⟨T.card - 1, by
    have := Finset.card_pos.2 hTne; omega⟩
  have hspan : vectorSpan ℝ Q = vectorSpan ℝ (Q.extremePoints ℝ) := by
    rw [← direction_affineSpan, ← direction_affineSpan, ← affineSpan_convexHull (𝕜 := ℝ)
      (Q.extremePoints ℝ), convexHull_extremePoints_eq S]
  have hle := finrank_vectorSpan_image_finset_le (k := ℝ) id T hn
  rw [Finset.image_id, hT] at hle
  rw [Set.ncard_eq_toFinset_card _ (extremePoints_finite S)]
  show Module.finrank ℝ (vectorSpan ℝ Q) + 1 ≤ T.card
  rw [hspan]; omega

/-- **An edge has exactly two extreme points.** -/
lemma ncard_extremePoints_of_dim_one (S : Finset (E d))
    (h1 : dim (convexHull ℝ (S : Set (E d))) = 1) :
    ((convexHull ℝ (S : Set (E d))).extremePoints ℝ).ncard = 2 := by
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : dim (convexHull ℝ (S : Set (E d))) = 0 := by simp [h, dim]
    omega
  have hge := dim_add_one_le_ncard_extremePoints S hS
  refine le_antisymm ?_ (by omega)
  refine le_of_not_gt fun hlt => ?_
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    (Set.two_lt_ncard_iff (extremePoints_finite S)).1 hlt
  have hxQ := hx.1; have hyQ := hy.1; have hzQ := hz.1
  have hW1 : Module.finrank ℝ (vectorSpan ℝ (convexHull ℝ (S : Set (E d)))) = 1 := h1
  have hyxW : y - x ∈ vectorSpan ℝ (convexHull ℝ (S : Set (E d))) := vsub_mem_vectorSpan ℝ hyQ hxQ
  have hzxW : z - x ∈ vectorSpan ℝ (convexHull ℝ (S : Set (E d))) := vsub_mem_vectorSpan ℝ hzQ hxQ
  have hyx0 : (⟨y - x, hyxW⟩ : vectorSpan ℝ (convexHull ℝ (S : Set (E d)))) ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    simp only [ZeroMemClass.coe_zero, sub_eq_zero] at this
    exact hxy this.symm
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' _ hyx0).1 hW1 ⟨z - x, hzxW⟩
  have ht' : z = x + t • (y - x) := by
    have := congrArg Subtype.val ht
    simp only [SetLike.val_smul] at this
    rw [this]; abel
  rcases lt_trichotomy t 0 with htneg | ht0 | htpos
  · have h1t : (1 - t) ≠ 0 := by linarith
    have hseg : x ∈ openSegment ℝ z y := by
      refine ⟨1 / (1 - t), -t / (1 - t), by apply div_pos one_pos; linarith,
        by apply div_pos (by linarith); linarith, ?_, ?_⟩
      · field_simp; ring
      · rw [ht']
        match_scalars <;> field_simp <;> ring_nf
    have := ((mem_extremePoints.1 hx).2 z hzQ y hyQ hseg).1
    exact hxz this.symm
  · rw [ht0, zero_smul, add_zero] at ht'
    exact hxz ht'.symm
  · rcases lt_trichotomy t 1 with htlt | ht1 | htgt
    · have hseg : z ∈ openSegment ℝ x y :=
        ⟨1 - t, t, by linarith, htpos, by ring, by rw [ht']; module⟩
      have := ((mem_extremePoints.1 hz).2 x hxQ y hyQ hseg).1
      exact hxz this
    · rw [ht1, one_smul, add_sub_cancel] at ht'
      exact hyz ht'.symm
    · have ht0' : t ≠ 0 := by linarith
      have hseg : y ∈ openSegment ℝ x z := by
        refine ⟨1 - 1 / t, 1 / t, by
          rw [sub_pos, div_lt_one (by linarith)]; linarith,
          by positivity, by ring, ?_⟩
        rw [ht']
        match_scalars <;> field_simp <;> ring_nf
      have := ((mem_extremePoints.1 hy).2 x hxQ z hzQ hseg).1
      exact hxy this

end Kalai5
