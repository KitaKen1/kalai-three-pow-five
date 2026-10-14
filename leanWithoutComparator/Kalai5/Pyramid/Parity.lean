import Kalai5.Pyramid.FullPyramid

/-!
# The exceptional facet forces `f₄ ≡ 0 (mod 4)`

If a centrally symmetric 5-polytope with 14 vertices has a facet with row `(7,15,14,6; 29)`, it
is the linear image of the bipyramid over a centrally symmetric 4-polytope `R`
(`IsCSPolytope5.exists_bipyramid_model`).  The facets of a bipyramid are the two pyramids over
each facet of `R` (`fvec_bipyr_facets`, via the vertices of the polar prism), and `R` has an even
number of facets.  Hence `f₄(P) = 2 f₃(R) ≡ 0 (mod 4)`; in particular the exceptional row cannot
occur when `f₄ = 22` (`IsCSPolytope5.excRow_not_mem_of_mod`), without any appeal to SWZ.
-/

namespace Kalai5

open Set

variable {d : ℕ}

/-! ### Dimensions and face numbers under injective linear maps -/

lemma dim_image_of_injective {m k : ℕ} (L : E m →ₗ[ℝ] E k) (hL : Function.Injective L)
    (S : Set (E m)) : dim (L '' S) = dim S := by
  change Module.finrank ℝ (vectorSpan ℝ (L '' S)) = Module.finrank ℝ (vectorSpan ℝ S)
  have h := AffineMap.map_vectorSpan (k := ℝ) (f := L.toAffineMap) (s := S)
  rw [LinearMap.toAffineMap_linear, LinearMap.coe_toAffineMap] at h
  rw [← h]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective L hL _)).symm

lemma fvec_image_of_injective {m k : ℕ} (L : E m →ₗ[ℝ] E k) (hL : Function.Injective L)
    (K : Set (E m)) (j : ℕ) : fvec (L '' K) j = fvec K j := by
  unfold fvec
  symm
  refine Set.ncard_congr (fun F _ => L '' F) ?_ ?_ ?_
  · rintro F ⟨hF, hd⟩
    exact ⟨image_mem_faces_of_injective L hL hF, by rw [dim_image_of_injective L hL]; exact hd⟩
  · intro F F' _ _ h
    exact Set.image_injective.2 hL h
  · rintro G ⟨hG, hd⟩
    have hGr : G ⊆ Set.range L := (face_subset hG).trans (Set.image_subset_range _ _)
    refine ⟨L ⁻¹' G, ⟨preimage_mem_faces_of_injective L hL hG, ?_⟩,
      Set.image_preimage_eq_of_subset hGr⟩
    have := dim_image_of_injective L hL (L ⁻¹' G)
    rw [Set.image_preimage_eq_of_subset hGr] at this
    rw [← this]; exact hd

/-! ### Vertices of a prism -/

variable {n : ℕ}

/-- `y ↦ (y, t)` as an affine map. -/
noncomputable def liftAt (n : ℕ) (t : ℝ) : E n →ᵃ[ℝ] E (n + 1) :=
  (embZero n).toAffineMap + AffineMap.const ℝ (E n) (mkPt 0 t)

lemma liftAt_apply (t : ℝ) (y : E n) : liftAt n t y = mkPt y t := by
  refine PiLp.ext fun j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [liftAt]

lemma liftAt_linear (t : ℝ) : (liftAt n t).linear = embZero n := by
  simp [liftAt]

lemma embZero_injective : Function.Injective (embZero n) := fun y y' h => by
  have := congrArg fstPart h
  simpa using this

lemma mkPt_fstPart (z : E (n + 1)) : mkPt (fstPart z) (z (Fin.last n)) = z := by
  refine PiLp.ext fun j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) j <;> simp

lemma prismFace_fixed_eq (F : Set (E n)) (k : Fin 3) (t : ℝ) (ht : segFace k = {t}) :
    prismFace F k = liftAt n t '' F := by
  ext z
  constructor
  · rintro ⟨hz1, hz2⟩
    rw [ht, Set.mem_singleton_iff] at hz2
    refine ⟨fstPart z, hz1, ?_⟩
    rw [liftAt_apply, ← hz2, mkPt_fstPart]
  · rintro ⟨y, hy, rfl⟩
    rw [liftAt_apply]
    refine ⟨by simpa using hy, ?_⟩
    rw [ht, mkPt_last]
    exact Set.mem_singleton t

lemma dim_liftAt_image (t : ℝ) (S : Set (E n)) : dim (liftAt n t '' S) = dim S := by
  change Module.finrank ℝ (vectorSpan ℝ (liftAt n t '' S)) = Module.finrank ℝ (vectorSpan ℝ S)
  rw [← AffineMap.map_vectorSpan, liftAt_linear]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ embZero_injective _)).symm

lemma dim_prismFace_of_ne_two (F : Set (E n)) (k : Fin 3) (hk : k ≠ 2) :
    dim (prismFace F k) = dim F :=
  match k, hk with
  | 0, _ => by rw [prismFace_fixed_eq F 0 1 rfl, dim_liftAt_image]
  | 1, _ => by rw [prismFace_fixed_eq F 1 (-1) rfl, dim_liftAt_image]
  | 2, h => absurd rfl h

lemma dim_prismFace_two_ne_zero {F : Set (E n)} (hF : F.Nonempty) : dim (prismFace F 2) ≠ 0 := by
  obtain ⟨y, hy⟩ := hF
  intro h0
  have hbot : vectorSpan ℝ (prismFace F 2) = ⊥ := Submodule.finrank_eq_zero.1 h0
  have h1 : mkPt y 1 ∈ prismFace F 2 := ⟨by simpa using hy, by simp [segFace]⟩
  have h2 : mkPt y (-1) ∈ prismFace F 2 := ⟨by simpa using hy, by norm_num [segFace]⟩
  have hmem := vsub_mem_vectorSpan ℝ h1 h2
  rw [hbot, Submodule.mem_bot, vsub_eq_sub, sub_eq_zero] at hmem
  have := congrArg (fun z : E (n + 1) => z (Fin.last n)) hmem
  simp at this
  norm_num at this

/-- **A prism has twice as many vertices as its base.** -/
theorem fvec_prism_zero (A : Set (E n)) : fvec (prism A) 0 = 2 * fvec A 0 := by
  unfold fvec
  have h2 : ({F | F ∈ faces A ∧ dim F = 0} ×ˢ ({0, 1} : Set (Fin 3))).ncard =
      {F | F ∈ faces A ∧ dim F = 0}.ncard * 2 := by
    rw [Set.ncard_prod, Set.ncard_pair (by decide)]
  rw [mul_comm, ← h2]
  symm
  refine Set.ncard_congr (fun Fk _ => prismFace Fk.1 Fk.2) ?_ ?_ ?_
  · rintro ⟨F, k⟩ ⟨⟨hF, hd⟩, hk⟩
    refine ⟨prismFace_mem_faces hF k, ?_⟩
    have hk2 : k ≠ 2 := by
      rcases hk with h | h
      · change k = 0 at h
        rw [h]; decide
      · change k ∈ ({1} : Set (Fin 3)) at h
        rw [Set.mem_singleton_iff] at h
        rw [h]; decide
    rw [dim_prismFace_of_ne_two F k hk2]
    exact hd
  · rintro ⟨F, k⟩ ⟨F', k'⟩ ⟨⟨hF, -⟩, -⟩ ⟨⟨hF', -⟩, -⟩ h
    obtain ⟨h1, h2⟩ := prismFace_inj hF.1 hF'.1 h
    exact Prod.ext h1 h2
  · rintro H ⟨hH, hd⟩
    obtain ⟨F, hF, k, rfl⟩ := exists_prismFace hH
    by_cases hk : k = 2
    · subst hk
      exact absurd hd (dim_prismFace_two_ne_zero hF.1)
    · refine ⟨(F, k), ⟨⟨hF, ?_⟩, ?_⟩, rfl⟩
      · rw [← dim_prismFace_of_ne_two F k hk]; exact hd
      · fin_cases k
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd rfl hk

/-- **Facets of a bipyramid**: twice the facets of the base. -/
theorem fvec_bipyr_facets {V : Finset (E 4)}
    (h0 : (0 : E 4) ∈ interior (convexHull ℝ (V : Set (E 4)))) :
    fvec (convexHull ℝ ((bipyrV V : Finset (E (4 + 1))) : Set (E (4 + 1)))) 4 =
      2 * fvec (convexHull ℝ (V : Set (E 4))) 3 := by
  have h1 := fvec_polarSet_zero (zero_mem_interior_bipyr h0) (by norm_num : 1 ≤ 4 + 1)
  rw [polarSet_bipyr, fvec_prism_zero] at h1
  have h2 := fvec_polarSet_zero h0 (by norm_num : 1 ≤ 4)
  rw [h2] at h1
  simpa using h1.symm

/-! ### Centrally symmetric polytopes have an even number of `k`-faces -/

lemma IsCSPolytope.eq_of_neg_eq {P F : Set (E d)} (hP : IsCSPolytope d P) (hF : F ∈ faces P)
    (hneg : -F = F) : F = P := by
  obtain ⟨x, hx⟩ := hF.1
  have hnx : -x ∈ F := by rw [← hneg]; simpa using hx
  have h0 : (0 : E d) ∈ F := by
    have := face_convex hP.convex hF hx hnx (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa [← smul_add] using this
  exact face_eq_of_mem_interior hF h0 hP.zero_mem_interior

theorem IsCSPolytope.even_fvec {P : Set (E d)} (hP : IsCSPolytope d P) (k : ℕ) (hk : k < d) :
    Even (fvec P k) := by
  classical
  have hfin : {F | F ∈ faces P ∧ dim F = k}.Finite :=
    (faces_finite hP.toIsPolytope).subset fun F hF => hF.1
  rw [fvec, Set.ncard_eq_toFinset_card _ hfin]
  refine even_card_of_involution _ (fun F => -F) ?_ (fun F _ => neg_neg F) ?_
  · intro F hF
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hF ⊢
    exact ⟨neg_mem_faces hP.symm hF.1, by rw [dim_neg]; exact hF.2⟩
  · intro F hF hFF
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hF
    have := hP.eq_of_neg_eq hF.1 hFF
    have hd := dim_eq_of_interior hP.convex hP.full
    rw [← this, hF.2] at hd
    omega

/-! ### The exceptional row at `f₄ ≡ 2 (mod 4)` -/

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **No exceptional facet unless `4 ∣ f₄`.** -/
theorem IsCSPolytope5.excRow_not_mem_of_mod (h14 : fvec P 0 = 14) (hmod : fvec P 4 % 4 = 2) :
    excRow ∉ facetRows P := by
  intro hR
  obtain ⟨V', L, hLinj, hR'cs, hLbip⟩ := hP.exists_bipyramid_model h14 hR
  have h1 : fvec P 4 = 2 * fvec (convexHull ℝ (V' : Set (E 4))) 3 := by
    rw [← hLbip, fvec_image_of_injective L hLinj, fvec_bipyr_facets hR'cs.zero_mem_interior]
  obtain ⟨m, hm⟩ := hR'cs.even_fvec 3 (by norm_num)
  omega

end cs

end Kalai5
