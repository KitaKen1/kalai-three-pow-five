import Kalai5.Cube3.AuxCount
import Kalai5.Cube3.CubeSections
import Kalai5.LemmaB.Planar
import Kalai5.Small.General

/-!
# The centrally symmetric lift of a planar polygon

A point k is sent to (1,k-a), together with its negative. Convex position is
preserved at each of the two height faces. Full planar dimension forces the
lift to span three dimensions, so the origin is an interior point.
-/

namespace Kalai5.Cube3

open Set Module Pointwise

local notation "⟪" x ", " y "⟫" => inner ℝ x y

noncomputable def polygonLift (a k : E 2) : E 3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![1, (k-a) 0, (k-a) 1]

noncomputable def polygonLiftMap (a : E 2) : E 2 →ᵃ[ℝ] E 3 :=
  let L : E 2 →ₗ[ℝ] E 3 :=
    { toFun := fun k => (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0,k 0,k 1]
      map_add' := by intro k l; ext i; fin_cases i <;> simp
      map_smul' := by intro t k; ext i; fin_cases i <;> simp }
  AffineMap.const ℝ (E 2) (polygonLift a 0) + L.toAffineMap

lemma polygonLiftMap_apply (a k : E 2) : polygonLiftMap a k = polygonLift a k := by
  ext i; fin_cases i <;> simp [polygonLiftMap, polygonLift] <;> ring

lemma polygonLift_injective (a : E 2) : Function.Injective (polygonLift a) := by
  intro k l h
  have h1 := congrArg (fun p : E 3 => p 1) h
  have h2 := congrArg (fun p : E 3 => p 2) h
  ext i; fin_cases i <;> simp [polygonLift] at h1 h2 ⊢ <;> linarith

noncomputable def signedPolygon (A : Finset (E 2)) (a : E 2) : Finset (E 3) :=
  A.image (polygonLift a) ∪ A.image (fun k => -polygonLift a k)

lemma mem_signedPolygon {A : Finset (E 2)} {a : E 2} {y : E 3} :
    y ∈ signedPolygon A a ↔
      (∃ k ∈ A, polygonLift a k = y) ∨ (∃ k ∈ A, -polygonLift a k = y) := by
  simp [signedPolygon]

lemma signedPolygon_neg {A : Finset (E 2)} {a : E 2} {y : E 3}
    (hy : y ∈ signedPolygon A a) : -y ∈ signedPolygon A a := by
  rcases mem_signedPolygon.1 hy with ⟨k,hk,rfl⟩ | ⟨k,hk,rfl⟩
  · exact mem_signedPolygon.2 (Or.inr ⟨k,hk,rfl⟩)
  · exact mem_signedPolygon.2 (Or.inl ⟨k,hk,by simp⟩)

lemma signedPolygon_symm (A : Finset (E 2)) (a : E 2) :
    -(signedPolygon A a : Set (E 3)) = (signedPolygon A a : Set (E 3)) := by
  ext y
  simp only [Set.mem_neg]
  exact ⟨fun h => by simpa using signedPolygon_neg h, signedPolygon_neg⟩

lemma signedPolygon_hull_symm {A : Finset (E 2)} {a : E 2} {y : E 3}
    (hy : y ∈ convexHull ℝ (signedPolygon A a : Set (E 3))) :
    -y ∈ convexHull ℝ (signedPolygon A a : Set (E 3)) := by
  have h : -(convexHull ℝ (signedPolygon A a : Set (E 3))) =
      convexHull ℝ (signedPolygon A a : Set (E 3)) := by
    rw [← convexHull_neg, signedPolygon_symm]
  rw [← h]
  exact Set.neg_mem_neg.2 hy

/-- The lifted generators span whenever the original set spans the plane affinely. -/
lemma signedPolygon_span (A : Finset (E 2)) (a : E 2) (hA : A.Nonempty)
    (hdim : dim (convexHull ℝ (A : Set (E 2))) = 2) :
    Submodule.span ℝ (signedPolygon A a : Set (E 3)) = ⊤ := by
  have hspan : vectorSpan ℝ (convexHull ℝ (A : Set (E 2))) = vectorSpan ℝ (A : Set (E 2)) := by
    simpa only [direction_affineSpan] using
      congrArg (fun S : AffineSubspace ℝ (E 2) => S.direction)
        (affineSpan_convexHull (𝕜 := ℝ) (A : Set (E 2)))
  have hdimA : dim (A : Set (E 2)) = 2 := by
    unfold dim at hdim ⊢
    rwa [hspan] at hdim
  rw [← Submodule.orthogonal_eq_bot_iff]
  apply (Submodule.eq_bot_iff _).2
  intro z hz
  have hzA : ∀ k ∈ A, ⟪polygonLift a k, z⟫ = 0 := by
    intro k hk
    exact (Submodule.mem_orthogonal _ _).1 hz _
      (Submodule.subset_span (mem_signedPolygon.2 (Or.inl ⟨k,hk,rfl⟩)))
  let b : E 2 := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![z 1,z 2]
  have hconst : ∀ k ∈ (A : Set (E 2)), ⟪k,b⟫ = ⟪a,b⟫ - z 0 := by
    intro k hk
    have h := hzA k hk
    simp [polygonLift, PiLp.inner_apply, Fin.sum_univ_three] at h
    simp [b, LemmaB.Eight.inner_E2]
    nlinarith
  have hb : b = 0 := by
    by_contra hb
    have hle := LemmaB.dim_le_one_of_const hb hconst
    rw [hdimA] at hle
    omega
  have hz1 : z 1 = 0 := congrArg (fun b : E 2 => b 0) hb
  have hz2 : z 2 = 0 := congrArg (fun b : E 2 => b 1) hb
  obtain ⟨k,hk⟩ := hA
  have hz0 := hzA k hk
  simp [polygonLift, PiLp.inner_apply, Fin.sum_univ_three, hz1, hz2] at hz0
  ext i; fin_cases i <;> simp [hz0,hz1,hz2]

lemma signedPolygon_zero_interior (A : Finset (E 2)) (a : E 2) (hA : A.Nonempty)
    (hdim : dim (convexHull ℝ (A : Set (E 2))) = 2) :
    (0 : E 3) ∈ interior (convexHull ℝ (signedPolygon A a : Set (E 3))) := by
  let K := convexHull ℝ (signedPolygon A a : Set (E 3))
  have hconv : Convex ℝ K := convex_convexHull ℝ _
  obtain ⟨k,hk⟩ := hA
  have hkK : polygonLift a k ∈ K := subset_convexHull ℝ _
    (mem_signedPolygon.2 (Or.inl ⟨k,hk,rfl⟩))
  have hzero : (0 : E 3) ∈ K := by
    have h := hconv hkK (signedPolygon_hull_symm hkK)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    simpa [← smul_add] using h
  have hsp : Submodule.span ℝ K = ⊤ := by
    apply top_unique
    rw [← signedPolygon_span A a ⟨k,hk⟩ hdim]
    exact Submodule.span_mono (subset_convexHull ℝ _)
  have hasp : affineSpan ℝ K = ⊤ := by
    apply SetLike.coe_injective
    have h := affineSpan_insert_zero (k := ℝ) K
    rw [Set.insert_eq_of_mem hzero, hsp] at h
    exact h
  obtain ⟨z,hz⟩ := hconv.interior_nonempty_iff_affineSpan_eq_top.2 hasp
  have hneg : -z ∈ interior K := by
    have hsub : (fun x : E 3 => -x) ⁻¹' interior K ⊆ K := fun x hx => by
      simpa using signedPolygon_hull_symm (interior_subset hx)
    exact interior_maximal hsub (isOpen_interior.preimage continuous_neg) (by simpa using hz)
  have h := hconv.interior hz hneg (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simpa [← smul_add] using h

/-- Injective affine images preserve the extreme points used here. -/
lemma extreme_affine_image {d m : ℕ} (L : E d →ᵃ[ℝ] E m) (hL : Function.Injective L)
    {S : Set (E d)} {p : E d} (hp : p ∈ S.extremePoints ℝ) :
    L p ∈ (L '' S).extremePoints ℝ := by
  refine mem_extremePoints.2 ⟨⟨p,hp.1,rfl⟩, ?_⟩
  rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩ hseg
  rw [← image_openSegment ℝ L u v] at hseg
  obtain ⟨w,hw,he⟩ := hseg
  have hwp := hL he
  subst w
  obtain ⟨hu',hv'⟩ := (mem_extremePoints.1 hp).2 u hu v hv hw
  exact ⟨congrArg L hu',congrArg L hv'⟩

lemma polygonLift_extreme_positive {A : Finset (E 2)} {a p : E 2}
    (hp : p ∈ (convexHull ℝ (A : Set (E 2))).extremePoints ℝ) :
    polygonLift a p ∈ (convexHull ℝ (A.image (polygonLift a) : Set (E 3))).extremePoints ℝ := by
  have hL : Function.Injective (polygonLiftMap a) := by
    intro k l h
    apply polygonLift_injective a
    simpa only [polygonLiftMap_apply] using h
  have h := extreme_affine_image (polygonLiftMap a) hL hp
  rw [AffineMap.image_convexHull] at h
  simpa only [Finset.coe_image, polygonLiftMap_apply] using h

/-- The height-one face consists exactly of the positive lifted polygon. -/
lemma signedPolygon_top {A : Finset (E 2)} {a : E 2} {y : E 3}
    (hy : y ∈ convexHull ℝ (signedPolygon A a : Set (E 3))) :
    |y 0| ≤ 1 ∧ (y 0 = 1 → y ∈ convexHull ℝ (A.image (polygonLift a) : Set (E 3))) := by
  classical
  let l : StrongDual ℝ (E 3) := (EuclideanSpace.proj 0)
  have hl : ∀ w ∈ signedPolygon A a, l w ≤ 1 := by
    intro w hw
    rcases mem_signedPolygon.1 hw with ⟨k,hk,rfl⟩ | ⟨k,hk,rfl⟩ <;>
      norm_num [l, polygonLift]
  have hn : ∀ w ∈ signedPolygon A a, (-l) w ≤ 1 := by
    intro w hw
    rcases mem_signedPolygon.1 hw with ⟨k,hk,rfl⟩ | ⟨k,hk,rfl⟩ <;>
      norm_num [l, polygonLift]
  have hp := le_on_convexHull l hl hy
  have hm := le_on_convexHull (-l) hn hy
  have hfilt : (signedPolygon A a).filter (fun w => l w = 1) = A.image (polygonLift a) := by
    ext w
    constructor
    · rintro hw
      obtain ⟨hw,he⟩ := Finset.mem_filter.1 hw
      rcases mem_signedPolygon.1 hw with ⟨k,hk,rfl⟩ | ⟨k,hk,rfl⟩
      · exact Finset.mem_image.2 ⟨k,hk,rfl⟩
      · norm_num [l,polygonLift] at he
    · intro hw
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hw
      exact Finset.mem_filter.2 ⟨mem_signedPolygon.2 (Or.inl ⟨k,hk,rfl⟩),by simp [l,polygonLift]⟩
  refine ⟨abs_le.2 ⟨?_,hp.1⟩, ?_⟩
  · have h := hm.1
    change -y 0 ≤ 1 at h
    linarith
  · intro he
    have h := hp.2 he
    rwa [hfilt] at h

lemma polygonLift_extreme_signed {A : Finset (E 2)} {a p : E 2}
    (hp : p ∈ (convexHull ℝ (A : Set (E 2))).extremePoints ℝ) :
    polygonLift a p ∈ (convexHull ℝ (signedPolygon A a : Set (E 3))).extremePoints ℝ := by
  have hpA : p ∈ A := extremePoints_convexHull_subset hp
  have hext := polygonLift_extreme_positive (a := a) hp
  refine mem_extremePoints.2 ⟨subset_convexHull ℝ _
    (mem_signedPolygon.2 (Or.inl ⟨p,hpA,rfl⟩)), ?_⟩
  intro u hu v hv hseg
  obtain ⟨t,s,ht,hs,hts,he⟩ := hseg
  have he0 : t * u 0 + s * v 0 = 1 := by
    simpa [polygonLift] using congrArg (fun w : E 3 => w 0) he
  obtain ⟨hu0,hv0⟩ := endpoint_combination (signedPolygon_top hu).1 (signedPolygon_top hv).1
    ht hs hts he0 (Or.inl rfl)
  exact (mem_extremePoints.1 hext).2 u ((signedPolygon_top hu).2 hu0)
    v ((signedPolygon_top hv).2 hv0) ⟨t,s,ht,hs,hts,he⟩

lemma signedPolygon_convpos {A : Finset (E 2)} (a : E 2)
    (hA : ∀ p ∈ A, p ∈ (convexHull ℝ (A : Set (E 2))).extremePoints ℝ) :
    ∀ p ∈ signedPolygon A a,
      p ∈ (convexHull ℝ (signedPolygon A a : Set (E 3))).extremePoints ℝ := by
  intro p hp
  rcases mem_signedPolygon.1 hp with ⟨k,hk,rfl⟩ | ⟨k,hk,rfl⟩
  · exact polygonLift_extreme_signed (hA k hk)
  · exact CS.neg_mem_extremePoints (fun _ h => signedPolygon_hull_symm h)
      (polygonLift_extreme_signed (hA k hk))

lemma signedPolygon_card (A : Finset (E 2)) (a : E 2) :
    (signedPolygon A a).card = 2 * A.card := by
  classical
  have hdis : Disjoint (A.image (polygonLift a)) (A.image (fun k => -polygonLift a k)) := by
    apply Finset.disjoint_left.2
    intro p hp hn
    obtain ⟨k,hk,hkp⟩ := Finset.mem_image.1 hp
    obtain ⟨l,hl,hlp⟩ := Finset.mem_image.1 hn
    have h := congrArg (fun y : E 3 => y 0) (hkp.trans hlp.symm)
    norm_num [polygonLift] at h
  have hneg : Function.Injective (fun k => -polygonLift a k) := by
    intro k l h
    exact polygonLift_injective a (neg_injective h)
  rw [signedPolygon, Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ (polygonLift_injective a),
    Finset.card_image_of_injective _ hneg]
  omega

theorem signedPolygon_vertices {A : Finset (E 2)} (a : E 2)
    (hA : ∀ p ∈ A, p ∈ (convexHull ℝ (A : Set (E 2))).extremePoints ℝ) :
    fvec (convexHull ℝ (signedPolygon A a : Set (E 3))) 0 = 2 * A.card := by
  have hext : (convexHull ℝ (signedPolygon A a : Set (E 3))).extremePoints ℝ =
      (signedPolygon A a : Set (E 3)) :=
    Subset.antisymm extremePoints_convexHull_subset (signedPolygon_convpos a hA)
  rw [fvec_zero_eq, hext, Set.ncard_coe_finset, signedPolygon_card]

lemma inner_polygonLift (a k : E 2) (y : E 3) :
    ⟪polygonLift a k,y⟫ = y 0 + y 1 * (k-a) 0 + y 2 * (k-a) 1 := by
  simp [polygonLift, PiLp.inner_apply, Fin.sum_univ_three]

theorem mem_signedPolygon_polar {A : Finset (E 2)} {a : E 2} {y : E 3} :
    y ∈ polarSet (convexHull ℝ (signedPolygon A a : Set (E 3))) ↔
      ∀ k ∈ A, |y 0 + y 1 * (k-a) 0 + y 2 * (k-a) 1| ≤ 1 := by
  rw [mem_polarSet_convexHull]
  constructor
  · intro h k hk
    have hp := h _ (mem_signedPolygon.2 (Or.inl ⟨k,hk,rfl⟩))
    have hn := h _ (mem_signedPolygon.2 (Or.inr ⟨k,hk,rfl⟩))
    rw [inner_polygonLift] at hp
    rw [inner_neg_left, inner_polygonLift] at hn
    exact abs_le.2 ⟨by linarith,hp⟩
  · intro h p hp
    rcases mem_signedPolygon.1 hp with ⟨k,hk,rfl⟩ | ⟨k,hk,rfl⟩
    · rw [inner_polygonLift]; exact (abs_le.1 (h k hk)).2
    · rw [inner_neg_left, inner_polygonLift]; linarith [(abs_le.1 (h k hk)).1]

/-- An actual seven-element vertex family of the auxiliary polar. -/
theorem signedPolygon_polar_seven {A : Finset (E 2)} (a : E 2)
    (hA : ∀ p ∈ A, p ∈ (convexHull ℝ (A : Set (E 2))).extremePoints ℝ)
    (h5 : 5 ≤ A.card) :
    ∃ f : Fin 7 → E 3, Function.Injective f ∧
      ∀ i, f i ∈ (polarSet (convexHull ℝ (signedPolygon A a : Set (E 3)))).extremePoints ℝ := by
  classical
  have hne : A.Nonempty := Finset.card_pos.1 (by omega)
  have hd := LemmaB.dim_eq_two_of_convpos hA (by omega : 3 ≤ A.card)
  have h0 := signedPolygon_zero_interior A a hne hd
  have h7 := seven_polar_vertices_of_ten_vertices (signedPolygon A a) h0
    (by rw [signedPolygon_vertices a hA]; omega)
  obtain ⟨W,hW⟩ := exists_polarSet_eq_convexHull h0
  rw [hW, fvec_zero_eq, ← hW] at h7
  let hf := extremePoints_polarSet_finite (signedPolygon A a)
  let S := hf.toFinset
  have hS : 7 ≤ S.card := by
    change 7 ≤ hf.toFinset.card
    rwa [← Set.ncard_eq_toFinset_card _ hf]
  obtain ⟨e⟩ : Nonempty (Fin 7 ↪ S) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hS)
  refine ⟨fun i => (e i).val, ?_, ?_⟩
  · intro i j h
    exact e.injective (Subtype.ext h)
  · intro i
    exact (Set.Finite.mem_toFinset hf).1 (e i).property

end Kalai5.Cube3
