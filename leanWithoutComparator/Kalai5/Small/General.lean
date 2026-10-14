import Kalai5.Small.Model
import Kalai5.Polar.General

/-!
# Kalai's bound for centrally symmetric polytopes with at most `2d + 2` vertices

The argument of `Kalai5.Small.Model` in every dimension `d ≥ 1` (namespace `Kalai5.CS`): the polar
of a centrally symmetric `d`-polytope with at most `2d + 2` vertices is linearly isomorphic to a
central section of the `(d+1)`-cube by a hyperplane with nonnegative normal, and such sections
have at least `3^d` nonempty faces (`three_pow_le_three_mul_sectionFaceCount`).

Main results: `IsCSPolytope.three_pow_le_of_fvec_zero_le` (at most `2d + 2` vertices) and
`IsCSPolytope.three_pow_le_of_fvec_facets_le` (at most `2d + 2` facets).
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace CS

variable {d : ℕ}

lemma eq_zero_of_eq_neg {x : E d} (h : x = -x) : x = 0 := by
  have h2 : (2 : ℝ) • x = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel x
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- A symmetric finite set without `0` has a half `R` with `X ⊆ R ∪ -R`. -/
lemma exists_half : ∀ N : ℕ, ∀ X : Finset (E d), X.card = N → (∀ x ∈ X, -x ∈ X) → (0 : E d) ∉ X →
    ∃ R ⊆ X, (∀ x ∈ X, x ∈ R ∨ -x ∈ R) ∧ 2 * R.card ≤ X.card := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro X hN hsymm h0
    rcases X.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
    · have hnx : -x ∈ X := hsymm x hx
      have hxne : -x ≠ x := fun h => h0 (by rw [← eq_zero_of_eq_neg h.symm]; exact hx)
      have hnx' : -x ∈ X.erase x := Finset.mem_erase.2 ⟨hxne, hnx⟩
      set X' := (X.erase x).erase (-x) with hX'
      have hcard1 : (X.erase x).card + 1 = X.card := Finset.card_erase_add_one hx
      have hcard2 : X'.card + 1 = (X.erase x).card := Finset.card_erase_add_one hnx'
      have hsymm' : ∀ y ∈ X', -y ∈ X' := by
        intro y hy
        rw [hX', Finset.mem_erase, Finset.mem_erase] at hy ⊢
        obtain ⟨hy1, hy2, hy3⟩ := hy
        refine ⟨fun h => hy2 (by rw [← neg_neg y, h, neg_neg]), fun h => hy1 ?_, hsymm y hy3⟩
        rw [← neg_neg y, h]
      have h0' : (0 : E d) ∉ X' := fun h =>
        h0 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
      obtain ⟨R', hR'X, hR'cov, hR'card⟩ := ih X'.card (by omega) X' rfl hsymm' h0'
      refine ⟨insert x R', ?_, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact hx
        · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hR'X hy))
      · intro y hy
        by_cases hyx : y = x
        · left; rw [hyx]; exact Finset.mem_insert_self _ _
        · by_cases hynx : y = -x
          · right; rw [hynx, neg_neg]; exact Finset.mem_insert_self _ _
          · have hy' : y ∈ X' := by
              rw [hX', Finset.mem_erase, Finset.mem_erase]
              exact ⟨hynx, hyx, hy⟩
            rcases hR'cov y hy' with h | h
            · left; exact Finset.mem_insert_of_mem h
            · right; exact Finset.mem_insert_of_mem h
      · have := Finset.card_insert_le x R'
        omega

/-- **`d + 1` vectors cover at most `2d + 2` symmetric vertices up to sign.** -/
lemma exists_cover (X : Finset (E d)) (hsymm : ∀ x ∈ X, -x ∈ X) (h0 : (0 : E d) ∉ X)
    (h12 : X.card ≤ 2 * d + 2) :
    ∃ v : Fin (d + 1) → E d, (∀ i, v i ∈ X ∨ v i = 0) ∧ ∀ x ∈ X, ∃ i, x = v i ∨ x = -v i := by
  classical
  obtain ⟨R, hRX, hcov, hcard⟩ := exists_half _ X rfl hsymm h0
  have hR6 : R.card ≤ d + 1 := by omega
  set e := R.equivFin
  obtain ⟨v, hv⟩ : ∃ v : Fin (d + 1) → E d,
      ∀ i, v i = if h : (i : ℕ) < R.card then ((e.symm ⟨i, h⟩ : R) : E d) else 0 :=
    ⟨_, fun _ => rfl⟩
  have key : ∀ y ∈ R, ∃ i : Fin (d + 1), v i = y := by
    intro y hy
    have hlt : ((e ⟨y, hy⟩ : Fin R.card) : ℕ) < R.card := (e ⟨y, hy⟩).2
    refine ⟨⟨e ⟨y, hy⟩, by omega⟩, ?_⟩
    rw [hv]
    split_ifs with h'
    · simp
    · exact absurd hlt h'
  refine ⟨v, fun i => ?_, fun x hx => ?_⟩
  · rw [hv]
    split_ifs with h
    · left; exact hRX (e.symm ⟨i, h⟩).2
    · right; rfl
  · rcases hcov x hx with h | h
    · obtain ⟨i, hi⟩ := key x h
      exact ⟨i, Or.inl hi.symm⟩
    · obtain ⟨i, hi⟩ := key (-x) h
      exact ⟨i, Or.inr (by rw [hi, neg_neg])⟩

lemma neg_mem_extremePoints {P : Set (E d)} (hsymm : ∀ x ∈ P, -x ∈ P) {x : E d}
    (hx : x ∈ P.extremePoints ℝ) : -x ∈ P.extremePoints ℝ := by
  rw [mem_extremePoints] at hx ⊢
  refine ⟨hsymm x hx.1, fun y hy z hz hxyz => ?_⟩
  have h : x ∈ openSegment ℝ (-y) (-z) := by
    obtain ⟨a, b, ha, hb, hab, h⟩ := hxyz
    exact ⟨a, b, ha, hb, hab, by rw [smul_neg, smul_neg, ← neg_add, h, neg_neg]⟩
  obtain ⟨h1, h2⟩ := hx.2 (-y) (hsymm y hy) (-z) (hsymm z hz) h
  exact ⟨by rw [← h1, neg_neg], by rw [← h2, neg_neg]⟩

lemma zero_not_mem_extremePoints {P : Set (E d)} (hP : IsCSPolytope d P) (hd : 0 < d) :
    (0 : E d) ∉ P.extremePoints ℝ := by
  intro h0
  obtain ⟨r, hr, hball⟩ :=
    Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hP.zero_mem_interior)
  obtain ⟨u, hu⟩ : ∃ u : E d, u = (r / 2) • EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) := ⟨_, rfl⟩
  have hnorm : ‖u‖ = r / 2 := by
    rw [hu, norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have huP : u ∈ P := hball (by rw [Metric.mem_ball, dist_zero_right, hnorm]; linarith)
  have hnuP : -u ∈ P := hP.symm u huP
  have hseg : (0 : E d) ∈ openSegment ℝ u (-u) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by rw [smul_neg, add_neg_cancel]⟩
  have hu0 : u = 0 := ((mem_extremePoints.1 h0).2 u huP (-u) hnuP hseg).1
  rw [hu0, norm_zero] at hnorm
  linarith

/-! ### The coordinate map -/

/-- `y ↦ (⟪y, vᵢ⟫)ᵢ`. -/
noncomputable def coordMap (v : Fin (d + 1) → E d) : E d →ₗ[ℝ] E (d + 1) where
  toFun y := WithLp.toLp 2 (fun i => ⟪y, v i⟫)
  map_add' y z := by
    refine PiLp.ext fun i => ?_
    simp [inner_add_left]
  map_smul' c y := by
    refine PiLp.ext fun i => ?_
    simp [real_inner_smul_left]

lemma coordMap_apply (v : Fin (d + 1) → E d) (y : E d) (i : Fin (d + 1)) : coordMap v y i = ⟪y, v i⟫ := rfl


section cover

variable {P : Set (E d)} {X : Finset (E d)} (hPX : P = convexHull ℝ (X : Set (E d))) {v : Fin (d + 1) → E d}
  (hvP : ∀ i, v i ∈ P) (hvP' : ∀ i, -v i ∈ P) (hcov : ∀ x ∈ X, ∃ i, x = v i ∨ x = -v i)
include hPX hvP hvP' hcov

/-- **The polar is cut out by the `d + 1` slabs.** -/
lemma mem_polar_iff (y : E d) : y ∈ polarSet P ↔ ∀ i, -1 ≤ ⟪y, v i⟫ ∧ ⟪y, v i⟫ ≤ 1 := by
  constructor
  · intro hy i
    have h1 : ⟪v i, y⟫ ≤ 1 := hy (v i) (hvP i)
    have h2 : ⟪-v i, y⟫ ≤ 1 := hy (-v i) (hvP' i)
    rw [inner_neg_left] at h2
    rw [real_inner_comm] at h1 h2
    constructor <;> linarith
  · intro h
    rw [hPX, mem_polarSet_convexHull]
    intro x hx
    obtain ⟨i, rfl | rfl⟩ := hcov x hx
    · rw [real_inner_comm]; exact (h i).2
    · rw [inner_neg_left, real_inner_comm]; linarith [(h i).1]

lemma coordMap_injective (h0 : (0 : E d) ∈ interior P) : Function.Injective (coordMap v) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  have hzero : ∀ i, ⟪y, v i⟫ = 0 := fun i => by
    rw [← coordMap_apply, hy]
    rfl
  have hmem : ∀ t : ℝ, t • y ∈ polarSet P := fun t => by
    rw [mem_polar_iff hPX hvP hvP' hcov]
    intro i
    rw [real_inner_smul_left, hzero i, mul_zero]
    norm_num
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (polarSet_isBounded h0)
  have hR0 : 0 ≤ R := by
    have := hR 0 (zero_mem_polarSet P)
    rwa [norm_zero] at this
  by_contra hy0
  have hpos : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have := hR (((R + 1) / ‖y‖) • y) (hmem _)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_cancel₀ _ hpos.ne'] at this
  linarith

end cover

lemma exists_perp {f : E d →ₗ[ℝ] E (d + 1)} (hf : Function.Injective f) :
    ∃ b : E (d + 1), b ≠ 0 ∧ ∀ y, ⟪b, f y⟫ = 0 := by
  have h1 : Module.finrank ℝ (LinearMap.range f)ᗮ = 1 := by
    have := Submodule.finrank_add_finrank_orthogonal (LinearMap.range f)
    rw [LinearMap.finrank_range_of_inj hf] at this
    simp only [finrank_euclideanSpace_fin] at this
    omega
  have hne : (LinearMap.range f)ᗮ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h1
    exact zero_ne_one h1
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨b, hb0, fun y => (Submodule.mem_orthogonal' _ _).1 hb (f y) (LinearMap.mem_range_self f y)⟩

lemma range_eq_perp {f : E d →ₗ[ℝ] E (d + 1)} (hf : Function.Injective f) {b : E (d + 1)} (hb : b ≠ 0)
    (hperp : ∀ y, ⟪b, f y⟫ = 0) : LinearMap.range f = (ℝ ∙ b)ᗮ := by
  haveI : Fact (Module.finrank ℝ (E (d + 1)) = d + 1) := ⟨by simp⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hperp y
  · rw [LinearMap.finrank_range_of_inj hf, Submodule.finrank_orthogonal_span_singleton (n := d) hb]
    simp

/-! ### The model -/

section model

variable {P : Set (E d)} (hP : IsCSPolytope d P)
include hP

/-- **Polar model for at most `2d + 2` vertices**: `P` has as many faces as a central section of
the `(d+1)`-cube by a hyperplane with nonnegative normal. -/
theorem small_section_model (hd : 0 < d) (h12 : fvec P 0 ≤ 2 * d + 2) :
    ∃ a : Fin (d + 1) → ℝ, (∀ i, 0 ≤ a i) ∧ (faces P).ncard = sectionFaceCount a := by
  classical
  obtain ⟨V, hV⟩ := hP.polytope
  -- the vertex set
  set X := (extremePoints_finite V).toFinset with hXdef
  have hXcoe : (X : Set (E d)) = P.extremePoints ℝ := by rw [hXdef, Set.Finite.coe_toFinset, hV]
  have hPX : P = convexHull ℝ (X : Set (E d)) := by
    rw [hXcoe, hV, convexHull_extremePoints_eq]
  have hXcard : X.card ≤ 2 * d + 2 := by
    have h1 := fvec_zero_eq V
    rw [Set.ncard_eq_toFinset_card _ (extremePoints_finite V)] at h1
    rw [hV] at h12
    rw [hXdef, ← h1]
    exact h12
  have hXsymm : ∀ x ∈ X, -x ∈ X := by
    intro x hx
    rw [← Finset.mem_coe, hXcoe] at hx ⊢
    exact neg_mem_extremePoints hP.symm hx
  have hX0 : (0 : E d) ∉ X := by
    rw [← Finset.mem_coe, hXcoe]
    exact zero_not_mem_extremePoints hP hd
  have hXP : ∀ x ∈ X, x ∈ P := by
    intro x hx
    rw [← Finset.mem_coe, hXcoe] at hx
    exact hx.1
  -- six vectors covering the vertices up to sign
  obtain ⟨v, hvX, hcov⟩ := exists_cover X hXsymm hX0 hXcard
  have h0P : (0 : E d) ∈ P := interior_subset hP.zero_mem_interior
  have hvP : ∀ i, v i ∈ P := fun i =>
    (hvX i).elim (hXP _) (fun h => by rw [h]; exact h0P)
  have hvP' : ∀ i, -v i ∈ P := fun i => hP.symm _ (hvP i)
  -- the normal of the image hyperplane
  obtain ⟨b, hb0, hperp⟩ :=
    exists_perp (coordMap_injective hPX hvP hvP' hcov hP.zero_mem_interior)
  -- sign normalization
  obtain ⟨ε, hε⟩ : ∃ ε : Fin (d + 1) → ℝ, ∀ i, ε i = if b i < 0 then -1 else 1 := ⟨_, fun _ => rfl⟩
  have hε1 : ∀ i, ε i = 1 ∨ ε i = -1 := fun i => by
    rw [hε]; split_ifs
    · right; rfl
    · left; rfl
  have hεb : ∀ i, |b i| * ε i = b i := fun i => by
    rw [hε]; split_ifs with h
    · rw [abs_of_neg h]; ring
    · rw [abs_of_nonneg (not_lt.1 h)]; ring
  set v' : Fin (d + 1) → E d := fun i => ε i • v i with hv'
  have hv'P : ∀ i, v' i ∈ P := fun i => by
    rcases hε1 i with h | h
    · simp only [hv', h, one_smul]; exact hvP i
    · simp only [hv', h, neg_one_smul]; exact hvP' i
  have hv'P' : ∀ i, -v' i ∈ P := fun i => hP.symm _ (hv'P i)
  have hcov' : ∀ x ∈ X, ∃ i, x = v' i ∨ x = -v' i := by
    intro x hx
    obtain ⟨i, hi⟩ := hcov x hx
    refine ⟨i, ?_⟩
    rcases hε1 i with h | h <;> rcases hi with hi | hi <;>
      simp only [hv', h, one_smul, neg_one_smul, neg_neg] <;> tauto
  have hinj' := coordMap_injective hPX hv'P hv'P' hcov' hP.zero_mem_interior
  -- the normalized normal `a = |b|`
  set a : Fin (d + 1) → ℝ := fun i => |b i| with ha
  obtain ⟨aV, haV⟩ : ∃ aV : E (d + 1), ∀ i, aV i = a i := ⟨WithLp.toLp 2 a, fun _ => rfl⟩
  have haV0 : aV ≠ 0 := by
    intro h
    apply hb0
    refine PiLp.ext fun i => ?_
    have h1 := haV i
    rw [h] at h1
    have h2 : |b i| = 0 := by
      have h3 : a i = 0 := by rw [← h1]; rfl
      simpa [ha] using h3
    simpa using abs_eq_zero.1 h2
  have hperp' : ∀ y, ⟪aV, coordMap v' y⟫ = 0 := by
    intro y
    have hb := hperp y
    rw [inner_eq_sum] at hb ⊢
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hb
    rw [haV, coordMap_apply, coordMap_apply, hv']
    simp only [ha, real_inner_smul_right]
    rw [← mul_assoc, hεb]
  have hrange := range_eq_perp hinj' haV0 hperp'
  -- the image of the polar is the central section
  have himage : coordMap v' '' polarSet P = cubeSection a := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_polar_iff hPX hv'P hv'P' hcov'] at hy
      refine ⟨fun i => hy i, ?_⟩
      have := hperp' y
      rw [inner_eq_sum] at this
      simpa [haV] using this
    · rintro ⟨hzc, hz0⟩
      have hzr : z ∈ LinearMap.range (coordMap v') := by
        rw [hrange, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_eq_sum]
        simpa [haV] using hz0
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hzr
      refine ⟨y, ?_, rfl⟩
      rw [mem_polar_iff hPX hv'P hv'P' hcov']
      exact fun i => hzc i
  refine ⟨a, fun i => abs_nonneg (b i), ?_⟩
  have h0V : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d))) := hV ▸ hP.zero_mem_interior
  have hpol : (faces P).ncard = (faces (polarSet P)).ncard := by
    rw [hV]; exact (ncard_faces_polarSet h0V).symm
  rw [hpol, ← ncard_faces_image_of_injective _ hinj', himage,
    ncard_faces_cubeSection a fun i => abs_nonneg (b i)]

end model

end CS

variable {d : ℕ}

/-- The polar of a centrally symmetric polytope is a centrally symmetric polytope. -/
lemma IsCSPolytope.polar {P : Set (E d)} (hP : IsCSPolytope d P) : IsCSPolytope d (polarSet P) := by
  obtain ⟨V, hV⟩ := hP.polytope
  have h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d))) := hV ▸ hP.zero_mem_interior
  refine ⟨⟨?_, ?_⟩, fun y hy => neg_mem_polarSet hP.symm hy⟩
  · rw [hV]; exact exists_polarSet_eq_convexHull h0
  · rw [hV]; exact ⟨0, zero_mem_interior_polarSet V⟩

/-- **Kalai's `3^d` bound for centrally symmetric `d`-polytopes with at most `2d + 2` vertices.** -/
theorem IsCSPolytope.three_pow_le_of_fvec_zero_le {P : Set (E d)} (hP : IsCSPolytope d P)
    (hd : 0 < d) (hv : fvec P 0 ≤ 2 * d + 2) : 3 ^ d ≤ (faces P).ncard := by
  obtain ⟨a, ha, h⟩ := CS.small_section_model hP hd hv
  rw [h]
  have := three_pow_le_three_mul_sectionFaceCount a ha
  rw [pow_succ'] at this
  exact Nat.le_of_mul_le_mul_left this (by norm_num)

/-- **The polar statement**: at most `2d + 2` facets. -/
theorem IsCSPolytope.three_pow_le_of_fvec_facets_le {P : Set (E d)} (hP : IsCSPolytope d P)
    (hd : 0 < d) (hf : fvec P (d - 1) ≤ 2 * d + 2) : 3 ^ d ≤ (faces P).ncard := by
  obtain ⟨V, hV⟩ := hP.polytope
  have h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d))) := hV ▸ hP.zero_mem_interior
  have hv' : fvec (polarSet P) 0 ≤ 2 * d + 2 := by
    rw [hV, fvec_polarSet_zero h0 hd]
    rw [hV] at hf
    exact hf
  have := hP.polar.three_pow_le_of_fvec_zero_le hd hv'
  rw [hV, ncard_faces_polarSet h0] at this
  rwa [hV]

end Kalai5
