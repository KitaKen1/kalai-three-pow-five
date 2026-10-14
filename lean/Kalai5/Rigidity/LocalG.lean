import Kalai5.Rigidity.WhiteleyAssembly
import Kalai5.Rigidity.Stress
import Kalai5.Alexandrov.Final

/-!
# Local `g ≥ 0`: the facets of a centrally symmetric 5-polytope have `g₂ ≥ 0`

For a facet `F` with vertex set `X_F` (spanning an affine 4-space with direction `L`), the bars
`B_F` of the Whiteley bar set inside `F` brace `X_F` (`WhiteleyCSLoc`: the fans brace the
`2`-faces, then Whiteley's theorem in dimension four).  The tangential rigidity map
`R : (X_F → L) → ℝ^{B_F}` then has kernel inside the `10`-dimensional space of tangential trivial
motions, so `4 |X_F| - 10 ≤ rank R ≤ |B_F|`, i.e. `g(F) = |B_F| - 4 f₀(F) + 10 ≥ 0`.

* `card_le_of_braces_hyperplane`: `4 |XF| ≤ |BF| + 10` for a braced framework spanning an affine
  4-space.
* `IsCSPolytope5.facet_g_nonneg`: `∀ R ∈ facetRows P, 0 ≤ R.g`.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The tangential rigidity map of the bars `BF` on the joints `XF`, velocities in `L`. -/
noncomputable def tanRig (XF : Finset E5) (L : Submodule ℝ E5) (BF : Finset (Sym2 E5)) :
    (XF → L) →ₗ[ℝ] EuclideanSpace ℝ BF where
  toFun w := WithLp.toLp 2 (fun b => barVal (extTan XF L w) b.1)
  map_add' w w' := by
    refine PiLp.ext fun b => ?_
    simp only [PiLp.add_apply]
    rw [← barVal_add]
    congr 1
    funext p
    exact extTan_add XF L w w' p
  map_smul' c w := by
    refine PiLp.ext fun b => ?_
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← barVal_smul]
    congr 1
    funext p
    exact extTan_smul XF L c w p

lemma tanRig_apply (XF : Finset E5) (L : Submodule ℝ E5) (BF : Finset (Sym2 E5)) (w : XF → L)
    (b : BF) : tanRig XF L BF w b = barVal (extTan XF L w) b.1 := rfl

set_option maxHeartbeats 1000000 in
/-- **Kernel bound for a braced framework spanning an affine `d`-space**: the tangential motions
are the trivial ones, `c = #{(a, b) | a < b}` rotations and `d` translations. -/
theorem finrank_ker_tanRig_le {d c : ℕ}
    (hcard : Fintype.card {q : Fin d × Fin d // q.1 < q.2} = c) {XF : Finset E5}
    {BF : Finset (Sym2 E5)} {L : Submodule ℝ E5} (hL : Module.finrank ℝ L = d) {p0 : E5}
    (hp0 : p0 ∈ XF) (hdiff : ∀ p ∈ XF, p - p0 ∈ L)
    (hspan : L ≤ Submodule.span ℝ ((fun p => p - p0) '' (XF : Set E5)))
    (hbr : Braces (BF : Set (Sym2 E5)) (XF : Set E5)) :
    Module.finrank ℝ (LinearMap.ker (tanRig XF L BF)) ≤ c + d := by
  classical
  -- an orthonormal basis of `L`
  set ob := (stdOrthonormalBasis ℝ L).reindex (finCongr hL)
  set f : Fin d → E5 := fun i => (ob i : E5) with hfdef
  have hfL : ∀ i, f i ∈ L := fun i => (ob i).2
  have hfo : Orthonormal ℝ f := ob.orthonormal.comp_linearIsometry L.subtypeₗᵢ
  have hortho : ∀ a b : Fin d, ⟪f a, f b⟫ = if a = b then 1 else 0 := orthonormal_iff_ite.1 hfo
  have hLspan : ∀ x ∈ L, x ∈ Submodule.span ℝ (Set.range f) := by
    intro x hx
    have h := congrArg Subtype.val (ob.sum_repr ⟨x, hx⟩)
    rw [Submodule.coe_sum] at h
    change _ = x at h
    rw [← h]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  -- elementary rotations
  let rot : {q : Fin d × Fin d // q.1 < q.2} → E5 →ₗ[ℝ] E5 := fun q =>
    (innerₛₗ ℝ (f q.1.2)).smulRight (f q.1.1) - (innerₛₗ ℝ (f q.1.1)).smulRight (f q.1.2)
  have hrot : ∀ q y, rot q y = ⟪f q.1.2, y⟫ • f q.1.1 - ⟪f q.1.1, y⟫ • f q.1.2 := fun q y => by
    simp [rot]
  let M : ({q : Fin d × Fin d // q.1 < q.2} → ℝ) → E5 →ₗ[ℝ] E5 := fun lam => ∑ q, lam q • rot q
  have hM : ∀ lam y, M lam y = ∑ q, lam q • rot q y := fun lam y => by
    simp [M]
  have hM_mem : ∀ lam y, M lam y ∈ L := fun lam y => by
    rw [hM]
    refine L.sum_mem fun q _ => L.smul_mem _ ?_
    rw [hrot]
    exact L.sub_mem (L.smul_mem _ (hfL _)) (L.smul_mem _ (hfL _))
  have hM_inner : ∀ lam y, ⟪M lam y, y⟫ = 0 := fun lam y => by
    rw [hM, sum_inner]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [real_inner_smul_left, hrot, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_comm y (f q.1.1), real_inner_comm y (f q.1.2)]
    ring
  have hM_skew : ∀ lam x y, ⟪M lam x, y⟫ = -⟪x, M lam y⟫ := by
    intro lam x y
    have h := hM_inner lam (x + y)
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, hM_inner, hM_inner] at h
    rw [← real_inner_comm x (M lam y)]
    linarith
  have hbasis : ∀ lam (q0 : {q : Fin d × Fin d // q.1 < q.2}),
      ⟪f q0.1.1, M lam (f q0.1.2)⟫ = lam q0 := by
    intro lam q0
    rw [hM, inner_sum]
    rw [Finset.sum_eq_single q0]
    · rw [real_inner_smul_right, hrot, inner_sub_right, real_inner_smul_right,
        real_inner_smul_right]
      simp only [hortho]
      have hne : q0.1.1 ≠ q0.1.2 := ne_of_lt q0.2
      simp [hne]
    · intro q _ hq
      rw [real_inner_smul_right, hrot, inner_sub_right, real_inner_smul_right,
        real_inner_smul_right]
      simp only [hortho]
      have hp1 : ((if q.1.2 = q0.1.2 then (1 : ℝ) else 0) *
          if q0.1.1 = q.1.1 then 1 else 0) = 0 := by
        by_cases hA : q.1.2 = q0.1.2
        · by_cases hB : q0.1.1 = q.1.1
          · exact absurd (Subtype.ext (Prod.ext hB.symm hA)) hq
          · rw [if_neg hB, mul_zero]
        · rw [if_neg hA, zero_mul]
      have hp2 : ((if q.1.1 = q0.1.2 then (1 : ℝ) else 0) *
          if q0.1.1 = q.1.2 then 1 else 0) = 0 := by
        by_cases hA : q.1.1 = q0.1.2
        · by_cases hB : q0.1.1 = q.1.2
          · have hq1 := q.2
            have hq0 := q0.2
            rw [hA, ← hB] at hq1
            exact absurd (lt_trans hq1 hq0) (lt_irrefl _)
          · rw [if_neg hB, mul_zero]
        · rw [if_neg hA, zero_mul]
      rw [hp1, hp2]
      ring
    · intro h
      exact absurd (Finset.mem_univ q0) h
  -- the trivial tangential motions
  let Θ : (({q : Fin d × Fin d // q.1 < q.2} → ℝ) × L) →ₗ[ℝ] (XF → L) :=
    { toFun := fun x p => ⟨M x.1 ((p : E5) - p0), hM_mem _ _⟩ + x.2
      map_add' := fun x y => by
        funext p
        apply Subtype.ext
        simp only [Pi.add_apply, Submodule.coe_add, Prod.fst_add, Prod.snd_add, hM, add_smul,
          Finset.sum_add_distrib]
        abel
      map_smul' := fun c x => by
        funext p
        apply Subtype.ext
        simp only [Pi.smul_apply, Submodule.coe_add, Submodule.coe_smul, Prod.smul_fst,
          Prod.smul_snd, hM, smul_eq_mul, mul_smul, RingHom.id_apply]
        rw [smul_add, Finset.smul_sum] }
  have hΘ : ∀ x (p : XF), ((Θ x p : L) : E5) = M x.1 ((p : E5) - p0) + (x.2 : E5) :=
    fun _ _ => rfl
  -- the tangential rigidity map
  set R := tanRig XF L BF with hRdef
  have hR : ∀ w (b : BF), R w b = barVal (extTan XF L w) b.1 := fun _ _ => rfl
  -- the direction of the affine hull of `XF` is `L`
  have hVS : vectorSpan ℝ (XF : Set E5) = L := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (Finset.mem_coe.2 hp0)]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨p, hp, rfl⟩
      exact hdiff p hp
    · exact hspan
  -- motions of the bars are trivial
  have hker : LinearMap.ker R ≤ LinearMap.range Θ := by
    intro w hw
    rw [LinearMap.mem_ker] at hw
    set u := extTan XF L w with hu
    have hmot : IsMotion (BF : Set (Sym2 E5)) u := by
      intro b hb
      have := congrArg (fun z : EuclideanSpace ℝ BF => z ⟨b, hb⟩) hw
      simpa [hR] using this
    obtain ⟨A, c, hA, hAc⟩ := trivialOn_of_pairs ⟨p0, Finset.mem_coe.2 hp0⟩ (hbr u hmot)
    rw [hVS] at hA hAc
    set lam : {q : Fin d × Fin d // q.1 < q.2} → ℝ := fun q => ⟪f q.1.1, A (f q.1.2)⟫
      with hlam
    -- `M lam` is the tangential part of `A`
    have hMA : ∀ y ∈ L, ∀ z ∈ L, ⟪z, M lam y⟫ = ⟪z, A y⟫ := by
      intro y hy z hz
      have key := eq_zero_of_mem_span₂ (t := Set.range f)
        (fun z y => ⟪z, M lam y⟫ - ⟪z, A y⟫)
        (by intro x x' y; simp only [inner_add_left]; ring)
        (by intro a x y; simp only [real_inner_smul_left]; ring)
        (by intro x y y'; simp only [map_add, inner_add_right]; ring)
        (by intro a x y; simp only [map_smul, real_inner_smul_right]; ring)
        (by
          rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
          show ⟪f a, M lam (f b)⟫ - ⟪f a, A (f b)⟫ = 0
          rcases lt_trichotomy a b with hab | rfl | hab
          · have h1 : ⟪f a, M lam (f b)⟫ = ⟪f a, A (f b)⟫ := hbasis lam ⟨(a, b), hab⟩
            rw [h1, sub_self]
          · have h1 := hM_inner lam (f a)
            rw [real_inner_comm] at h1
            have h2 := hA (f a) (hfL a) (f a) (hfL a)
            rw [real_inner_comm (f a) (A (f a))] at h2
            rw [h1]
            linarith
          · have h1 := hM_skew lam (f a) (f b)
            rw [real_inner_comm (f b) (M lam (f a))] at h1
            have h2 : ⟪f b, M lam (f a)⟫ = ⟪f b, A (f a)⟫ := hbasis lam ⟨(b, a), hab⟩
            have h3 := hA (f b) (hfL b) (f a) (hfL a)
            rw [real_inner_comm (f a) (A (f b))] at h3
            linarith)
        (hLspan z hz) (hLspan y hy)
      have key' : ⟪z, M lam y⟫ - ⟪z, A y⟫ = 0 := key
      linarith
    rw [LinearMap.mem_range]
    refine ⟨(lam, L.orthogonalProjectionOnto (A p0 + c)), ?_⟩
    funext p
    apply Subtype.ext
    rw [hΘ]
    show M lam ((p : E5) - p0) + ((L.orthogonalProjectionOnto (A p0 + c) : L) : E5) = (w p : E5)
    have hpL : (p : E5) - p0 ∈ L := hdiff p p.2
    have hvL : M lam ((p : E5) - p0) + ((L.orthogonalProjectionOnto (A p0 + c) : L) : E5) -
        (w p : E5) ∈ L :=
      L.sub_mem (L.add_mem (hM_mem _ _) (Submodule.coe_mem _)) (w p).2
    have hvperp : ∀ z ∈ L, ⟪z, M lam ((p : E5) - p0) +
        ((L.orthogonalProjectionOnto (A p0 + c) : L) : E5) - (w p : E5)⟫ = 0 := by
      intro z hz
      have e1 : ⟪z, M lam ((p : E5) - p0)⟫ = ⟪z, A ((p : E5) - p0)⟫ := hMA _ hpL z hz
      have e2 : ⟪z, ((L.orthogonalProjectionOnto (A p0 + c) : L) : E5)⟫ = ⟪z, A p0 + c⟫ := by
        have h := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (K := L) ⟨z, hz⟩
          (A p0 + c)
        rw [Submodule.coe_inner] at h
        rw [real_inner_comm, h, real_inner_comm]
      have e3 : ⟪u p - (A p + c), z⟫ = 0 := hAc p (Finset.mem_coe.2 p.2) z hz
      have e4 : u p = (w p : E5) := by
        rw [hu]
        unfold extTan
        rw [dif_pos p.2]
      rw [e4, inner_sub_left, inner_add_left] at e3
      rw [inner_sub_right, inner_add_right, e1, e2, map_sub, inner_sub_right, inner_add_right,
        real_inner_comm (w p : E5) z, real_inner_comm (A p) z, real_inner_comm c z]
      linarith
    have hv0 := inner_self_eq_zero.1 (hvperp _ hvL)
    exact sub_eq_zero.1 hv0
  -- dimensions
  have hdomΘ : Module.finrank ℝ (({q : Fin d × Fin d // q.1 < q.2} → ℝ) × L) = c + d := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hcard, hL]
  calc Module.finrank ℝ (LinearMap.ker R) ≤ Module.finrank ℝ (LinearMap.range Θ) :=
        Submodule.finrank_mono hker
    _ ≤ c + d := by rw [← hdomΘ]; exact LinearMap.finrank_range_le Θ

/-- **Stresses of a braced framework spanning an affine `d`-space**:
`dim stress(BF) + d |XF| ≤ |BF| + c + d`. -/
theorem finrank_stress_add_le_of_braces {d c : ℕ}
    (hcard : Fintype.card {q : Fin d × Fin d // q.1 < q.2} = c) {XF : Finset E5}
    {BF : Finset (Sym2 E5)} {L : Submodule ℝ E5} (hL : Module.finrank ℝ L = d) {p0 : E5}
    (hp0 : p0 ∈ XF) (hdiff : ∀ p ∈ XF, p - p0 ∈ L)
    (hspan : L ≤ Submodule.span ℝ ((fun p => p - p0) '' (XF : Set E5)))
    (hbr : Braces (BF : Set (Sym2 E5)) (XF : Set E5)) :
    Module.finrank ℝ (stressSpace BF) + d * XF.card ≤ BF.card + c + d := by
  classical
  have hker := finrank_ker_tanRig_le hcard hL hp0 hdiff hspan hbr
  have hrn := LinearMap.finrank_range_add_finrank_ker (tanRig XF L BF)
  have hdom : Module.finrank ℝ (XF → L) = XF.card * d := by
    rw [Module.finrank_pi_fintype]
    simp [hL]
  rw [hdom] at hrn
  -- stresses are orthogonal to the image
  have hperp : stressSpace BF ≤ (LinearMap.range (tanRig XF L BF))ᗮ := by
    intro ω hω
    rw [Submodule.mem_orthogonal']
    rintro _ ⟨w, rfl⟩
    rw [inner_euclid]
    have h0 := hω (extTan XF L w)
    rw [← h0]
    rfl
  have h3 := Submodule.finrank_add_finrank_orthogonal (LinearMap.range (tanRig XF L BF))
  rw [finrank_euclideanSpace, Fintype.card_coe] at h3
  have h4 : Module.finrank ℝ (stressSpace BF) ≤
      Module.finrank ℝ (LinearMap.range (tanRig XF L BF))ᗮ := Submodule.finrank_mono hperp
  have : XF.card * d = d * XF.card := Nat.mul_comm _ _
  omega

/-- **Rank bound for a braced framework spanning an affine 4-space**: `4 |XF| ≤ |BF| + 10`
(the infinitesimal motions tangent to the 4-space are the 6 rotations and 4 translations). -/
theorem card_le_of_braces_hyperplane {XF : Finset E5} {BF : Finset (Sym2 E5)}
    {L : Submodule ℝ E5} (hL : Module.finrank ℝ L = 4) {p0 : E5} (hp0 : p0 ∈ XF)
    (hdiff : ∀ p ∈ XF, p - p0 ∈ L)
    (hspan : L ≤ Submodule.span ℝ ((fun p => p - p0) '' (XF : Set E5)))
    (hbr : Braces (BF : Set (Sym2 E5)) (XF : Set E5)) :
    4 * XF.card ≤ BF.card + 10 := by
  classical
  have hker := finrank_ker_tanRig_le (c := 6) (by decide) hL hp0 hdiff hspan hbr
  have hrn := LinearMap.finrank_range_add_finrank_ker (tanRig XF L BF)
  have hdom : Module.finrank ℝ (XF → L) = XF.card * 4 := by
    rw [Module.finrank_pi_fintype]
    simp [hL]
  rw [hdom] at hrn
  have hrange : Module.finrank ℝ (LinearMap.range (tanRig XF L BF)) ≤ BF.card := by
    calc Module.finrank ℝ (LinearMap.range (tanRig XF L BF))
        ≤ Module.finrank ℝ (EuclideanSpace ℝ BF) := Submodule.finrank_le _
      _ = BF.card := by rw [finrank_euclideanSpace, Fintype.card_coe]
  omega

/-! ### Facets of centrally symmetric 5-polytopes -/

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **Local `g ≥ 0`** for every facet, from local rigidity. -/
theorem IsCSPolytope5.facet_g_nonneg_of_loc (hW : WhiteleyCSLoc P) :
    ∀ R ∈ facetRows P, 0 ≤ R.g := by
  classical
  intro R hR
  obtain ⟨F, hF, h4, rfl⟩ := hP.mem_facetRows hR
  obtain ⟨B, hBX, -, -, hBloc, -, hBbr, -, -⟩ := hW
  obtain ⟨V, hV⟩ := hP.polytope
  -- the vertex set of `P`
  set X := (extremePoints_finite V).toFinset with hXdef
  have hXcoe : (X : Set E5) = P.extremePoints ℝ := by rw [hXdef, Set.Finite.coe_toFinset, hV]
  -- the bars inside `F`
  set BF := B.filter (fun b => ∀ p ∈ b, p ∈ F) with hBFdef
  -- the vertices of `F`
  have hFext : IsExtreme ℝ P F := hF.2.isExtreme
  set XF := X.filter (· ∈ F) with hXFdef
  have hXFcoe : (XF : Set E5) = F.extremePoints ℝ := by
    rw [hFext.extremePoints_eq, hXFdef, Finset.coe_filter, ← hXcoe]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_coe]
    tauto
  have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
  set SF := V.filter (· ∈ F) with hSFdef
  have hFSF : F = convexHull ℝ (SF : Set E5) := face_eq_convexHull_filter hF'
  have hXFcard : XF.card = cnt P F 0 := by
    have h1 : cnt P F 0 = fvec F 0 := by
      rw [hV]
      exact (fvec_face_eq_cnt hF' 0).symm
    have h2 : fvec F 0 = (F.extremePoints ℝ).ncard := by
      have := fvec_zero_eq SF
      rwa [← hFSF] at this
    rw [h1, h2, ← hXFcoe, Set.ncard_coe_finset]
  have hFne : F.Nonempty := hF.1
  have hFconv : F = convexHull ℝ (F.extremePoints ℝ) := by
    conv_lhs => rw [hFSF]
    rw [← convexHull_extremePoints_eq SF, ← hFSF]
  obtain ⟨p0, hp0⟩ : (F.extremePoints ℝ).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, convexHull_empty] at hFconv
    rw [hFconv] at hFne
    exact Set.not_nonempty_empty hFne
  have hp0XF : p0 ∈ XF := by rw [← Finset.mem_coe, hXFcoe]; exact hp0
  have hXF_F : ∀ p ∈ XF, p ∈ F := fun p hp => (Finset.mem_filter.1 hp).2
  have hdiff : ∀ p ∈ XF, p - p0 ∈ vectorSpan ℝ F := fun p hp =>
    vsub_mem_vectorSpan ℝ (hXF_F p hp) (hXF_F p0 hp0XF)
  have hspanF : vectorSpan ℝ F ≤ Submodule.span ℝ ((fun p => p - p0) '' (XF : Set E5)) := by
    have e1 : vectorSpan ℝ F = vectorSpan ℝ (F.extremePoints ℝ) := by
      conv_lhs => rw [hFconv]
      rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
    rw [e1, vectorSpan_eq_span_vsub_set_right ℝ hp0, hXFcoe]
    rfl
  have hbr : Braces (BF : Set (Sym2 E5)) (XF : Set E5) := by
    rw [hXFcoe]
    exact hBbr F hF h4
  have hlow := card_le_of_braces_hyperplane (L := vectorSpan ℝ F) h4 hp0XF hdiff hspanF hbr
  -- assemble
  have hloc := hBloc F hF h4
  rw [← hBFdef] at hloc
  rw [hP.facet_g_eq hF h4]
  rw [hXFcard] at hlow
  have hlow' : 4 * (cnt P F 0 : ℤ) ≤ BF.card + 10 := by exact_mod_cast hlow
  linarith

/-- **Local `g ≥ 0`**: every facet of a centrally symmetric 5-polytope has `g₂ ≥ 0`
(Kalai's inequality for 4-polytopes, via Whiteley's rigidity theorem). -/
theorem IsCSPolytope5.facet_g_nonneg : ∀ R ∈ facetRows P, 0 ≤ R.g :=
  hP.facet_g_nonneg_of_loc (hP.whiteleyCSLoc_of_w3 alexandrov3_proof)

end cs

end Kalai5
