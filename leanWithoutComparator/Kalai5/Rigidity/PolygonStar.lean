import Kalai5.Rigidity.LocalG
import Kalai5.Polar.Intervals

/-!
# The polygon-star lemma: `G ≥ 2 (k - 3)(ℓ - 3)`

For a `2`-face `Q` (a `k`-gon) of a centrally symmetric 5-polytope lying in `ℓ` three-faces
`T₁, …, T_ℓ`, the bars of the Whiteley bar set inside `U = T₁ ∪ … ∪ T_ℓ` carry many stresses:

* **motions** (`finrank_ker_rigU`): the trivial motions restricted to `Q` (12 dimensions: 5
  translations, the rotation of the plane of `Q`, 6 rotations mixing it with its normal space)
  and, at every vertex of `U` outside `Q`, the 2 normal directions of its three-face, so
  `dim stress(B_U) ≥ |B_U| - 5 |X_U| + 12 + 2 M`;
* **localization**: a stress vanishing on the bars at `Q` restricts to a stress of every `T_j`,
  and `T_j` is braced in its 3-space (`finrank_stress_add_le_of_braces`), so these stresses have
  dimension `≤ Σ_j (|B_j| - 3 |X_j| + 6)`;
* the bar counts of the three-faces cancel, leaving `(k - 3)(ℓ - 3)` with `|B_Q| = 2k - 3`;
* **antisymmetrization** (`two_mul_finrank_stress_le_of_incident`): no bar at `Q` has its
  antipode in `U`, so the stresses modulo those vanishing at `Q` embed into the antisymmetric
  stresses of the whole framework, of dimension `≤ G / 2`.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {d : ℕ}

/-! ### Antisymmetrization of stresses that may contain antipodal bars -/

/-- The stresses of `BF` vanishing on the bars of `BI`. -/
def stressVanish (BF BI : Finset (Sym2 (E d))) : Submodule ℝ (EuclideanSpace ℝ BF) where
  carrier := {ω | ω ∈ stressSpace BF ∧ ∀ b : BF, b.1 ∈ BI → ω b = 0}
  add_mem' := by
    rintro ω ω' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨(stressSpace BF).add_mem h1 h1', fun b hb => ?_⟩
    simp [h2 b hb, h2' b hb]
  zero_mem' := ⟨(stressSpace BF).zero_mem, fun b _ => by simp⟩
  smul_mem' := by
    rintro c ω ⟨h1, h2⟩
    refine ⟨(stressSpace BF).smul_mem c h1, fun b hb => ?_⟩
    simp [h2 b hb]

lemma mem_stressVanish {BF BI : Finset (Sym2 (E d))} {ω : EuclideanSpace ℝ BF} :
    ω ∈ stressVanish BF BI ↔ ω ∈ stressSpace BF ∧ ∀ b : BF, b.1 ∈ BI → ω b = 0 := Iff.rfl

/-- **Stresses of a sub-framework, modulo those vanishing on bars `BI` whose antipodes are not
in the sub-framework**, embed into the antisymmetric stresses of a symmetric rigid framework:
`2 · dim stress(BF) + d |X| ≤ |B| + 2d + 2 · dim stress_BI(BF)`. -/
theorem two_mul_finrank_stress_le_of_incident {X : Finset (E d)} {B BF BI : Finset (Sym2 (E d))}
    (hXs : ∀ x ∈ X, -x ∈ X) (hX0 : (0 : E d) ∉ X)
    (hspan : Submodule.span ℝ (X : Set (E d)) = ⊤)
    (hBs : ∀ b ∈ B, b.map Neg.neg ∈ B) (hBfree : ∀ b ∈ B, b.map Neg.neg ≠ b)
    (hrig : IsInfRigid (X : Set (E d)) (B : Set (Sym2 (E d))))
    (hBF : BF ⊆ B) (hBI : ∀ b ∈ BI, b.map Neg.neg ∉ BF) :
    2 * Module.finrank ℝ (stressSpace BF) + d * X.card ≤
      B.card + 2 * d + 2 * Module.finrank ℝ (stressVanish BF BI) := by
  classical
  have hXfree : ∀ x ∈ X, -x ≠ x := fun x hx h => by
    have h2 : (2 : ℝ) • x = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h]
      exact neg_add_cancel x
    have : x = 0 := (smul_eq_zero.1 h2).resolve_left two_ne_zero
    exact hX0 (this ▸ hx)
  have hσσ : ∀ b : Sym2 (E d), (b.map Neg.neg).map Neg.neg = b := fun b => by
    rw [Sym2.map_map]; simp
  obtain ⟨Xp, hXpX, hXcov, hXdis, hXcard⟩ :=
    exists_half_of_involution (fun x : E d => -x) (fun a => neg_neg a) _ X rfl hXs hXfree
  obtain ⟨Bp, hBpB, hBcov, hBdis, hBcard⟩ :=
    exists_half_of_involution (fun b : Sym2 (E d) => b.map Neg.neg) hσσ _ B rfl hBs hBfree
  have hkerle := finrank_ker_evenRigMap_le hXs hspan hXpX hXdis hBcov hrig
  have hrn := LinearMap.finrank_range_add_finrank_ker (evenRigMap Xp Bp)
  have hdom : Module.finrank ℝ (Xp → E d) = Xp.card * d := by
    rw [Module.finrank_pi_fintype]
    simp
  -- the antisymmetrization map
  let T : stressSpace BF →ₗ[ℝ] EuclideanSpace ℝ Bp :=
    { toFun := fun ω => WithLp.toLp 2
        (fun b => extZero BF ω b.1 - extZero BF ω (b.1.map Neg.neg))
      map_add' := fun ω ω' => by
        refine PiLp.ext fun b => ?_
        simp only [PiLp.add_apply, Submodule.coe_add, extZero_add]
        ring
      map_smul' := fun a ω => by
        refine PiLp.ext fun b => ?_
        simp only [PiLp.toLp_apply, PiLp.smul_apply, Submodule.coe_smul, extZero_smul,
          smul_eq_mul, RingHom.id_apply]
        ring }
  have hT : ∀ ω (b : Bp), T ω b = extZero BF ω b.1 - extZero BF ω (b.1.map Neg.neg) :=
    fun _ _ => rfl
  -- the kernel consists of stresses vanishing on `BI`
  have hkerT : ∀ ω : stressSpace BF, T ω = 0 →
      (ω : EuclideanSpace ℝ BF) ∈ stressVanish BF BI := by
    intro ω hω
    refine ⟨ω.2, fun c hcI => ?_⟩
    have hcB : c.1 ∈ B := hBF c.2
    have hnot : c.1.map Neg.neg ∉ BF := hBI c.1 hcI
    have hval : extZero BF ω c.1 = (ω : EuclideanSpace ℝ BF) c := by
      unfold extZero
      rw [dif_pos c.2]
    rcases hBcov c.1 hcB with h | h
    · have := congrArg (fun z : EuclideanSpace ℝ Bp => z ⟨c.1, h⟩) hω
      simp only [hT, PiLp.zero_apply] at this
      have h0 : extZero BF ω (c.1.map Neg.neg) = 0 := by
        unfold extZero; rw [dif_neg hnot]
      rw [h0, sub_zero, hval] at this
      exact this
    · have := congrArg (fun z : EuclideanSpace ℝ Bp => z ⟨_, h⟩) hω
      simp only [hT, PiLp.zero_apply, hσσ] at this
      have h0 : extZero BF ω (c.1.map Neg.neg) = 0 := by
        unfold extZero; rw [dif_neg hnot]
      rw [h0, zero_sub, hval, neg_eq_zero] at this
      exact this
  let ι : LinearMap.ker T →ₗ[ℝ] stressVanish BF BI :=
    LinearMap.codRestrict (stressVanish BF BI)
      ((stressSpace BF).subtype ∘ₗ (LinearMap.ker T).subtype)
      (fun x => hkerT x.1 (LinearMap.mem_ker.1 x.2))
  have hι : Function.Injective ι := by
    intro x y h
    have := congrArg (fun z : stressVanish BF BI => (z : EuclideanSpace ℝ BF)) h
    exact Subtype.ext (Subtype.ext this)
  have hkle : Module.finrank ℝ (LinearMap.ker T) ≤ Module.finrank ℝ (stressVanish BF BI) :=
    LinearMap.finrank_le_finrank_of_injective hι
  have hrnT := LinearMap.finrank_range_add_finrank_ker T
  -- orthogonality to the image of the rigidity map
  have hT_perp : LinearMap.range T ≤ (LinearMap.range (evenRigMap Xp Bp))ᗮ := by
    rintro _ ⟨ω, rfl⟩
    rw [Submodule.mem_orthogonal']
    rintro _ ⟨w, rfl⟩
    rw [inner_euclid]
    set f := barVal (evenExt Xp w) with hf
    have heven : ∀ p, evenExt Xp w (-p) = evenExt Xp w p := evenExt_neg hXdis w
    have hfneg : ∀ b, f (b.map Neg.neg) = -f b := fun b => barVal_neg_of_even heven b
    set Ω := extZero BF (ω : EuclideanSpace ℝ BF) with hΩ
    have hsum1 : ∑ b : Bp, T ω b * evenRigMap Xp Bp w b =
        ∑ b ∈ Bp, (Ω b - Ω (b.map Neg.neg)) * f b := by
      rw [← Finset.sum_coe_sort Bp]
      rfl
    rw [hsum1]
    have hsplit : ∑ b ∈ Bp, (Ω b - Ω (b.map Neg.neg)) * f b =
        ∑ b ∈ Bp, Ω b * f b + ∑ b ∈ Bp, Ω (b.map Neg.neg) * f (b.map Neg.neg) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hfneg]; ring
    have hinj : Set.InjOn (fun b : Sym2 (E d) => b.map Neg.neg) (Bp : Set (Sym2 (E d))) :=
      fun a _ b _ hab => by
        have := congrArg (fun z : Sym2 (E d) => z.map Neg.neg) hab
        simpa only [hσσ] using this
    have himg : ∑ b ∈ Bp, Ω (b.map Neg.neg) * f (b.map Neg.neg) =
        ∑ c ∈ Bp.image (fun b => b.map Neg.neg), Ω c * f c :=
      (Finset.sum_image (f := fun c => Ω c * f c) hinj).symm
    have hdisj : Disjoint Bp (Bp.image fun b => b.map Neg.neg) := by
      rw [Finset.disjoint_left]
      intro c hc hc'
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hc'
      exact hBdis b hb hc
    have hunion : Bp ∪ Bp.image (fun b => b.map Neg.neg) = B := by
      ext c
      constructor
      · intro hc
        rcases Finset.mem_union.1 hc with hc | hc
        · exact hBpB hc
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hc
          exact hBs b (hBpB hb)
      · intro hc
        rcases hBcov c hc with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, h, hσσ c⟩)
    rw [hsplit, himg, ← Finset.sum_union hdisj, hunion]
    have hsub : ∑ c ∈ B, Ω c * f c = ∑ c ∈ BF, Ω c * f c := by
      symm
      refine Finset.sum_subset hBF fun c _ hc => ?_
      rw [hΩ]
      unfold extZero
      rw [dif_neg hc, zero_mul]
    rw [hsub]
    have hstress := (ω.2 : (ω : EuclideanSpace ℝ BF) ∈ stressSpace BF) (evenExt Xp w)
    rw [← hstress, ← Finset.sum_coe_sort BF]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hΩ]
    unfold extZero
    rw [dif_pos c.2]
  -- dimension count
  have h2 : Module.finrank ℝ (LinearMap.range T) ≤
      Module.finrank ℝ (LinearMap.range (evenRigMap Xp Bp))ᗮ := Submodule.finrank_mono hT_perp
  have h3 := Submodule.finrank_add_finrank_orthogonal (LinearMap.range (evenRigMap Xp Bp))
  rw [finrank_euclideanSpace, Fintype.card_coe] at h3
  rw [hdom] at hrn
  have hXc : X.card = 2 * Xp.card := hXcard.symm
  have hBc : B.card = 2 * Bp.card := hBcard.symm
  have key : Module.finrank ℝ (stressSpace BF) + Xp.card * d ≤
      Bp.card + d + Module.finrank ℝ (stressVanish BF BI) := by omega
  rw [hXc, hBc]
  calc 2 * Module.finrank ℝ (stressSpace BF) + d * (2 * Xp.card)
      = 2 * (Module.finrank ℝ (stressSpace BF) + Xp.card * d) := by ring
    _ ≤ 2 * (Bp.card + d + Module.finrank ℝ (stressVanish BF BI)) := Nat.mul_le_mul_left 2 key
    _ = 2 * Bp.card + 2 * d + 2 * Module.finrank ℝ (stressVanish BF BI) := by ring

/-! ### Velocity fields on a finite set of joints -/

lemma barVal_congr {u u' : E d → E d} {b : Sym2 (E d)} (h : ∀ p ∈ b, u p = u' p) :
    barVal u b = barVal u' b := by
  induction b using Sym2.ind with
  | _ p q =>
    rw [barVal_mk, barVal_mk, h p (Sym2.mem_mk_left p q), h q (Sym2.mem_mk_right p q)]

lemma barVal_eq_zero_of {u : E d → E d} {b : Sym2 (E d)} (h : ∀ p ∈ b, u p = 0) :
    barVal u b = 0 := by
  induction b using Sym2.ind with
  | _ p q =>
    rw [barVal_mk, h p (Sym2.mem_mk_left p q), h q (Sym2.mem_mk_right p q), sub_self,
      inner_zero_left]

open Classical in
/-- Extension of a velocity field on the joints `X` by zero. -/
noncomputable def extAll (X : Finset E5) (w : X → E5) (p : E5) : E5 :=
  if h : p ∈ X then w ⟨p, h⟩ else 0

lemma extAll_add (X : Finset E5) (w w' : X → E5) (p : E5) :
    extAll X (w + w') p = extAll X w p + extAll X w' p := by
  unfold extAll
  split_ifs <;> simp

lemma extAll_smul (X : Finset E5) (c : ℝ) (w : X → E5) (p : E5) :
    extAll X (c • w) p = c • extAll X w p := by
  unfold extAll
  split_ifs <;> simp

lemma extAll_of_mem (X : Finset E5) (w : X → E5) {p : E5} (hp : p ∈ X) :
    extAll X w p = w ⟨p, hp⟩ := by
  unfold extAll
  rw [dif_pos hp]

/-- The rigidity map of the bars `B` on the joints `X`. -/
noncomputable def rigMap (X : Finset E5) (B : Finset (Sym2 E5)) :
    (X → E5) →ₗ[ℝ] EuclideanSpace ℝ B where
  toFun w := WithLp.toLp 2 (fun b => barVal (extAll X w) b.1)
  map_add' w w' := by
    refine PiLp.ext fun b => ?_
    simp only [PiLp.add_apply]
    rw [← barVal_add]
    congr 1
    funext p
    exact extAll_add X w w' p
  map_smul' c w := by
    refine PiLp.ext fun b => ?_
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← barVal_smul]
    congr 1
    funext p
    exact extAll_smul X c w p

lemma rigMap_apply (X : Finset E5) (B : Finset (Sym2 E5)) (w : X → E5) (b : B) :
    rigMap X B w b = barVal (extAll X w) b.1 := rfl

lemma barVal_extAll {X : Finset E5} (u : E5 → E5) {b : Sym2 E5} (hb : ∀ p ∈ b, p ∈ X) :
    barVal (extAll X fun p => u p) b = barVal u b :=
  barVal_congr fun p hp => by rw [extAll_of_mem X _ (hb p hp)]

/-- **Stresses from motions**: `|B| + dim(motions) ≤ dim stress(B) + 5 |X|`. -/
theorem card_add_finrank_ker_le {X : Finset E5} {B : Finset (Sym2 E5)}
    (hB : ∀ b ∈ B, ∀ p ∈ b, p ∈ X) :
    B.card + Module.finrank ℝ (LinearMap.ker (rigMap X B)) ≤
      Module.finrank ℝ (stressSpace B) + 5 * X.card := by
  classical
  have hrn := LinearMap.finrank_range_add_finrank_ker (rigMap X B)
  have hdom : Module.finrank ℝ (X → E5) = X.card * 5 := by
    rw [Module.finrank_pi_fintype]
    simp
  rw [hdom] at hrn
  have hperp : (LinearMap.range (rigMap X B))ᗮ ≤ stressSpace B := by
    intro ω hω u
    rw [Submodule.mem_orthogonal] at hω
    have h0 := hω (rigMap X B fun p => u p) (LinearMap.mem_range_self _ _)
    rw [inner_euclid] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm, rigMap_apply, barVal_extAll u (hB b.1 b.2)]
  have h3 := Submodule.finrank_add_finrank_orthogonal (LinearMap.range (rigMap X B))
  rw [finrank_euclideanSpace, Fintype.card_coe] at h3
  have h4 : Module.finrank ℝ (LinearMap.range (rigMap X B))ᗮ ≤
      Module.finrank ℝ (stressSpace B) := Submodule.finrank_mono hperp
  omega

/-! ### Polygon stars -/

/-- A **polygon star**: a polygon `XF` spanning a plane (direction `D`, through `p0 ∈ XF`) and
the vertex sets `XS j` of three-faces through it, spanning 3-spaces (directions `L j`) and
pairwise meeting only in `XF`. -/
structure PolyStar (ι : Type*) where
  XF : Finset E5
  XS : ι → Finset E5
  p0 : E5
  D : Submodule ℝ E5
  L : ι → Submodule ℝ E5
  hp0 : p0 ∈ XF
  hD : Module.finrank ℝ D = 2
  hXFD : ∀ p ∈ XF, p - p0 ∈ D
  hDspan : D ≤ Submodule.span ℝ ((fun p => p - p0) '' (XF : Set E5))
  hL : ∀ j, Module.finrank ℝ (L j) = 3
  hXFS : ∀ j, XF ⊆ XS j
  hXSL : ∀ j, ∀ p ∈ XS j, p - p0 ∈ L j
  hLspan : ∀ j, L j ≤ Submodule.span ℝ ((fun p => p - p0) '' (XS j : Set E5))
  hdisj : ∀ j j', j ≠ j' → ∀ p ∈ XS j, p ∈ XS j' → p ∈ XF

namespace PolyStar

variable {ι : Type*} [Fintype ι] (S : PolyStar ι)

open Classical in
/-- All joints of the star. -/
noncomputable def XU : Finset E5 := Finset.univ.biUnion S.XS

open Classical in
/-- The joints off the polygon. -/
noncomputable def priv : Finset E5 := S.XU \ S.XF

lemma mem_XU {p : E5} : p ∈ S.XU ↔ ∃ j, p ∈ S.XS j := by
  classical
  simp [XU]

lemma mem_priv {p : E5} : p ∈ S.priv ↔ (∃ j, p ∈ S.XS j) ∧ p ∉ S.XF := by
  classical
  rw [priv, Finset.mem_sdiff, mem_XU]

lemma XS_subset_XU (j : ι) : S.XS j ⊆ S.XU := fun _ hp => S.mem_XU.2 ⟨j, hp⟩

lemma XF_subset_XU [Nonempty ι] : S.XF ⊆ S.XU :=
  fun _ hp => S.mem_XU.2 ⟨Classical.arbitrary ι, S.hXFS _ hp⟩

lemma sub_mem_L {j : ι} {p q : E5} (hp : p ∈ S.XS j) (hq : q ∈ S.XS j) : p - q ∈ S.L j := by
  have := (S.L j).sub_mem (S.hXSL j p hp) (S.hXSL j q hq)
  rwa [sub_sub_sub_cancel_right] at this

set_option maxHeartbeats 4000000 in
/-- **Motions of a polygon star**: the trivial motions restricted to the polygon (12
dimensions) and two normal directions at every joint off the polygon. -/
theorem finrank_ker_rigMap_ge [Nonempty ι] (BU : Finset (Sym2 E5))
    (hBU : ∀ b ∈ BU, ∃ j, ∀ p ∈ b, p ∈ S.XS j) :
    12 + 2 * S.priv.card ≤ Module.finrank ℝ (LinearMap.ker (rigMap S.XU BU)) := by
  classical
  -- orthonormal bases adapted to the plane of the polygon
  have hDperp : Module.finrank ℝ S.Dᗮ = 3 := by
    have := Submodule.finrank_add_finrank_orthogonal S.D
    rw [finrank_euclideanSpace, Fintype.card_fin, S.hD] at this
    omega
  set obD := (stdOrthonormalBasis ℝ S.D).reindex (finCongr S.hD)
  set obN := (stdOrthonormalBasis ℝ S.Dᗮ).reindex (finCongr hDperp)
  set f : Fin 2 → E5 := fun a => (obD a : E5) with hfdef
  set h : Fin 3 → E5 := fun b => (obN b : E5) with hhdef
  have hfD : ∀ a, f a ∈ S.D := fun a => (obD a).2
  have hhN : ∀ b, h b ∈ S.Dᗮ := fun b => (obN b).2
  have hff : ∀ a a', ⟪f a, f a'⟫ = if a = a' then 1 else 0 :=
    orthonormal_iff_ite.1 (obD.orthonormal.comp_linearIsometry S.D.subtypeₗᵢ)
  have hhh : ∀ b b', ⟪h b, h b'⟫ = if b = b' then 1 else 0 :=
    orthonormal_iff_ite.1 (obN.orthonormal.comp_linearIsometry S.Dᗮ.subtypeₗᵢ)
  have hhf : ∀ b a, ⟪h b, f a⟫ = 0 := fun b a =>
    Submodule.inner_left_of_mem_orthogonal (hfD a) (hhN b)
  -- normal bases of the three-faces
  have hLperp : ∀ j, Module.finrank ℝ (S.L j)ᗮ = 2 := fun j => by
    have := Submodule.finrank_add_finrank_orthogonal (S.L j)
    rw [finrank_euclideanSpace, Fintype.card_fin, S.hL j] at this
    omega
  let obL : (j : ι) → OrthonormalBasis (Fin 2) ℝ (S.L j)ᗮ := fun j =>
    (stdOrthonormalBasis ℝ (S.L j)ᗮ).reindex (finCongr (hLperp j))
  let g : ι → Fin 2 → E5 := fun j c => (obL j c : E5)
  have hgN : ∀ j c, g j c ∈ (S.L j)ᗮ := fun j c => (obL j c).2
  have hgg : ∀ j c c', ⟪g j c, g j c'⟫ = if c = c' then 1 else 0 := fun j =>
    orthonormal_iff_ite.1 ((obL j).orthonormal.comp_linearIsometry (S.L j)ᗮ.subtypeₗᵢ)
  have hgL : ∀ j c, ∀ y ∈ S.L j, ⟪g j c, y⟫ = 0 := fun j c y hy =>
    Submodule.inner_left_of_mem_orthogonal hy (hgN j c)
  -- the three-face of a joint off the polygon
  have hjex : ∀ x ∈ S.priv, ∃ j, x ∈ S.XS j := fun x hx => (S.mem_priv.1 hx).1
  choose! jOf hjOf using hjex
  have hjuniq : ∀ x ∈ S.priv, ∀ j, x ∈ S.XS j → j = jOf x := by
    intro x hx j hj
    by_contra hne
    exact (S.mem_priv.1 hx).2 (S.hdisj j (jOf x) hne x hj (hjOf x hx))
  -- rotations
  let rotD : E5 →ₗ[ℝ] E5 :=
    (innerₛₗ ℝ (f 1)).smulRight (f 0) - (innerₛₗ ℝ (f 0)).smulRight (f 1)
  have hrotD : ∀ y, rotD y = ⟪f 1, y⟫ • f 0 - ⟪f 0, y⟫ • f 1 := fun y => by simp [rotD]
  let rotM : Fin 2 → Fin 3 → E5 →ₗ[ℝ] E5 := fun a b =>
    (innerₛₗ ℝ (h b)).smulRight (f a) - (innerₛₗ ℝ (f a)).smulRight (h b)
  have hrotM : ∀ a b y, rotM a b y = ⟪h b, y⟫ • f a - ⟪f a, y⟫ • h b := fun a b y => by
    simp [rotM]
  let A : ℝ → (Fin 2 → Fin 3 → ℝ) → E5 →ₗ[ℝ] E5 := fun θ μ =>
    θ • rotD + ∑ a, ∑ b, μ a b • rotM a b
  have hA : ∀ θ μ y, A θ μ y = θ • rotD y + ∑ a, ∑ b, μ a b • rotM a b y := fun θ μ y => by
    simp [A]
  have hA_skew : ∀ θ μ y, ⟪A θ μ y, y⟫ = 0 := by
    intro θ μ y
    rw [hA, inner_add_left, real_inner_smul_left, hrotD, inner_sub_left, real_inner_smul_left,
      real_inner_smul_left, sum_inner]
    have h0 : ∑ a, ⟪∑ b, μ a b • rotM a b y, y⟫ = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [sum_inner]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [real_inner_smul_left, hrotM, inner_sub_left, real_inner_smul_left, real_inner_smul_left]
      ring
    rw [h0]
    ring
  have hA_add : ∀ θ θ' μ μ' y, A (θ + θ') (μ + μ') y = A θ μ y + A θ' μ' y := by
    intro θ θ' μ μ' y
    simp only [hA, add_smul, Pi.add_apply, Finset.sum_add_distrib]
    abel
  have hA_smul : ∀ (c θ : ℝ) μ y, A (c * θ) (c • μ) y = c • A θ μ y := by
    intro c θ μ y
    simp only [hA, Pi.smul_apply, smul_eq_mul, mul_smul, smul_add, Finset.smul_sum]
  -- normal velocities at the joints off the polygon
  let N : (S.priv → Fin 2 → ℝ) → E5 → E5 := fun ν p =>
    if hp : p ∈ S.priv then ν ⟨p, hp⟩ 0 • g (jOf p) 0 + ν ⟨p, hp⟩ 1 • g (jOf p) 1 else 0
  have hN_add : ∀ ν ν' p, N (ν + ν') p = N ν p + N ν' p := by
    intro ν ν' p
    by_cases hp : p ∈ S.priv
    · simp only [N, dif_pos hp, Pi.add_apply, add_smul]
      abel
    · simp only [N, dif_neg hp, add_zero]
  have hN_smul : ∀ (c : ℝ) ν p, N (c • ν) p = c • N ν p := by
    intro c ν p
    by_cases hp : p ∈ S.priv
    · simp only [N, dif_pos hp, Pi.smul_apply, smul_eq_mul, mul_smul, smul_add]
    · simp only [N, dif_neg hp, smul_zero]
  have hNperp : ∀ ν j, ∀ p ∈ S.XS j, ∀ y ∈ S.L j, ⟪N ν p, y⟫ = 0 := by
    intro ν j p hp y hy
    by_cases hpv : p ∈ S.priv
    · simp only [N, dif_pos hpv]
      rw [← hjuniq p hpv j hp, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        hgL j 0 y hy, hgL j 1 y hy]
      ring
    · simp only [N, dif_neg hpv, inner_zero_left]
  have hNF : ∀ ν, ∀ p ∈ S.XF, N ν p = 0 := fun ν p hp => by
    simp only [N]
    rw [dif_neg (fun h' => (S.mem_priv.1 h').2 hp)]
  -- the motions
  let Φ : ((E5 × ℝ × (Fin 2 → Fin 3 → ℝ)) × (S.priv → Fin 2 → ℝ)) →ₗ[ℝ] (S.XU → E5) :=
    { toFun := fun z p => z.1.1 + A z.1.2.1 z.1.2.2 ((p : E5) - S.p0) + N z.2 p
      map_add' := fun z z' => by
        funext p
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, hA_add, hN_add]
        abel
      map_smul' := fun c z => by
        funext p
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          hA_smul, hN_smul, smul_add] }
  have hΦ : ∀ z (p : S.XU), Φ z p = z.1.1 + A z.1.2.1 z.1.2.2 ((p : E5) - S.p0) + N z.2 p :=
    fun _ _ => rfl
  -- they are motions of the bars
  have hΦ_ker : ∀ z, Φ z ∈ LinearMap.ker (rigMap S.XU BU) := by
    intro z
    rw [LinearMap.mem_ker]
    refine PiLp.ext fun b => ?_
    rw [rigMap_apply, PiLp.zero_apply]
    obtain ⟨j0, hj0⟩ := hBU b.1 b.2
    have key : ∀ c : Sym2 E5, (∀ p ∈ c, p ∈ S.XS j0) → barVal (extAll S.XU (Φ z)) c = 0 := by
      intro c hc
      induction c using Sym2.ind with
      | _ p q =>
        have hp : p ∈ S.XS j0 := hc p (Sym2.mem_mk_left p q)
        have hq : q ∈ S.XS j0 := hc q (Sym2.mem_mk_right p q)
        rw [barVal_mk, extAll_of_mem _ _ (S.XS_subset_XU j0 hp),
          extAll_of_mem _ _ (S.XS_subset_XU j0 hq), hΦ, hΦ]
        have e : z.1.1 + A z.1.2.1 z.1.2.2 (p - S.p0) + N z.2 p -
            (z.1.1 + A z.1.2.1 z.1.2.2 (q - S.p0) + N z.2 q) =
            A z.1.2.1 z.1.2.2 (p - q) + (N z.2 p - N z.2 q) := by
          simp only [map_sub]
          abel
        have hpq := S.sub_mem_L hp hq
        rw [e, inner_add_left, hA_skew, inner_sub_left, hNperp z.2 j0 p hp _ hpq,
          hNperp z.2 j0 q hq _ hpq]
        ring
    exact key b.1 hj0
  -- injectivity
  have hΦ_inj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨c, θ, μ⟩, ν⟩ hz
    have hval : ∀ p (hp : p ∈ S.XU), c + A θ μ (p - S.p0) + N ν p = 0 := fun p hp =>
      congrFun hz ⟨p, hp⟩
    have hc : c = 0 := by
      have := hval S.p0 (S.XF_subset_XU S.hp0)
      rwa [sub_self, map_zero, add_zero, hNF ν _ S.hp0, add_zero] at this
    subst hc
    -- `A θ μ` vanishes on the plane of the polygon
    have hAD : S.D ≤ LinearMap.ker (A θ μ) := by
      refine S.hDspan.trans (Submodule.span_le.2 ?_)
      rintro _ ⟨p, hp, rfl⟩
      have := hval p (S.XF_subset_XU hp)
      rw [zero_add, hNF ν p hp, add_zero] at this
      exact this
    have hAf : ∀ a, A θ μ (f a) = 0 := fun a => hAD (hfD a)
    have hμ : μ = 0 := by
      funext a' b'
      have h1 := congrArg (fun v => ⟪h b', v⟫) (hAf a')
      simp only [inner_zero_right] at h1
      rw [hA, inner_add_right, real_inner_smul_right, hrotD, inner_sub_right,
        real_inner_smul_right, real_inner_smul_right, hhf, hhf, inner_sum] at h1
      simp only [inner_sum, real_inner_smul_right, hrotM, inner_sub_right, hhf, hff, hhh] at h1
      fin_cases a' <;> fin_cases b' <;>
        simp [Fin.sum_univ_two, Fin.sum_univ_three] at h1 ⊢ <;> linarith
    subst hμ
    have hθ : θ = 0 := by
      have h1 := congrArg (fun v => ⟪f 0, v⟫) (hAf 1)
      simp only [inner_zero_right] at h1
      rw [hA, inner_add_right, real_inner_smul_right, hrotD, inner_sub_right,
        real_inner_smul_right, real_inner_smul_right, hff, hff, hff] at h1
      simp at h1
      exact h1
    subst hθ
    have hν : ν = 0 := by
      funext x c'
      have hx := hval x.1 (Finset.mem_sdiff.1 (show x.1 ∈ S.XU \ S.XF from x.2)).1
      have hA0 : A 0 0 (x.1 - S.p0) = 0 := by simp [hA]
      rw [zero_add, hA0, zero_add] at hx
      simp only [N, dif_pos x.2] at hx
      have h1 := congrArg (fun v => ⟪g (jOf x.1) c', v⟫) hx
      simp only [inner_zero_right, inner_add_right, real_inner_smul_right, hgg] at h1
      fin_cases c' <;> simpa using h1
    subst hν
    rfl
  -- dimensions
  have hdom : Module.finrank ℝ ((E5 × ℝ × (Fin 2 → Fin 3 → ℝ)) × (S.priv → Fin 2 → ℝ)) =
      12 + 2 * S.priv.card := by
    simp only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self,
      Module.finrank_pi_fintype, Module.finrank_fin_fun, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, Fintype.card_coe, smul_eq_mul]
    ring
  have hrange : LinearMap.range Φ ≤ LinearMap.ker (rigMap S.XU BU) := by
    rintro _ ⟨z, rfl⟩
    exact hΦ_ker z
  calc 12 + 2 * S.priv.card = Module.finrank ℝ (LinearMap.range Φ) := by
        rw [LinearMap.finrank_range_of_inj hΦ_inj, hdom]
    _ ≤ Module.finrank ℝ (LinearMap.ker (rigMap S.XU BU)) := Submodule.finrank_mono hrange

open Classical in
/-- **Localization**: a stress of the star vanishing on the bars at the polygon restricts to a
stress of every three-face. -/
theorem finrank_stressVanish_le (BU : Finset (Sym2 E5))
    (hBU : ∀ b ∈ BU, ∃ j, ∀ p ∈ b, p ∈ S.XS j) :
    Module.finrank ℝ (stressVanish BU (BU.filter fun b => ∃ p ∈ b, p ∈ S.XF)) ≤
      ∑ j, Module.finrank ℝ (stressSpace (BU.filter fun b => ∀ p ∈ b, p ∈ S.XS j)) := by
  classical
  set BI := BU.filter fun b => ∃ p ∈ b, p ∈ S.XF with hBIdef
  set Bj : ι → Finset (Sym2 E5) := fun j => BU.filter fun b => ∀ p ∈ b, p ∈ S.XS j with hBjdef
  have hBjU : ∀ j, ∀ b ∈ Bj j, b ∈ BU := fun j b hb => (Finset.mem_filter.1 hb).1
  have hBjX : ∀ j, ∀ b ∈ Bj j, ∀ p ∈ b, p ∈ S.XS j := fun j b hb => (Finset.mem_filter.1 hb).2
  -- the restriction of a stress vanishing at the polygon is a stress of each three-face
  have hres : ∀ ω ∈ stressVanish BU BI, ∀ j,
      (WithLp.toLp 2 (fun b : Bj j => ω ⟨b.1, hBjU j b.1 b.2⟩) : EuclideanSpace ℝ (Bj j)) ∈
        stressSpace (Bj j) := by
    intro ω hω j u
    obtain ⟨hst, hvan⟩ := hω
    set u' : E5 → E5 := fun p => if p ∈ S.XS j ∧ p ∉ S.XF then u p else 0 with hu'
    have h0 := hst u'
    set Ω := extZero BU ω with hΩ
    have hΩb : ∀ b : BU, ω b = Ω b.1 := fun b => by
      rw [hΩ]; unfold extZero; rw [dif_pos b.2]
    -- termwise comparison
    have hterm : ∀ c ∈ BU, Ω c * barVal u' c = if c ∈ Bj j then Ω c * barVal u c else 0 := by
      intro c hc
      by_cases hI : ∃ p ∈ c, p ∈ S.XF
      · have : Ω c = 0 := by
          rw [← hΩb ⟨c, hc⟩]
          exact hvan ⟨c, hc⟩ (Finset.mem_filter.2 ⟨hc, hI⟩)
        simp [this]
      · push_neg at hI
        obtain ⟨j', hj'⟩ := hBU c hc
        by_cases hcj : c ∈ Bj j
        · rw [if_pos hcj]
          congr 1
          refine barVal_congr fun p hp => ?_
          rw [hu']
          simp only
          rw [if_pos ⟨hBjX j c hcj p hp, hI p hp⟩]
        · rw [if_neg hcj]
          have hj'j : j' ≠ j := fun h => hcj (Finset.mem_filter.2 ⟨hc, h ▸ hj'⟩)
          have : barVal u' c = 0 := barVal_eq_zero_of fun p hp => by
            rw [hu']
            simp only
            rw [if_neg]
            rintro ⟨h1, h2⟩
            exact h2 (S.hdisj j' j hj'j p (hj' p hp) h1)
          rw [this, mul_zero]
    have h1 : ∑ b : BU, ω b * barVal u' b.1 = ∑ c ∈ BU, Ω c * barVal u' c := by
      rw [← Finset.sum_coe_sort BU]
      exact Finset.sum_congr rfl fun b _ => by rw [hΩb]
    have h2 : ∑ c ∈ BU, Ω c * barVal u' c = ∑ c ∈ Bj j, Ω c * barVal u c := by
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
      congr 1
      ext c
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hBjU j c h, h⟩⟩
    have h3 : ∑ b : Bj j, (WithLp.toLp 2 (fun b : Bj j => ω ⟨b.1, hBjU j b.1 b.2⟩) :
        EuclideanSpace ℝ (Bj j)) b * barVal u b.1 = ∑ c ∈ Bj j, Ω c * barVal u c := by
      rw [← Finset.sum_coe_sort (Bj j)]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [PiLp.toLp_apply]
      rw [hΩb]
    rw [h3, ← h2, ← h1]
    exact h0
  -- the restriction map is injective
  let ψ : stressVanish BU BI →ₗ[ℝ] ((j : ι) → stressSpace (Bj j)) :=
    { toFun := fun ω j => ⟨WithLp.toLp 2 (fun b : Bj j =>
          (ω : EuclideanSpace ℝ BU) ⟨b.1, hBjU j b.1 b.2⟩), hres ω.1 ω.2 j⟩
      map_add' := fun ω ω' => by
        funext j
        apply Subtype.ext
        refine PiLp.ext fun b => ?_
        simp
      map_smul' := fun c ω => by
        funext j
        apply Subtype.ext
        refine PiLp.ext fun b => ?_
        simp }
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ω hω
    apply Subtype.ext
    refine PiLp.ext fun b => ?_
    obtain ⟨j, hj⟩ := hBU b.1 b.2
    have hbj : b.1 ∈ Bj j := Finset.mem_filter.2 ⟨b.2, hj⟩
    have := congrArg (fun z => ((z j : stressSpace (Bj j)) : EuclideanSpace ℝ (Bj j)) ⟨b.1, hbj⟩)
      hω
    simpa [ψ] using this
  calc Module.finrank ℝ (stressVanish BU BI)
      ≤ Module.finrank ℝ ((j : ι) → stressSpace (Bj j)) :=
        LinearMap.finrank_le_finrank_of_injective hψ
    _ = ∑ j, Module.finrank ℝ (stressSpace (Bj j)) := Module.finrank_pi_fintype ℝ

open Classical in
/-- **The star bound**: `(k - 3)(ℓ - 3) + dim stress_Q(B_U) ≤ dim stress(B_U)`, for bars of the
star bracing every three-face and with at most `2k - 3` bars on the polygon. -/
theorem star_bound [Nonempty ι] (BU : Finset (Sym2 E5))
    (hBU : ∀ b ∈ BU, ∃ j, ∀ p ∈ b, p ∈ S.XS j)
    (hbr : ∀ j, Braces ((BU.filter fun b => ∀ p ∈ b, p ∈ S.XS j : Finset (Sym2 E5)) :
      Set (Sym2 E5)) (S.XS j))
    (hBF : (BU.filter fun b => ∀ p ∈ b, p ∈ S.XF).card + 3 ≤ 2 * S.XF.card) :
    ((S.XF.card : ℤ) - 3) * ((Fintype.card ι : ℤ) - 3) +
      Module.finrank ℝ (stressVanish BU (BU.filter fun b => ∃ p ∈ b, p ∈ S.XF)) ≤
        Module.finrank ℝ (stressSpace BU) := by
  classical
  set Bj : ι → Finset (Sym2 E5) := fun j => BU.filter fun b => ∀ p ∈ b, p ∈ S.XS j with hBjdef
  set BF := BU.filter fun b => ∀ p ∈ b, p ∈ S.XF with hBFdef
  -- motions and stresses of the star
  have hker := S.finrank_ker_rigMap_ge BU hBU
  have hXU : ∀ b ∈ BU, ∀ p ∈ b, p ∈ S.XU := fun b hb p hp => by
    obtain ⟨j, hj⟩ := hBU b hb
    exact S.XS_subset_XU j (hj p hp)
  have hstU := card_add_finrank_ker_le hXU
  -- localization and the rigidity of the three-faces
  have hloc := S.finrank_stressVanish_le BU hBU
  have hT : ∀ j, Module.finrank ℝ (stressSpace (Bj j)) + 3 * (S.XS j).card ≤
      (Bj j).card + 3 + 3 := fun j =>
    finrank_stress_add_le_of_braces (d := 3) (c := 3) (by decide) (S.hL j)
      (S.hXFS j S.hp0) (S.hXSL j) (S.hLspan j) (hbr j)
  have hTsum : ∑ j, (Module.finrank ℝ (stressSpace (Bj j)) + 3 * (S.XS j).card) ≤
      ∑ j, ((Bj j).card + 6) := Finset.sum_le_sum fun j _ => hT j
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at hTsum
  -- counting the joints
  have hXSsum : ∑ j, (S.XS j).card = Fintype.card ι * S.XF.card + S.priv.card := by
    have hpriv : S.priv = Finset.univ.biUnion fun j => S.XS j \ S.XF := by
      ext p
      simp only [S.mem_priv, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨j, hj⟩, hp⟩; exact ⟨j, hj, hp⟩
      · rintro ⟨j, hj, hp⟩; exact ⟨⟨j, hj⟩, hp⟩
    have hdisj : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι), i ≠ j →
        Disjoint (S.XS i \ S.XF) (S.XS j \ S.XF) := by
      intro i _ j _ hij
      rw [Finset.disjoint_left]
      intro p hpi hpj
      exact (Finset.mem_sdiff.1 hpi).2
        (S.hdisj i j hij p (Finset.mem_sdiff.1 hpi).1 (Finset.mem_sdiff.1 hpj).1)
    rw [hpriv, Finset.card_biUnion hdisj]
    have hc : ∀ j, (S.XS j).card = S.XF.card + (S.XS j \ S.XF).card := fun j => by
      rw [Finset.card_sdiff_of_subset (S.hXFS j)]
      have := Finset.card_le_card (S.hXFS j)
      omega
    rw [Finset.sum_congr rfl fun j _ => hc j, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
  have hXUcard : S.XU.card = S.XF.card + S.priv.card := by
    rw [PolyStar.priv, Finset.card_sdiff_of_subset S.XF_subset_XU]
    have := Finset.card_le_card S.XF_subset_XU
    omega
  -- counting the bars
  have hBsum : ∑ j, (Bj j).card + BF.card ≤ BU.card + Fintype.card ι * BF.card := by
    have hBFj : ∀ j, BF ⊆ Bj j := fun j b hb => by
      rw [hBFdef, Finset.mem_filter] at hb
      exact Finset.mem_filter.2 ⟨hb.1, fun p hp => S.hXFS j (hb.2 p hp)⟩
    have hdisj : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι), i ≠ j →
        Disjoint (Bj i \ BF) (Bj j \ BF) := by
      intro i _ j _ hij
      rw [Finset.disjoint_left]
      intro b hbi hbj
      apply (Finset.mem_sdiff.1 hbi).2
      have hbi' := Finset.mem_filter.1 (Finset.mem_sdiff.1 hbi).1
      have hbj' := Finset.mem_filter.1 (Finset.mem_sdiff.1 hbj).1
      exact Finset.mem_filter.2 ⟨hbi'.1, fun p hp => S.hdisj i j hij p (hbi'.2 p hp) (hbj'.2 p hp)⟩
    have hdisjF : Disjoint BF (Finset.univ.biUnion fun j => Bj j \ BF) := by
      rw [Finset.disjoint_left]
      intro b hb hb'
      obtain ⟨j, -, hbj⟩ := Finset.mem_biUnion.1 hb'
      exact (Finset.mem_sdiff.1 hbj).2 hb
    have hsub : BF ∪ (Finset.univ.biUnion fun j => Bj j \ BF) ⊆ BU := by
      intro b hb
      rcases Finset.mem_union.1 hb with hb | hb
      · exact (Finset.mem_filter.1 hb).1
      · obtain ⟨j, -, hbj⟩ := Finset.mem_biUnion.1 hb
        exact (Finset.mem_filter.1 (Finset.mem_sdiff.1 hbj).1).1
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisjF, Finset.card_biUnion hdisj] at hcard
    have hc : ∀ j, (Bj j).card = BF.card + (Bj j \ BF).card := fun j => by
      rw [Finset.card_sdiff_of_subset (hBFj j)]
      have := Finset.card_le_card (hBFj j)
      omega
    rw [Finset.sum_congr rfl fun j _ => hc j, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
    omega
  -- assemble
  have hℓ : 1 ≤ Fintype.card ι := Fintype.card_pos
  set k := S.XF.card
  set ℓ := Fintype.card ι
  set M := S.priv.card
  set SV := Module.finrank ℝ (stressVanish BU (BU.filter fun b => ∃ p ∈ b, p ∈ S.XF))
  set SU := Module.finrank ℝ (stressSpace BU)
  set KR := Module.finrank ℝ (LinearMap.ker (rigMap S.XU BU))
  set Sst := ∑ j, Module.finrank ℝ (stressSpace (Bj j))
  set SB := ∑ j, (Bj j).card
  have e1 : (BU.card : ℤ) + KR ≤ SU + 5 * (k + M) := by
    have := hstU; rw [hXUcard] at this; exact_mod_cast this
  have e2 : (12 : ℤ) + 2 * M ≤ KR := by exact_mod_cast hker
  have e3 : (SV : ℤ) ≤ Sst := by exact_mod_cast hloc
  have e4 : (Sst : ℤ) + 3 * (ℓ * k + M) ≤ SB + ℓ * 6 := by
    have := hTsum; rw [hXSsum] at this; push_cast at this ⊢; linarith
  have e5 : (SB : ℤ) + BF.card ≤ BU.card + ℓ * BF.card := by exact_mod_cast hBsum
  have e6 : (BF.card : ℤ) + 3 ≤ 2 * k := by exact_mod_cast hBF
  have e7 : (0 : ℤ) ≤ ((ℓ : ℤ) - 1) * (2 * k - 3 - BF.card) :=
    mul_nonneg (by have h1 : (1 : ℤ) ≤ ℓ := (by exact_mod_cast hℓ); linarith) (by linarith)
  nlinarith

end PolyStar

/-! ### Faces of a polytope as joint sets -/

/-- The direction of a face is spanned by its vertices, seen from one of them. -/
lemma face_vectorSpan_le {V : Finset E5} {F : Set E5} (hF : F ∈ faces (convexHull ℝ (V : Set E5)))
    {XF : Finset E5} (hXF : (XF : Set E5) = F.extremePoints ℝ) {p0 : E5} (hp0 : p0 ∈ XF) :
    vectorSpan ℝ F ≤ Submodule.span ℝ ((fun p => p - p0) '' (XF : Set E5)) := by
  classical
  have hFS : F = convexHull ℝ ((V.filter (· ∈ F) : Finset E5) : Set E5) :=
    face_eq_convexHull_filter hF
  have hFconv : F = convexHull ℝ (F.extremePoints ℝ) := by
    conv_lhs => rw [hFS]
    rw [← convexHull_extremePoints_eq (V.filter (· ∈ F)), ← hFS]
  have e1 : vectorSpan ℝ F = vectorSpan ℝ (F.extremePoints ℝ) := by
    conv_lhs => rw [hFconv]
    rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
  have hp0' : p0 ∈ F.extremePoints ℝ := by rw [← hXF]; exact hp0
  rw [e1, vectorSpan_eq_span_vsub_set_right ℝ hp0', hXF]
  rfl

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Two distinct three-faces through a `2`-face meet exactly in it. -/
lemma IsCSPolytope5.inter_eq_of_three_faces {Q T T' : Set E5} (hQ : Q ∈ faces P) (h2 : dim Q = 2)
    (hT : T ∈ faces P) (hT3 : dim T = 3) (hT' : T' ∈ faces P) (hT'3 : dim T' = 3)
    (hQT : Q ⊆ T) (hQT' : Q ⊆ T') (hne : T ≠ T') : T ∩ T' = Q := by
  obtain ⟨V, hV⟩ := hP.polytope
  subst hV
  have hI : T ∩ T' ∈ faces (convexHull ℝ (V : Set E5)) :=
    inter_mem_faces_of_nonempty hT hT' (hQ.1.mono (Set.subset_inter hQT hQT'))
  have hIT : T ∩ T' ≠ T := by
    intro h
    have hTT' : T ⊆ T' := by rw [← h]; exact Set.inter_subset_right
    have hTf : T ∈ faces T' := (mem_faces_face_iff hT').2 ⟨hT, hTT'⟩
    have := dim_lt_of_mem_faces_ne hTf hne
    omega
  have hIf : T ∩ T' ∈ faces T := (mem_faces_face_iff hT).2 ⟨hI, Set.inter_subset_left⟩
  have hId := dim_lt_of_mem_faces_ne hIf hIT
  by_contra hQI
  have hQf : Q ∈ faces (T ∩ T') := (mem_faces_face_iff hI).2 ⟨hQ, Set.subset_inter hQT hQT'⟩
  have := dim_lt_of_mem_faces_ne hQf (Ne.symm hQI)
  omega

/-- A `2`-face lies in as many three-faces as facets (its face figure is a polygon). -/
lemma IsCSPolytope5.up_three_eq_up_four {Q : Set E5} (hQ : Q ∈ faces P) (h2 : dim Q = 2) :
    {T | T ∈ faces P ∧ Q ⊆ T ∧ dim T = 3}.ncard =
      {F | F ∈ faces P ∧ Q ⊆ F ∧ dim F = 4}.ncard := by
  have hne : Q ≠ P := fun h => by have := hP.dim_self; rw [← h, h2] at this; omega
  rw [hP.ncard_up hQ hne 3 (by norm_num), hP.ncard_up hQ hne 4 le_rfl]
  obtain ⟨W, hW, hmem, hdim⟩ := hP.dualFace_facts hQ hne
  rw [hW]
  exact cnt_one_eq_cnt_zero hmem (by omega)

set_option maxHeartbeats 1000000 in
open Classical in
/-- **The polygon-star lemma** from local rigidity: `2 (k - 3)(ℓ - 3) ≤ G` for a `2`-face with
`k` vertices lying in `ℓ` three-faces. -/
theorem IsCSPolytope5.polygon_star_of_loc (hW : WhiteleyCSLoc P) {Q : Set E5} (hQ : Q ∈ faces P)
    (h2 : dim Q = 2) :
    2 * (((cnt P Q 0 : ℤ) - 3) *
      (({T | T ∈ faces P ∧ Q ⊆ T ∧ dim T = 3}.ncard : ℤ) - 3)) ≤ (flagDataOf P).G := by
  classical
  obtain ⟨B, hBX, hBs, hBcard, -, hrig, -, hB3, hB2, -⟩ := hW
  obtain ⟨V, hV⟩ := hP.polytope
  -- the vertex set of `P`
  set X := (extremePoints_finite V).toFinset with hXdef
  have hXcoe : (X : Set E5) = P.extremePoints ℝ := by rw [hXdef, Set.Finite.coe_toFinset, hV]
  have hXcard : X.card = fvec P 0 := by
    have h1 := fvec_zero_eq V
    rw [Set.ncard_eq_toFinset_card _ (extremePoints_finite V)] at h1
    rw [hV, hXdef, h1]
  have hXs : ∀ x ∈ X, -x ∈ X := by
    intro x hx
    rw [← Finset.mem_coe, hXcoe] at hx ⊢
    exact neg_mem_extremePoints hP.symm hx
  have hX0 : (0 : E5) ∉ X := by
    rw [← Finset.mem_coe, hXcoe]
    exact hP.zero_not_mem_extremePoints
  have hspan : Submodule.span ℝ (X : Set E5) = ⊤ := by
    rw [hXcoe, hV]
    exact span_extremePoints_eq_top (hV ▸ hP.zero_mem_interior)
  -- vertex sets of faces
  set vtx : Set E5 → Finset E5 := fun F => X.filter (· ∈ F) with hvtxdef
  have hvtx : ∀ F ∈ faces P, (vtx F : Set E5) = F.extremePoints ℝ := by
    intro F hF
    have hFext : IsExtreme ℝ P F := hF.2.isExtreme
    rw [hFext.extremePoints_eq, hvtxdef, Finset.coe_filter, ← hXcoe]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_coe]
    tauto
  have hvtx_sub : ∀ F, ∀ p ∈ vtx F, p ∈ F := fun F p hp => (Finset.mem_filter.1 hp).2
  have hvtx_card : ∀ F ∈ faces P, (vtx F).card = cnt P F 0 := by
    intro F hF
    have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
    have hFSF : F = convexHull ℝ ((V.filter (· ∈ F) : Finset E5) : Set E5) :=
      face_eq_convexHull_filter hF'
    have h1 : cnt P F 0 = fvec F 0 := by
      rw [hV]
      exact (fvec_face_eq_cnt hF' 0).symm
    have h2' : fvec F 0 = (F.extremePoints ℝ).ncard := by
      have := fvec_zero_eq (V.filter (· ∈ F))
      rwa [← hFSF] at this
    rw [h1, h2', ← hvtx F hF, Set.ncard_coe_finset]
  have hvtx_ne : ∀ F ∈ faces P, (vtx F).Nonempty := by
    intro F hF
    have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
    have hFSF : F = convexHull ℝ ((V.filter (· ∈ F) : Finset E5) : Set E5) :=
      face_eq_convexHull_filter hF'
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hext : F.extremePoints ℝ = ∅ := by rw [← hvtx F hF, hemp, Finset.coe_empty]
    have hFconv : F = convexHull ℝ (F.extremePoints ℝ) := by
      conv_lhs => rw [hFSF]
      rw [← convexHull_extremePoints_eq (V.filter (· ∈ F)), ← hFSF]
    rw [hext, convexHull_empty] at hFconv
    exact Set.not_nonempty_empty (hFconv ▸ hF.1)
  have hP' : ∀ {F : Set E5}, F ∈ faces P → F ∈ faces (convexHull ℝ (V : Set E5)) :=
    fun hF => hV ▸ hF
  -- the three-faces through `Q`
  have hTfin : {T | T ∈ faces P ∧ Q ⊆ T ∧ dim T = 3}.Finite :=
    hP.faces_finite.subset fun T hT => hT.1
  set ιs := hTfin.toFinset with hιs
  have hmemι : ∀ {T : Set E5}, T ∈ ιs ↔ T ∈ faces P ∧ Q ⊆ T ∧ dim T = 3 := fun {T} =>
    Set.Finite.mem_toFinset _
  have hℓ : 3 ≤ ιs.card := by
    rw [hιs, ← Set.ncard_eq_toFinset_card _ hTfin, hP.up_three_eq_up_four hQ h2]
    exact hP.three_le_up hQ h2
  haveI : Nonempty {T // T ∈ ιs} := by
    obtain ⟨T, hT⟩ := Finset.card_pos.1 (by omega : 0 < ιs.card)
    exact ⟨⟨T, hT⟩⟩
  obtain ⟨p0, hp0⟩ := hvtx_ne Q hQ
  -- the polygon star
  let S : PolyStar {T // T ∈ ιs} :=
    { XF := vtx Q
      XS := fun T => vtx T.1
      p0 := p0
      D := vectorSpan ℝ Q
      L := fun T => vectorSpan ℝ T.1
      hp0 := hp0
      hD := h2
      hXFD := fun p hp => vsub_mem_vectorSpan ℝ (hvtx_sub Q p hp) (hvtx_sub Q p0 hp0)
      hDspan := face_vectorSpan_le (hP' hQ) (hvtx Q hQ) hp0
      hL := fun T => (hmemι.1 T.2).2.2
      hXFS := fun T p hp => Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hp).1,
        (hmemι.1 T.2).2.1 (Finset.mem_filter.1 hp).2⟩
      hXSL := fun T p hp => vsub_mem_vectorSpan ℝ (hvtx_sub T.1 p hp)
        ((hmemι.1 T.2).2.1 (hvtx_sub Q p0 hp0))
      hLspan := fun T => face_vectorSpan_le (hP' (hmemι.1 T.2).1) (hvtx T.1 (hmemι.1 T.2).1)
        (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hp0).1,
          (hmemι.1 T.2).2.1 (Finset.mem_filter.1 hp0).2⟩)
      hdisj := fun T T' hTT' p hp hp' => by
        have hne : T.1 ≠ T'.1 := fun h => hTT' (Subtype.ext h)
        have hI := hP.inter_eq_of_three_faces hQ h2 (hmemι.1 T.2).1 (hmemι.1 T.2).2.2
          (hmemι.1 T'.2).1 (hmemι.1 T'.2).2.2 (hmemι.1 T.2).2.1 (hmemι.1 T'.2).2.1 hne
        refine Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hp).1, ?_⟩
        rw [← hI]
        exact ⟨hvtx_sub _ p hp, hvtx_sub _ p hp'⟩ }
  -- the bars of the star
  set BU := B.filter (fun b => ∃ T ∈ ιs, ∀ p ∈ b, p ∈ T) with hBUdef
  have hBUB : BU ⊆ B := Finset.filter_subset _ _
  have hvert : ∀ b ∈ B, ∀ p ∈ b, p ∈ X := fun b hb p hp => by
    rw [← Finset.mem_coe, hXcoe]; exact hBX b hb p hp
  have hBU : ∀ b ∈ BU, ∃ j, ∀ p ∈ b, p ∈ S.XS j := by
    intro b hb
    rw [hBUdef, Finset.mem_filter] at hb
    obtain ⟨T, hT, hbT⟩ := hb.2
    exact ⟨⟨T, hT⟩, fun p hp => Finset.mem_filter.2 ⟨hvert b hb.1 p hp, hbT p hp⟩⟩
  have hBj : ∀ j : {T // T ∈ ιs},
      (BU.filter fun b => ∀ p ∈ b, p ∈ S.XS j) = B.filter (fun b => ∀ p ∈ b, p ∈ j.1) := by
    intro j
    ext b
    simp only [Finset.mem_filter, hBUdef]
    constructor
    · rintro ⟨⟨hbB, -⟩, hbj⟩
      exact ⟨hbB, fun p hp => hvtx_sub j.1 p (hbj p hp)⟩
    · rintro ⟨hbB, hbj⟩
      exact ⟨⟨hbB, j.1, j.2, hbj⟩, fun p hp => Finset.mem_filter.2 ⟨hvert b hbB p hp, hbj p hp⟩⟩
  have hbr : ∀ j, Braces ((BU.filter fun b => ∀ p ∈ b, p ∈ S.XS j : Finset (Sym2 E5)) :
      Set (Sym2 E5)) (S.XS j) := by
    intro j
    rw [hBj j]
    show Braces _ ((vtx j.1 : Finset E5) : Set E5)
    rw [hvtx j.1 (hmemι.1 j.2).1]
    exact hB3 j.1 (hmemι.1 j.2).1 (hmemι.1 j.2).2.2
  have hBF : (BU.filter fun b => ∀ p ∈ b, p ∈ S.XF).card + 3 ≤ 2 * S.XF.card := by
    have hsub : (BU.filter fun b => ∀ p ∈ b, p ∈ S.XF) ⊆ B.filter (fun b => ∀ p ∈ b, p ∈ Q) := by
      intro b hb
      rw [Finset.mem_filter] at hb ⊢
      exact ⟨hBUB hb.1, fun p hp => hvtx_sub Q p (hb.2 p hp)⟩
    have h1 := Finset.card_le_card hsub
    have h2' := hB2 Q hQ h2
    have h3 : S.XF.card = cnt P Q 0 := hvtx_card Q hQ
    have h4 : (B.filter (fun b => ∀ p ∈ b, p ∈ Q)).card + 3 ≤ 2 * cnt P Q 0 := by
      convert h2'
    omega
  have hstar := S.star_bound BU hBU hbr hBF
  -- antisymmetrization
  have hBI : ∀ b ∈ BU.filter (fun b => ∃ p ∈ b, p ∈ S.XF), b.map Neg.neg ∉ BU := by
    intro b hb hnb
    rw [Finset.mem_filter] at hb
    obtain ⟨p, hpb, hpQ⟩ := hb.2
    rw [hBUdef, Finset.mem_filter] at hnb
    obtain ⟨T, hT, hTb⟩ := hnb.2
    have hnp : -p ∈ T := hTb (-p) (Sym2.mem_map.2 ⟨p, hpb, rfl⟩)
    have hpT : p ∈ T := (hmemι.1 hT).2.1 (hvtx_sub Q p hpQ)
    have hTP := hP.eq_of_mem_of_neg_mem (hmemι.1 hT).1 hpT hnp
    have h3 := (hmemι.1 hT).2.2
    rw [hTP, hP.dim_self] at h3
    omega
  have hanti := two_mul_finrank_stress_le_of_incident hXs hX0 hspan
    (fun b hb => (hBs b hb).1) (fun b hb => (hBs b hb).2) (by rw [hXcoe]; exact hrig) hBUB hBI
  -- assemble
  have hk : (S.XF.card : ℤ) = cnt P Q 0 := by exact_mod_cast hvtx_card Q hQ
  have hℓ' : (Fintype.card {T // T ∈ ιs} : ℤ) =
      ({T | T ∈ faces P ∧ Q ⊆ T ∧ dim T = 3}.ncard : ℤ) := by
    rw [Fintype.card_coe, hιs, ← Set.ncard_eq_toFinset_card _ hTfin]
  rw [hk, hℓ'] at hstar
  have hG : (flagDataOf P).G = (B.card : ℤ) - 5 * X.card + 10 := by
    simp only [FlagData.G, flagDataOf]
    rw [hBcard, hXcard]
  rw [hG]
  have hanti' : (2 : ℤ) * Module.finrank ℝ (stressSpace BU) + 5 * X.card ≤
      B.card + 10 + 2 * Module.finrank ℝ
        (stressVanish BU (BU.filter fun b => ∃ p ∈ b, p ∈ S.XF)) := by
    exact_mod_cast hanti
  linarith

/-- **The polygon-star lemma** `2 (k - 3)(ℓ - 3) ≤ G`. -/
theorem IsCSPolytope5.polygon_star {Q : Set E5} (hQ : Q ∈ faces P) (h2 : dim Q = 2) :
    2 * (((cnt P Q 0 : ℤ) - 3) *
      (({T | T ∈ faces P ∧ Q ⊆ T ∧ dim T = 3}.ncard : ℤ) - 3)) ≤ (flagDataOf P).G :=
  hP.polygon_star_of_loc (hP.whiteleyCSLoc_of_w3 alexandrov3_proof) hQ h2

/-- `A` as a sum over the `2`-faces. -/
lemma IsCSPolytope5.A_eq_sum : (flagDataOf P).A = ∑ Q ∈ (hP.kfaces_finite 2).toFinset,
    ((cnt P Q 0 : ℤ) - 3) * (({F | F ∈ faces P ∧ Q ⊆ F ∧ dim F = 4}.ncard : ℤ) - 3) := by
  simp only [FlagData.A, flagDataOf]
  rw [hP.flag3_eq_sum_mid 0 2 4, hP.flag2_eq_sum 0 2, hP.flag2_eq_sum_up 2 4, fvec,
    Set.ncard_eq_toFinset_card _ (hP.kfaces_finite 2)]
  push_cast
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun Q _ => ?_
  push_cast; ring

/-- **Weak polygon-star**: `G = 0` forces `A = 0`. -/
theorem IsCSPolytope5.A_eq_zero_of_G_eq_zero (hG : (flagDataOf P).G = 0) :
    (flagDataOf P).A = 0 := by
  rw [hP.A_eq_sum]
  refine Finset.sum_eq_zero fun Q hQ => ?_
  rw [Set.Finite.mem_toFinset] at hQ
  have h1 := hP.three_le_cnt hQ.1 hQ.2
  have h2 := hP.three_le_up hQ.1 hQ.2
  have hps := hP.polygon_star hQ.1 hQ.2
  rw [hP.up_three_eq_up_four hQ.1 hQ.2, hG] at hps
  have hnn : (0 : ℤ) ≤ ((cnt P Q 0 : ℤ) - 3) *
      (({F | F ∈ faces P ∧ Q ⊆ F ∧ dim F = 4}.ncard : ℤ) - 3) :=
    mul_nonneg (by omega) (by omega)
  linarith

end cs

end Kalai5
