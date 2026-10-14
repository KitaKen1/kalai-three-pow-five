import Kalai5.Rigidity.Toric
import Kalai5.Polar.Facet4

/-!
# Stresses, and stress localization `G ≥ 2 g(F)` from Whiteley's theorem

A *self-stress* of a bar set `B` is a weight vector `ω` with `Σ_b ω_b · barVal u b = 0` for every
velocity field `u` (equilibrium at every vertex, written dually).

* `two_mul_finrank_stress_le`: for a symmetric infinitesimally rigid framework `(X, B)` and a
  sub-bar-set `BF ⊆ B` containing no antipodal pair, antisymmetrization embeds the stresses of
  `BF` into the orthogonal complement of the image of the even rigidity map, so
  `2 · dim stress(BF) + d |X| ≤ |B| + 2d`.
* `le_finrank_stress_of_hyperplane`: if the vertices of `BF` lie in an affine 4-space, the
  tangential trivial motions (6 rotations, 4 translations) lie in the kernel of the rigidity map,
  so `dim stress(BF) ≥ |BF| - 4 |X_F| + 10`.
* `IsCSPolytope5.stress_localization_of_whiteley`: for a facet `F`,
  `g(F) = |B_F| - 4 f₀(F) + 10 ≤ dim stress(B_F) ≤ G/2`.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {d : ℕ}

lemma inner_euclid {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) :
    ⟪x, y⟫ = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, mul_comm]

/-! ### Stress spaces -/

/-- The self-stresses of the bars `B`. -/
def stressSpace (B : Finset (Sym2 (E d))) : Submodule ℝ (EuclideanSpace ℝ B) where
  carrier := {ω | ∀ u : E d → E d, ∑ b : B, ω b * barVal u b.1 = 0}
  add_mem' := by
    intro ω ω' hω hω' u
    have h1 : ∑ b : B, ω b * barVal u b.1 = 0 := hω u
    have h2 : ∑ b : B, ω' b * barVal u b.1 = 0 := hω' u
    show ∑ b : B, (ω + ω') b * barVal u b.1 = 0
    simp only [PiLp.add_apply, add_mul, Finset.sum_add_distrib, h1, h2, add_zero]
  zero_mem' := by
    intro u
    simp
  smul_mem' := by
    intro c ω hω u
    have h1 : ∑ b : B, ω b * barVal u b.1 = 0 := hω u
    show ∑ b : B, (c • ω) b * barVal u b.1 = 0
    simp only [PiLp.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, h1, mul_zero]

lemma mem_stressSpace {B : Finset (Sym2 (E d))} {ω : EuclideanSpace ℝ B} :
    ω ∈ stressSpace B ↔ ∀ u : E d → E d, ∑ b : B, ω b * barVal u b.1 = 0 := Iff.rfl

/-! ### The even rigidity map -/

/-- The rigidity map on even velocity fields (parametrised by a half `Xp`), on a half `Bp` of the
bars. -/
noncomputable def evenRigMap (Xp : Finset (E d)) (Bp : Finset (Sym2 (E d))) :
    (Xp → E d) →ₗ[ℝ] EuclideanSpace ℝ Bp where
  toFun w := WithLp.toLp 2 (fun b => barVal (evenExt Xp w) b.1)
  map_add' w w' := by
    refine PiLp.ext fun b => ?_
    simp only [PiLp.toLp_apply, PiLp.add_apply]
    rw [← barVal_add]
    congr 1
    funext p
    exact evenExt_add w w' p
  map_smul' c w := by
    refine PiLp.ext fun b => ?_
    simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← barVal_smul]
    congr 1
    funext p
    exact evenExt_smul c w p

lemma evenRigMap_apply (Xp : Finset (E d)) (Bp : Finset (Sym2 (E d))) (w : Xp → E d) (b : Bp) :
    evenRigMap Xp Bp w b = barVal (evenExt Xp w) b.1 := rfl

/-- Even infinitesimal motions are translations, so the kernel has dimension at most `d`. -/
lemma finrank_ker_evenRigMap_le {X Xp : Finset (E d)} {B Bp : Finset (Sym2 (E d))}
    (hXs : ∀ x ∈ X, -x ∈ X) (hspan : Submodule.span ℝ (X : Set (E d)) = ⊤)
    (hXpX : Xp ⊆ X) (hXdis : ∀ x ∈ Xp, -x ∉ Xp)
    (hBcov : ∀ b ∈ B, b ∈ Bp ∨ b.map Neg.neg ∈ Bp)
    (hrig : IsInfRigid (X : Set (E d)) (B : Set (Sym2 (E d)))) :
    Module.finrank ℝ (LinearMap.ker (evenRigMap Xp Bp)) ≤ d := by
  classical
  let κ : E d →ₗ[ℝ] (Xp → E d) := LinearMap.pi fun _ => LinearMap.id
  have hker : LinearMap.ker (evenRigMap Xp Bp) ≤ LinearMap.range κ := by
    intro w hw
    rw [LinearMap.mem_ker] at hw
    have hw' : ∀ b : Bp, barVal (evenExt Xp w) b.1 = 0 := fun b => by
      have := congrArg (fun z : EuclideanSpace ℝ Bp => z b) hw
      simpa [evenRigMap_apply] using this
    set u := evenExt Xp w with hu
    have heven : ∀ p, u (-p) = u p := evenExt_neg hXdis w
    have hmot : ∀ b ∈ (B : Set (Sym2 (E d))), barVal u b = 0 := by
      intro b hb
      rcases hBcov b hb with h | h
      · exact hw' ⟨b, h⟩
      · have h1 := hw' ⟨_, h⟩
        rw [barVal_neg_of_even heven] at h1
        linarith
    obtain ⟨A, c, -, hAc⟩ := hrig u hmot
    have hA : A = 0 := by
      apply LinearMap.ext_on hspan
      intro p hp
      have h1 := hAc p hp
      have h2 := hAc (-p) (hXs p hp)
      rw [heven, h1, map_neg] at h2
      have h4 := congrArg (fun z => z - c) h2
      simp only [add_sub_cancel_right] at h4
      have h3 : (2 : ℝ) • A p = 0 := by
        rw [two_smul]
        nth_rewrite 1 [h4]
        exact neg_add_cancel (A p)
      simpa using (smul_eq_zero.1 h3).resolve_left two_ne_zero
    rw [LinearMap.mem_range]
    refine ⟨c, ?_⟩
    funext q
    have := hAc q.1 (hXpX q.2)
    rw [hA, LinearMap.zero_apply, zero_add, hu, evenExt_of_mem w q.2] at this
    simp only [κ, LinearMap.pi_apply, LinearMap.id_apply]
    exact this.symm
  calc Module.finrank ℝ (LinearMap.ker (evenRigMap Xp Bp))
      ≤ Module.finrank ℝ (LinearMap.range κ) := Submodule.finrank_mono hker
    _ ≤ Module.finrank ℝ (E d) := LinearMap.finrank_range_le κ
    _ = d := finrank_euclideanSpace_fin

/-! ### Antisymmetrized stresses of a sub-framework -/

open Classical in
/-- Extension of a stress on `BF` by zero. -/
noncomputable def extZero (BF : Finset (Sym2 (E d))) (ω : EuclideanSpace ℝ BF) (c : Sym2 (E d)) :
    ℝ :=
  if h : c ∈ BF then ω ⟨c, h⟩ else 0

lemma extZero_add (BF : Finset (Sym2 (E d))) (ω ω' : EuclideanSpace ℝ BF) (c : Sym2 (E d)) :
    extZero BF (ω + ω') c = extZero BF ω c + extZero BF ω' c := by
  unfold extZero
  split_ifs <;> simp

lemma extZero_smul (BF : Finset (Sym2 (E d))) (a : ℝ) (ω : EuclideanSpace ℝ BF) (c : Sym2 (E d)) :
    extZero BF (a • ω) c = a * extZero BF ω c := by
  unfold extZero
  split_ifs <;> simp

/-- **Stresses of a sub-framework without antipodal bars** embed into the antisymmetric stresses
of a symmetric rigid framework: `2 · dim stress(BF) + d |X| ≤ |B| + 2d`. -/
theorem two_mul_finrank_stress_le {X : Finset (E d)} {B BF : Finset (Sym2 (E d))}
    (hXs : ∀ x ∈ X, -x ∈ X) (hX0 : (0 : E d) ∉ X)
    (hspan : Submodule.span ℝ (X : Set (E d)) = ⊤)
    (hBs : ∀ b ∈ B, b.map Neg.neg ∈ B) (hBfree : ∀ b ∈ B, b.map Neg.neg ≠ b)
    (hrig : IsInfRigid (X : Set (E d)) (B : Set (Sym2 (E d))))
    (hBF : BF ⊆ B) (hBFdis : ∀ b ∈ BF, b.map Neg.neg ∉ BF) :
    2 * Module.finrank ℝ (stressSpace BF) + d * X.card ≤ B.card + 2 * d := by
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
  -- injectivity
  have hT_inj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ω hω
    apply Subtype.ext
    refine PiLp.ext fun c => ?_
    show (ω : EuclideanSpace ℝ BF) c = 0
    have hcB : c.1 ∈ B := hBF c.2
    have hnot : c.1.map Neg.neg ∉ BF := hBFdis c.1 c.2
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
  have h1 : Module.finrank ℝ (stressSpace BF) = Module.finrank ℝ (LinearMap.range T) :=
    (LinearMap.finrank_range_of_inj hT_inj).symm
  have h2 : Module.finrank ℝ (LinearMap.range T) ≤
      Module.finrank ℝ (LinearMap.range (evenRigMap Xp Bp))ᗮ := Submodule.finrank_mono hT_perp
  have h3 := Submodule.finrank_add_finrank_orthogonal (LinearMap.range (evenRigMap Xp Bp))
  rw [finrank_euclideanSpace, Fintype.card_coe] at h3
  rw [hdom] at hrn
  have hXc : X.card = 2 * Xp.card := hXcard.symm
  have hBc : B.card = 2 * Bp.card := hBcard.symm
  have key : Module.finrank ℝ (stressSpace BF) + Xp.card * d ≤ Bp.card + d := by omega
  rw [hXc, hBc]
  calc 2 * Module.finrank ℝ (stressSpace BF) + d * (2 * Xp.card)
      = 2 * (Module.finrank ℝ (stressSpace BF) + Xp.card * d) := by ring
    _ ≤ 2 * (Bp.card + d) := Nat.mul_le_mul_left 2 key
    _ = 2 * Bp.card + 2 * d := by ring

/-! ### Stresses of a framework in an affine 4-space -/

section hyperplane

open Classical in
/-- Extension of a tangential velocity field on `XF` by zero. -/
noncomputable def extTan (XF : Finset E5) (L : Submodule ℝ E5) (w : XF → L) (p : E5) : E5 :=
  if h : p ∈ XF then (w ⟨p, h⟩ : E5) else 0

lemma extTan_add (XF : Finset E5) (L : Submodule ℝ E5) (w w' : XF → L) (p : E5) :
    extTan XF L (w + w') p = extTan XF L w p + extTan XF L w' p := by
  unfold extTan
  split_ifs <;> simp

lemma extTan_smul (XF : Finset E5) (L : Submodule ℝ E5) (c : ℝ) (w : XF → L) (p : E5) :
    extTan XF L (c • w) p = c • extTan XF L w p := by
  unfold extTan
  split_ifs <;> simp

/-- Only the tangential part of a velocity field matters on bars inside `L`-translates. -/
lemma barVal_extTan_proj {XF : Finset E5} {L : Submodule ℝ E5}
    (hdiff : ∀ p ∈ XF, ∀ q ∈ XF, p - q ∈ L) (u : E5 → E5) (b : Sym2 E5)
    (hb : ∀ p ∈ b, p ∈ XF) :
    barVal (extTan XF L (fun p => L.orthogonalProjectionOnto (u p))) b = barVal u b := by
  induction b using Sym2.ind with
  | _ p q =>
    have hp : p ∈ XF := hb p (Sym2.mem_mk_left p q)
    have hq : q ∈ XF := hb q (Sym2.mem_mk_right p q)
    rw [barVal_mk, barVal_mk]
    unfold extTan
    rw [dif_pos hp, dif_pos hq]
    have hpq : p - q ∈ L := hdiff p hp q hq
    have e : ∀ v : E5, ⟪(L.orthogonalProjectionOnto v : E5), p - q⟫ = ⟪v, p - q⟫ := fun v => by
      have := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (K := L) ⟨p - q, hpq⟩ v
      rwa [Submodule.coe_inner] at this
    rw [inner_sub_left, inner_sub_left, e, e]

set_option maxHeartbeats 1000000 in
/-- **Lower bound for the stresses of a framework spanning an affine 4-space**:
`|BF| + 10 ≤ dim stress(BF) + 4 |XF|` (the 6 tangential rotations and 4 tangential translations
are infinitesimal motions). -/
theorem le_finrank_stress_of_hyperplane {XF : Finset E5} {BF : Finset (Sym2 E5)}
    {L : Submodule ℝ E5} (hL : Module.finrank ℝ L = 4) {p0 : E5} (hp0 : p0 ∈ XF)
    (hdiff : ∀ p ∈ XF, p - p0 ∈ L)
    (hspan : L ≤ Submodule.span ℝ ((fun p => p - p0) '' (XF : Set E5)))
    (hBF : ∀ b ∈ BF, ∀ p ∈ b, p ∈ XF) :
    BF.card + 10 ≤ Module.finrank ℝ (stressSpace BF) + 4 * XF.card := by
  classical
  have hdiff2 : ∀ p ∈ XF, ∀ q ∈ XF, p - q ∈ L := fun p hp q hq => by
    have := L.sub_mem (hdiff p hp) (hdiff q hq)
    rwa [sub_sub_sub_cancel_right] at this
  -- an orthonormal basis of `L`
  set ob := (stdOrthonormalBasis ℝ L).reindex (finCongr hL)
  set f : Fin 4 → E5 := fun i => (ob i : E5) with hfdef
  have hfL : ∀ i, f i ∈ L := fun i => (ob i).2
  have hfo : Orthonormal ℝ f := ob.orthonormal.comp_linearIsometry L.subtypeₗᵢ
  have hortho : ∀ a b : Fin 4, ⟪f a, f b⟫ = if a = b then 1 else 0 := orthonormal_iff_ite.1 hfo
  -- elementary rotations
  let rot : {q : Fin 4 × Fin 4 // q.1 < q.2} → E5 →ₗ[ℝ] E5 := fun q =>
    (innerₛₗ ℝ (f q.1.2)).smulRight (f q.1.1) - (innerₛₗ ℝ (f q.1.1)).smulRight (f q.1.2)
  have hrot : ∀ q y, rot q y = ⟪f q.1.2, y⟫ • f q.1.1 - ⟪f q.1.1, y⟫ • f q.1.2 := fun q y => by
    simp [rot]
  let M : ({q : Fin 4 × Fin 4 // q.1 < q.2} → ℝ) → E5 →ₗ[ℝ] E5 := fun lam => ∑ q, lam q • rot q
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
  have hbasis : ∀ lam (q0 : {q : Fin 4 × Fin 4 // q.1 < q.2}),
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
  let Θ : (({q : Fin 4 × Fin 4 // q.1 < q.2} → ℝ) × L) →ₗ[ℝ] (XF → L) :=
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
  let R : (XF → L) →ₗ[ℝ] EuclideanSpace ℝ BF :=
    { toFun := fun w => WithLp.toLp 2 (fun b => barVal (extTan XF L w) b.1)
      map_add' := fun w w' => by
        refine PiLp.ext fun b => ?_
        simp only [PiLp.toLp_apply, PiLp.add_apply]
        rw [← barVal_add]
        congr 1
        funext p
        exact extTan_add XF L w w' p
      map_smul' := fun c w => by
        refine PiLp.ext fun b => ?_
        simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← barVal_smul]
        congr 1
        funext p
        exact extTan_smul XF L c w p }
  have hR : ∀ w (b : BF), R w b = barVal (extTan XF L w) b.1 := fun _ _ => rfl
  -- trivial motions are in the kernel
  have hker : LinearMap.range Θ ≤ LinearMap.ker R := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    refine PiLp.ext fun b => ?_
    rw [hR, PiLp.zero_apply]
    have key : ∀ c : Sym2 E5, (∀ p ∈ c, p ∈ XF) → barVal (extTan XF L (Θ x)) c = 0 := by
      intro c hc
      induction c using Sym2.ind with
      | _ p q =>
        have hp : p ∈ XF := hc p (Sym2.mem_mk_left p q)
        have hq : q ∈ XF := hc q (Sym2.mem_mk_right p q)
        rw [barVal_mk]
        unfold extTan
        rw [dif_pos hp, dif_pos hq, hΘ, hΘ]
        have e : M x.1 (p - p0) + (x.2 : E5) - (M x.1 (q - p0) + (x.2 : E5)) =
            M x.1 (p - q) := by
          rw [add_sub_add_right_eq_sub, ← map_sub]
          congr 1
          abel
        rw [e]
        exact hM_inner x.1 (p - q)
    exact key b.1 (hBF b.1 b.2)
  -- injectivity of the trivial motions
  have hΘ_inj : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨lam, c⟩ hx
    have hx' : ∀ p : XF, M lam ((p : E5) - p0) + (c : E5) = 0 := fun p => by
      have := congrArg (fun z : XF → L => ((z p : L) : E5)) hx
      simpa [hΘ] using this
    have hc : (c : E5) = 0 := by
      have := hx' ⟨p0, hp0⟩
      simpa using this
    have hMp : ∀ p ∈ XF, M lam (p - p0) = 0 := fun p hp => by
      have := hx' ⟨p, hp⟩
      rwa [hc, add_zero] at this
    have hLker : L ≤ LinearMap.ker (M lam) := hspan.trans (Submodule.span_le.2 (by
      rintro _ ⟨p, hp, rfl⟩
      exact hMp p hp))
    have hlam : lam = 0 := by
      funext q
      have h1 : M lam (f q.1.2) = 0 := hLker (hfL q.1.2)
      have h2 := hbasis lam q
      rw [h1, inner_zero_right] at h2
      exact h2.symm
    rw [hlam, Prod.mk_eq_zero]
    exact ⟨rfl, Subtype.ext hc⟩
  -- dimensions
  have hcard : Fintype.card {q : Fin 4 × Fin 4 // q.1 < q.2} = 6 := by decide
  have hdomΘ : Module.finrank ℝ (({q : Fin 4 × Fin 4 // q.1 < q.2} → ℝ) × L) = 10 := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hcard, hL]
  have hdomR : Module.finrank ℝ (XF → L) = XF.card * 4 := by
    rw [Module.finrank_pi_fintype]
    simp [hL]
  have hrangeΘ : Module.finrank ℝ (LinearMap.range Θ) = 10 := by
    rw [LinearMap.finrank_range_of_inj hΘ_inj, hdomΘ]
  have hkerR : 10 ≤ Module.finrank ℝ (LinearMap.ker R) := by
    rw [← hrangeΘ]
    exact Submodule.finrank_mono hker
  have hrn := LinearMap.finrank_range_add_finrank_ker R
  rw [hdomR] at hrn
  -- the orthogonal complement of the image consists of stresses
  have hperp : (LinearMap.range R)ᗮ ≤ stressSpace BF := by
    intro ω hω u
    rw [Submodule.mem_orthogonal] at hω
    have h0 := hω (R fun p => L.orthogonalProjectionOnto (u p)) (LinearMap.mem_range_self R _)
    rw [inner_euclid] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm, hR, barVal_extTan_proj hdiff2 u b.1 (hBF b.1 b.2)]
  have h3 := Submodule.finrank_add_finrank_orthogonal (LinearMap.range R)
  rw [finrank_euclideanSpace, Fintype.card_coe] at h3
  have h4 : Module.finrank ℝ (LinearMap.range R)ᗮ ≤ Module.finrank ℝ (stressSpace BF) :=
    Submodule.finrank_mono hperp
  omega

end hyperplane

/-! ### Stress localization for centrally symmetric 5-polytopes -/

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **Stress localization** `2 g(F) ≤ G` for every facet, from Whiteley's theorem. -/
theorem IsCSPolytope5.stress_localization_of_whiteley (hW : WhiteleyCS P) :
    ∀ R ∈ facetRows P, 2 * R.g ≤ (flagDataOf P).G := by
  classical
  intro R hR
  obtain ⟨F, hF, h4, rfl⟩ := hP.mem_facetRows hR
  obtain ⟨B, hBX, hBs, hBcard, hBloc, hrig⟩ := hW
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
  -- the bars inside `F`
  set BF := B.filter (fun b => ∀ p ∈ b, p ∈ F) with hBFdef
  have hBFsub : BF ⊆ B := Finset.filter_subset _ _
  have hBFdis : ∀ b ∈ BF, b.map Neg.neg ∉ BF := by
    intro b hb hnb
    rw [hBFdef, Finset.mem_filter] at hb hnb
    obtain ⟨p, hpb⟩ : ∃ p, p ∈ b := by
      induction b using Sym2.ind with
      | _ x y => exact ⟨x, Sym2.mem_mk_left x y⟩
    have hpF : p ∈ F := hb.2 p hpb
    have hnpF : -p ∈ F := hnb.2 (-p) (Sym2.mem_map.2 ⟨p, hpb, rfl⟩)
    have hFP := hP.eq_of_mem_of_neg_mem hF hpF hnpF
    rw [hFP, hP.dim_self] at h4
    omega
  have hup := two_mul_finrank_stress_le hXs hX0 hspan (fun b hb => (hBs b hb).1)
    (fun b hb => (hBs b hb).2) (by rw [hXcoe]; exact hrig) hBFsub hBFdis
  -- the vertices of `F`
  have hFext : IsExtreme ℝ P F := hF.2.isExtreme
  set XF := X.filter (· ∈ F) with hXFdef
  have hXFcoe : (XF : Set E5) = F.extremePoints ℝ := by
    rw [hFext.extremePoints_eq, hXFdef, Finset.coe_filter, ← hXcoe]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_coe]
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
  have hBF : ∀ b ∈ BF, ∀ p ∈ b, p ∈ XF := by
    intro b hb p hp
    rw [hBFdef, Finset.mem_filter] at hb
    rw [hXFdef, Finset.mem_filter, ← Finset.mem_coe, hXcoe]
    exact ⟨hBX b hb.1 p hp, hb.2 p hp⟩
  have hlow := le_finrank_stress_of_hyperplane (L := vectorSpan ℝ F) h4 hp0XF hdiff hspanF hBF
  -- assemble
  have hloc := hBloc F hF h4
  rw [← hBFdef] at hloc
  have hg := hP.facet_g_eq hF h4
  simp only [FlagData.G, flagDataOf]
  rw [hg]
  rw [hXcard] at hup
  rw [hXFcard] at hlow
  have hup' : (2 : ℤ) * Module.finrank ℝ (stressSpace BF) + 5 * fvec P 0 ≤ B.card + 10 := by
    exact_mod_cast hup
  have hlow' : (BF.card : ℤ) + 10 ≤ Module.finrank ℝ (stressSpace BF) + 4 * cnt P F 0 := by
    exact_mod_cast hlow
  rw [hBcard] at hup'
  linarith

end cs

end Kalai5
