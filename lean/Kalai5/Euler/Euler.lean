import Kalai5.Euler.Arrangement

/-!
# The Euler–Poincaré relation

For a polytope `Q = conv V` (any dimension, any ambient `ℝᵈ`):

  `Σ_{nonempty faces F} (-1)^(dim F) = 1`.

Proof: the vectors `c` are partitioned according to the face `argmax_Q ⟪·, c⟫`; the part `R_F`
belonging to a face `F` is a convex set, algebraically open in `(vectorSpan F)ᗮ` (of dimension
`d - dim F`).  Refining everything by the arrangement of the hyperplanes `(v - u)ᗮ`
(`v, u ∈ V`), each cell lies in exactly one `R_F`; counting cells with signs globally and inside
each `R_F` (`arrangement_count`) gives `Σ_F (-1)^(d - dim F) = (-1)^d`.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {d : ℕ}

lemma faces_finite_convexHull (V : Finset (E d)) : (faces (convexHull ℝ (V : Set (E d)))).Finite := by
  classical
  apply ((V.powerset.image fun S : Finset (E d) => convexHull ℝ (S : Set (E d))).finite_toSet).subset
  intro F hF
  exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨V.filter (· ∈ F),
    Finset.mem_powerset.2 (Finset.filter_subset _ _), (face_eq_convexHull_filter hF).symm⟩)

lemma inner_vectorSpan_eq_zero_of_const {F : Set (E d)} {z : E d} {κ : ℝ}
    (hz : ∀ x ∈ F, ⟪x, z⟫ = κ) : ∀ u ∈ vectorSpan ℝ F, ⟪u, z⟫ = 0 := by
  intro u hu
  rw [vectorSpan_def] at hu
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, x', hx', rfl⟩ := hw
    show ⟪x - x', z⟫ = 0
    rw [inner_sub_left, hz x hx, hz x' hx', sub_self]
  | zero => simp
  | add u₁ u₂ _ _ h₁ h₂ => rw [inner_add_left, h₁, h₂, add_zero]
  | smul r u _ h => rw [real_inner_smul_left, h, mul_zero]

section euler

variable (V : Finset (E d))

/-- The face of `conv V` maximizing `⟪·, c⟫`. -/
def argmaxFace (c : E d) : Set (E d) :=
  {x | x ∈ convexHull ℝ (V : Set (E d)) ∧ ∀ y ∈ convexHull ℝ (V : Set (E d)), ⟪y, c⟫ ≤ ⟪x, c⟫}

/-- The vertices of `V` maximizing `⟪·, c⟫`. -/
noncomputable def maxVerts [DecidableEq (E d)] (c : E d) : Finset (E d) :=
  V.filter fun v => ∀ u ∈ V, ⟪u, c⟫ ≤ ⟪v, c⟫

variable {V}

lemma exists_max_vertex (hV : V.Nonempty) (c : E d) :
    ∃ v ∈ V, ∀ u ∈ V, ⟪u, c⟫ ≤ ⟪v, c⟫ := by
  obtain ⟨v, hv, hmax⟩ := V.exists_max_image (fun u => ⟪u, c⟫) hV
  exact ⟨v, hv, hmax⟩

lemma argmaxFace_eq [DecidableEq (E d)] (hV : V.Nonempty) (c : E d) :
    argmaxFace V c = convexHull ℝ (maxVerts V c : Set (E d)) := by
  obtain ⟨v, hv, hmax⟩ := exists_max_vertex hV c
  have hle : ∀ u ∈ V, ip c u ≤ ⟪v, c⟫ := fun u hu => by rw [ip_apply]; exact hmax u hu
  have hfilt : maxVerts V c = V.filter fun u => ip c u = ⟪v, c⟫ := by
    ext u; simp only [maxVerts, Finset.mem_filter, ip_apply]
    constructor
    · rintro ⟨hu, hu'⟩; exact ⟨hu, le_antisymm (hmax u hu) (hu' v hv)⟩
    · rintro ⟨hu, he⟩; exact ⟨hu, fun w hw => he ▸ hmax w hw⟩
  ext x; constructor
  · rintro ⟨hx, hxmax⟩
    have hxv : ⟪x, c⟫ = ⟪v, c⟫ :=
      le_antisymm (by have := (le_on_convexHull (ip c) hle hx).1; rwa [ip_apply] at this)
        (hxmax v (subset_convexHull ℝ _ hv))
    rw [hfilt]
    exact (le_on_convexHull (ip c) hle hx).2 (by rw [ip_apply]; exact hxv)
  · intro hx
    have hsub : (maxVerts V c : Set (E d)) ⊆ V := fun u hu => (Finset.mem_filter.1 hu).1
    have hxV : x ∈ convexHull ℝ (V : Set (E d)) := convexHull_mono hsub hx
    refine ⟨hxV, fun y hy => ?_⟩
    have h1 := (le_on_convexHull (ip c) hle hy).1
    rw [ip_apply] at h1
    -- `⟪·, c⟫ ≥ ⟪v, c⟫` on the hull of the maximizing vertices
    have hge : ∀ u ∈ maxVerts V c, (-(ip c)) u ≤ -⟪v, c⟫ := fun u hu => by
      rw [hfilt, Finset.mem_filter] at hu
      simp [hu.2]
    have h2 := (le_on_convexHull (-(ip c)) hge hx).1
    simp only [ContinuousLinearMap.neg_apply, ip_apply, neg_le_neg_iff] at h2
    linarith

lemma argmaxFace_mem_faces (hV : V.Nonempty) (c : E d) :
    argmaxFace V c ∈ faces (convexHull ℝ (V : Set (E d))) := by
  obtain ⟨v, hv, hmax⟩ := exists_max_vertex hV c
  refine ⟨⟨v, subset_convexHull ℝ _ hv, fun y hy => ?_⟩, fun _ => ⟨ip c, ?_⟩⟩
  · have := (le_on_convexHull (ip c) (fun u hu => by rw [ip_apply]; exact hmax u hu) hy).1
    rwa [ip_apply] at this
  · ext x; simp [argmaxFace, ip_apply]

lemma exists_argmaxFace_eq {F : Set (E d)} (hF : F ∈ faces (convexHull ℝ (V : Set (E d)))) :
    ∃ c, argmaxFace V c = F := by
  obtain ⟨l, hl⟩ := exists_functional hF
  set c := (InnerProductSpace.toDual ℝ (E d)).symm l
  have hc : ∀ z, ⟪z, c⟫ = l z := fun z => by
    rw [real_inner_comm]; exact InnerProductSpace.toDual_symm_apply
  refine ⟨c, ?_⟩
  rw [hl]; ext x; simp [argmaxFace, hc]

/-- The open normal cone of a face. -/
def normalPart (F : Set (E d)) : Set (E d) := {c | argmaxFace V c = F}

lemma argmaxFace_value (hV : V.Nonempty) (c : E d) :
    ∃ x0 ∈ argmaxFace V c, ∀ x ∈ argmaxFace V c, ⟪x, c⟫ = ⟪x0, c⟫ := by
  obtain ⟨x0, hx0⟩ := (argmaxFace_mem_faces hV c).1
  exact ⟨x0, hx0, fun x hx => le_antisymm (hx0.2 x hx.1) (hx.2 x0 hx0.1)⟩

lemma normalPart_subset (hV : V.Nonempty) {F : Set (E d)} {c : E d}
    (hc : c ∈ normalPart (V := V) F) : c ∈ (vectorSpan ℝ F)ᗮ := by
  have hc' : argmaxFace V c = F := hc
  obtain ⟨x0, hx0, hconst⟩ := argmaxFace_value hV c
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← hc'] at hu
  exact inner_vectorSpan_eq_zero_of_const hconst u hu

lemma normalPart_convex (hV : V.Nonempty) (F : Set (E d)) :
    Convex ℝ (normalPart (V := V) F) := by
  intro c1 hc1 c2 hc2 t s ht hs hts
  have h1 : argmaxFace V c1 = F := hc1
  have h2 : argmaxFace V c2 = F := hc2
  show argmaxFace V (t • c1 + s • c2) = F
  obtain ⟨x0, hx0, -⟩ := argmaxFace_value hV c1
  have hx0' : x0 ∈ argmaxFace V c2 := by rw [h2, ← h1]; exact hx0
  ext x; constructor
  · rintro ⟨hxQ, hxmax⟩
    have hge := hxmax x0 hx0.1
    simp only [inner_add_right, real_inner_smul_right] at hge
    have a1 := hx0.2 x hxQ
    have a2 := hx0'.2 x hxQ
    rcases eq_or_lt_of_le ht with htz | htp
    · have hs1 : s = 1 := by linarith
      rw [← htz, hs1] at hge
      rw [← h2]
      exact ⟨hxQ, fun y hy => le_trans (hx0'.2 y hy) (by linarith)⟩
    · have : ⟪x, c1⟫ = ⟪x0, c1⟫ := by nlinarith
      rw [← h1]
      exact ⟨hxQ, fun y hy => le_trans (hx0.2 y hy) this.ge⟩
  · intro hx
    have hx1 : x ∈ argmaxFace V c1 := h1 ▸ hx
    have hx2 : x ∈ argmaxFace V c2 := h2 ▸ hx
    refine ⟨hx1.1, fun y hy => ?_⟩
    simp only [inner_add_right, real_inner_smul_right]
    have := hx1.2 y hy; have := hx2.2 y hy
    nlinarith

lemma normalPart_relOpen [DecidableEq (E d)] (hV : V.Nonempty) {F : Set (E d)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E d)))) :
    RelOpen (vectorSpan ℝ F)ᗮ (normalPart (V := V) F) := by
  classical
  refine ⟨fun c hc => normalPart_subset hV hc, fun c hc w hw => ?_⟩
  have hc' : argmaxFace V c = F := hc
  obtain ⟨x0, hx0, hconst⟩ := argmaxFace_value hV c
  rw [hc'] at hx0 hconst
  set M := ⟪x0, c⟫
  set κ := ⟪x0, w⟫
  have hwF : ∀ x ∈ F, ⟪x, w⟫ = κ := by
    intro x hx
    have hxU : x -ᵥ x0 ∈ vectorSpan ℝ F := vsub_mem_vectorSpan ℝ hx hx0
    have := Submodule.inner_right_of_mem_orthogonal hxU hw
    rw [vsub_eq_sub, inner_sub_left] at this; linarith
  have hx0max : ∀ y ∈ convexHull ℝ (V : Set (E d)), ⟪y, c⟫ ≤ M := by
    have := hx0; rw [← hc'] at this; exact this.2
  have hstrict : ∀ v ∈ V, v ∉ F → ⟪v, c⟫ < M := by
    intro v hv hvF
    rcases lt_or_eq_of_le (hx0max v (subset_convexHull ℝ _ hv)) with h | h
    · exact h
    · exfalso; apply hvF; rw [← hc']
      exact ⟨subset_convexHull ℝ _ hv, fun y hy => h ▸ hx0max y hy⟩
  obtain ⟨ε, hε, hεle⟩ := exists_eps_pert (V.filter fun v => v ∉ F)
    (fun v => ⟪v, c⟫ - M + 1) (fun v => ⟪v, w⟫ - κ) (fun v hv => by
      rw [Finset.mem_filter] at hv; linarith [hstrict v hv.1 hv.2])
  refine ⟨ε / 2, by positivity, ?_⟩
  set c' := c + (ε / 2) • w
  have hval : ∀ v ∈ V, ip c' v ≤ M + ε / 2 * κ := by
    intro v hv
    rw [ip_apply, inner_add_right, real_inner_smul_right]
    by_cases hvF : v ∈ F
    · rw [hconst v hvF, hwF v hvF]
    · have := hεle v (Finset.mem_filter.2 ⟨hv, hvF⟩)
      have hs := hstrict v hv hvF
      nlinarith [le_abs_self (⟪v, w⟫ - κ), abs_nonneg (⟪v, w⟫ - κ)]
  have hvalF : ∀ v ∈ V, ip c' v = M + ε / 2 * κ → v ∈ F := by
    intro v hv heq
    by_contra hvF
    rw [ip_apply, inner_add_right, real_inner_smul_right] at heq
    have := hεle v (Finset.mem_filter.2 ⟨hv, hvF⟩)
    have hs := hstrict v hv hvF
    nlinarith [le_abs_self (⟪v, w⟫ - κ), abs_nonneg (⟪v, w⟫ - κ)]
  have hx0val : ⟪x0, c'⟫ = M + ε / 2 * κ := by
    rw [inner_add_right, real_inner_smul_right]
  show argmaxFace V c' = F
  ext x; constructor
  · rintro ⟨hxQ, hxmax⟩
    have hle := (le_on_convexHull (ip c') hval hxQ).1
    rw [ip_apply] at hle
    have hxv : ip c' x = M + ε / 2 * κ := by
      rw [ip_apply]; exact le_antisymm hle (hx0val ▸ hxmax x0 (face_subset hF hx0))
    have hmem := (le_on_convexHull (ip c') hval hxQ).2 hxv
    rw [face_eq_convexHull_filter hF]
    exact convexHull_mono (fun v hv => by
      rw [Finset.mem_coe, Finset.mem_filter] at hv ⊢
      exact ⟨hv.1, hvalF v hv.1 hv.2⟩) hmem
  · intro hx
    refine ⟨face_subset hF hx, fun y hy => ?_⟩
    have := (le_on_convexHull (ip c') hval hy).1
    rw [ip_apply] at this
    have hxv : ⟪x, c'⟫ = M + ε / 2 * κ := by
      rw [inner_add_right, real_inner_smul_right, hconst x hx, hwF x hx]
    rw [hxv]; exact this

lemma sdim_orthogonal (F : Set (E d)) : sdim (vectorSpan ℝ F)ᗮ + dim F = d := by
  have := Submodule.finrank_add_finrank_orthogonal (vectorSpan ℝ F)
  rw [finrank_euclideanSpace_fin] at this
  simp only [sdim, dim]; omega

lemma neg_one_pow_mul_sub {k : ℕ} (hk : k ≤ d) : (-1 : ℤ) ^ d * (-1) ^ (d - k) = (-1) ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
    one_pow, mul_one]

open Classical in
/-- **Euler–Poincaré relation**: `Σ_{nonempty faces F} (-1)^(dim F) = 1`. -/
theorem euler_poincare (hV : V.Nonempty) :
    ∑ F ∈ (faces_finite_convexHull V).toFinset, (-1 : ℤ) ^ dim F = 1 := by
  set FS := (faces_finite_convexHull V).toFinset
  -- the arrangement of vertex differences
  set P2 := V ×ˢ V
  set e := P2.equivFin
  set m := P2.card
  set a : Fin m → E d := fun i => (e.symm i).1.1 - (e.symm i).1.2
  have hidx : ∀ v ∈ V, ∀ u ∈ V, ∃ i, a i = v - u := fun v hv u hu =>
    ⟨e ⟨(v, u), Finset.mem_product.2 ⟨hv, hu⟩⟩, by simp [a]⟩
  have hmaxv : ∀ c v, v ∈ maxVerts V c ↔ v ∈ V ∧ ∀ u ∈ V, ⟪u, c⟫ ≤ ⟪v, c⟫ := fun c v => by
    simp [maxVerts]
  -- the face of a cell is well defined
  have hsame : ∀ σ, ∀ c ∈ cell Set.univ a σ, ∀ c' ∈ cell Set.univ a σ,
      argmaxFace V c = argmaxFace V c' := by
    intro σ c hc c' hc'
    rw [argmaxFace_eq hV, argmaxFace_eq hV]
    congr 2
    ext v
    rw [hmaxv, hmaxv]
    refine and_congr_right fun hv => forall₂_congr fun u hu => ?_
    obtain ⟨i, hi⟩ := hidx v hv u hu
    have key : ∀ c ∈ cell Set.univ a σ, (⟪u, c⟫ ≤ ⟪v, c⟫ ↔ σ i ≠ -1) := by
      intro c hc
      have e := hc.2 i
      rw [hi, inner_sub_left] at e
      rw [← e, Ne, sign_eq_neg_one_iff, sub_neg, not_lt]
    exact (key c hc).trans (key c' hc').symm
  -- the span of a cell lies in the orthogonal complement of its face
  have hspan_le : ∀ σ, ∀ c₀ ∈ cell Set.univ a σ, ∀ x ∈ cellSpan ⊤ a σ,
      x ∈ (vectorSpan ℝ (argmaxFace V c₀))ᗮ := by
    intro σ c₀ hc₀ x hx
    rw [argmaxFace_eq hV c₀]
    have hvs : vectorSpan ℝ (convexHull ℝ (maxVerts V c₀ : Set (E d))) =
        vectorSpan ℝ (maxVerts V c₀ : Set (E d)) := by
      rw [← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]
    rw [hvs, Submodule.mem_orthogonal]
    obtain ⟨v0, hv0V, hv0max⟩ := exists_max_vertex hV c₀
    have hv0 : v0 ∈ maxVerts V c₀ := (hmaxv c₀ v0).2 ⟨hv0V, hv0max⟩
    refine inner_vectorSpan_eq_zero_of_const (κ := ⟪v0, x⟫) (fun v hv => ?_)
    rw [Finset.mem_coe, hmaxv] at hv
    obtain ⟨i, hi⟩ := hidx v hv.1 v0 hv0V
    have hσ : σ i = 0 := by
      have e := hc₀.2 i
      rw [hi, inner_sub_left] at e
      have : ⟪v, c₀⟫ = ⟪v0, c₀⟫ := le_antisymm (hv0max v hv.1) (hv.2 v0 hv0V)
      rw [this, sub_self, sign_zero] at e; exact e.symm
    have := hx.2 i hσ
    rw [hi, inner_sub_left] at this; linarith
  -- each cell lies in exactly one normal part
  have hper : ∀ σ : Fin m → SignType,
      (∑ F ∈ FS, if (cell (normalPart (V := V) F) a σ).Nonempty then
          (-1 : ℤ) ^ sdim (cellSpan (vectorSpan ℝ F)ᗮ a σ) else 0) =
        if (cell Set.univ a σ).Nonempty then (-1 : ℤ) ^ sdim (cellSpan ⊤ a σ) else 0 := by
    intro σ
    by_cases hne : (cell Set.univ a σ).Nonempty
    · obtain ⟨c₀, hc₀⟩ := hne
      set F₀ := argmaxFace V c₀
      have hF₀ : F₀ ∈ FS := (Set.Finite.mem_toFinset _).2 (argmaxFace_mem_faces hV c₀)
      rw [if_pos ⟨c₀, hc₀⟩, Finset.sum_eq_single F₀]
      · have hcellne : (cell (normalPart (V := V) F₀) a σ).Nonempty := ⟨c₀, rfl, hc₀.2⟩
        rw [if_pos hcellne]
        congr 2
        ext x
        simp only [mem_cellSpan, Submodule.mem_top, true_and]
        exact ⟨fun h => h.2, fun h => ⟨hspan_le σ c₀ hc₀ x ⟨Submodule.mem_top, h⟩, h⟩⟩
      · intro F _ hF
        rw [if_neg]
        rintro ⟨c, hcF, hcσ⟩
        apply hF
        have hcF' : argmaxFace V c = F := hcF
        rw [← hcF']
        exact hsame σ c ⟨Set.mem_univ _, hcσ⟩ c₀ hc₀
      · intro h; exact absurd hF₀ h
    · rw [if_neg hne]
      refine Finset.sum_eq_zero fun F _ => ?_
      rw [if_neg]
      rintro ⟨c, -, hcσ⟩
      exact hne ⟨c, Set.mem_univ _, hcσ⟩
  have hglobal := arrangement_count ⊤ Set.univ ⟨0, Set.mem_univ _⟩
    ⟨fun _ _ => Submodule.mem_top, fun _ _ _ _ => ⟨1, one_pos, Set.mem_univ _⟩⟩ convex_univ m a
  have hlocal : ∀ F ∈ FS, (∑ σ, if (cell (normalPart (V := V) F) a σ).Nonempty then
      (-1 : ℤ) ^ sdim (cellSpan (vectorSpan ℝ F)ᗮ a σ) else 0) =
        (-1 : ℤ) ^ sdim (vectorSpan ℝ F)ᗮ := by
    intro F hF
    rw [Set.Finite.mem_toFinset] at hF
    obtain ⟨c, hc⟩ := exists_argmaxFace_eq hF
    exact arrangement_count _ _ ⟨c, hc⟩ (normalPart_relOpen hV hF) (normalPart_convex hV F) m a
  have hsum : ∑ F ∈ FS, (-1 : ℤ) ^ sdim (vectorSpan ℝ F)ᗮ = (-1 : ℤ) ^ d := by
    rw [← Finset.sum_congr rfl hlocal, Finset.sum_comm,
      Finset.sum_congr rfl fun σ _ => hper σ, hglobal]
    simp [sdim, finrank_top, finrank_euclideanSpace_fin]
  calc ∑ F ∈ FS, (-1 : ℤ) ^ dim F
        = ∑ F ∈ FS, (-1 : ℤ) ^ d * (-1) ^ sdim (vectorSpan ℝ F)ᗮ := by
          refine Finset.sum_congr rfl fun F _ => ?_
          have h := sdim_orthogonal F
          rw [show sdim (vectorSpan ℝ F)ᗮ = d - dim F by omega, neg_one_pow_mul_sub (by omega)]
    _ = (-1 : ℤ) ^ d * (-1) ^ d := by rw [← Finset.mul_sum, hsum]
    _ = 1 := by rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

end euler

end Kalai5
