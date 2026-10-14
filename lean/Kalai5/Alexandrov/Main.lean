import Kalai5.Alexandrov.FaceMain
import Kalai5.Alexandrov.Inactive
import Kalai5.Rigidity.Joints

/-!
# Alexandrov's theorem in dimension three

**`alexandrov3_proof : WProp 3`**: for a `3`-polytope (in any `E m`), every infinitesimal motion
keeping the distances between vertices of a common `2`-face keeps all distances between vertices.

A face-by-face version of Pak's proof of Dehn's theorem (I. Pak, *A short proof of rigidity of
convex polytopes*, 2006).  After subtracting a trivial motion, three vertices of a `2`-face are
*dead* (velocity orthogonal to the polytope's directions).  Orient each edge `vw` by the sign of
`⟪w - v, a v⟫ = ⟪w - v, a w⟫` and weigh the corners `(v, G)`:
`C = 2·posC·negC + zerC` (opposite edges count `2`, a zero edge `1`).

* vertex side (`vertex_side`, the cut lemma on the vertex figure): `Σ_{G ∋ v} C ≤ 4` at a live
  vertex, `= 2 #{G ∋ v}` at a dead one;
* face side (`face_side`): `Σ_{v ∈ G} C ≥ 2 k_G - 4 + 2 min(#dead, 2)`;
* Euler (`sum_facePts_sub_two`) and the inactive bound (`inactive_bound`) make the two sides
  incompatible as soon as one vertex is alive.
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

/-! ### The vertex side -/

open Classical in
/-- Counts at `v` inside a face through `v` are counts on the slice polygon. -/
lemma VSlice.card_filter_nbrs {V : Finset (E n)} {v : E n} (σ : VSlice V v) (hcp : ConvPos V)
    {G : Set (E n)} (hG : G ∈ faces (convexHull ℝ (V : Set (E n)))) (hvG : v ∈ G) (d : E n)
    (P : ℝ → Prop) [DecidablePred P] (hP : ∀ t τ : ℝ, 0 < τ → (P (τ * t) ↔ P t)) :
    ((nbrs (facePts V G) v).filter fun w => P ⟪w - v, d⟫).card =
      (σ.sW.filter fun x => x ∈ G ∩ σ.H ∧ P ⟪x - v, d⟫).card := by
  classical
  have hvV : v ∈ V := σ.ha₀
  refine Finset.card_bij (fun w _ => σ.e w) ?_ ?_ ?_
  · intro w hw
    obtain ⟨hwn, hwP⟩ := Finset.mem_filter.1 hw
    obtain ⟨hwnV, hwG⟩ := (mem_nbrs_facePts hcp hG hvV hvG).1 hwn
    obtain ⟨hwV, hwv, -⟩ := mem_nbrs.1 hwnV
    refine Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hwnV,
      ⟨(σ.e_mem_iff hG hvG hwV hwv).2 hwG, σ.e_mem_H hwV hwv⟩, ?_⟩
    rw [σ.e_sub, real_inner_smul_left, hP _ _ (σ.τ_pos hwV hwv)]
    exact hwP
  · intro w hw w' hw' h
    obtain ⟨hwV, hwv, -⟩ :=
      mem_nbrs.1 ((mem_nbrs_facePts hcp hG hvV hvG).1 (Finset.mem_filter.1 hw).1).1
    obtain ⟨hwV', hwv', -⟩ :=
      mem_nbrs.1 ((mem_nbrs_facePts hcp hG hvV hvG).1 (Finset.mem_filter.1 hw').1).1
    exact σ.e_injOn hcp hwV hwv hwV' hwv' h
  · intro x hx
    obtain ⟨hxW, ⟨hxG, -⟩, hxP⟩ := Finset.mem_filter.1 hx
    obtain ⟨w, hwn, rfl⟩ := Finset.mem_image.1 hxW
    obtain ⟨hwV, hwv, -⟩ := mem_nbrs.1 hwn
    have hwG := (σ.e_mem_iff hG hvG hwV hwv).1 hxG
    refine ⟨w, Finset.mem_filter.2 ⟨(mem_nbrs_facePts hcp hG hvV hvG).2 ⟨hwn, hwG⟩, ?_⟩, rfl⟩
    rw [σ.e_sub, real_inner_smul_left, hP _ _ (σ.τ_pos hwV hwv)] at hxP
    exact hxP

open Classical in
/-- **The vertex side**: at a live vertex the corner weights add up to at most `4`. -/
theorem vertex_side {V : Finset (E n)} (hcp : ConvPos V)
    (h3 : dim (convexHull ℝ (V : Set (E n))) = 3) (a : E n → E n) {v : E n} (hv : v ∈ V)
    (hlive : ∃ w ∈ V, ⟪w - v, a v⟫ ≠ 0) :
    ∑ G ∈ (twoFinset V).filter (fun G => v ∈ G),
      (2 * (posC (facePts V G) (fun v w => ⟪w - v, a v⟫) v *
        negC (facePts V G) (fun v w => ⟪w - v, a v⟫) v) +
        zerC (facePts V G) (fun v w => ⟪w - v, a v⟫) v) ≤ 4 := by
  obtain ⟨σ⟩ := exists_vslice (hcp v hv)
  have hterm : ∀ G ∈ (twoFinset V).filter (fun G => v ∈ G),
      2 * (posC (facePts V G) (fun v w => ⟪w - v, a v⟫) v *
        negC (facePts V G) (fun v w => ⟪w - v, a v⟫) v) +
        zerC (facePts V G) (fun v w => ⟪w - v, a v⟫) v =
      2 * ((σ.sW.filter fun x => x ∈ G ∩ σ.H ∧ ⟪v, a v⟫ < ⟪x, a v⟫).card *
        (σ.sW.filter fun x => x ∈ G ∩ σ.H ∧ ⟪x, a v⟫ < ⟪v, a v⟫).card) +
        (σ.sW.filter fun x => x ∈ G ∩ σ.H ∧ ⟪x, a v⟫ = ⟪v, a v⟫).card := by
    intro G hG
    obtain ⟨hGt, hvG⟩ := Finset.mem_filter.1 hG
    have hGf := (mem_twoFinset.1 hGt).1
    have e1 : posC (facePts V G) (fun v w => ⟪w - v, a v⟫) v =
        (σ.sW.filter fun x => x ∈ G ∩ σ.H ∧ ⟪v, a v⟫ < ⟪x, a v⟫).card := by
      have key := σ.card_filter_nbrs hcp hGf hvG (a v) (fun t : ℝ => 0 < t)
        (fun t τ hτ => ⟨fun h => pos_of_mul_pos_right h hτ.le, fun h => mul_pos hτ h⟩)
      refine key.trans ?_
      congr 1
      refine Finset.filter_congr fun x _ => ?_
      simp only [inner_sub_left, sub_pos]
    have e2 : negC (facePts V G) (fun v w => ⟪w - v, a v⟫) v =
        (σ.sW.filter fun x => x ∈ G ∩ σ.H ∧ ⟪x, a v⟫ < ⟪v, a v⟫).card := by
      have key := σ.card_filter_nbrs hcp hGf hvG (a v) (fun t : ℝ => t < 0)
        (fun t τ hτ => ⟨fun h => neg_of_mul_neg_right h hτ.le,
          fun h => mul_neg_of_pos_of_neg hτ h⟩)
      refine key.trans ?_
      congr 1
      refine Finset.filter_congr fun x _ => ?_
      simp only [inner_sub_left, sub_neg]
    have e3 : zerC (facePts V G) (fun v w => ⟪w - v, a v⟫) v =
        (σ.sW.filter fun x => x ∈ G ∩ σ.H ∧ ⟪x, a v⟫ = ⟪v, a v⟫).card := by
      have key := σ.card_filter_nbrs hcp hGf hvG (a v) (fun t : ℝ => t = 0)
        (fun t τ hτ => ⟨fun h => (mul_eq_zero.1 h).resolve_left hτ.ne',
          fun h => by rw [h, mul_zero]⟩)
      refine key.trans ?_
      congr 1
      refine Finset.filter_congr fun x _ => ?_
      simp only [inner_sub_left, sub_eq_zero]
    rw [e1, e2, e3]
  -- a slice vertex with a nonzero value
  have hne : ∃ z ∈ σ.sW, ⟪z, a v⟫ ≠ ⟪v, a v⟫ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨w₀, hw₀, hw₀ne⟩ := hlive
    have hall : ∀ y ∈ nbrs V v, ⟪y - v, a v⟫ = 0 := by
      intro y hy
      obtain ⟨hyV, hyv, -⟩ := mem_nbrs.1 hy
      have := hcon (σ.e y) (Finset.mem_image_of_mem _ hy)
      have h' : ⟪σ.e y - v, a v⟫ = 0 := by rw [inner_sub_left, this, sub_self]
      rw [σ.e_sub, real_inner_smul_left] at h'
      exact (mul_eq_zero.1 h').resolve_left (σ.τ_pos hyV hyv).ne'
    apply hw₀ne
    obtain ⟨μ, -, hsum⟩ := nbrs_cone hcp hv hw₀
    rw [hsum, inner_sum_smul]
    exact Finset.sum_eq_zero fun y hy => by rw [hall y hy, mul_zero]
  calc ∑ G ∈ (twoFinset V).filter (fun G => v ∈ G),
        (2 * (posC (facePts V G) (fun v w => ⟪w - v, a v⟫) v *
          negC (facePts V G) (fun v w => ⟪w - v, a v⟫) v) +
          zerC (facePts V G) (fun v w => ⟪w - v, a v⟫) v)
      = ∑ G ∈ (twoFinset V).filter (fun G => v ∈ G),
          (2 * ((σ.sW.filter fun x => x ∈ G ∩ σ.H ∧ ⟪v, a v⟫ < ⟪x, a v⟫).card *
            (σ.sW.filter fun x => x ∈ G ∩ σ.H ∧ ⟪x, a v⟫ < ⟪v, a v⟫).card) +
            (σ.sW.filter fun x => x ∈ G ∩ σ.H ∧ ⟪x, a v⟫ = ⟪v, a v⟫).card) :=
        Finset.sum_congr rfl hterm
    _ = ∑ Φ ∈ edgeFinset σ.sW,
          (2 * ((σ.sW.filter fun x => x ∈ Φ ∧ ⟪v, a v⟫ < ⟪x, a v⟫).card *
            (σ.sW.filter fun x => x ∈ Φ ∧ ⟪x, a v⟫ < ⟪v, a v⟫).card) +
            (σ.sW.filter fun x => x ∈ Φ ∧ ⟪x, a v⟫ = ⟪v, a v⟫).card) :=
        by convert σ.sum_twoFaces hcp h3 (fun Φ =>
          2 * ((σ.sW.filter fun x => x ∈ Φ ∧ ⟪v, a v⟫ < ⟪x, a v⟫).card *
            (σ.sW.filter fun x => x ∈ Φ ∧ ⟪x, a v⟫ < ⟪v, a v⟫).card) +
            (σ.sW.filter fun x => x ∈ Φ ∧ ⟪x, a v⟫ = ⟪v, a v⟫).card)
    _ ≤ 4 := cut_lemma (σ.convPos_sW hcp) (σ.dim_sW hcp h3) (a v) ⟪v, a v⟫ hne

/-! ### Normalisation -/

open Classical in
/-- **Three dead vertices**: a trivial motion agreeing with a motion of `bars2` at three vertices of
a `2`-face (up to velocities orthogonal to the polytope). -/
theorem exists_normalization {V : Finset (E n)} (hcp : ConvPos V)
    (h3 : dim (convexHull ℝ (V : Set (E n))) = 3) {u : E n → E n}
    (hmot : ∀ G ∈ twoFinset V, ∀ p ∈ facePts V G, ∀ q ∈ facePts V G, ⟪u p - u q, p - q⟫ = 0) :
    ∃ (A : E n →ₗ[ℝ] E n) (c : E n),
      (∀ x ∈ vectorSpan ℝ (V : Set (E n)), ∀ y ∈ vectorSpan ℝ (V : Set (E n)),
        ⟪A x, y⟫ = -⟪x, A y⟫) ∧
      3 ≤ (V.filter fun v => ∀ w ∈ V, ⟪w - v, u v - (A v + c)⟫ = 0).card := by
  classical
  set R := convexHull ℝ (V : Set (E n)) with hR
  set W := vectorSpan ℝ (V : Set (E n)) with hW
  have hvs : vectorSpan ℝ R = W := by
    rw [hR, hW, ← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]
  have hW3 : finrank ℝ W = 3 := by rw [← hvs]; exact h3
  -- a vertex and a `2`-face through it
  obtain ⟨v₀, hv₀⟩ : V.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [hR, Finset.coe_empty, convexHull_empty] at h3
    unfold dim at h3
    rw [vectorSpan_empty, finrank_bot] at h3
    omega
  obtain ⟨G₀, hG₀⟩ : ((twoFinset V).filter fun G => v₀ ∈ G).Nonempty := by
    rw [← Finset.card_pos, card_twoFaces_at hcp h3 hv₀]
    obtain ⟨σ⟩ := exists_vslice (hcp v₀ hv₀)
    rw [← σ.card_sW hcp]
    have := three_le_card_polygon (σ.convPos_sW hcp) (σ.dim_sW hcp h3)
    omega
  have hG₀t := (Finset.mem_filter.1 hG₀).1
  obtain ⟨hG₀f, hG₀2⟩ := mem_twoFinset.1 hG₀t
  obtain ⟨p₀, hp₀, q₀, hq₀, r₀, hr₀, hpq, hpr, hqr⟩ :=
    (Finset.two_lt_card (s := facePts V G₀)).1 (by have := three_le_card_facePts hcp hG₀t; omega)
  obtain ⟨hp₀V, hp₀G⟩ := mem_facePts.1 hp₀
  obtain ⟨hq₀V, hq₀G⟩ := mem_facePts.1 hq₀
  obtain ⟨hr₀V, hr₀G⟩ := mem_facePts.1 hr₀
  -- a vertex off the face
  obtain ⟨s, hsV, hsG⟩ : ∃ s ∈ V, s ∉ G₀ := by
    by_contra hcon
    push_neg at hcon
    have hsub : R ⊆ G₀ := convexHull_min (fun y hy => hcon y (by exact_mod_cast hy))
      (face_convex (convex_convexHull ℝ _) hG₀f)
    have := Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
    have h2' : finrank ℝ (vectorSpan ℝ G₀) = 2 := hG₀2
    have h3' : finrank ℝ (vectorSpan ℝ R) = 3 := h3
    omega
  -- the three directions span the space
  set U₂ := Submodule.span ℝ {q₀ - p₀, r₀ - p₀} with hU₂
  set U₃ := Submodule.span ℝ {q₀ - p₀, r₀ - p₀, s - p₀} with hU₃
  have hli := linIndep_of_three (hcp p₀ hp₀V) (hcp q₀ hq₀V) (hcp r₀ hr₀V) hpq hpr hqr
  have hU₂2 : finrank ℝ U₂ = 2 := finrank_span_pair hli
  have hsU₂ : s - p₀ ∉ U₂ := by
    intro h
    have hle : U₂ ≤ vectorSpan ℝ G₀ := by
      rw [hU₂, Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact vsub_mem_vectorSpan ℝ hq₀G hp₀G
      · exact vsub_mem_vectorSpan ℝ hr₀G hp₀G
    exact hsG (mem_face_of_vsub_mem hG₀f hp₀G (subset_convexHull ℝ _ (by exact_mod_cast hsV))
      (hle h))
  have hU₂U₃ : U₂ < U₃ := by
    refine lt_of_le_of_ne (Submodule.span_mono (by intro y hy; rcases hy with rfl | rfl <;> simp))
      fun h => hsU₂ ?_
    rw [h]; exact Submodule.subset_span (by simp)
  have hU₃W : U₃ ≤ W := by
    rw [hU₃, Submodule.span_le]
    rintro _ (rfl | rfl | rfl)
    · exact vsub_mem_vectorSpan ℝ (by exact_mod_cast hq₀V) (by exact_mod_cast hp₀V)
    · exact vsub_mem_vectorSpan ℝ (by exact_mod_cast hr₀V) (by exact_mod_cast hp₀V)
    · exact vsub_mem_vectorSpan ℝ (by exact_mod_cast hsV) (by exact_mod_cast hp₀V)
  have hU₃eq : U₃ = W := by
    refine Submodule.eq_of_le_of_finrank_le hU₃W ?_
    have := Submodule.finrank_lt_finrank_of_lt hU₂U₃
    omega
  -- solve for the velocity of a virtual point at `s`
  set dir : Fin 3 → E n := ![s - p₀, s - q₀, s - r₀] with hdir
  set M : ↥W →ₗ[ℝ] (Fin 3 → ℝ) := LinearMap.pi fun i =>
    ((innerSL ℝ (dir i) : E n →L[ℝ] ℝ) : E n →ₗ[ℝ] ℝ).comp W.subtype with hM
  have hMapp : ∀ X : ↥W, ∀ i, M X i = ⟪dir i, (X : E n)⟫ := fun X i => by
    simp [hM, innerSL_apply_apply]
  have hinj : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have h0 : ∀ i, ⟪dir i, (X : E n)⟫ = 0 := fun i => by rw [← hMapp, hX]; rfl
    have h0' : ⟪s - p₀, (X : E n)⟫ = 0 := h0 0
    have h1' : ⟪s - q₀, (X : E n)⟫ = 0 := h0 1
    have h2' : ⟪s - r₀, (X : E n)⟫ = 0 := h0 2
    have hker : U₃ ≤ LinearMap.ker ((innerSL ℝ (X : E n) : E n →L[ℝ] ℝ) : E n →ₗ[ℝ] ℝ) := by
      rw [hU₃, Submodule.span_le]
      rintro _ (rfl | rfl | rfl) <;>
        simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
          innerSL_apply_apply]
      · rw [show q₀ - p₀ = (s - p₀) - (s - q₀) by abel, inner_sub_right,
          real_inner_comm (s - p₀) (X : E n), real_inner_comm (s - q₀) (X : E n), h0', h1', sub_self]
      · rw [show r₀ - p₀ = (s - p₀) - (s - r₀) by abel, inner_sub_right,
          real_inner_comm (s - p₀) (X : E n), real_inner_comm (s - r₀) (X : E n), h0', h2', sub_self]
      · rw [real_inner_comm (s - p₀) (X : E n), h0']
    have hXmem : (X : E n) ∈ U₃ := by rw [hU₃eq]; exact X.2
    have := hker hXmem
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply,
      inner_self_eq_zero] at this
    exact Subtype.ext this
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [hW3, Module.finrank_fin_fun])).1 hinj
  obtain ⟨X, hX⟩ := hsurj ![⟪s - p₀, u p₀⟫, ⟪s - q₀, u q₀⟫, ⟪s - r₀, u r₀⟫]
  have hXp : ∀ i, ⟪dir i, (X : E n)⟫ = ![⟪s - p₀, u p₀⟫, ⟪s - q₀, u q₀⟫, ⟪s - r₀, u r₀⟫] i :=
    fun i => by rw [← hMapp, hX]
  -- the virtual motion on `{p₀, q₀, r₀, s}`
  set u' := Function.update u s (X : E n) with hu'
  have hps : ∀ {p}, p ∈ G₀ → p ≠ s := fun hp h => hsG (h ▸ hp)
  have hu'p : ∀ {p}, p ∈ G₀ → u' p = u p := fun hp => Function.update_of_ne (hps hp) _ _
  have hu's : u' s = X := Function.update_self _ _ _
  have hbar_s : ∀ {p : E n}, p ∈ G₀ → ⟪(X : E n) - u p, s - p⟫ = 0 →
      ⟪u' s - u' p, s - p⟫ = 0 := fun hp h => by rw [hu's, hu'p hp]; exact h
  have hsp₀ : ⟪(X : E n) - u p₀, s - p₀⟫ = 0 := by
    have h : ⟪s - p₀, (X : E n)⟫ = ⟪s - p₀, u p₀⟫ := hXp 0
    rw [inner_sub_left, real_inner_comm, h, real_inner_comm, sub_self]
  have hsq₀ : ⟪(X : E n) - u q₀, s - q₀⟫ = 0 := by
    have h : ⟪s - q₀, (X : E n)⟫ = ⟪s - q₀, u q₀⟫ := hXp 1
    rw [inner_sub_left, real_inner_comm, h, real_inner_comm, sub_self]
  have hsr₀ : ⟪(X : E n) - u r₀, s - r₀⟫ = 0 := by
    have h : ⟪s - r₀, (X : E n)⟫ = ⟪s - r₀, u r₀⟫ := hXp 2
    rw [inner_sub_left, real_inner_comm, h, real_inner_comm, sub_self]
  set S₀ : Set (E n) := {p₀, q₀, r₀} with hS₀
  set S : Set (E n) := insert s S₀ with hS
  have hS₀face : ∀ {p}, p ∈ S₀ → p ∈ facePts V G₀ := by
    intro p hp
    rcases hp with rfl | rfl | rfl
    · exact hp₀
    · exact hq₀
    · exact hr₀
  have hpairs : ∀ p ∈ S, ∀ q ∈ S, ⟪u' p - u' q, p - q⟫ = 0 := by
    have hface : ∀ {p q}, p ∈ S₀ → q ∈ S₀ → ⟪u' p - u' q, p - q⟫ = 0 := by
      intro p q hp hq
      rw [hu'p (mem_facePts.1 (hS₀face hp)).2, hu'p (mem_facePts.1 (hS₀face hq)).2]
      exact hmot G₀ hG₀t _ (hS₀face hp) _ (hS₀face hq)
    have hsS : ∀ {p}, p ∈ S₀ → ⟪u' s - u' p, s - p⟫ = 0 := by
      intro p hp
      rcases hp with rfl | rfl | rfl
      · exact hbar_s hp₀G hsp₀
      · exact hbar_s hq₀G hsq₀
      · exact hbar_s hr₀G hsr₀
    have hsym : ∀ {p q : E n}, ⟪u' p - u' q, p - q⟫ = 0 → ⟪u' q - u' p, q - p⟫ = 0 := by
      intro p q h
      rw [show u' q - u' p = -(u' p - u' q) by abel, show q - p = -(p - q) by abel,
        inner_neg_neg, h]
    intro p hp q hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · rw [sub_self, sub_self, inner_zero_left]
    · exact hsS hq
    · exact hsym (hsS hp)
    · exact hface hp hq
  obtain ⟨A, c, hA, hAc⟩ := trivialOn_of_pairs (S := S) ⟨s, Set.mem_insert _ _⟩ hpairs
  have hSV : S ⊆ (V : Set (E n)) := by
    intro y hy
    rcases hy with rfl | hy
    · exact_mod_cast hsV
    · exact_mod_cast (mem_facePts.1 (hS₀face hy)).1
  have hp₀S : p₀ ∈ S := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hq₀S : q₀ ∈ S := Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hr₀S : r₀ ∈ S := Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hsS' : s ∈ S := Set.mem_insert _ _
  have hvsS : vectorSpan ℝ S = W := by
    refine le_antisymm (vectorSpan_mono ℝ hSV) ?_
    rw [← hU₃eq, hU₃, Submodule.span_le]
    rintro _ (rfl | rfl | rfl)
    · exact vsub_mem_vectorSpan ℝ hq₀S hp₀S
    · exact vsub_mem_vectorSpan ℝ hr₀S hp₀S
    · exact vsub_mem_vectorSpan ℝ hsS' hp₀S
  refine ⟨A, c, fun x hx y hy => hA x (hvsS ▸ hx) y (hvsS ▸ hy), ?_⟩
  -- the three dead vertices
  have hdead : ∀ p ∈ S₀, ∀ w ∈ V, ⟪w - p, u p - (A p + c)⟫ = 0 := by
    intro p hp w hw
    have hpS : p ∈ S := Set.mem_insert_of_mem _ hp
    have hpf := mem_facePts.1 (hS₀face hp)
    have hwp : w - p ∈ vectorSpan ℝ S := by
      rw [hvsS]; exact vsub_mem_vectorSpan ℝ (by exact_mod_cast hw) (by exact_mod_cast hpf.1)
    have := hAc p hpS (w - p) hwp
    rw [hu'p hpf.2] at this
    rw [real_inner_comm]; exact this
  calc 3 = ({p₀, q₀, r₀} : Finset (E n)).card := by
        rw [Finset.card_insert_of_notMem (by simp [hpq, hpr]),
          Finset.card_insert_of_notMem (by simp [hqr]), Finset.card_singleton]
    _ ≤ _ := by
        refine Finset.card_le_card fun p hp => ?_
        have hpS₀ : p ∈ S₀ := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
          · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        exact Finset.mem_filter.2 ⟨(mem_facePts.1 (hS₀face hpS₀)).1, hdead p hpS₀⟩

end Kalai5
