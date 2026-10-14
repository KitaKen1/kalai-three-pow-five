import Kalai5.Polar.Basic
import Kalai5.Faces.Counting

/-!
# Faces of the polar

For a polytope `K = conv V` with `0` in its interior and a nonempty proper face `F`, the dual face
`F♦ = {y ∈ K° | ∀ x ∈ F, ⟪x, y⟫ = 1}` is a nonempty proper face of `K°`, `F` is recovered from
`F♦`, and `dim F♦ + dim F + 1 = d`.  Applying this to `K` and to `K°` (bipolar theorem) gives, for
a centrally symmetric 5-polytope `P`, `fvec P° (4 - k) = fvec P k` and equal face numbers.
-/

namespace Kalai5

open Set Metric

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {d : ℕ}

/-- The dual face `F♦ = {y ∈ K° | ∀ x ∈ F, ⟪x, y⟫ = 1}`. -/
def dualFace (K F : Set (E d)) : Set (E d) := {y | y ∈ polarSet K ∧ ∀ x ∈ F, ⟪x, y⟫ = 1}

lemma inner_vectorSpan_eq_zero {F : Set (E d)} {z : E d} (hz : ∀ x ∈ F, ⟪x, z⟫ = 1) :
    ∀ u ∈ vectorSpan ℝ F, ⟪u, z⟫ = 0 := by
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

section dual

variable {V : Finset (E d)} {F : Set (E d)}
  (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d))))
  (hF : F ∈ faces (convexHull ℝ (V : Set (E d)))) (hne : F ≠ convexHull ℝ (V : Set (E d)))
include h0 hF hne

/-- A proper face is cut out by `⟪·, c⟫ = 1` for some `c` in the polar. -/
lemma exists_dual_vector :
    ∃ c : E d, (∀ x ∈ convexHull ℝ (V : Set (E d)), ⟪x, c⟫ ≤ 1) ∧
      (∀ x ∈ convexHull ℝ (V : Set (E d)), (x ∈ F ↔ ⟪x, c⟫ = 1)) := by
  set K := convexHull ℝ (V : Set (E d))
  obtain ⟨l, hl⟩ := exists_functional hF
  obtain ⟨f₀, hf₀⟩ := hF.1
  have hf₀K : f₀ ∈ K := face_subset hF hf₀
  set M := l f₀
  have hmax : ∀ y ∈ K, l y ≤ M := by have := hf₀; rw [hl] at this; exact this.2
  have hF_iff : ∀ y ∈ K, (y ∈ F ↔ l y = M) := by
    intro y hy; constructor
    · intro hyF; have := hyF; rw [hl] at this; exact le_antisymm (hmax y hy) (this.2 f₀ hf₀K)
    · intro hly; rw [hl]; exact ⟨hy, fun z hz => hly ▸ hmax z hz⟩
  have h0K : (0 : E d) ∈ K := interior_subset h0
  have hM : 0 < M := by
    have hle : 0 ≤ M := by have := hmax 0 h0K; simpa using this
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso; apply hne
      exact face_eq_of_mem_interior hF ((hF_iff 0 h0K).2 (by simp [← h])) h0
  set a := (InnerProductSpace.toDual ℝ (E d)).symm l
  have ha : ∀ z, ⟪a, z⟫ = l z := fun z => InnerProductSpace.toDual_symm_apply
  refine ⟨M⁻¹ • a, fun x hx => ?_, fun x hx => ?_⟩
  · rw [real_inner_smul_right, real_inner_comm, ha, inv_mul_le_iff₀ hM, mul_one]
    exact hmax x hx
  · rw [real_inner_smul_right, real_inner_comm, ha, hF_iff x hx, inv_mul_eq_one₀ hM.ne']
    exact eq_comm

lemma dualFace_nonempty : (dualFace (convexHull ℝ (V : Set (E d))) F).Nonempty := by
  obtain ⟨c, hcK, hcF⟩ := exists_dual_vector h0 hF hne
  exact ⟨c, hcK, fun x hx => (hcF x (face_subset hF hx)).1 hx⟩

omit h0 hne in
lemma dualFace_ne_polarSet :
    dualFace (convexHull ℝ (V : Set (E d))) F ≠ polarSet (convexHull ℝ (V : Set (E d))) := by
  intro h
  obtain ⟨f₀, hf₀⟩ := hF.1
  have h0mem : (0 : E d) ∈ dualFace (convexHull ℝ (V : Set (E d))) F := by
    rw [h]; exact zero_mem_polarSet _
  have := h0mem.2 f₀ hf₀
  simp at this

/-- `F` is recovered from its dual face. -/
lemma eq_of_dualFace :
    F = {x | x ∈ convexHull ℝ (V : Set (E d)) ∧
      ∀ y ∈ dualFace (convexHull ℝ (V : Set (E d))) F, ⟪x, y⟫ = 1} := by
  obtain ⟨c, hcK, hcF⟩ := exists_dual_vector h0 hF hne
  have hc : c ∈ dualFace (convexHull ℝ (V : Set (E d))) F :=
    ⟨hcK, fun x hx => (hcF x (face_subset hF hx)).1 hx⟩
  ext x; constructor
  · intro hx; exact ⟨face_subset hF hx, fun y hy => hy.2 x hx⟩
  · rintro ⟨hxK, hall⟩; exact (hcF x hxK).2 (hall c hc)

/-- **The dual face is a face of the polar.** -/
lemma dualFace_mem_faces :
    dualFace (convexHull ℝ (V : Set (E d))) F ∈ faces (polarSet (convexHull ℝ (V : Set (E d)))) := by
  classical
  set K := convexHull ℝ (V : Set (E d))
  obtain ⟨c, hcK, hcF⟩ := exists_dual_vector h0 hF hne
  have hcpol : c ∈ polarSet K := hcK
  set S0 := V.filter (· ∈ F)
  have hFS : F = convexHull ℝ (S0 : Set (E d)) := face_eq_convexHull_filter hF
  have hS0 : S0.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    obtain ⟨x, hx⟩ := hF.1
    rw [hFS, h, Finset.coe_empty, convexHull_empty] at hx
    exact hx
  set n : ℝ := (S0.card : ℝ)
  have hn : 0 < n := by simp only [n]; exact_mod_cast Finset.card_pos.2 hS0
  set p : E d := n⁻¹ • ∑ v ∈ S0, v
  have hp : ∀ y, ⟪p, y⟫ = n⁻¹ * ∑ v ∈ S0, ⟪v, y⟫ := fun y => by
    rw [real_inner_smul_left, sum_inner]
  have hS0K : ∀ v ∈ S0, v ∈ K := fun v hv => subset_convexHull ℝ _ (Finset.mem_filter.1 hv).1
  have hle : ∀ y ∈ polarSet K, ⟪p, y⟫ ≤ 1 := fun y hy => by
    rw [hp, inv_mul_le_iff₀ hn, mul_one]
    calc ∑ v ∈ S0, ⟪v, y⟫ ≤ ∑ _v ∈ S0, (1 : ℝ) := Finset.sum_le_sum fun v hv => hy v (hS0K v hv)
      _ = n := by simp [n]
  have hiff : ∀ y ∈ polarSet K, (⟪p, y⟫ = 1 ↔ ∀ x ∈ F, ⟪x, y⟫ = 1) := by
    intro y hy
    constructor
    · intro hpy
      have hnn : ∀ v ∈ S0, 0 ≤ 1 - ⟪v, y⟫ := fun v hv => sub_nonneg.2 (hy v (hS0K v hv))
      have hsum : ∑ v ∈ S0, (1 - ⟪v, y⟫) = 0 := by
        rw [Finset.sum_sub_distrib]
        rw [hp] at hpy
        have : ∑ v ∈ S0, ⟪v, y⟫ = n := by
          field_simp at hpy; linarith
        simp [this, n]
      have hv1 : ∀ v ∈ S0, ⟪v, y⟫ = 1 := fun v hv => by
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum v hv; linarith
      intro x hx
      rw [hFS] at hx
      have h1 := (le_on_convexHull (ip y) (c := 1)
        (fun v hv => by rw [ip_apply, hv1 v hv]) hx).1
      have h2 := (le_on_convexHull (-(ip y)) (c := -1)
        (fun v hv => by simp [hv1 v hv]) hx).1
      simp only [ip_apply, ContinuousLinearMap.neg_apply] at h1 h2
      linarith
    · intro hall
      rw [hp, Finset.sum_congr rfl fun v hv => hall v (Finset.mem_filter.1 hv).2]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact inv_mul_cancel₀ hn.ne'
  refine ⟨⟨c, hcpol, fun x hx => (hcF x (face_subset hF hx)).1 hx⟩, fun _ => ⟨ip p, ?_⟩⟩
  have hpc : ⟪p, c⟫ = 1 := (hiff c hcpol).2 fun x hx => (hcF x (face_subset hF hx)).1 hx
  ext y
  simp only [Set.mem_setOf_eq, ip_apply]
  constructor
  · rintro ⟨hy, hall⟩
    refine ⟨hy, fun z hz => ?_⟩
    rw [real_inner_comm p z, real_inner_comm p y, (hiff y hy).2 hall]
    exact hle z hz
  · rintro ⟨hy, hmax⟩
    refine ⟨hy, (hiff y hy).1 ?_⟩
    have h1 := hmax c hcpol
    rw [real_inner_comm p c, real_inner_comm p y, hpc] at h1
    linarith [hle y hy]

/-- **Dimension of the dual face**: `dim F♦ + dim F + 1 = d`. -/
lemma dim_dualFace : dim (dualFace (convexHull ℝ (V : Set (E d))) F) + dim F + 1 = d := by
  classical
  set K := convexHull ℝ (V : Set (E d))
  obtain ⟨f₀, hf₀⟩ := hF.1
  obtain ⟨c, hcK, hcF⟩ := exists_dual_vector h0 hF hne
  have hf₀K : f₀ ∈ K := face_subset hF hf₀
  have hcF' : ∀ x ∈ F, ⟪x, c⟫ = 1 := fun x hx => (hcF x (face_subset hF hx)).1 hx
  have hcf₀ : ⟪f₀, c⟫ = 1 := hcF' f₀ hf₀
  set U := vectorSpan ℝ F
  set S := (ℝ ∙ f₀) ⊔ U
  have hf₀U : f₀ ∉ U := fun h => by
    have := inner_vectorSpan_eq_zero hcF' f₀ h
    rw [hcf₀] at this; exact one_ne_zero this
  have hf₀0 : f₀ ≠ 0 := fun h => by
    rw [h, inner_zero_left] at hcf₀; exact zero_ne_one hcf₀
  have hinf : (ℝ ∙ f₀) ⊓ U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx.1
    by_contra ht
    have htne : t ≠ 0 := fun h' => ht (by rw [h', zero_smul])
    have := U.smul_mem t⁻¹ hx.2
    rw [smul_smul, inv_mul_cancel₀ htne, one_smul] at this
    exact hf₀U this
  have hS : Module.finrank ℝ S = Module.finrank ℝ U + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (ℝ ∙ f₀) U
    rw [hinf, finrank_bot, add_zero, finrank_span_singleton hf₀0] at h
    have h' : Module.finrank ℝ S = Module.finrank ℝ ↥((ℝ ∙ f₀) ⊔ U : Submodule ℝ (E d)) := rfl
    omega
  have hvs : vectorSpan ℝ (dualFace K F) = Sᗮ := by
    apply le_antisymm
    · rw [vectorSpan_def, Submodule.span_le]
      rintro w ⟨y, hy, y', hy', rfl⟩
      dsimp only
      rw [SetLike.mem_coe, Submodule.mem_orthogonal]
      intro u hu
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hu
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hu₁
      have e1 := inner_vectorSpan_eq_zero hy.2 u₂ hu₂
      have e2 := inner_vectorSpan_eq_zero hy'.2 u₂ hu₂
      rw [vsub_eq_sub, inner_add_left, real_inner_smul_left, inner_sub_right, inner_sub_right,
        hy.2 f₀ hf₀, hy'.2 f₀ hf₀, e1, e2]
      ring
    · intro w hw
      have hwf₀ : ⟪f₀, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal
        (Submodule.mem_sup_left (Submodule.mem_span_singleton_self f₀)) hw
      have hwF : ∀ x ∈ F, ⟪x, w⟫ = 0 := by
        intro x hx
        have hxU : x -ᵥ f₀ ∈ U := vsub_mem_vectorSpan ℝ hx hf₀
        have := Submodule.inner_right_of_mem_orthogonal (Submodule.mem_sup_right hxU) hw
        rwa [vsub_eq_sub, inner_sub_left, hwf₀, sub_zero] at this
      obtain ⟨ε, hε, hεle⟩ := exists_eps_pert (V.filter fun v => v ∉ F) (fun v => ⟪v, c⟫)
        (fun v => ⟪v, w⟫) (fun v hv => by
          rw [Finset.mem_filter] at hv
          have hvK : v ∈ K := subset_convexHull ℝ _ hv.1
          exact lt_of_le_of_ne (hcK v hvK) fun h => hv.2 ((hcF v hvK).2 h))
      have hc : c ∈ dualFace K F := ⟨hcK, hcF'⟩
      have hmem : c + ε • w ∈ dualFace K F := by
        refine ⟨mem_polarSet_convexHull.2 fun v hv => ?_, fun x hx => ?_⟩
        · rw [inner_add_right, real_inner_smul_right]
          by_cases hvF : v ∈ F
          · rw [hwF v hvF, hcF' v hvF]; simp
          · have := hεle v (Finset.mem_filter.2 ⟨hv, hvF⟩)
            have hb : ε * ⟪v, w⟫ ≤ ε * |⟪v, w⟫| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
            linarith
        · rw [inner_add_right, real_inner_smul_right, hwF x hx, hcF' x hx]; simp
      have h1 : (c + ε • w) -ᵥ c ∈ vectorSpan ℝ (dualFace K F) := vsub_mem_vectorSpan ℝ hmem hc
      rw [vsub_eq_sub, add_sub_cancel_left] at h1
      have := (vectorSpan ℝ (dualFace K F)).smul_mem ε⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hε.ne', one_smul] at this
  have hfin := Submodule.finrank_add_finrank_orthogonal S
  rw [finrank_euclideanSpace_fin] at hfin
  have e1 : dim (dualFace K F) = Module.finrank ℝ Sᗮ := by unfold dim; rw [hvs]
  have e2 : dim F = Module.finrank ℝ U := rfl
  omega

end dual

/-- `F ↦ F♦` injects the `k`-faces of a polytope with `0` inside into the `(d-1-k)`-faces of its
polar. -/
lemma fvec_le_fvec_polarSet {V : Finset (E d)}
    (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d)))) (k : ℕ) (hk : k + 1 ≤ d) :
    fvec (convexHull ℝ (V : Set (E d))) k ≤
      fvec (polarSet (convexHull ℝ (V : Set (E d)))) (d - 1 - k) := by
  set K := convexHull ℝ (V : Set (E d))
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have hpoly : IsPolytope (polarSet K) := ⟨⟨W, hW⟩, ⟨0, zero_mem_interior_polarSet V⟩⟩
  have hdimK : dim K = d := dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0⟩
  have hne : ∀ F, F ∈ faces K → dim F = k → F ≠ K := fun F _ hd h => by
    rw [← h, hd] at hdimK; omega
  refine Set.ncard_le_ncard_of_injOn (dualFace K) ?_ ?_
    ((faces_finite hpoly).subset fun G hG => hG.1)
  · rintro F ⟨hF, hd⟩
    refine ⟨dualFace_mem_faces h0 hF (hne F hF hd), ?_⟩
    have h1 := dim_dualFace h0 hF (hne F hF hd)
    change dim (dualFace K F) + dim F + 1 = d at h1
    show dim (dualFace K F) = d - 1 - k
    omega
  · rintro F ⟨hF, hd⟩ G ⟨hG, hdG⟩ hFG
    rw [eq_of_dualFace h0 hF (hne F hF hd), eq_of_dualFace h0 hG (hne G hG hdG), hFG]

/-! ### Centrally symmetric 5-polytopes -/

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.polar : IsCSPolytope5 (polarSet P) := by
  obtain ⟨V, hV⟩ := hP.polytope
  have h0 : (0 : E5) ∈ interior (convexHull ℝ (V : Set E5)) := hV ▸ hP.zero_mem_interior
  refine ⟨⟨?_, ?_⟩, fun y hy => neg_mem_polarSet hP.symm hy⟩
  · rw [hV]; exact exists_polarSet_eq_convexHull h0
  · rw [hV]; exact ⟨0, zero_mem_interior_polarSet V⟩

lemma IsCSPolytope5.polarSet_polarSet : polarSet (polarSet P) = P := by
  obtain ⟨V, hV⟩ := hP.polytope
  refine Kalai5.polarSet_polarSet hP.convex ?_ (interior_subset hP.zero_mem_interior)
  rw [hV]; exact Set.Finite.isClosed_convexHull ℝ V.finite_toSet

lemma IsCSPolytope5.fvec_le_fvec_polar (k : ℕ) (hk : k ≤ 4) :
    fvec P k ≤ fvec (polarSet P) (4 - k) := by
  obtain ⟨V, hV⟩ := hP.polytope
  have h0 : (0 : E5) ∈ interior (convexHull ℝ (V : Set E5)) := hV ▸ hP.zero_mem_interior
  have := fvec_le_fvec_polarSet h0 k (by omega)
  rw [← hV] at this
  simpa using this

/-- **Polarity reverses the face numbers**: `f_{4-k}(P°) = f_k(P)`. -/
theorem IsCSPolytope5.fvec_polar (k : ℕ) (hk : k ≤ 4) : fvec (polarSet P) (4 - k) = fvec P k := by
  have h1 := hP.fvec_le_fvec_polar k hk
  have h2 := hP.polar.fvec_le_fvec_polar (4 - k) (by omega)
  rw [hP.polarSet_polarSet, show 4 - (4 - k) = k by omega] at h2
  omega

theorem IsCSPolytope5.faces_ncard_polar : (faces (polarSet P)).ncard = (faces P).ncard := by
  rw [hP.polar.faces_ncard, hP.faces_ncard]
  have e0 := hP.fvec_polar 0 (by norm_num)
  have e1 := hP.fvec_polar 1 (by norm_num)
  have e2 := hP.fvec_polar 2 (by norm_num)
  have e3 := hP.fvec_polar 3 (by norm_num)
  have e4 := hP.fvec_polar 4 (by norm_num)
  simp only [Nat.sub_zero, Nat.sub_self] at e0 e4
  norm_num at e1 e2 e3
  omega

/-- **Polarity** (obligation `polar`). -/
theorem IsCSPolytope5.polar_exists : ∃ Q, IsCSPolytope5 Q ∧
    (faces Q).ncard = (faces P).ncard ∧ fvec Q 0 = fvec P 4 ∧ fvec Q 4 = fvec P 0 :=
  ⟨polarSet P, hP.polar, hP.faces_ncard_polar,
    by simpa using hP.fvec_polar 4 le_rfl, by simpa using hP.fvec_polar 0 (by norm_num)⟩

end Kalai5
