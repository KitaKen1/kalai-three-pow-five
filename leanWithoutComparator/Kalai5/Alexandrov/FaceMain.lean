import Kalai5.Alexandrov.FaceRot
import Kalai5.Rigidity.Braces

/-!
# The face lemma

* `rot_count_of_not_mem`: the rotation centre outside the polygon — central projection from the
  centre onto a line.
* `face_count`: **for an infinitesimal motion of a polygon (all pairs of vertices kept) which moves
  some edge, `2 #same + Σ zerC ≤ 4`.**
* `face_side`: the form used in the global count:
  `2 #T + 2 min(#dead, 2) ≤ Σ_v (2 posC negC + zerC) + 4`.
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

section rot

variable {T : Finset (E n)} (hcp : ConvPos T) (h2 : dim (convexHull ℝ (T : Set (E n))) = 2)
  {A : E n →ₗ[ℝ] E n} {z : E n}
  (hskew : ∀ x ∈ vectorSpan ℝ (T : Set (E n)), ∀ y ∈ vectorSpan ℝ (T : Set (E n)),
    ⟪A x, y⟫ = -⟪x, A y⟫)
  (hz : ∀ p ∈ T, p - z ∈ vectorSpan ℝ (T : Set (E n)))
  (hnd : ∀ x ∈ vectorSpan ℝ (T : Set (E n)), x ≠ 0 →
    ∃ y ∈ vectorSpan ℝ (T : Set (E n)), ⟪A x, y⟫ ≠ 0)

include hcp h2 hskew hz hnd in
/-- **The rotation centre outside the polygon.** -/
theorem rot_count_of_not_mem (hzT : z ∉ convexHull ℝ (T : Set (E n))) :
    2 * (sameC T fun v w => ⟪w - v, A (v - z)⟫).card +
      ∑ v ∈ T, zerC T (fun v w => ⟪w - v, A (v - z)⟫) v ≤ 4 := by
  classical
  set σ : E n → E n → ℝ := fun v w => ⟪w - v, A (v - z)⟫ with hσ
  have hzV : z ∉ T := fun h => hzT (subset_convexHull ℝ _ (by exact_mod_cast h))
  have hvz : ∀ v ∈ T, v ≠ z := fun v hv h => hzV (h ▸ hv)
  -- a separating functional
  obtain ⟨f, u, hfz, hfT⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
    (Set.Finite.isClosed_convexHull ℝ T.finite_toSet) hzT
  have hlam : ∀ p ∈ T, 0 < f p - f z := fun p hp => by
    have := hfT p (subset_convexHull ℝ _ (by exact_mod_cast hp)); linarith
  set π : E n → E n := fun p => (f p - f z)⁻¹ • (p - z) with hπ
  have hπf : ∀ p ∈ T, f (π p) = 1 := by
    intro p hp
    simp only [hπ, map_smul, map_sub, smul_eq_mul]
    exact inv_mul_cancel₀ (hlam p hp).ne'
  have hπinner : ∀ p ∈ T, ∀ D : E n, ⟪π p, D⟫ = (f p - f z)⁻¹ * ⟪p - z, D⟫ := fun p _ D => by
    simp only [hπ, real_inner_smul_left]
  -- the line
  set U := vectorSpan ℝ (T : Set (E n)) ⊓ LinearMap.ker (f : E n →ₗ[ℝ] ℝ) with hU
  have hUdim : finrank ℝ U ≤ 1 := by
    obtain ⟨p₀, hp₀⟩ : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      rw [Finset.coe_empty, convexHull_empty] at h2
      unfold dim at h2
      rw [vectorSpan_empty, finrank_bot] at h2
      omega
    have hvs : vectorSpan ℝ (convexHull ℝ (T : Set (E n))) = vectorSpan ℝ (T : Set (E n)) := by
      rw [← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]
    have h2' : finrank ℝ (vectorSpan ℝ (T : Set (E n))) = 2 := by rw [← hvs]; exact h2
    have hlt : U < vectorSpan ℝ (T : Set (E n)) := by
      refine lt_of_le_of_ne inf_le_left fun h => ?_
      have hmem : p₀ - z ∈ U := by rw [h]; exact hz p₀ hp₀
      have := (Submodule.mem_inf.1 hmem).2
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub] at this
      linarith [hlam p₀ hp₀]
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hπU : ∀ p ∈ T, ∀ q ∈ T, π q - π p ∈ U := by
    intro p hp q hq
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (hz q hq))
        (Submodule.smul_mem _ _ (hz p hp))
    · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hπf q hq, hπf p hp, sub_self]
  -- same corners: strict positivity of a signed form on the projections
  have hsame_pos : ∀ v ∈ sameC T σ, ∃ D : E n, ⟪π v, D⟫ = 0 ∧
      ∀ p ∈ T, p ≠ v → 0 < ⟪π p, D⟫ := by
    intro v hv
    have hvT := (mem_sameC.1 hv).1
    obtain ⟨D, hD, hpos⟩ := rot_same_pos hcp h2 hz hnd hv
    have hzD : ⟪z - v, D⟫ = 0 := by
      rcases hD with rfl | rfl
      · exact rot_self hskew hz hvT
      · rw [inner_neg_right, rot_self hskew hz hvT, neg_zero]
    have hshift : ∀ p, ⟪p - z, D⟫ = ⟪p - v, D⟫ := fun p => by
      rw [show p - z = (p - v) - (z - v) by abel, inner_sub_left, hzD, sub_zero]
    refine ⟨D, ?_, fun p hp hpv => ?_⟩
    · rw [hπinner v hvT, hshift, sub_self, inner_zero_left, mul_zero]
    · rw [hπinner p hp, hshift]
      exact mul_pos (inv_pos.2 (hlam p hp)) (hpos p hp hpv)
  -- zero edges: a signed form nonnegative on the projections, vanishing at `v, w`
  have hzero_nn : ∀ v ∈ T, ∀ w ∈ nbrs T v, σ v w = 0 → π w = π v ∧ ∃ D : E n, ⟪π v, D⟫ = 0 ∧
      ∀ p ∈ T, 0 ≤ ⟪π p, D⟫ ∧ (⟪π p, D⟫ = 0 → p = v ∨ p = w) := by
    intro v hv w hw hw0
    obtain ⟨hwT, hwv, -⟩ := mem_nbrs.1 hw
    obtain ⟨D, hnn, hzero, hzD⟩ := rot_zero_nbr hcp h2 hskew hz hnd hv (hvz v hv) hw hw0
    have hshift : ∀ p, ⟪p - z, D⟫ = ⟪p - v, D⟫ := fun p => by
      rw [show p - z = (p - v) - (z - v) by abel, inner_sub_left, hzD, sub_zero]
    -- `w` is on the line `zv`
    have hline := rot_line h2 hz hnd hv (hvz v hv)
    obtain ⟨μ, hμ⟩ := exists_smul_of_finrank_le_one hline (mem_rot_line_z hskew hz hv)
      (mem_rot_line hv hwT hw0) (sub_ne_zero.2 (Ne.symm (hvz v hv)))
    have hwz : w - z = (1 - μ) • (v - z) := by
      have : w - z = (w - v) + (v - z) := by abel
      rw [this, hμ, sub_smul, one_smul, smul_sub, smul_sub]
      abel
    have hπw : π w = π v := by
      have hf : f (w - z) = (1 - μ) * f (v - z) := by rw [hwz, map_smul, smul_eq_mul]
      rw [map_sub, map_sub] at hf
      have hv0 := (hlam v hv).ne'
      have hw0' := (hlam w hwT).ne'
      simp only [hπ]
      rw [hwz, smul_smul]
      congr 1
      field_simp
      linarith
    refine ⟨hπw, D, ?_, fun p hp => ⟨?_, fun hp0 => ?_⟩⟩
    · rw [hπinner v hv, hshift, sub_self, inner_zero_left, mul_zero]
    · rw [hπinner p hp, hshift]
      exact mul_nonneg (inv_pos.2 (hlam p hp)).le (hnn p hp)
    · rw [hπinner p hp, hshift] at hp0
      rcases mul_eq_zero.1 hp0 with h | h
      · exact absurd h (inv_pos.2 (hlam p hp)).ne'
      · exact hzero p hp h
  -- extremality in the projected set
  have hext_of : ∀ v ∈ T, ∀ D : E n, ⟪π v, D⟫ = 0 → (∀ p ∈ T, 0 ≤ ⟪π p, D⟫) →
      (∀ p ∈ T, ⟪π p, D⟫ = 0 → π p = π v) →
      ∀ y₁ ∈ (T.image π : Set (E n)), ∀ y₂ ∈ (T.image π : Set (E n)),
        π v ∈ openSegment ℝ y₁ y₂ → y₁ = π v := by
    intro v hv D h0 hnn hzero y₁ hy₁ y₂ hy₂ hseg
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy₁)
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy₂)
    obtain ⟨a, b, ha, hb, hab, habv⟩ := hseg
    have hval : a * ⟪π p, D⟫ + b * ⟪π q, D⟫ = 0 := by
      rw [← real_inner_smul_left, ← real_inner_smul_left, ← inner_add_left, habv, h0]
    have h1 : a * ⟪π p, D⟫ = 0 := by
      have := mul_nonneg ha.le (hnn p hp)
      have := mul_nonneg hb.le (hnn q hq)
      linarith
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h ha.ne'
    · exact hzero p hp h
  -- the items
  set S := sameC T σ with hS
  set Z := T.filter fun v => 1 ≤ zerC T σ v with hZ
  have hzer1 : ∀ v ∈ T, zerC T σ v ≤ 1 := fun v hv => rot_zer_le_one hcp h2 hz hnd hv (hvz v hv)
  have hsumZ : ∑ v ∈ T, zerC T σ v = Z.card := by
    rw [hZ, Finset.card_eq_sum_ones, Finset.sum_filter]
    refine Finset.sum_congr rfl fun v hv => ?_
    have := hzer1 v hv
    split_ifs with h <;> omega
  -- a zero neighbour of a vertex of `Z`
  have hZnbr : ∀ v ∈ Z, ∃ w ∈ nbrs T v, σ v w = 0 := by
    intro v hv
    obtain ⟨hvT, hv1⟩ := Finset.mem_filter.1 hv
    obtain ⟨w, hw⟩ := Finset.card_pos.1 (by unfold zerC at hv1; omega :
      0 < ((nbrs T v).filter fun w => σ v w = 0).card)
    exact ⟨w, (Finset.mem_filter.1 hw).1, (Finset.mem_filter.1 hw).2⟩
  have hSZ : ∀ v ∈ S, zerC T σ v = 0 := by
    intro v hv
    obtain ⟨hvT, h⟩ := mem_sameC.1 hv
    have := pos_neg_zer hcp h2 σ hvT
    omega
  -- injectivity on `S`, disjointness, fibres on `Z`
  have hinjS : Set.InjOn π (S : Set (E n)) := by
    intro v hv v' hv' h
    obtain ⟨D, h0, hpos⟩ := hsame_pos v hv
    by_contra hne
    have := hpos v' (mem_sameC.1 hv').1 (Ne.symm hne)
    rw [← h, h0] at this
    exact lt_irrefl _ this
  have hdisj : Disjoint (S.image π) (Z.image π) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨v', hv', hvv'⟩ := Finset.mem_image.1 hx'
    obtain ⟨D, h0, hpos⟩ := hsame_pos v hv
    have hv'T := (Finset.mem_filter.1 hv').1
    by_cases hne : v' = v
    · rw [hne] at hv'
      have := hSZ v hv
      have := (Finset.mem_filter.1 hv').2
      omega
    · have := hpos v' hv'T hne
      rw [hvv', h0] at this
      exact lt_irrefl _ this
  have hfib : ∀ x ∈ Z.image π, (Z.filter fun v => π v = x).card ≤ 2 := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨w, hw, hw0⟩ := hZnbr v hv
    obtain ⟨-, D, h0, hD⟩ := hzero_nn v (Finset.mem_filter.1 hv).1 w hw hw0
    calc (Z.filter fun v' => π v' = π v).card ≤ ({v, w} : Finset (E n)).card := by
          refine Finset.card_le_card fun v' hv' => ?_
          obtain ⟨hv'Z, hπ'⟩ := Finset.mem_filter.1 hv'
          have hv'T := (Finset.mem_filter.1 hv'Z).1
          have h0' : ⟪π v', D⟫ = 0 := by rw [hπ', h0]
          rcases (hD v' hv'T).2 h0' with rfl | rfl <;> simp
      _ ≤ 2 := Finset.card_le_two
  -- the point set on the line
  set P := S.image π ∪ Z.image π with hP
  have hPle : P.card ≤ 2 := by
    refine card_le_two_of_line (K := (T.image π : Set (E n))) ?_ ?_ ?_
    · intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
        exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (mem_sameC.1 hv).1)
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
        exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_filter.1 hv).1)
    · intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨D, h0, hpos⟩ := hsame_pos v hv
        have hvT := (mem_sameC.1 hv).1
        refine hext_of v hvT D h0 (fun p hp => ?_) (fun p hp hp0 => ?_)
        · by_cases hpv : p = v
          · rw [hpv, h0]
          · exact (hpos p hp hpv).le
        · by_contra hne
          have hpv : p ≠ v := fun h => hne (by rw [h])
          exact (hpos p hp hpv).ne' hp0
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
        have hvT := (Finset.mem_filter.1 hv).1
        obtain ⟨w, hw, hw0⟩ := hZnbr v hv
        obtain ⟨hπw, D, h0, hD⟩ := hzero_nn v hvT w hw hw0
        refine hext_of v hvT D h0 (fun p hp => (hD p hp).1) (fun p hp hp0 => ?_)
        rcases (hD p hp).2 hp0 with rfl | rfl
        · rfl
        · exact hπw
    · intro x₁ hx₁ x₂ hx₂ x₃ hx₃ h12 h13 h23
      have hT : ∀ x ∈ P, ∃ p ∈ T, x = π p := by
        intro x hx
        rcases Finset.mem_union.1 hx with hx | hx
        · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
          exact ⟨v, (mem_sameC.1 hv).1, rfl⟩
        · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
          exact ⟨v, (Finset.mem_filter.1 hv).1, rfl⟩
      obtain ⟨p₁, hp₁, rfl⟩ := hT x₁ hx₁
      obtain ⟨p₂, hp₂, rfl⟩ := hT x₂ hx₂
      obtain ⟨p₃, hp₃, rfl⟩ := hT x₃ hx₃
      exact between_of_finrank_le_one hUdim (hπU p₁ hp₁ p₂ hp₂) (hπU p₁ hp₁ p₃ hp₃) h12 h13 h23
  have hcardP : P.card = S.card + (Z.image π).card := by
    rw [hP, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinjS]
  have hZle : Z.card ≤ 2 * (Z.image π).card := Finset.card_le_mul_card_image Z 2 hfib
  rw [hsumZ]
  omega

include hcp h2 hskew hz hnd in
theorem rot_count :
    2 * (sameC T fun v w => ⟪w - v, A (v - z)⟫).card +
      ∑ v ∈ T, zerC T (fun v w => ⟪w - v, A (v - z)⟫) v ≤ 4 := by
  by_cases hzT : z ∈ convexHull ℝ (T : Set (E n))
  · exact rot_count_of_mem hcp h2 hskew hz hnd hzT
  · exact rot_count_of_not_mem hcp h2 hskew hz hnd hzT

end rot

/-- **The face lemma.** -/
theorem face_count {T : Finset (E n)} (hcp : ConvPos T)
    (h2 : dim (convexHull ℝ (T : Set (E n))) = 2) {a : E n → E n}
    (hmot : ∀ p ∈ T, ∀ q ∈ T, ⟪a p - a q, p - q⟫ = 0)
    (hor : ∃ v ∈ T, ∃ w ∈ nbrs T v, ⟪w - v, a v⟫ ≠ 0) :
    2 * (sameC T fun v w => ⟪w - v, a v⟫).card + ∑ v ∈ T, zerC T (fun v w => ⟪w - v, a v⟫) v
      ≤ 4 := by
  classical
  obtain ⟨o, ho, -⟩ := id hor
  obtain ⟨A, c, hskew, hu⟩ := trivialOn_of_pairs (S := (T : Set (E n))) ⟨o, by exact_mod_cast ho⟩
    (fun p hp q hq => hmot p hp q hq)
  have hvs : vectorSpan ℝ (convexHull ℝ (T : Set (E n))) = vectorSpan ℝ (T : Set (E n)) := by
    rw [← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]
  have hU2 : finrank ℝ (vectorSpan ℝ (T : Set (E n))) = 2 := by rw [← hvs]; exact h2
  -- the motion on edges is the in-plane rigid motion
  have hval : ∀ v ∈ T, ∀ w ∈ T, ⟪w - v, a v⟫ = ⟪w - v, A v + c⟫ := by
    intro v hv w hw
    have := hu v (by exact_mod_cast hv) (w - v) (vsub_mem_vs hv hw)
    rw [inner_sub_left, real_inner_comm (w - v) (a v), real_inner_comm (w - v) (A v + c)] at this
    linarith
  by_cases htr : ∀ x ∈ vectorSpan ℝ (T : Set (E n)), ∀ y ∈ vectorSpan ℝ (T : Set (E n)),
      ⟪A x, y⟫ = 0
  · -- translation
    set c₀ := A o + c with hc₀
    have hσ : ∀ v ∈ T, ∀ w ∈ nbrs T v, ⟪w - v, a v⟫ = ⟪w - v, c₀⟫ := by
      intro v hv w hw
      have hwT := (mem_nbrs.1 hw).1
      rw [hval v hv w hwT, show A v + c = A (v - o) + c₀ by rw [hc₀, map_sub]; abel,
        inner_add_right, real_inner_comm, htr _ (vsub_mem_vs ho hv) _ (vsub_mem_vs hv hwT),
        zero_add]
    have hsame := sameC_congr hσ
    have hzer : ∀ v ∈ T, zerC T (fun v w => ⟪w - v, a v⟫) v = zerC T (fun v w => ⟪w - v, c₀⟫) v :=
      fun v hv => (counts_congr (hσ v hv)).2.2
    obtain ⟨v₀, hv₀, w₀, hw₀, hne⟩ := hor
    rw [hsame, Finset.sum_congr rfl hzer]
    exact trans_count hcp h2 c₀ ⟨v₀, hv₀, w₀, hw₀, by rwa [← hσ v₀ hv₀ w₀ hw₀]⟩
  · -- rotation
    push_neg at htr
    obtain ⟨x₀, hx₀, y₀, hy₀, hδ⟩ := htr
    obtain ⟨hnd, hcen⟩ := plane_center hU2 hskew hx₀ hy₀ hδ
    obtain ⟨u, huU, hu0⟩ := hcen (A o + c)
    set z := o + u with hzdef
    have hz : ∀ p ∈ T, p - z ∈ vectorSpan ℝ (T : Set (E n)) := by
      intro p hp
      rw [hzdef, show p - (o + u) = (p - o) - u by abel]
      exact Submodule.sub_mem _ (vsub_mem_vs ho hp) huU
    have hσ : ∀ v ∈ T, ∀ w ∈ nbrs T v, ⟪w - v, a v⟫ = ⟪w - v, A (v - z)⟫ := by
      intro v hv w hw
      have hwT := (mem_nbrs.1 hw).1
      rw [hval v hv w hwT]
      have hc' : ⟪w - v, A z + c⟫ = 0 := by
        have := hu0 (w - v) (vsub_mem_vs hv hwT)
        rw [hzdef, map_add, show A o + A u + c = A u + (A o + c) by abel, inner_add_right, this]
        ring
      rw [show A v + c = A (v - z) + (A z + c) by rw [map_sub]; abel, inner_add_right, hc', add_zero]
    have hsame := sameC_congr hσ
    have hzer : ∀ v ∈ T,
        zerC T (fun v w => ⟪w - v, a v⟫) v = zerC T (fun v w => ⟪w - v, A (v - z)⟫) v :=
      fun v hv => (counts_congr (hσ v hv)).2.2
    rw [hsame, Finset.sum_congr rfl hzer]
    exact rot_count hcp h2 hskew hz hnd

/-- The per-vertex identity `2 pq + r + 2[same] + r = 2 + 2[r = 2]` for `p + q + r = 2`. -/
lemma corner_identity {p q r : ℕ} (h : p + q + r = 2) :
    2 * (p * q) + r + 2 * (if p = 2 ∨ q = 2 then 1 else 0) + r = 2 + 2 * (if r = 2 then 1 else 0) := by
  have hp : p ≤ 2 := by omega
  have hq : q ≤ 2 := by omega
  have hr : r ≤ 2 := by omega
  interval_cases p <;> interval_cases q <;> interval_cases r <;> simp_all

/-- **The face side of the count.** -/
theorem face_side {T : Finset (E n)} (hcp : ConvPos T)
    (h2 : dim (convexHull ℝ (T : Set (E n))) = 2) {a : E n → E n}
    (hmot : ∀ p ∈ T, ∀ q ∈ T, ⟪a p - a q, p - q⟫ = 0) (dead : E n → Prop) [DecidablePred dead]
    (hdead : ∀ v ∈ T, dead v → zerC T (fun v w => ⟪w - v, a v⟫) v = 2) :
    2 * T.card + 2 * min (T.filter dead).card 2 ≤
      ∑ v ∈ T, (2 * (posC T (fun v w => ⟪w - v, a v⟫) v * negC T (fun v w => ⟪w - v, a v⟫) v) +
        zerC T (fun v w => ⟪w - v, a v⟫) v) + 4 := by
  classical
  set σ : E n → E n → ℝ := fun v w => ⟪w - v, a v⟫ with hσ
  -- the per-vertex identity, summed
  have hid : ∑ v ∈ T, (2 * (posC T σ v * negC T σ v) + zerC T σ v) + 2 * (sameC T σ).card +
      ∑ v ∈ T, zerC T σ v = 2 * T.card + 2 * (T.filter fun v => zerC T σ v = 2).card := by
    have hsame : (sameC T σ).card = ∑ v ∈ T, (if posC T σ v = 2 ∨ negC T σ v = 2 then 1 else 0) := by
      rw [← Finset.card_filter]; rfl
    have h2c : (T.filter fun v => zerC T σ v = 2).card =
        ∑ v ∈ T, (if zerC T σ v = 2 then 1 else 0) := Finset.card_filter _ _
    have key : ∑ v ∈ T, (2 * (posC T σ v * negC T σ v) + zerC T σ v +
        2 * (if posC T σ v = 2 ∨ negC T σ v = 2 then 1 else 0) + zerC T σ v) =
        ∑ v ∈ T, (2 + 2 * (if zerC T σ v = 2 then 1 else 0)) :=
      Finset.sum_congr rfl fun v hv => corner_identity (pos_neg_zer hcp h2 σ hv)
    rw [hsame, h2c]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at key ⊢
    omega
  have hdeadle : (T.filter dead).card ≤ (T.filter fun v => zerC T σ v = 2).card :=
    Finset.card_le_card fun v hv => Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hv).1,
      hdead v (Finset.mem_filter.1 hv).1 (Finset.mem_filter.1 hv).2⟩
  by_cases hor : ∃ v ∈ T, ∃ w ∈ nbrs T v, ⟪w - v, a v⟫ ≠ 0
  · have hfc : 2 * (sameC T σ).card + ∑ v ∈ T, zerC T σ v ≤ 4 := face_count hcp h2 hmot hor
    have : min (T.filter dead).card 2 ≤ (T.filter dead).card := min_le_left _ _
    omega
  · push_neg at hor
    -- every vertex has two zero edges
    have hall : ∀ v ∈ T, zerC T σ v = 2 := by
      intro v hv
      rw [← card_nbrs hcp h2 hv]
      unfold zerC
      congr 1
      exact Finset.filter_true_of_mem fun w hw => hor v hv w hw
    have hfil : (T.filter fun v => zerC T σ v = 2) = T := Finset.filter_true_of_mem hall
    have hsame0 : (sameC T σ).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro v hv
      obtain ⟨hvT, h⟩ := mem_sameC.1 hv
      have := pos_neg_zer hcp h2 σ hvT
      have := hall v hvT
      omega
    have hsumZ : ∑ v ∈ T, zerC T σ v = 2 * T.card := by
      rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hfil, hsame0, hsumZ] at hid
    have : min (T.filter dead).card 2 ≤ 2 := min_le_right _ _
    omega

end Kalai5
