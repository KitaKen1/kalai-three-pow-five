import Kalai5.Faces.LowDim
import Kalai5.Rows.Dual

/-!
# Box inequalities for rows of 4-polytopes

* `two_mul_fvec_one_le`: a polytope with `n` vertices has at most `C(n, 2)` edges (an edge is
  the convex hull of its two vertices);
* `realRow_ube`: `2e ≤ n (n - 1)` for real rows, and `realRow_ubp`: `2p ≤ r (r - 1)` (dually).
-/

namespace Kalai5

open Set

variable {d : ℕ}

/-- **At most `C(n, 2)` edges**: the map from edges to their pairs of vertices is injective. -/
lemma two_mul_fvec_one_le (V : Finset (E d)) :
    2 * fvec (convexHull ℝ (V : Set (E d))) 1 ≤
      fvec (convexHull ℝ (V : Set (E d))) 0 * (fvec (convexHull ℝ (V : Set (E d))) 0 - 1) := by
  classical
  set Q := convexHull ℝ (V : Set (E d)) with hQ
  have hXfin : (Q.extremePoints ℝ).Finite := extremePoints_finite V
  set Xf := hXfin.toFinset with hXf
  have hn : fvec Q 0 = Xf.card := by rw [hQ, fvec_zero_eq, Set.ncard_eq_toFinset_card _ hXfin]
  -- the target: two-element subsets of the vertex set
  set T : Set (Set (E d)) :=
    (fun S : Finset (E d) => (S : Set (E d))) '' (Xf.powersetCard 2 : Set (Finset (E d))) with hT
  have hTfin : T.Finite := (Finset.finite_toSet _).image _
  have hTcard : T.ncard = Xf.card.choose 2 := by
    rw [hT, Set.ncard_image_of_injective _ Finset.coe_injective, Set.ncard_coe_finset,
      Finset.card_powersetCard]
  have hhull : ∀ {G : Set (E d)}, G ∈ faces Q → convexHull ℝ (G.extremePoints ℝ) = G := by
    intro G hG
    have hGS := face_eq_convexHull_filter hG
    rw [hGS]
    exact convexHull_extremePoints_eq _
  have hmaps : ∀ G ∈ {G | G ∈ faces Q ∧ dim G = 1}, G.extremePoints ℝ ∈ T := by
    rintro G ⟨hG, h1⟩
    have hGS := face_eq_convexHull_filter hG
    have hfin : (G.extremePoints ℝ).Finite := by rw [hGS]; exact extremePoints_finite _
    have h2 : (G.extremePoints ℝ).ncard = 2 := by
      rw [hGS] at h1 ⊢
      exact ncard_extremePoints_of_dim_one _ h1
    have hsub : G.extremePoints ℝ ⊆ Q.extremePoints ℝ :=
      hG.2.isExtreme.extremePoints_subset_extremePoints
    refine ⟨hfin.toFinset, ?_, Set.Finite.coe_toFinset _⟩
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨fun z hz => ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset] at hz ⊢
      exact hsub hz
    · rw [← Set.ncard_eq_toFinset_card _ hfin, h2]
  have hinj : Set.InjOn (fun G : Set (E d) => G.extremePoints ℝ) {G | G ∈ faces Q ∧ dim G = 1} := by
    rintro G ⟨hG, -⟩ G' ⟨hG', -⟩ he
    rw [← hhull hG, ← hhull hG']
    exact congrArg (convexHull ℝ) he
  have hle := Set.ncard_le_ncard_of_injOn _ hmaps hinj hTfin
  rw [hTcard] at hle
  have h1 : fvec Q 1 = {G | G ∈ faces Q ∧ dim G = 1}.ncard := rfl
  rw [h1, hn]
  have hch := Nat.choose_two_right Xf.card
  have hev : 2 ∣ Xf.card * (Xf.card - 1) := (Nat.even_mul_pred_self _).two_dvd
  have h2 : 2 * Xf.card.choose 2 = Xf.card * (Xf.card - 1) := by
    rw [hch, Nat.mul_div_cancel' hev]
  omega

/-- **`2e ≤ n (n - 1)`** for rows of 4-polytopes. -/
theorem realRow_ube {R : Row} (hR : IsRealRow R) : 2 * R.e ≤ R.n * (R.n - 1) := by
  obtain ⟨d, Q, ⟨V, rfl⟩, -, rfl⟩ := hR
  exact two_mul_fvec_one_le V

/-- **`2p ≤ r (r - 1)`** for rows of 4-polytopes (the dual row). -/
theorem realRow_ubp {R : Row} (hR : IsRealRow R) : 2 * R.p ≤ R.r * (R.r - 1) :=
  realRow_ube (realRow_dual hR)

/-- **A 4-polytope has at least five vertices.** -/
theorem realRow_five_le_n {R : Row} (hR : IsRealRow R) : 5 ≤ R.n := by
  obtain ⟨d, Q, ⟨V, rfl⟩, hdim, rfl⟩ := hR
  have hV : V.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.coe_empty, convexHull_empty] at hdim
    unfold dim at hdim
    rw [vectorSpan_empty, finrank_bot] at hdim
    omega
  have h := dim_add_one_le_ncard_extremePoints V hV
  rw [hdim] at h
  show 5 ≤ fvec (convexHull ℝ (V : Set (E d))) 0
  rw [fvec_zero_eq]
  omega

/-- **A 4-polytope has at least five facets.** -/
theorem realRow_five_le_r {R : Row} (hR : IsRealRow R) : 5 ≤ R.r :=
  realRow_five_le_n (realRow_dual hR)

end Kalai5
