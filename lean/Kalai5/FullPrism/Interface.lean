import Kalai5.FullPrism.Assemble
import Kalai5.Full.Basic

/-!
# From a labelled full prism facet to 243 faces

`IsCSPolytope5.three_pow_five_of_prism_labels`: if a full facet `F` of a centrally symmetric
5-polytope `P` has its vertices labelled `v⁺_k, v⁻_k` (`k < 4`), and for each `k` some linear form
`r_k` vanishes at all the other six vertices of `F` and is positive at `v^±_k`, then `P` has at
least 243 nonempty faces.  (The vertices of `P` are `±v`, so `P = conv {±v}`; then `prism_core`.)
-/

namespace Kalai5

open Set FullPrism

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {P : Set E5}

theorem IsCSPolytope5.three_pow_five_of_prism_labels (hP : IsCSPolytope5 P) {F : Set E5}
    (hF : F ∈ faces P) (hne : F ≠ P) (hfull : 2 * cnt P F 0 = fvec P 0) (v : Fin 8 → E5)
    (hvF : ∀ j, v j ∈ F) (hvext : ∀ j, v j ∈ P.extremePoints ℝ) (hvinj : Function.Injective v)
    (hcover : ∀ x ∈ P.extremePoints ℝ, x ∈ F → ∃ j, x = v j) (r : Fin 4 → E5)
    (hr0 : ∀ (k : Fin 4) (j : Fin 8), j.val / 2 ≠ k.val → ⟪r k, v j⟫ = 0)
    (hrp : ∀ k, 0 < ⟪r k, vp v k⟫) (hrm : ∀ k, 0 < ⟪r k, vm v k⟫) :
    243 ≤ (faces P).ncard := by
  classical
  obtain ⟨u, hu1, hFu, hpm⟩ := hP.exists_full_normal hF hne hfull
  set u' := (InnerProductSpace.toDual ℝ E5).symm u with hu'
  have hu'v : ∀ j, ⟪u', v j⟫ = 1 := by
    intro j
    rw [hu', InnerProductSpace.toDual_symm_apply]
    have := hvF j
    rw [hFu] at this
    exact this.2
  have hne' : ∀ k, vp v k ≠ vm v k := by
    intro k h
    have := hvinj h
    simp only [Fin.mk.injEq] at this
    omega
  have h243 := prism_core hu'v r hr0 hrp hrm hne'
  -- the vertices of `P` are `±v`
  have hrange : range (pm16 v) = P.extremePoints ℝ := by
    ext x
    rw [mem_range_pm16]
    constructor
    · rintro ⟨j, rfl | rfl⟩
      · exact hvext j
      · exact neg_mem_extremePoints hP.symm (hvext j)
    · intro hx
      rcases hpm x hx with h1 | h1
      · obtain ⟨j, rfl⟩ := hcover x hx (by rw [hFu]; exact ⟨hx.1, h1⟩)
        exact ⟨j, Or.inl rfl⟩
      · have hnx : -x ∈ P.extremePoints ℝ := neg_mem_extremePoints hP.symm hx
        have hux : u (-x) = 1 := by rw [map_neg, h1, neg_neg]
        obtain ⟨j, hj⟩ := hcover (-x) hnx (by rw [hFu]; exact ⟨hnx.1, hux⟩)
        exact ⟨j, Or.inr (by rw [← hj, neg_neg])⟩
  obtain ⟨V, hV⟩ := hP.polytope
  have hPconv : convexHull ℝ (range (pm16 v)) = P := by
    rw [hrange, hV]
    exact convexHull_extremePoints_eq V
  rwa [hPconv] at h243

end Kalai5
