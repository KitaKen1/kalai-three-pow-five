import Kalai5.Cube3.TriangleNormalizedSupport

/-! All three equal oriented normals force a common width ratio. -/
namespace Kalai5.Cube3.TriangleData
local notation "⟪" x ", " y "⟫" => inner ℝ x y

theorem matching_permutation (T U : TriangleData) (h : ∀ i,∃ j,T.normal i=U.normal j) :
    ∃ σ : Equiv.Perm (Fin 3),∀ i,T.normal i=U.normal (σ i) := by
  classical
  choose f hf using h
  have hinj : Function.Injective f := by
    intro i j hij; apply T.normal_injective; rw [hf,hf,hij]
  exact ⟨Equiv.ofBijective f ⟨hinj,Finite.surjective_of_injective hinj⟩,hf⟩

theorem width_ratio_constant (T U : TriangleData) (σ : Equiv.Perm (Fin 3))
    (hn : ∀ i,T.normal i=U.normal (σ i)) (j k : Fin 3) :
    U.width (σ j)/T.width j=U.width (σ k)/T.width k := by
  have he (k : Fin 3) : (∑ i,(T.height i+U.height (σ i))/T.width i)-U.width (σ k)/T.width k=1 := by
    have hh := T.normalized_support_sum (U.point (σ k))
    have hval (i : Fin 3) : (T.height i+⟪T.normal i,U.point (σ k)⟫)/T.width i=
        (T.height i+U.height (σ i))/T.width i-(if i=k then U.width (σ i)/T.width i else 0) := by
      rw [hn,U.normal_eval]
      by_cases hik : i=k
      · subst i; simp; ring
      · have hσ : σ i ≠ σ k := fun h => hik (σ.injective h)
        simp [hik,hσ]
    simp_rw [hval] at hh
    simpa [Finset.sum_sub_distrib] using hh
  linarith [he j,he k]

theorem widths_all_or_none (T U : TriangleData) (σ : Equiv.Perm (Fin 3))
    (hn : ∀ i,T.normal i=U.normal (σ i)) {j : Fin 3} (hj : T.width j=U.width (σ j)) :
    ∀ k,T.width k=U.width (σ k) := by
  intro k
  have hr := T.width_ratio_constant U σ hn k j
  rw [← hj,div_self (T.width_positive j).ne'] at hr
  exact ((div_eq_one_iff_eq (T.width_positive k).ne').1 hr).symm

end Kalai5.Cube3.TriangleData
