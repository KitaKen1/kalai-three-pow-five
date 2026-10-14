import Kalai5.Cube3.LiftedPolygon
import Kalai5.Cube3.SingletonLift

/-!
# Geometry of the actual singleton auxiliary body

The seven vertices are now derived from the actual planar fibre. Consequently,
the low-height alternative is impossible at eighteen facets. It suffices to
retain one point of height at least three; no maximum-height construction is
needed for the remaining branch.
-/

namespace Kalai5.Cube3

open Set FullPrism

variable {x : Fin 8 → E5} (C : Config x)

namespace Config

theorem singletonAux_eq_polar (q : Fin 3 → E 2) :
    C.singletonAux q = polarSet (convexHull ℝ
      (signedPolygon (fibre C.c C.k 0) (anchor q) : Set (E 3))) := by
  ext y
  rw [mem_signedPolygon_polar]
  constructor
  · intro h k hk
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.1 hk
    have hv0 : C.c v = 0 := by simpa using hv
    exact h v hv0
  · intro h v hv
    exact h (C.k v) (Finset.mem_image.2 ⟨v,by simp [hv],rfl⟩)

lemma singletonAux_zero_interior (q : Fin 3 → E 2) :
    (0 : E 3) ∈ interior (C.singletonAux q) := by
  rw [C.singletonAux_eq_polar]
  exact zero_mem_interior_polarSet _

lemma singletonAux_convex (q : Fin 3 → E 2) : Convex ℝ (C.singletonAux q) := by
  rw [C.singletonAux_eq_polar]
  exact polarSet_convex _

lemma singletonAux_neg (q : Fin 3 → E 2) {y : E 3}
    (hy : y ∈ C.singletonAux q) : -y ∈ C.singletonAux q := by
  rw [C.singletonAux_eq_polar] at hy ⊢
  exact neg_mem_polarSet (fun _ h => signedPolygon_hull_symm h) hy

lemma singletonAux_compact (q : Fin 3 → E 2) (h3 : 3 ≤ (C.cls 0).card) :
    IsCompact (C.singletonAux q) := by
  rw [C.singletonAux_eq_polar]
  apply polarSet_isCompact
  apply signedPolygon_zero_interior
  · apply Finset.card_pos.1
    rw [C.card_fibre]
    omega
  · exact C.dim_fibre_eq_two h3

lemma singletonAux_polytope (q : Fin 3 → E 2) (h3 : 3 ≤ (C.cls 0).card) :
    ∃ V : Finset (E 3), C.singletonAux q = convexHull ℝ (V : Set (E 3)) := by
  rw [C.singletonAux_eq_polar]
  apply exists_polarSet_eq_convexHull
  apply signedPolygon_zero_interior
  · apply Finset.card_pos.1
    rw [C.card_fibre]
    omega
  · exact C.dim_fibre_eq_two h3

/-- Seven genuine vertices, without an additional geometric hypothesis. -/
theorem singletonAux_seven (q : Fin 3 → E 2) (h5 : 5 ≤ (C.cls 0).card) :
    ∃ y : Fin 7 → E 3, Function.Injective y ∧
      ∀ i, y i ∈ (C.singletonAux q).extremePoints ℝ := by
  rw [C.singletonAux_eq_polar]
  exact signedPolygon_polar_seven (anchor q) (C.convpos_fibre 0)
    (by rw [C.card_fibre]; exact h5)

/-- The entire low-height alternative is excluded for the actual auxiliary body. -/
theorem singleton_low_height_impossible {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (q : Fin 3 → E 2)
    (hsingle : ∀ i : Fin 3, ∀ v, C.c v = (![1,2,3] i : Fin 4) → C.k v = q i)
    (h5 : 5 ≤ (C.cls 0).card)
    (hheight : ∀ y ∈ (C.singletonAux q).extremePoints ℝ, |y 0| < 3) : False := by
  obtain ⟨y,hyinj,hy⟩ := C.singletonAux_seven q h5
  exact C.singleton_small_height_excluded hP hrange hh q hsingle y hyinj hy
    (fun i => hheight _ (hy i))

/-- Replace a maximum-height case split by one concrete tall point. -/
theorem singleton_tall_point {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (q : Fin 3 → E 2)
    (hsingle : ∀ i : Fin 3, ∀ v, C.c v = (![1,2,3] i : Fin 4) → C.k v = q i)
    (h5 : 5 ≤ (C.cls 0).card) : ∃ y ∈ C.singletonAux q, 3 ≤ y 0 := by
  have hex : ∃ y ∈ (C.singletonAux q).extremePoints ℝ, 3 ≤ |y 0| := by
    by_contra h
    push_neg at h
    exact C.singleton_low_height_impossible hP hrange hh q hsingle h5 h
  obtain ⟨y,hy,hhgt⟩ := hex
  by_cases hpos : 0 ≤ y 0
  · exact ⟨y,hy.1,by rwa [abs_of_nonneg hpos] at hhgt⟩
  · refine ⟨-y,C.singletonAux_neg q hy.1,?_⟩
    simpa [abs_of_neg (lt_of_not_ge hpos)] using hhgt

end Config
end Kalai5.Cube3
