import Kalai5.Cube3.Config

/-!
# Extreme-point lifting in a fibre product

These are the two lifting steps needed for the (5,1,1,1) distribution. A
section vertex is lifted only when the other coordinate is itself extreme;
an arbitrary section vertex is never asserted to be a vertex of its ambient
polytope. No regularity of the height maps is needed for these implications.
-/

namespace Kalai5.Cube3

open Set

def fibreProduct {d m : ℕ} (D : Set (E d)) (B : Set (E m))
    (s : E d → ℝ) (t : E m → ℝ) : Set (E d × E m) :=
  {p | p.1 ∈ D ∧ p.2 ∈ B ∧ s p.1 = t p.2}

/-- A vertex of D, together with a vertex of the corresponding B-section,
is a vertex of the fibre product. -/
theorem extreme_fibreProduct_left {d m : ℕ} {D : Set (E d)} {B : Set (E m)}
    {s : E d → ℝ} {t : E m → ℝ} {y : E d} {x : E m}
    (hy : y ∈ D.extremePoints ℝ)
    (hx : x ∈ (B ∩ {z | s y = t z}).extremePoints ℝ) :
    (y, x) ∈ (fibreProduct D B s t).extremePoints ℝ := by
  rw [mem_extremePoints]
  refine ⟨⟨hy.1, hx.1.1, hx.1.2⟩, ?_⟩
  intro a ha b hb hseg
  have hyseg : y ∈ openSegment ℝ a.1 b.1 := by
    change y ∈ openSegment ℝ
      ((LinearMap.fst ℝ (E d) (E m)).toAffineMap a)
      ((LinearMap.fst ℝ (E d) (E m)).toAffineMap b)
    rw [← image_openSegment ℝ (LinearMap.fst ℝ (E d) (E m)).toAffineMap a b]
    exact ⟨(y, x), hseg, rfl⟩
  obtain ⟨ha1, hb1⟩ := (mem_extremePoints.1 hy).2 a.1 ha.1 b.1 hb.1 hyseg
  have hax : a.2 ∈ B ∩ {z | s y = t z} := ⟨ha.2.1, by rw [← ha1]; exact ha.2.2⟩
  have hbx : b.2 ∈ B ∩ {z | s y = t z} := ⟨hb.2.1, by rw [← hb1]; exact hb.2.2⟩
  have hxseg : x ∈ openSegment ℝ a.2 b.2 := by
    change x ∈ openSegment ℝ
      ((LinearMap.snd ℝ (E d) (E m)).toAffineMap a)
      ((LinearMap.snd ℝ (E d) (E m)).toAffineMap b)
    rw [← image_openSegment ℝ (LinearMap.snd ℝ (E d) (E m)).toAffineMap a b]
    exact ⟨(y, x), hseg, rfl⟩
  obtain ⟨ha2, hb2⟩ := (mem_extremePoints.1 hx).2 a.2 hax b.2 hbx hxseg
  exact ⟨Prod.ext ha1 ha2, Prod.ext hb1 hb2⟩

/-- The symmetric lift: a vertex of B fixes the section of D. -/
theorem extreme_fibreProduct_right {d m : ℕ} {D : Set (E d)} {B : Set (E m)}
    {s : E d → ℝ} {t : E m → ℝ} {y : E d} {x : E m}
    (hx : x ∈ B.extremePoints ℝ)
    (hy : y ∈ (D ∩ {z | s z = t x}).extremePoints ℝ) :
    (y, x) ∈ (fibreProduct D B s t).extremePoints ℝ := by
  rw [mem_extremePoints]
  refine ⟨⟨hy.1.1, hx.1, hy.1.2⟩, ?_⟩
  intro a ha b hb hseg
  have hxseg : x ∈ openSegment ℝ a.2 b.2 := by
    change x ∈ openSegment ℝ
      ((LinearMap.snd ℝ (E d) (E m)).toAffineMap a)
      ((LinearMap.snd ℝ (E d) (E m)).toAffineMap b)
    rw [← image_openSegment ℝ (LinearMap.snd ℝ (E d) (E m)).toAffineMap a b]
    exact ⟨(y, x), hseg, rfl⟩
  obtain ⟨ha2, hb2⟩ := (mem_extremePoints.1 hx).2 a.2 ha.2.1 b.2 hb.2.1 hxseg
  have hay : a.1 ∈ D ∩ {z | s z = t x} := ⟨ha.1, by rw [← ha2]; exact ha.2.2⟩
  have hby : b.1 ∈ D ∩ {z | s z = t x} := ⟨hb.1, by rw [← hb2]; exact hb.2.2⟩
  have hyseg : y ∈ openSegment ℝ a.1 b.1 := by
    change y ∈ openSegment ℝ
      ((LinearMap.fst ℝ (E d) (E m)).toAffineMap a)
      ((LinearMap.fst ℝ (E d) (E m)).toAffineMap b)
    rw [← image_openSegment ℝ (LinearMap.fst ℝ (E d) (E m)).toAffineMap a b]
    exact ⟨(y, x), hseg, rfl⟩
  obtain ⟨ha1, hb1⟩ := (mem_extremePoints.1 hy).2 a.1 hay b.1 hby hyseg
  exact ⟨Prod.ext ha1 ha2, Prod.ext hb1 hb2⟩

end Kalai5.Cube3
