import Kalai5.Rigidity.Braces
import Kalai5.Faces.LowDim
import Kalai5.Euler.Euler

/-!
# Vertex slices of polytopes

For a finite set `V`, a point `a₀ ∈ V` and a direction `c` such that `⟪c, ·⟫` drops by more than
`t > 0` from `a₀` to every other point of `V` (`VSlice`), the hyperplane
`H = {⟪c, ·⟫ = ⟪c, a₀⟫ - t}` meets each segment `[a₀, x]` (`x ∈ V \ {a₀}`) in the point
`e x = a₀ + τ x • (x - a₀)`, `τ x = t / (⟪c, a₀⟫ - ⟪c, x⟫) ∈ (0, 1)`.

* `convexHull_inter_H`: `conv T ∩ H = conv (e '' (T \ {a₀}))` for `a₀ ∈ T ⊆ V`.
* Face correspondence (`F ↦ F ∩ H`, faces `F ∋ a₀`, `F ≠ {a₀}`, onto the faces of `conv V ∩ H`):
  `inter_mem_faces`, `exists_face_of_mem_faces`, `dim_inter_add_one` (the dimension drops by one),
  `e_mem_iff` (`e x ∈ F ↔ x ∈ F`).
* `exists_vslice`: every extreme point has a slice.
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

lemma dim_convexHull' (S : Set (E n)) : dim (convexHull ℝ S) = dim S := by
  unfold dim
  rw [← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]

/-- A slice of `conv V` near `a₀`. -/
structure VSlice (V : Finset (E n)) (a₀ : E n) where
  /-- the direction -/
  c : E n
  /-- the depth -/
  t : ℝ
  ha₀ : a₀ ∈ V
  ht : 0 < t
  hgap : ∀ x ∈ V, x ≠ a₀ → t < ⟪c, a₀⟫ - ⟪c, x⟫

namespace VSlice

variable {V : Finset (E n)} {a₀ : E n} (σ : VSlice V a₀)

/-- The level of the slice. -/
noncomputable def lev : ℝ := ⟪σ.c, a₀⟫ - σ.t

/-- The slicing hyperplane. -/
def H : Set (E n) := {z | ⟪σ.c, z⟫ = σ.lev}

/-- The ratio of the slice point on `[a₀, x]`. -/
noncomputable def τ (x : E n) : ℝ := σ.t / (⟪σ.c, a₀⟫ - ⟪σ.c, x⟫)

/-- The slice point on `[a₀, x]`. -/
noncomputable def e (x : E n) : E n := a₀ + σ.τ x • (x - a₀)

lemma gap_pos {x : E n} (hx : x ∈ V) (hxa : x ≠ a₀) : 0 < ⟪σ.c, a₀⟫ - ⟪σ.c, x⟫ :=
  σ.ht.trans (σ.hgap x hx hxa)

lemma τ_pos {x : E n} (hx : x ∈ V) (hxa : x ≠ a₀) : 0 < σ.τ x :=
  div_pos σ.ht (σ.gap_pos hx hxa)

lemma τ_lt_one {x : E n} (hx : x ∈ V) (hxa : x ≠ a₀) : σ.τ x < 1 :=
  (div_lt_one (σ.gap_pos hx hxa)).2 (σ.hgap x hx hxa)

lemma τ_mul {x : E n} (hx : x ∈ V) (hxa : x ≠ a₀) :
    σ.τ x * (⟪σ.c, a₀⟫ - ⟪σ.c, x⟫) = σ.t := by
  unfold τ; field_simp [(σ.gap_pos hx hxa).ne']

lemma inner_e {x : E n} (hx : x ∈ V) (hxa : x ≠ a₀) : ⟪σ.c, σ.e x⟫ = σ.lev := by
  have h := σ.τ_mul hx hxa
  simp only [e, lev, inner_add_right, real_inner_smul_right, inner_sub_right]
  linarith

lemma e_mem_H {x : E n} (hx : x ∈ V) (hxa : x ≠ a₀) : σ.e x ∈ σ.H := σ.inner_e hx hxa

lemma not_mem_H : a₀ ∉ σ.H := by
  intro h
  have : ⟪σ.c, a₀⟫ = ⟪σ.c, a₀⟫ - σ.t := h
  linarith [σ.ht]

lemma e_mem_segment {x : E n} (hx : x ∈ V) (hxa : x ≠ a₀) : σ.e x ∈ openSegment ℝ a₀ x := by
  refine ⟨1 - σ.τ x, σ.τ x, by linarith [σ.τ_lt_one hx hxa], σ.τ_pos hx hxa, by ring, ?_⟩
  simp only [e, sub_smul, one_smul, smul_sub]
  abel

lemma e_sub {x : E n} : σ.e x - a₀ = σ.τ x • (x - a₀) := by
  simp [e]

lemma convex_H : Convex ℝ σ.H :=
  convex_hyperplane (f := fun z => ⟪σ.c, z⟫) ⟨fun x y => inner_add_right _ _ _,
    fun a x => real_inner_smul_right _ _ _⟩ σ.lev

/-- **The slice of `conv T`.** -/
theorem convexHull_inter_H {T : Finset (E n)} (hT : T ⊆ V) (ha : a₀ ∈ T) :
    convexHull ℝ (T : Set (E n)) ∩ σ.H = convexHull ℝ (σ.e '' ((T : Set (E n)) \ {a₀})) := by
  classical
  apply Subset.antisymm
  · rintro z ⟨hz, hzH⟩
    obtain ⟨μ, hμ0, hμ1, hμz⟩ := Finset.mem_convexHull'.1 hz
    set T' := T.erase a₀
    have hT' : ∀ y ∈ T', y ∈ V ∧ y ≠ a₀ := fun y hy =>
      ⟨hT (Finset.mem_of_mem_erase hy), Finset.ne_of_mem_erase hy⟩
    -- weights on the slice points
    set ν : E n → ℝ := fun y => μ y / σ.τ y
    have hsum1 := Finset.add_sum_erase T μ ha
    have hsumz := Finset.add_sum_erase T (fun y => μ y • y) ha
    have hlev : ∑ y ∈ T, μ y * ⟪σ.c, y⟫ = σ.lev := by
      have : ⟪σ.c, z⟫ = σ.lev := hzH
      rw [← hμz, inner_sum] at this
      simpa [real_inner_smul_right] using this
    have hlev' := Finset.add_sum_erase T (fun y => μ y * ⟪σ.c, y⟫) ha
    have hν : ∑ y ∈ T', ν y = 1 := by
      have e1 : ∀ y ∈ T', ν y = μ y * (⟪σ.c, a₀⟫ - ⟪σ.c, y⟫) / σ.t := by
        intro y hy
        obtain ⟨hyV, hya⟩ := hT' y hy
        simp only [ν, τ]
        field_simp [(σ.gap_pos hyV hya).ne', σ.ht.ne']
      rw [Finset.sum_congr rfl e1, ← Finset.sum_div, div_eq_one_iff_eq σ.ht.ne']
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      simp only [lev] at hlev
      have hs' : ∑ y ∈ T', μ y = 1 - μ a₀ := by linarith
      rw [hs']
      linear_combination -hlev' - hlev
    have hνz : ∑ y ∈ T', ν y • σ.e y = z := by
      have e1 : ∀ y ∈ T', ν y • σ.e y = ν y • a₀ + μ y • y - μ y • a₀ := by
        intro y hy
        obtain ⟨hyV, hya⟩ := hT' y hy
        have h1 : ν y * σ.τ y = μ y := by
          simp only [ν]; field_simp [(σ.τ_pos hyV hya).ne']
        simp only [e, smul_add, smul_smul, h1, smul_sub]
        abel
      rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.sum_smul, hν, one_smul, ← Finset.sum_smul, ← hμz]
      rw [← hsumz]
      have : ∑ y ∈ T', μ y = 1 - μ a₀ := by linarith
      rw [this, sub_smul, one_smul]
      abel
    have hνpos : ∀ y ∈ T', 0 ≤ ν y := fun y hy =>
      div_nonneg (hμ0 y (Finset.mem_of_mem_erase hy)) (σ.τ_pos (hT' y hy).1 (hT' y hy).2).le
    rw [← hνz]
    have hcm := Finset.centerMass_mem_convexHull (t := T') (w := ν) (z := σ.e)
      (s := σ.e '' ((T : Set (E n)) \ {a₀})) hνpos (by rw [hν]; norm_num)
      (fun y hy => ⟨y, ⟨by exact_mod_cast Finset.mem_of_mem_erase hy,
        by simpa using Finset.ne_of_mem_erase hy⟩, rfl⟩)
    rwa [Finset.centerMass, hν, inv_one, one_smul] at hcm
  · refine convexHull_min ?_ ((convex_convexHull ℝ _).inter σ.convex_H)
    rintro _ ⟨y, ⟨hyT, hya⟩, rfl⟩
    have hya' : y ≠ a₀ := by simpa using hya
    have hyV : y ∈ V := hT hyT
    refine ⟨?_, σ.e_mem_H hyV hya'⟩
    have := σ.e_mem_segment hyV hya'
    exact (convex_convexHull ℝ _).openSegment_subset (subset_convexHull ℝ _ (by exact_mod_cast ha))
      (subset_convexHull ℝ _ hyT) this

/-- The slice polytope. -/
def Q : Set (E n) := convexHull ℝ (V : Set (E n)) ∩ σ.H

lemma Q_eq : σ.Q = convexHull ℝ (σ.e '' ((V : Set (E n)) \ {a₀})) :=
  σ.convexHull_inter_H subset_rfl σ.ha₀

/-! ### The face correspondence -/

/-- `e x ∈ F ↔ x ∈ F` for faces `F ∋ a₀`. -/
lemma e_mem_iff {F : Set (E n)} (hF : F ∈ faces (convexHull ℝ (V : Set (E n)))) (ha : a₀ ∈ F)
    {x : E n} (hx : x ∈ V) (hxa : x ≠ a₀) : σ.e x ∈ F ↔ x ∈ F := by
  constructor
  · intro h
    exact hF.2.isExtreme.left_mem_of_mem_openSegment
      (subset_convexHull ℝ _ (by exact_mod_cast hx))
      (subset_convexHull ℝ _ (by exact_mod_cast σ.ha₀)) h
      (by rw [openSegment_symm]; exact σ.e_mem_segment hx hxa)
  · intro h
    have hconv : Convex ℝ F := face_convex (convex_convexHull ℝ _) hF
    exact hconv.openSegment_subset ha h (σ.e_mem_segment hx hxa)

/-- Faces through `a₀` (other than `{a₀}`) cut faces of the slice. -/
theorem inter_mem_faces {F : Set (E n)} (hF : F ∈ faces (convexHull ℝ (V : Set (E n))))
    (ha : a₀ ∈ F) (hne : F ≠ {a₀}) : F ∩ σ.H ∈ faces σ.Q := by
  classical
  obtain ⟨l, hl⟩ := exists_functional hF
  -- a vertex of `F` other than `a₀`
  obtain ⟨y, hyV, hyF, hya⟩ : ∃ y ∈ V, y ∈ F ∧ y ≠ a₀ := by
    by_contra hcon
    push_neg at hcon
    apply hne
    rw [face_eq_convexHull_filter hF]
    have : (V.filter (· ∈ F)) = {a₀} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h => hcon y h.1 h.2, fun h => h ▸ ⟨σ.ha₀, ha⟩⟩
    rw [this, Finset.coe_singleton, convexHull_singleton]
  have hey : σ.e y ∈ F ∩ σ.H := ⟨(σ.e_mem_iff hF ha hyV hya).2 hyF, σ.e_mem_H hyV hya⟩
  have hFmax : ∀ z ∈ F, ∀ w ∈ convexHull ℝ (V : Set (E n)), l w ≤ l z := by
    intro z hz; rw [hl] at hz; exact hz.2
  refine ⟨⟨_, hey⟩, fun _ => ⟨l, ?_⟩⟩
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hzF, hzH⟩
    refine ⟨⟨face_subset hF hzF, hzH⟩, fun w hw => hFmax z hzF w hw.1⟩
  · rintro ⟨⟨hzV, hzH⟩, hmax⟩
    refine ⟨?_, hzH⟩
    rw [hl]
    refine ⟨hzV, fun w hw => ?_⟩
    have h1 := hFmax _ hey.1 w hw
    have h2 := hmax _ ⟨face_subset hF hey.1, hey.2⟩
    linarith

/-- **Every face of the slice comes from a face through `a₀`.** -/
theorem exists_face_of_mem_faces {Φ : Set (E n)} (hΦ : Φ ∈ faces σ.Q) :
    ∃ F ∈ faces (convexHull ℝ (V : Set (E n))), a₀ ∈ F ∧ F ≠ {a₀} ∧ F ∩ σ.H = Φ := by
  classical
  obtain ⟨l, hl⟩ := exists_functional hΦ
  set ψ := (InnerProductSpace.toDual ℝ (E n)).symm l
  have hψ : ∀ z, l z = ⟪ψ, z⟫ := fun z => by
    rw [InnerProductSpace.toDual_symm_apply]
  -- the other points
  have hV' : (V.erase a₀).Nonempty := by
    obtain ⟨z, hz⟩ := hΦ.1
    have hzQ : z ∈ σ.Q := face_subset hΦ hz
    rw [Q_eq] at hzQ
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hempty : (V : Set (E n)) \ {a₀} = ∅ := by
      ext y
      simp only [Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false, not_and, not_not]
      intro hy
      by_contra hya
      have : y ∈ V.erase a₀ := Finset.mem_erase.2 ⟨hya, hy⟩
      rw [h] at this
      simp at this
    rw [hempty, Set.image_empty, convexHull_empty] at hzQ
    exact hzQ
  -- the slopes `g y = ⟪ψ, y - a₀⟫ / (⟪c, a₀⟫ - ⟪c, y⟫)`
  set g : E n → ℝ := fun y => ⟪ψ, y - a₀⟫ / (⟪σ.c, a₀⟫ - ⟪σ.c, y⟫)
  obtain ⟨y₀, hy₀, hmax⟩ := (V.erase a₀).exists_max_image g hV'
  set M := g y₀
  have hy₀V : y₀ ∈ V := Finset.mem_of_mem_erase hy₀
  have hy₀a : y₀ ≠ a₀ := Finset.ne_of_mem_erase hy₀
  -- values on the slice points
  have hψe : ∀ y ∈ V, y ≠ a₀ → ⟪ψ, σ.e y⟫ = ⟪ψ, a₀⟫ + σ.t * g y := by
    intro y hy hya
    simp only [e, inner_add_right, real_inner_smul_right, g, τ]
    field_simp [(σ.gap_pos hy hya).ne']
  set m := ⟪ψ, a₀⟫ + σ.t * M with hm
  -- `Φ` is the set of points of the slice where `ψ` reaches `m`
  have hQle : ∀ z ∈ σ.Q, ⟪ψ, z⟫ ≤ m := by
    intro z hz
    rw [Q_eq] at hz
    have hconv : Convex ℝ {w : E n | ⟪ψ, w⟫ ≤ m} :=
      convex_halfSpace_le ⟨fun x y => inner_add_right _ _ _,
        fun a x => real_inner_smul_right _ _ _⟩ m
    refine convexHull_min ?_ hconv hz
    rintro _ ⟨y, ⟨hy, hya⟩, rfl⟩
    have hya' : y ≠ a₀ := by simpa using hya
    show ⟪ψ, σ.e y⟫ ≤ m
    rw [hψe y hy hya']
    have := hmax y (Finset.mem_erase.2 ⟨hya', hy⟩)
    nlinarith [σ.ht]
  have hey₀ : σ.e y₀ ∈ σ.Q := by
    rw [Q_eq]; exact subset_convexHull ℝ _ ⟨y₀, ⟨hy₀V, by simpa using hy₀a⟩, rfl⟩
  have hey₀m : ⟪ψ, σ.e y₀⟫ = m := hψe y₀ hy₀V hy₀a
  have hΦm : ∀ z, z ∈ Φ ↔ z ∈ σ.Q ∧ m ≤ ⟪ψ, z⟫ := by
    intro z
    rw [hl]
    simp only [Set.mem_setOf_eq, hψ]
    constructor
    · rintro ⟨hz, h⟩; exact ⟨hz, hey₀m ▸ h _ hey₀⟩
    · rintro ⟨hz, h⟩; exact ⟨hz, fun w hw => (hQle w hw).trans h⟩
  -- the face of `conv V` exposed by `φ = ψ + M c`
  set φ := ψ + M • σ.c with hφ
  have hφw : ∀ w, ⟪φ, w⟫ = ⟪ψ, w⟫ + M * ⟪σ.c, w⟫ := fun w => by
    rw [hφ, inner_add_left, real_inner_smul_left]
  have hφV : ∀ y ∈ V, ⟪φ, y⟫ ≤ ⟪φ, a₀⟫ := by
    intro y hy
    by_cases hya : y = a₀
    · rw [hya]
    · have hg := hmax y (Finset.mem_erase.2 ⟨hya, hy⟩)
      have hgap := σ.gap_pos hy hya
      have key : ⟪ψ, y - a₀⟫ ≤ M * (⟪σ.c, a₀⟫ - ⟪σ.c, y⟫) := by
        have := (div_le_iff₀ hgap).1 hg
        linarith
      rw [inner_sub_right] at key
      rw [hφw, hφw]
      nlinarith
  set F := {x ∈ convexHull ℝ (V : Set (E n)) | ∀ w ∈ convexHull ℝ (V : Set (E n)),
    ⟪φ, w⟫ ≤ ⟪φ, x⟫}
  have hφle : ∀ w ∈ convexHull ℝ (V : Set (E n)), ⟪φ, w⟫ ≤ ⟪φ, a₀⟫ := by
    intro w hw
    have hconv : Convex ℝ {w : E n | ⟪φ, w⟫ ≤ ⟪φ, a₀⟫} :=
      convex_halfSpace_le ⟨fun x y => inner_add_right _ _ _,
        fun a x => real_inner_smul_right _ _ _⟩ _
    exact convexHull_min (fun y hy => hφV y (by exact_mod_cast hy)) hconv hw
  have ha₀F : a₀ ∈ F := ⟨subset_convexHull ℝ _ (by exact_mod_cast σ.ha₀), hφle⟩
  have hF : F ∈ faces (convexHull ℝ (V : Set (E n))) := by
    refine ⟨⟨a₀, ha₀F⟩, fun _ => ⟨InnerProductSpace.toDual ℝ (E n) φ, ?_⟩⟩
    ext x
    simp only [F, Set.mem_setOf_eq, InnerProductSpace.toDual_apply_apply]
  have hFH : F ∩ σ.H = Φ := by
    ext z
    rw [hΦm]
    constructor
    · rintro ⟨⟨hzV, hzmax⟩, hzH⟩
      refine ⟨⟨hzV, hzH⟩, ?_⟩
      have h1 := hzmax a₀ (subset_convexHull ℝ _ (by exact_mod_cast σ.ha₀))
      have hzc : ⟪σ.c, z⟫ = ⟪σ.c, a₀⟫ - σ.t := hzH
      rw [hφw, hφw, hzc] at h1
      rw [hm]
      nlinarith
    · rintro ⟨⟨hzV, hzH⟩, hzm⟩
      refine ⟨⟨hzV, fun w hw => ?_⟩, hzH⟩
      have h1 := hφle w hw
      have hzc : ⟪σ.c, z⟫ = ⟪σ.c, a₀⟫ - σ.t := hzH
      rw [hφw, hφw] at h1
      rw [hm] at hzm
      rw [hφw, hφw, hzc]
      nlinarith
  refine ⟨F, hF, ha₀F, fun h => ?_, hFH⟩
  have : σ.e y₀ ∈ F ∩ σ.H := by rw [hFH, hΦm]; exact ⟨hey₀, hey₀m.ge⟩
  rw [h] at this
  have h2 : σ.e y₀ ∈ σ.H := this.2
  rw [show σ.e y₀ = a₀ from this.1] at h2
  exact σ.not_mem_H h2

/-- **The dimension drops by one.** -/
theorem dim_inter_add_one {F : Set (E n)} (hF : F ∈ faces (convexHull ℝ (V : Set (E n))))
    (ha : a₀ ∈ F) (hne : F ≠ {a₀}) : dim (F ∩ σ.H) + 1 = dim F := by
  classical
  set T := V.filter (· ∈ F)
  have hTV : T ⊆ V := Finset.filter_subset _ _
  have haT : a₀ ∈ T := Finset.mem_filter.2 ⟨σ.ha₀, ha⟩
  have hFT : F = convexHull ℝ (T : Set (E n)) := face_eq_convexHull_filter hF
  obtain ⟨y₀, hy₀T, hy₀a⟩ : ∃ y ∈ T, y ≠ a₀ := by
    by_contra hcon
    push_neg at hcon
    apply hne
    rw [hFT]
    have : T = {a₀} := by
      ext y; simp only [Finset.mem_singleton]
      exact ⟨fun h => hcon y h, fun h => h ▸ haT⟩
    rw [this, Finset.coe_singleton, convexHull_singleton]
  have hy₀V : y₀ ∈ V := hTV hy₀T
  have hFH : F ∩ σ.H = convexHull ℝ (σ.e '' ((T : Set (E n)) \ {a₀})) := by
    rw [hFT]; exact σ.convexHull_inter_H hTV haT
  rw [hFH, hFT, dim_convexHull', dim_convexHull']
  set S' := σ.e '' ((T : Set (E n)) \ {a₀})
  have hy₀S' : σ.e y₀ ∈ S' := ⟨y₀, ⟨hy₀T, by simpa using hy₀a⟩, rfl⟩
  set v := σ.e y₀ - a₀
  -- `U = U' ⊔ ℝ v`
  have hU'U : vectorSpan ℝ S' ≤ vectorSpan ℝ (T : Set (E n)) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨_, ⟨y, ⟨hyT, hya⟩, rfl⟩, _, ⟨y', ⟨hy'T, hy'a⟩, rfl⟩, rfl⟩
    dsimp only
    have h1 : σ.e y - a₀ ∈ vectorSpan ℝ (T : Set (E n)) := by
      rw [σ.e_sub]; exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ hyT (by exact_mod_cast haT))
    have h2 : σ.e y' - a₀ ∈ vectorSpan ℝ (T : Set (E n)) := by
      rw [σ.e_sub]; exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ hy'T (by exact_mod_cast haT))
    have : σ.e y -ᵥ σ.e y' = (σ.e y - a₀) - (σ.e y' - a₀) := by rw [vsub_eq_sub]; abel
    rw [SetLike.mem_coe, this]
    exact Submodule.sub_mem _ h1 h2
  have hvU : v ∈ vectorSpan ℝ (T : Set (E n)) := by
    show σ.e y₀ - a₀ ∈ vectorSpan ℝ (T : Set (E n))
    rw [σ.e_sub]; exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ hy₀T (by exact_mod_cast haT))
  have hUle : vectorSpan ℝ (T : Set (E n)) ≤ vectorSpan ℝ S' ⊔ Submodule.span ℝ {v} := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (show a₀ ∈ (T : Set (E n)) by exact_mod_cast haT),
      Submodule.span_le]
    rintro _ ⟨y, hyT, rfl⟩
    dsimp only
    by_cases hya : y = a₀
    · rw [hya, vsub_self]; exact Submodule.zero_mem _
    · have hyV := hTV hyT
      have hτ := σ.τ_pos hyV hya
      have hyS' : σ.e y ∈ S' := ⟨y, ⟨hyT, by simpa using hya⟩, rfl⟩
      have e1 : y -ᵥ a₀ = (σ.τ y)⁻¹ • ((σ.e y - σ.e y₀) + v) := by
        rw [vsub_eq_sub, show (σ.e y - σ.e y₀) + v = σ.e y - a₀ by simp only [v]; abel, σ.e_sub,
          smul_smul, inv_mul_cancel₀ hτ.ne', one_smul]
      rw [SetLike.mem_coe, e1]
      refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_)
      · exact Submodule.mem_sup_left (vsub_mem_vectorSpan ℝ hyS' hy₀S')
      · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
  have hU : vectorSpan ℝ (T : Set (E n)) = vectorSpan ℝ S' ⊔ Submodule.span ℝ {v} :=
    le_antisymm hUle (sup_le hU'U ((Submodule.span_singleton_le_iff_mem _ _).2 hvU))
  -- `v ∉ U'` since `U'` lies in `cᗮ`
  have hU'c : ∀ w ∈ vectorSpan ℝ S', ⟪σ.c, w⟫ = 0 := by
    intro w hw
    have := inner_vectorSpan_eq_zero_of_const (F := S') (z := σ.c) (κ := σ.lev) (by
      rintro _ ⟨y, ⟨hyT, hya⟩, rfl⟩
      rw [real_inner_comm]; exact σ.inner_e (hTV hyT) (by simpa using hya)) w hw
    rwa [real_inner_comm] at this
  have hvc : ⟪σ.c, v⟫ ≠ 0 := by
    simp only [v, inner_sub_right, σ.inner_e hy₀V hy₀a, lev]
    linarith [σ.ht]
  have hinf : vectorSpan ℝ S' ⊓ Submodule.span ℝ {v} = ⊥ := by
    rw [eq_bot_iff]
    intro w ⟨hw1, hw2⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw2
    rw [Submodule.mem_bot]
    by_cases ha0 : a = 0
    · rw [ha0, zero_smul]
    · exfalso
      have := hU'c _ hw1
      rw [real_inner_smul_right] at this
      exact hvc ((mul_eq_zero.1 this).resolve_left ha0)
  have hv0 : v ≠ 0 := fun h => hvc (by rw [h, inner_zero_right])
  have h := Submodule.finrank_sup_add_finrank_inf_eq (vectorSpan ℝ S') (Submodule.span ℝ {v})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hv0, ← hU] at h
  show finrank ℝ (vectorSpan ℝ S') + 1 = finrank ℝ (vectorSpan ℝ (T : Set (E n)))
  omega

/-- The slice has dimension one less. -/
theorem dim_Q_add_one (hdim : 1 ≤ dim (convexHull ℝ (V : Set (E n)))) :
    dim σ.Q + 1 = dim (convexHull ℝ (V : Set (E n))) := by
  have hV : (V : Set (E n)).Nonempty := ⟨a₀, by exact_mod_cast σ.ha₀⟩
  refine σ.dim_inter_add_one ⟨hV.convexHull, IsExposed.refl _⟩
    (subset_convexHull ℝ _ (by exact_mod_cast σ.ha₀)) fun h => ?_
  rw [h, dim_singleton] at hdim
  omega

end VSlice

/-- An extreme point is exposed by a direction. -/
lemma exists_dir_of_extreme {V : Finset (E n)} {a₀ : E n}
    (ha : a₀ ∈ (convexHull ℝ (V : Set (E n))).extremePoints ℝ) :
    ∃ c : E n, ∀ x ∈ V, x ≠ a₀ → ⟪c, x⟫ < ⟪c, a₀⟫ := by
  have hF := singleton_mem_faces_of_extreme ha
  obtain ⟨l, hl⟩ := exists_functional hF
  refine ⟨(InnerProductSpace.toDual ℝ (E n)).symm l, fun x hx hxa => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply, InnerProductSpace.toDual_symm_apply]
  have hka : a₀ ∈ ({a₀} : Set (E n)) := rfl
  rw [hl] at hka
  have hkx : x ∈ convexHull ℝ (V : Set (E n)) := subset_convexHull ℝ _ (by exact_mod_cast hx)
  by_contra hle
  push_neg at hle
  have : x ∈ ({a₀} : Set (E n)) := by
    rw [hl]; exact ⟨hkx, fun y hy => (hka.2 y hy).trans hle⟩
  exact hxa this

/-- **Every vertex has a slice.** -/
theorem exists_vslice {V : Finset (E n)} {a₀ : E n}
    (ha : a₀ ∈ (convexHull ℝ (V : Set (E n))).extremePoints ℝ) : Nonempty (VSlice V a₀) := by
  classical
  have ha₀ : a₀ ∈ V := by exact_mod_cast extremePoints_convexHull_subset ha
  obtain ⟨c, hc⟩ := exists_dir_of_extreme ha
  by_cases hV : (V.erase a₀).Nonempty
  · obtain ⟨y, hy, hmin⟩ := (V.erase a₀).exists_min_image (fun x => ⟪c, a₀⟫ - ⟪c, x⟫) hV
    have hpos : 0 < ⟪c, a₀⟫ - ⟪c, y⟫ := by
      have := hc y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy); linarith
    refine ⟨⟨c, (⟪c, a₀⟫ - ⟪c, y⟫) / 2, ha₀, by linarith, fun x hx hxa => ?_⟩⟩
    have := hmin x (Finset.mem_erase.2 ⟨hxa, hx⟩)
    linarith
  · refine ⟨⟨c, 1, ha₀, one_pos, fun x hx hxa => absurd ⟨x, Finset.mem_erase.2 ⟨hxa, hx⟩⟩ hV⟩⟩

end Kalai5
