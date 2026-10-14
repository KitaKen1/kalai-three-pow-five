import Kalai5.Rigidity.Joints

/-!
# Whiteley's induction step: slices, stars and gluing

* `braces_star` (slice step): at a vertex `a₀`, the vertices of the `2`-faces through `a₀` are
  braced.  A motion `u` gives velocities `w (e x) = (1 - τ x) u a₀ + τ x u x` at the slice points;
  `w` keeps the pairs inside the `2`-faces of the slice (they come from `3`-faces of `R`, braced by
  `WProp 3`, and `transfer`), so by the joint statement for the slice it keeps all pairs, and by
  `transfer` again `u` keeps the pairs of the star.
* `braces_of_stars` (gluing): with `c` exposing a vertex `v₁`, every other vertex has an edge going
  up (`exists_edge_up`); the stars are glued along these edges by strong induction on the number of
  vertices above, the overlap containing the `2`-faces through the edge, which span.
* `w_succ`: `WProp 3 → WJProp k → WProp (k + 1)`; hence `WProp 3 → WProp 4 → WProp 5`.
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

/-- Convex position. -/
def ConvPos (V : Finset (E n)) : Prop := ∀ x ∈ V, x ∈ (convexHull ℝ (V : Set (E n))).extremePoints ℝ

lemma convPos_vertFinset (V : Finset (E n)) : ConvPos (vertFinset V) := by
  intro x hx
  rw [convexHull_vertFinset, ← coe_vertFinset]
  exact hx

namespace VSlice

variable {V : Finset (E n)} {a₀ : E n} (σ : VSlice V a₀)

/-- In convex position the slice points are distinct. -/
lemma e_injOn (hcp : ConvPos V) {x y : E n} (hx : x ∈ V) (hxa : x ≠ a₀) (hy : y ∈ V)
    (hya : y ≠ a₀) (h : σ.e x = σ.e y) : x = y := by
  have hτx := σ.τ_pos hx hxa
  have hτy := σ.τ_pos hy hya
  have h' : σ.τ x • (x - a₀) = σ.τ y • (y - a₀) := by rw [← σ.e_sub, ← σ.e_sub, h]
  have ha₀ : a₀ ∈ convexHull ℝ (V : Set (E n)) := subset_convexHull ℝ _ (by exact_mod_cast σ.ha₀)
  -- the farther point would lie strictly between `a₀` and the other one
  have key : ∀ {p q : E n}, p ∈ V → q ∈ V → q ≠ a₀ → 0 < σ.τ p → 0 < σ.τ q →
      σ.τ p • (p - a₀) = σ.τ q • (q - a₀) → σ.τ p < σ.τ q → False := by
    intro p q hp hq hqa hτp hτq hpq hlt
    have hr : 0 < σ.τ p / σ.τ q := div_pos hτp hτq
    have hr1 : σ.τ p / σ.τ q < 1 := (div_lt_one hτq).2 hlt
    have e1 : q - a₀ = (σ.τ p / σ.τ q) • (p - a₀) := by
      rw [div_eq_inv_mul, mul_smul, hpq, smul_smul, inv_mul_cancel₀ hτq.ne', one_smul]
    have hqseg : q ∈ openSegment ℝ a₀ p := by
      set r := σ.τ p / σ.τ q with hrdef
      refine ⟨1 - r, r, by linarith, hr, by ring, ?_⟩
      have e2 : q = a₀ + r • (p - a₀) := by rw [← e1]; abel
      rw [e2, sub_smul, one_smul, smul_sub]; abel
    have hqe := (mem_extremePoints.1 (hcp q hq)).2 a₀ ha₀ p
      (subset_convexHull ℝ _ (by exact_mod_cast hp)) hqseg
    exact hqa hqe.1.symm
  rcases lt_trichotomy (σ.τ x) (σ.τ y) with hlt | heq | hgt
  · exact (key hx hy hya hτx hτy h' hlt).elim
  · rw [heq] at h'
    have := smul_right_injective (E n) hτy.ne' h'
    simpa using this
  · exact (key hy hx hxa hτy hτx h'.symm hgt).elim

end VSlice

/-- **Every edge lies in a `2`-face** (dimension `≥ 2`). -/
theorem exists_twoFace_of_edge {V : Finset (E n)} {F : Set (E n)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E n)))) (hF1 : dim F = 1) {p q : E n}
    (hp : p ∈ (convexHull ℝ (V : Set (E n))).extremePoints ℝ)
    (hq : q ∈ (convexHull ℝ (V : Set (E n))).extremePoints ℝ) (hpq : p ≠ q) (hpF : p ∈ F)
    (hqF : q ∈ F) (hdim : 2 ≤ dim (convexHull ℝ (V : Set (E n)))) :
    ∃ G ∈ twoFaces (convexHull ℝ (V : Set (E n))), p ∈ G ∧ q ∈ G := by
  set V' := vertFinset V
  have hV'R : convexHull ℝ (V' : Set (E n)) = convexHull ℝ (V : Set (E n)) :=
    convexHull_vertFinset V
  have hqV' : q ∈ V' := by rw [← Finset.mem_coe, coe_vertFinset]; exact hq
  have h := vectorSpan_le_twoFaces (V := V') (a₀ := p) (q := q) (by rw [hV'R]; exact hp) hqV'
    hpq.symm (by rw [hV'R]; exact hF) hF1 hpF hqF (by rw [hV'R]; exact hdim)
  by_contra hcon
  push_neg at hcon
  have hbot : Submodule.span ℝ ((fun z => z - p) '' {z | z ∈ V' ∧
      ∃ G ∈ faces (convexHull ℝ (V' : Set (E n))), dim G = 2 ∧ p ∈ G ∧ q ∈ G ∧ z ∈ G}) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨z, ⟨-, G, hG, hG2, hpG, hqG, -⟩, rfl⟩
    rw [hV'R] at hG
    exact absurd hqG (hcon G ⟨hG, hG2⟩ hpG)
  rw [hbot, le_bot_iff] at h
  have : dim (convexHull ℝ (V : Set (E n))) = 0 := by
    rw [← hV'R, dim_convexHull']; unfold dim; rw [h, finrank_bot]
  omega

/-- The star of a vertex: the vertices of the `2`-faces through it. -/
def star (R : Set (E n)) (v : E n) : Set (E n) :=
  {x | x ∈ R.extremePoints ℝ ∧ (x = v ∨ ∃ G ∈ twoFaces R, v ∈ G ∧ x ∈ G)}

lemma star_subset (R : Set (E n)) (v : E n) : star R v ⊆ R.extremePoints ℝ := fun _ hx => hx.1

lemma mem_star_self {R : Set (E n)} {v : E n} (hv : v ∈ R.extremePoints ℝ) : v ∈ star R v :=
  ⟨hv, Or.inl rfl⟩

/-- `2`-faces of a face are `2`-faces. -/
lemma bars2_face_subset {V : Finset (E n)} {C : Set (E n)}
    (hC : C ∈ faces (convexHull ℝ (V : Set (E n)))) :
    bars2 C (C.extremePoints ℝ) ⊆ bars2 (convexHull ℝ (V : Set (E n)))
      ((convexHull ℝ (V : Set (E n))).extremePoints ℝ) := by
  intro b hb
  simp only [bars2, Set.mem_iUnion] at hb ⊢
  obtain ⟨G, ⟨hG, hG2⟩, p, hp, q, hq, rfl⟩ := hb
  have hext := hC.2.isExtreme.extremePoints_subset_extremePoints
  exact ⟨G, ⟨faces_trans hC hG, hG2⟩, p, ⟨hext hp.1, hp.2⟩, q, ⟨hext hq.1, hq.2⟩, rfl⟩

/-- **The slice step.** -/
theorem braces_star {m k : ℕ} (hk : 2 ≤ k) (h3 : WProp 3) (hJ : WJProp k) {V : Finset (E m)}
    (hcp : ConvPos V) (hdim : dim (convexHull ℝ (V : Set (E m))) = k + 1) {a₀ : E m}
    (ha : a₀ ∈ V) :
    Braces (bars2 (convexHull ℝ (V : Set (E m))) ((convexHull ℝ (V : Set (E m))).extremePoints ℝ))
      (star (convexHull ℝ (V : Set (E m))) a₀) := by
  classical
  set R := convexHull ℝ (V : Set (E m)) with hR
  obtain ⟨σ⟩ := exists_vslice (hcp a₀ ha)
  have hvert : R.extremePoints ℝ = (V : Set (E m)) :=
    Subset.antisymm extremePoints_convexHull_subset (fun x hx => hcp x hx)
  -- the slice polytope and the joints
  have hdimQ := σ.dim_Q_add_one (by rw [← hR]; omega)
  rw [σ.Q_eq', ← hR] at hdimQ
  set N := V.filter fun x => x ≠ a₀ ∧ ∃ G ∈ twoFaces R, a₀ ∈ G ∧ x ∈ G
  set J := N.image σ.e
  have hJedge : ∀ j ∈ J, ∃ F ∈ faces (convexHull ℝ (σ.W : Set (E m))), dim F = 1 ∧ j ∈ F := by
    intro j hj
    obtain ⟨x, hxN, rfl⟩ := Finset.mem_image.1 hj
    obtain ⟨hxV, hxa, G, ⟨hG, hG2⟩, haG, hxG⟩ := Finset.mem_filter.1 hxN
    have hGne : G ≠ {a₀} := by intro h; rw [h, dim_singleton] at hG2; omega
    have hface := σ.inter_mem_faces hG haG hGne
    rw [σ.Q_eq'] at hface
    have hd := σ.dim_inter_add_one hG haG hGne
    exact ⟨G ∩ σ.H, hface, by omega, (σ.e_mem_iff hG haG hxV hxa).2 hxG, σ.e_mem_H hxV hxa⟩
  have hWJ := hJ m σ.W (by omega) J hJedge
  intro u hu
  -- interpolated velocities at the slice points
  set w : E m → E m := fun z => if h : ∃ x ∈ V, x ≠ a₀ ∧ σ.e x = z then
      (1 - σ.τ h.choose) • u a₀ + σ.τ h.choose • u h.choose else 0 with hwdef
  have hwe : ∀ x ∈ V, x ≠ a₀ → w (σ.e x) = (1 - σ.τ x) • u a₀ + σ.τ x • u x := by
    intro x hx hxa
    have h : ∃ x' ∈ V, x' ≠ a₀ ∧ σ.e x' = σ.e x := ⟨x, hx, hxa, rfl⟩
    simp only [hwdef, dif_pos h]
    have hc := h.choose_spec
    rw [σ.e_injOn hcp hc.1 hc.2.1 hx hxa hc.2.2]
  -- bars at `a₀` inside the `2`-faces
  have hbar0 : ∀ x ∈ N, ⟪u x - u a₀, x - a₀⟫ = 0 := by
    intro x hxN
    obtain ⟨hxV, -, G, hG, haG, hxG⟩ := Finset.mem_filter.1 hxN
    have := hu _ (mem_bars2 (show x ∈ R.extremePoints ℝ by rw [hvert]; exact_mod_cast hxV)
      (show a₀ ∈ R.extremePoints ℝ by rw [hvert]; exact_mod_cast ha) hG hxG haG)
    simpa using this
  -- `w` is a motion of the slice framework
  have hwmot : IsMotion (bars2 (convexHull ℝ (σ.W : Set (E m)))
      ((convexHull ℝ (σ.W : Set (E m))).extremePoints ℝ ∪ (J : Set (E m)))) w := by
    intro b hb
    simp only [bars2, Set.mem_iUnion] at hb
    obtain ⟨Φ, ⟨hΦ, hΦ2⟩, z, ⟨hz, hzΦ⟩, z', ⟨hz', hz'Φ⟩, rfl⟩ := hb
    -- both ends are slice points
    have hWpts : ∀ {z : E m}, z ∈ (convexHull ℝ (σ.W : Set (E m))).extremePoints ℝ ∪
        (J : Set (E m)) → ∃ x ∈ V, x ≠ a₀ ∧ σ.e x = z := by
      intro z hz
      rcases hz with hz | hz
      · have := extremePoints_convexHull_subset hz
        rw [σ.coe_W] at this
        obtain ⟨x, ⟨hxV, hxa⟩, rfl⟩ := this
        exact ⟨x, hxV, by simpa using hxa, rfl⟩
      · obtain ⟨x, hxN, rfl⟩ := Finset.mem_image.1 hz
        obtain ⟨hxV, hxa, -⟩ := Finset.mem_filter.1 hxN
        exact ⟨x, hxV, hxa, rfl⟩
    obtain ⟨x, hxV, hxa, rfl⟩ := hWpts hz
    obtain ⟨y, hyV, hya, rfl⟩ := hWpts hz'
    -- the `2`-face of the slice comes from a `3`-face through `a₀`
    rw [← σ.Q_eq'] at hΦ
    obtain ⟨C, hC, haC, hCne, hCH⟩ := σ.exists_face_of_mem_faces hΦ
    have hdC := σ.dim_inter_add_one hC haC hCne
    rw [hCH, hΦ2] at hdC
    have hxC : x ∈ C := (σ.e_mem_iff hC haC hxV hxa).1 (hCH ▸ hzΦ).1
    have hyC : y ∈ C := (σ.e_mem_iff hC haC hyV hya).1 (hCH ▸ hz'Φ).1
    -- `C` is braced
    set T := V.filter (· ∈ C)
    have hCT : C = convexHull ℝ (T : Set (E m)) := face_eq_convexHull_filter hC
    have hbrC := h3 m T (by rw [← hCT]; omega)
    rw [← hCT] at hbrC
    have hmotC : IsMotion (bars2 C (C.extremePoints ℝ)) u := hu.mono (bars2_face_subset hC)
    have hextC : ∀ {p : E m}, p ∈ V → p ∈ C → p ∈ C.extremePoints ℝ := fun hp hpC =>
      inter_extremePoints_subset_extremePoints_of_subset (face_subset hC) ⟨hpC, hcp _ hp⟩
    have h1 := hbrC u hmotC x (hextC hxV hxC) y (hextC hyV hyC)
    have h2 := hbrC u hmotC x (hextC hxV hxC) a₀ (hextC ha haC)
    have h3' := hbrC u hmotC y (hextC hyV hyC) a₀ (hextC ha haC)
    rw [barVal_mk, hwe x hxV hxa, hwe y hyV hya]
    show ⟪((1 - σ.τ x) • u a₀ + σ.τ x • u x) - ((1 - σ.τ y) • u a₀ + σ.τ y • u y),
      (a₀ + σ.τ x • (x - a₀)) - (a₀ + σ.τ y • (y - a₀))⟫ = 0
    rw [transfer (σ.τ x) (σ.τ y) h2 h3', h1, mul_zero]
  have hwpairs := hWJ w hwmot
  -- the pairs of the star
  intro p hp q hq
  have hpq_of : ∀ {x : E m}, x ∈ star R a₀ → x = a₀ ∨ x ∈ N := by
    intro x hx
    rcases hx.2 with h | ⟨G, hG, haG, hxG⟩
    · exact Or.inl h
    · by_cases hxa : x = a₀
      · exact Or.inl hxa
      · right
        have hxV : x ∈ V := by
          have := hx.1; rw [hvert] at this; exact_mod_cast this
        exact Finset.mem_filter.2 ⟨hxV, hxa, G, hG, haG, hxG⟩
  rcases hpq_of hp with rfl | hpN <;> rcases hpq_of hq with rfl | hqN
  · simp
  · have := hbar0 q hqN
    rw [← neg_sub (u q), ← neg_sub q, inner_neg_neg]; exact this
  · exact hbar0 p hpN
  · obtain ⟨hpV, hpa, -⟩ := Finset.mem_filter.1 hpN
    obtain ⟨hqV, hqa, -⟩ := Finset.mem_filter.1 hqN
    have h := hwpairs (σ.e p) (Or.inr (Finset.mem_image_of_mem _ hpN))
      (σ.e q) (Or.inr (Finset.mem_image_of_mem _ hqN))
    rw [hwe p hpV hpa, hwe q hqV hqa] at h
    change ⟪((1 - σ.τ p) • u a₀ + σ.τ p • u p) - ((1 - σ.τ q) • u a₀ + σ.τ q • u q),
      (a₀ + σ.τ p • (p - a₀)) - (a₀ + σ.τ q • (q - a₀))⟫ = 0 at h
    rw [transfer (σ.τ p) (σ.τ q) (hbar0 p hpN) (hbar0 q hqN)] at h
    have hτ : σ.τ p * σ.τ q ≠ 0 := (mul_pos (σ.τ_pos hpV hpa) (σ.τ_pos hqV hqa)).ne'
    exact (mul_eq_zero.1 h).resolve_left hτ

/-- **An edge goes up** at every vertex other than the top one. -/
theorem exists_edge_up {V : Finset (E n)} (hcp : ConvPos V) {c v₁ : E n} (hv₁ : v₁ ∈ V)
    (hc : ∀ x ∈ V, x ≠ v₁ → ⟪c, x⟫ < ⟪c, v₁⟫) {v : E n} (hv : v ∈ V) (hvv : v ≠ v₁) :
    ∃ w ∈ V, ⟪c, v⟫ < ⟪c, w⟫ ∧ ∃ F ∈ faces (convexHull ℝ (V : Set (E n))), dim F = 1 ∧ v ∈ F ∧ w ∈ F := by
  obtain ⟨σ⟩ := exists_vslice (hcp v hv)
  by_contra hcon
  push_neg at hcon
  -- all slice vertices lie below `v`
  have hbelow : ∀ z ∈ σ.Q.extremePoints ℝ, ⟪c, z⟫ ≤ ⟪c, v⟫ := by
    intro z hz
    obtain ⟨y, hyV, hya, rfl, F, hF, hF1, hvF, hyF⟩ := σ.extremePoints_Q hz
    have hle := hcon y hyV
    by_contra hgt
    push_neg at hgt
    have h1 : ⟪c, v⟫ < ⟪c, y⟫ := by
      have e1 : ⟪c, σ.e y⟫ - ⟪c, v⟫ = σ.τ y * (⟪c, y⟫ - ⟪c, v⟫) := by
        rw [← inner_sub_right, σ.e_sub, real_inner_smul_right, inner_sub_right]
      have := σ.τ_pos hyV hya
      nlinarith
    exact absurd (hle h1 F hF hF1 hvF) (fun h => h hyF)
  have hconv : Convex ℝ {z : E n | ⟪c, z⟫ ≤ ⟪c, v⟫} :=
    convex_halfSpace_le ⟨fun x y => inner_add_right _ _ _, fun a x => real_inner_smul_right _ _ _⟩ _
  have hQ : σ.Q ⊆ {z : E n | ⟪c, z⟫ ≤ ⟪c, v⟫} := by
    have hext := convexHull_extremePoints_eq σ.W
    rw [← σ.Q_eq'] at hext
    rw [← hext]
    exact convexHull_min hbelow hconv
  have hv₁Q : σ.e v₁ ∈ σ.Q := by
    rw [σ.Q_eq']
    exact subset_convexHull ℝ _ (by rw [σ.coe_W]; exact ⟨v₁, ⟨hv₁, by simpa using hvv.symm⟩, rfl⟩)
  have h1 := hQ hv₁Q
  simp only [Set.mem_setOf_eq] at h1
  have e1 : ⟪c, σ.e v₁⟫ - ⟪c, v⟫ = σ.τ v₁ * (⟪c, v₁⟫ - ⟪c, v⟫) := by
    rw [← inner_sub_right, σ.e_sub, real_inner_smul_right, inner_sub_right]
  have hτ := σ.τ_pos hv₁ (Ne.symm hvv)
  have h2 := hc v hv hvv
  nlinarith

/-- **Gluing the stars** along edges going up. -/
theorem braces_of_stars {V : Finset (E n)} (hcp : ConvPos V)
    (hdim : 2 ≤ dim (convexHull ℝ (V : Set (E n))))
    (hstar : ∀ v ∈ V, Braces (bars2 (convexHull ℝ (V : Set (E n)))
      ((convexHull ℝ (V : Set (E n))).extremePoints ℝ)) (star (convexHull ℝ (V : Set (E n))) v)) :
    Braces (bars2 (convexHull ℝ (V : Set (E n))) ((convexHull ℝ (V : Set (E n))).extremePoints ℝ))
      ((convexHull ℝ (V : Set (E n))).extremePoints ℝ) := by
  classical
  have hVne : V.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    have h0 : dim (convexHull ℝ ((∅ : Finset (E n)) : Set (E n))) = 0 := by
      rw [Finset.coe_empty, convexHull_empty]; simp [dim]
    omega
  set R := convexHull ℝ (V : Set (E n)) with hR
  set B := bars2 R (R.extremePoints ℝ)
  have hvert : R.extremePoints ℝ = (V : Set (E n)) :=
    Subset.antisymm extremePoints_convexHull_subset (fun x hx => hcp x hx)
  obtain ⟨v₁, hv₁ext⟩ := exists_extremePoint hVne
  have hv₁ : v₁ ∈ V := by exact_mod_cast extremePoints_convexHull_subset hv₁ext
  obtain ⟨c, hc⟩ := exists_dir_of_extreme hv₁ext
  have hext : ∀ {x : E n}, x ∈ V → x ∈ R.extremePoints ℝ := fun hx => hcp _ hx
  have hvsR : vectorSpan ℝ (V : Set (E n)) = vectorSpan ℝ R := by
    rw [← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]
  -- spanning overlaps along an edge
  have hglue : ∀ {v w : E n}, v ∈ V → w ∈ V → v ≠ w →
      (∃ F ∈ faces R, dim F = 1 ∧ v ∈ F ∧ w ∈ F) → ∀ S : Set (E n), S ⊆ R.extremePoints ℝ →
      Braces B (S ∪ star R w) → Braces B (S ∪ star R w ∪ star R v) := by
    intro v w hv hw hvw ⟨F, hF, hF1, hvF, hwF⟩ S hS hSw
    set X := {z | z ∈ V ∧ ∃ G ∈ faces (convexHull ℝ (V : Set (E n))), dim G = 2 ∧ v ∈ G ∧ w ∈ G ∧
      z ∈ G}
    have hspanX : vectorSpan ℝ (V : Set (E n)) ≤ Submodule.span ℝ ((fun z => z - v) '' X) :=
      vectorSpan_le_twoFaces (hext hv) hw hvw.symm hF hF1 hvF hwF hdim
    obtain ⟨G, ⟨hG, hG2⟩, hvG, hwG⟩ := exists_twoFace_of_edge hF hF1 (hext hv) (hext hw) hvw hvF hwF
      hdim
    have hvov : v ∈ (S ∪ star R w) ∩ star R v :=
      ⟨Or.inr ⟨hext hv, Or.inr ⟨G, ⟨hG, hG2⟩, hwG, hvG⟩⟩, mem_star_self (hext hv)⟩
    refine hSw.union (hstar v hv) ⟨v, hvov⟩ ?_
    calc vectorSpan ℝ (S ∪ star R w ∪ star R v)
        ≤ vectorSpan ℝ R := vectorSpan_mono ℝ (by
          rintro x ((hx | hx) | hx)
          · exact (hS hx).1
          · exact hx.1.1
          · exact hx.1.1)
      _ = vectorSpan ℝ (V : Set (E n)) := hvsR.symm
      _ ≤ Submodule.span ℝ ((fun z => z - v) '' X) := hspanX
      _ ≤ vectorSpan ℝ ((S ∪ star R w) ∩ star R v) := by
        rw [Submodule.span_le]
        rintro _ ⟨z, ⟨hzV, G', hG', hG'2, hvG', hwG', hzG'⟩, rfl⟩
        have hzov : z ∈ (S ∪ star R w) ∩ star R v :=
          ⟨Or.inr ⟨hext hzV, Or.inr ⟨G', ⟨hG', hG'2⟩, hwG', hzG'⟩⟩,
            ⟨hext hzV, Or.inr ⟨G', ⟨hG', hG'2⟩, hvG', hzG'⟩⟩⟩
        exact vsub_mem_vectorSpan ℝ hzov hvov
  -- strong induction on the number of vertices above
  set above : E n → ℕ := fun v => (V.filter fun x => ⟪c, v⟫ < ⟪c, x⟫).card
  have hstep : ∀ N, ∀ v ∈ V, above v = N → Braces B (star R v₁ ∪ star R v) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro v hv hN
      by_cases hvv : v = v₁
      · rw [hvv, union_self]; exact hstar v₁ hv₁
      obtain ⟨w, hw, hvw, F, hF, hF1, hvF, hwF⟩ := exists_edge_up hcp hv₁ hc hv hvv
      have hlt : above w < above v := by
        apply Finset.card_lt_card
        refine ⟨fun x hx => ?_, fun h => ?_⟩
        · obtain ⟨hxV, hx⟩ := Finset.mem_filter.1 hx
          exact Finset.mem_filter.2 ⟨hxV, hvw.trans hx⟩
        · have := Finset.mem_filter.1 (h (Finset.mem_filter.2 ⟨hw, hvw⟩))
          exact lt_irrefl _ this.2
      have hw' := ih (above w) (hN ▸ hlt) w hw rfl
      have hne : v ≠ w := fun h => by rw [h] at hvw; exact lt_irrefl _ hvw
      have := hglue hv hw hne ⟨F, hF, hF1, hvF, hwF⟩ (star R v₁) (star_subset R v₁) hw'
      exact this.mono subset_rfl (fun x hx => by
        rcases hx with hx | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inr hx)
  -- the star of `v₁` spans
  have hspan₁ : vectorSpan ℝ R ≤ vectorSpan ℝ (star R v₁) := by
    rw [← hvsR]
    refine (vectorSpan_le_edges hv₁ext).trans ?_
    rw [Submodule.span_le]
    rintro _ ⟨y, ⟨hyV, F, hF, hF1, hv₁F, hyF⟩, rfl⟩
    dsimp only
    by_cases hy : y = v₁
    · rw [hy, sub_self]; exact Submodule.zero_mem _
    obtain ⟨G, hG, hv₁G, hyG⟩ :=
      exists_twoFace_of_edge hF hF1 hv₁ext (hext hyV) (Ne.symm hy) hv₁F hyF hdim
    exact vsub_mem_vectorSpan ℝ ⟨hext hyV, Or.inr ⟨G, hG, hv₁G, hyG⟩⟩ (mem_star_self hv₁ext)
  -- glue everything along the star of `v₁`
  have hall : ∀ s : Finset (E n), s ⊆ V →
      Braces B (star R v₁ ∪ ⋃ v ∈ s, star R v) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using hstar v₁ hv₁
    | insert v s hvs ih =>
      intro hsub
      have h1 := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      have h2 := hstep _ v (hsub (Finset.mem_insert_self v s)) rfl
      have hun := h1.union h2 ⟨v₁, Or.inl (mem_star_self hv₁ext), Or.inl (mem_star_self hv₁ext)⟩
        (by
          calc vectorSpan ℝ ((star R v₁ ∪ ⋃ v ∈ s, star R v) ∪ (star R v₁ ∪ star R v))
              ≤ vectorSpan ℝ R := vectorSpan_mono ℝ (by
                intro x hx
                rcases hx with (hx | hx) | (hx | hx)
                · exact hx.1.1
                · simp only [Set.mem_iUnion] at hx
                  obtain ⟨y, -, hxy⟩ := hx
                  exact hxy.1.1
                · exact hx.1.1
                · exact hx.1.1)
            _ ≤ vectorSpan ℝ (star R v₁) := hspan₁
            _ ≤ vectorSpan ℝ ((star R v₁ ∪ ⋃ v ∈ s, star R v) ∩ (star R v₁ ∪ star R v)) :=
              vectorSpan_mono ℝ (fun x hx => ⟨Or.inl hx, Or.inl hx⟩))
      refine hun.mono subset_rfl (fun x hx => ?_)
      simp only [Finset.set_biUnion_insert, Set.mem_union] at hx
      rcases hx with hx | hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inr (Or.inr hx)
      · exact Or.inl (Or.inr hx)
  refine (hall V subset_rfl).mono subset_rfl (fun x hx => ?_)
  have hxV : x ∈ V := by
    have hx' := hx; rw [hvert] at hx'; exact_mod_cast hx'
  refine Or.inr ?_
  simp only [Set.mem_iUnion]
  exact ⟨x, hxV, mem_star_self hx⟩

/-- **Whiteley's induction step.** -/
theorem w_succ {k : ℕ} (hk : 2 ≤ k) (h3 : WProp 3) (hJ : WJProp k) : WProp (k + 1) := by
  intro m V hdim
  have hV'R : convexHull ℝ (vertFinset V : Set (E m)) = convexHull ℝ (V : Set (E m)) :=
    convexHull_vertFinset V
  have hcp := convPos_vertFinset V
  have hdim' : dim (convexHull ℝ (vertFinset V : Set (E m))) = k + 1 := by rw [hV'R]; exact hdim
  have := braces_of_stars hcp (by rw [hdim']; omega)
    (fun v hv => braces_star hk h3 hJ hcp hdim' hv)
  rwa [hV'R] at this

/-- **Whiteley's theorem in dimension four** (from dimension three). -/
theorem w4_of_w3 (h3 : WProp 3) : WProp 4 := w_succ (by norm_num) h3 (wj_of_w (by norm_num) h3)

/-- **Whiteley's theorem in dimension five** (from dimension three). -/
theorem w5_of_w3 (h3 : WProp 3) : WProp 5 :=
  w_succ (by norm_num) h3 (wj_of_w (by norm_num) (w4_of_w3 h3))

end Kalai5
