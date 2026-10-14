import Kalai5.Alexandrov.Cut
import Kalai5.Euler.Relations

/-!
# Three-dimensional polytopes: vertex figures and Euler

For `R = conv V` with `V` in convex position:

* `facePts V G`: the vertices in a face; adjacency inside a face is adjacency in `R`
  (`mem_nbrs_facePts`).
* the slice polygon at a vertex `a₀` has vertex set `σ.sW = e '' nbrs V a₀`; the `2`-faces through
  `a₀` correspond to its edges (`VSlice.sum_twoFaces`).
* if `dim R = 3`: `#{2-faces ∋ v} = #nbrs v` (`card_twoFaces_at`), `Σ_G #(V ∩ G) = 2 f₁`
  (`sum_facePts_card`), `f₀ - f₁ + f₂ = 2` (`euler3`).
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

open Classical in
/-- The vertices of `V` in `G`. -/
noncomputable def facePts (V : Finset (E n)) (G : Set (E n)) : Finset (E n) := V.filter (· ∈ G)

lemma mem_facePts {V : Finset (E n)} {G : Set (E n)} {x : E n} :
    x ∈ facePts V G ↔ x ∈ V ∧ x ∈ G := by
  classical
  unfold facePts
  rw [Finset.mem_filter]

lemma facePts_eq_filter {V : Finset (E n)} {G : Set (E n)} [DecidablePred (· ∈ G)] :
    facePts V G = V.filter (· ∈ G) := by
  ext x
  rw [mem_facePts, Finset.mem_filter]

lemma facePts_hull {V : Finset (E n)} {G : Set (E n)}
    (hG : G ∈ faces (convexHull ℝ (V : Set (E n)))) : G = convexHull ℝ (facePts V G : Set (E n)) := by
  classical
  rw [facePts_eq_filter]
  exact face_eq_convexHull_filter hG

lemma convPos_facePts {V : Finset (E n)} (hcp : ConvPos V) {G : Set (E n)}
    (hG : G ∈ faces (convexHull ℝ (V : Set (E n)))) : ConvPos (facePts V G) := by
  intro x hx
  rw [← facePts_hull hG]
  obtain ⟨hxV, hxG⟩ := mem_facePts.1 hx
  exact inter_extremePoints_subset_extremePoints_of_subset (face_subset hG) ⟨hxG, hcp x hxV⟩

/-- Adjacency inside a face is adjacency in the polytope. -/
lemma mem_nbrs_facePts {V : Finset (E n)} (hcp : ConvPos V) {G : Set (E n)}
    (hG : G ∈ faces (convexHull ℝ (V : Set (E n)))) {v w : E n} (hv : v ∈ V) (hvG : v ∈ G) :
    w ∈ nbrs (facePts V G) v ↔ w ∈ nbrs V v ∧ w ∈ G := by
  have hGT := facePts_hull hG
  constructor
  · intro h
    obtain ⟨hw, hwv, F, hF, hF1, hvF, hwF⟩ := mem_nbrs.1 h
    obtain ⟨hwV, hwG⟩ := mem_facePts.1 hw
    rw [← hGT] at hF
    exact ⟨mem_nbrs.2 ⟨hwV, hwv, F, faces_trans hG hF, hF1, hvF, hwF⟩, hwG⟩
  · rintro ⟨h, hwG⟩
    obtain ⟨hwV, hwv, F, hF, hF1, hvF, hwF⟩ := mem_nbrs.1 h
    have hseg := edge_eq_segment hF hF1 (hcp v hv) (hcp w hwV) (Ne.symm hwv) hvF hwF
    have hFG : F ⊆ G := by
      rw [hseg]; exact convexHull_pair_subset (face_convex (convex_convexHull ℝ _) hG) hvG hwG
    refine mem_nbrs.2 ⟨mem_facePts.2 ⟨hwV, hwG⟩, hwv, F, ?_, hF1, hvF, hwF⟩
    rw [← hGT]
    exact mem_faces_of_subset (face_subset hG) hF hFG

open Classical in
/-- The bijection between the neighbours of a vertex and the edges through it. -/
lemma card_nbrs_eq_edges {V : Finset (E n)} (hcp : ConvPos V) {x : E n} (hx : x ∈ V) :
    (nbrs V x).card = ((edgeFinset V).filter fun F => x ∈ F).card := by
  classical
  refine Finset.card_bij (fun y _ => convexHull ℝ ({x, y} : Set (E n))) ?_ ?_ ?_
  · intro y hy
    obtain ⟨hyV, hyx, F, hF, hF1, hxF, hyF⟩ := mem_nbrs.1 hy
    have hseg := edge_eq_segment hF hF1 (hcp x hx) (hcp y hyV) (Ne.symm hyx) hxF hyF
    rw [Finset.mem_filter, mem_edgeFinset, ← hseg]
    exact ⟨⟨hF, hF1⟩, hxF⟩
  · intro y hy y' hy' h
    obtain ⟨hy'V, hy'x, -⟩ := mem_nbrs.1 hy'
    obtain ⟨hyV, -, -⟩ := mem_nbrs.1 hy
    have hy'mem : y' ∈ convexHull ℝ ({x, y} : Set (E n)) := by
      rw [h]; exact subset_convexHull ℝ _ (by simp)
    have hsub : convexHull ℝ ({x, y} : Set (E n)) ⊆ convexHull ℝ (V : Set (E n)) :=
      convexHull_min (by
        rintro z (rfl | rfl)
        · exact subset_convexHull ℝ _ (by exact_mod_cast hx)
        · exact subset_convexHull ℝ _ (by exact_mod_cast hyV)) (convex_convexHull ℝ _)
    have hext : y' ∈ (convexHull ℝ ({x, y} : Set (E n))).extremePoints ℝ :=
      inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hy'mem, hcp y' hy'V⟩
    have := extremePoints_convexHull_subset hext
    rcases this with h1 | h1
    · exact absurd h1 hy'x
    · exact (Set.mem_singleton_iff.1 h1).symm
  · intro F hF
    rw [Finset.mem_filter, mem_edgeFinset] at hF
    obtain ⟨⟨hFf, hF1⟩, hxF⟩ := hF
    obtain ⟨p, q, hp, hq, hpq, hseg, hiff⟩ := filter_mem_edge hcp hFf hF1
    rcases (hiff x hx).1 hxF with rfl | rfl
    · exact ⟨q, mem_nbrs.2 ⟨hq, Ne.symm hpq, F, hFf, hF1, hxF, (hiff q hq).2 (Or.inr rfl)⟩,
        hseg.symm⟩
    · exact ⟨p, mem_nbrs.2 ⟨hp, hpq, F, hFf, hF1, hxF, (hiff p hp).2 (Or.inl rfl)⟩,
        by rw [hseg, Set.pair_comm]⟩

open Classical in
/-- An edge contains exactly two vertices. -/
lemma card_filter_mem_edge {V : Finset (E n)} (hcp : ConvPos V) {F : Set (E n)}
    (hF : F ∈ edgeFinset V) : (V.filter fun x => x ∈ F).card = 2 := by
  classical
  rw [mem_edgeFinset] at hF
  obtain ⟨p, q, hp, hq, hpq, -, hiff⟩ := filter_mem_edge hcp hF.1 hF.2
  rw [Finset.card_eq_two]
  refine ⟨p, q, hpq, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hxF⟩; exact (hiff x hx).1 hxF
  · rintro (rfl | rfl)
    · exact ⟨hp, (hiff _ hp).2 (Or.inl rfl)⟩
    · exact ⟨hq, (hiff _ hq).2 (Or.inr rfl)⟩

/-- `Σ_v #nbrs v = 2 f₁`. -/
lemma sum_card_nbrs {V : Finset (E n)} (hcp : ConvPos V) :
    ∑ v ∈ V, (nbrs V v).card = 2 * (edgeFinset V).card := by
  classical
  calc ∑ v ∈ V, (nbrs V v).card
      = ∑ v ∈ V, ∑ F ∈ edgeFinset V, if v ∈ F then 1 else 0 := by
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [card_nbrs_eq_edges hcp hv, Finset.card_filter]
    _ = ∑ F ∈ edgeFinset V, ∑ v ∈ V, if v ∈ F then 1 else 0 := Finset.sum_comm
    _ = ∑ F ∈ edgeFinset V, 2 := by
        refine Finset.sum_congr rfl fun F hF => ?_
        rw [← Finset.card_filter]
        exact card_filter_mem_edge hcp hF
    _ = 2 * (edgeFinset V).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- A polygon has as many edges as vertices. -/
lemma card_edgeFinset_polygon {W : Finset (E n)} (hcp : ConvPos W)
    (h2 : dim (convexHull ℝ (W : Set (E n))) = 2) : (edgeFinset W).card = W.card := by
  classical
  have h := sum_card_nbrs hcp
  rw [Finset.sum_congr rfl fun v hv => card_nbrs hcp h2 hv, Finset.sum_const, smul_eq_mul] at h
  omega

/-! ### The vertex figure -/

namespace VSlice

variable {V : Finset (E n)} {a₀ : E n} (σ : VSlice V a₀)

/-- Faces through `a₀` are determined by their slices. -/
lemma face_eq_of_inter_eq {F G : Set (E n)} (hF : F ∈ faces (convexHull ℝ (V : Set (E n))))
    (hG : G ∈ faces (convexHull ℝ (V : Set (E n)))) (haF : a₀ ∈ F) (haG : a₀ ∈ G)
    (h : F ∩ σ.H = G ∩ σ.H) : F = G := by
  have key : ∀ {F G : Set (E n)}, F ∈ faces (convexHull ℝ (V : Set (E n))) →
      G ∈ faces (convexHull ℝ (V : Set (E n))) → a₀ ∈ F → a₀ ∈ G → F ∩ σ.H = G ∩ σ.H →
      ∀ x ∈ V, x ∈ F → x ∈ G := by
    intro F G hF hG haF haG h x hx hxF
    by_cases hxa : x = a₀
    · rw [hxa]; exact haG
    have : σ.e x ∈ F ∩ σ.H := ⟨(σ.e_mem_iff hF haF hx hxa).2 hxF, σ.e_mem_H hx hxa⟩
    rw [h] at this
    exact (σ.e_mem_iff hG haG hx hxa).1 this.1
  have hfil : facePts V F = facePts V G := by
    ext x
    rw [mem_facePts, mem_facePts]
    exact ⟨fun ⟨hx, hxF⟩ => ⟨hx, key hF hG haF haG h x hx hxF⟩,
      fun ⟨hx, hxG⟩ => ⟨hx, key hG hF haG haF h.symm x hx hxG⟩⟩
  rw [facePts_hull hF, facePts_hull hG, hfil]

/-- The vertices of the slice polygon. -/
noncomputable def sW : Finset (E n) := (nbrs V a₀).image σ.e

lemma extremePoints_Q_eq (hcp : ConvPos V) : σ.Q.extremePoints ℝ = (σ.sW : Set (E n)) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨y, hyV, hya, rfl, F, hF, hF1, haF, hyF⟩ := σ.extremePoints_Q hz
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (mem_nbrs.2 ⟨hyV, hya, F, hF, hF1, haF, hyF⟩))
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hz)
    obtain ⟨hyV, hya, F, hF, hF1, haF, hyF⟩ := mem_nbrs.1 hy
    exact σ.e_extreme_of_edge hF hF1 haF hyV hya hyF

lemma Q_eq_sW (hcp : ConvPos V) : σ.Q = convexHull ℝ (σ.sW : Set (E n)) := by
  rw [← σ.extremePoints_Q_eq hcp, σ.Q_eq', convexHull_extremePoints_eq]

lemma convPos_sW (hcp : ConvPos V) : ConvPos σ.sW := by
  intro x hx
  rw [← σ.Q_eq_sW hcp, σ.extremePoints_Q_eq hcp]
  exact Finset.mem_coe.2 hx

lemma card_sW (hcp : ConvPos V) : σ.sW.card = (nbrs V a₀).card := by
  classical
  refine Finset.card_image_of_injOn fun x hx y hy h => ?_
  obtain ⟨hxV, hxa, -⟩ := mem_nbrs.1 hx
  obtain ⟨hyV, hya, -⟩ := mem_nbrs.1 hy
  exact σ.e_injOn hcp hxV hxa hyV hya h

lemma dim_sW (hcp : ConvPos V) (h3 : dim (convexHull ℝ (V : Set (E n))) = 3) :
    dim (convexHull ℝ (σ.sW : Set (E n))) = 2 := by
  have := σ.dim_Q_add_one (by omega)
  rw [σ.Q_eq_sW hcp] at this
  omega

end VSlice

/-- The `2`-faces. -/
lemma twoFaces_finite (V : Finset (E n)) :
    {F | F ∈ faces (convexHull ℝ (V : Set (E n))) ∧ dim F = 2}.Finite :=
  (faces_finite_convexHull V).subset fun _ h => h.1

noncomputable def twoFinset (V : Finset (E n)) : Finset (Set (E n)) := (twoFaces_finite V).toFinset

lemma mem_twoFinset {V : Finset (E n)} {F : Set (E n)} :
    F ∈ twoFinset V ↔ F ∈ faces (convexHull ℝ (V : Set (E n))) ∧ dim F = 2 :=
  Set.Finite.mem_toFinset _

namespace VSlice

variable {V : Finset (E n)} {a₀ : E n} (σ : VSlice V a₀)

open Classical in
/-- **The `2`-faces through `a₀` correspond to the edges of the slice polygon.** -/
lemma sum_twoFaces (hcp : ConvPos V) (h3 : dim (convexHull ℝ (V : Set (E n))) = 3)
    (g : Set (E n) → ℕ) :
    ∑ G ∈ (twoFinset V).filter (fun G => a₀ ∈ G), g (G ∩ σ.H) = ∑ Φ ∈ edgeFinset σ.sW, g Φ := by
  refine Finset.sum_bij (fun G _ => G ∩ σ.H) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro G hG
    obtain ⟨hGt, haG⟩ := Finset.mem_filter.1 hG
    obtain ⟨hGf, hG2⟩ := mem_twoFinset.1 hGt
    have hne : G ≠ {a₀} := by intro h; rw [h, dim_singleton] at hG2; omega
    rw [mem_edgeFinset, ← σ.Q_eq_sW hcp]
    refine ⟨σ.inter_mem_faces hGf haG hne, ?_⟩
    have := σ.dim_inter_add_one hGf haG hne
    omega
  · intro G hG G' hG' h
    obtain ⟨hGt, haG⟩ := Finset.mem_filter.1 hG
    obtain ⟨hGt', haG'⟩ := Finset.mem_filter.1 hG'
    exact σ.face_eq_of_inter_eq (mem_twoFinset.1 hGt).1 (mem_twoFinset.1 hGt').1 haG haG' h
  · intro Φ hΦ
    rw [mem_edgeFinset, ← σ.Q_eq_sW hcp] at hΦ
    obtain ⟨G, hG, haG, hne, hGH⟩ := σ.exists_face_of_mem_faces hΦ.1
    have hdim := σ.dim_inter_add_one hG haG hne
    rw [hGH, hΦ.2] at hdim
    exact ⟨G, Finset.mem_filter.2 ⟨mem_twoFinset.2 ⟨hG, by omega⟩, haG⟩, hGH⟩

end VSlice

open Classical in
/-- **A vertex of a `3`-polytope lies in as many `2`-faces as edges.** -/
lemma card_twoFaces_at {V : Finset (E n)} (hcp : ConvPos V)
    (h3 : dim (convexHull ℝ (V : Set (E n))) = 3) {v : E n} (hv : v ∈ V) :
    ((twoFinset V).filter fun G => v ∈ G).card = (nbrs V v).card := by
  obtain ⟨σ⟩ := exists_vslice (hcp v hv)
  have h := σ.sum_twoFaces hcp h3 (fun _ => 1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  rw [h, card_edgeFinset_polygon (σ.convPos_sW hcp) (σ.dim_sW hcp h3), σ.card_sW hcp]

open Classical in
/-- `Σ_G #(V ∩ G) = 2 f₁`. -/
lemma sum_facePts_card {V : Finset (E n)} (hcp : ConvPos V)
    (h3 : dim (convexHull ℝ (V : Set (E n))) = 3) :
    ∑ G ∈ twoFinset V, (facePts V G).card = 2 * (edgeFinset V).card := by
  calc ∑ G ∈ twoFinset V, (facePts V G).card
      = ∑ G ∈ twoFinset V, ∑ v ∈ V, if v ∈ G then 1 else 0 := by
        refine Finset.sum_congr rfl fun G _ => ?_
        rw [facePts_eq_filter, Finset.card_filter]
    _ = ∑ v ∈ V, ∑ G ∈ twoFinset V, if v ∈ G then 1 else 0 := Finset.sum_comm
    _ = ∑ v ∈ V, (nbrs V v).card := by
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [← Finset.card_filter]
        exact card_twoFaces_at hcp h3 hv
    _ = 2 * (edgeFinset V).card := sum_card_nbrs hcp

/-- **Euler's formula for `3`-polytopes.** -/
theorem euler3 {V : Finset (E n)} (hcp : ConvPos V) (h3 : dim (convexHull ℝ (V : Set (E n))) = 3) :
    (V.card : ℤ) - (edgeFinset V).card + (twoFinset V).card = 2 := by
  classical
  have hV : V.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, convexHull_empty] at h3
    unfold dim at h3
    rw [vectorSpan_empty, finrank_bot] at h3
    omega
  set R := convexHull ℝ (V : Set (E n)) with hR
  have hRf : R ∈ faces R := ⟨(Finset.coe_nonempty.2 hV).convexHull, IsExposed.refl _⟩
  have hle : ∀ G ∈ faces R, dim G ≤ 3 := fun G hG => by
    rw [← h3]; exact Submodule.finrank_mono (vectorSpan_mono ℝ (face_subset hG))
  have he := euler_fvec hV 3 hle
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at he
  -- the face numbers
  have h0 : fvec R 0 = V.card := by
    rw [fvec_face_eq_cnt hRf 0, cnt_zero_eq_card hcp hRf]
    congr 1
    exact Finset.filter_true_of_mem fun x hx => subset_convexHull ℝ _ (by exact_mod_cast hx)
  have h1 : fvec R 1 = (edgeFinset V).card := by
    rw [fvec, Set.ncard_eq_toFinset_card _ (edges_finite V)]; rfl
  have h2 : fvec R 2 = (twoFinset V).card := by
    rw [fvec, Set.ncard_eq_toFinset_card _ (twoFaces_finite V)]; rfl
  have h3' : fvec R 3 = 1 := by
    rw [fvec, Set.ncard_eq_one]
    refine ⟨R, ?_⟩
    ext G
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hG, hG3⟩
      by_contra hne
      have := dim_lt_of_mem_faces_ne hG hne
      omega
    · rintro rfl; exact ⟨hRf, h3⟩
  rw [h0, h1, h2, h3'] at he
  push_cast at he
  linarith

/-- `Σ_G (#(V ∩ G) - 2) = 2 f₀ - 4`. -/
theorem sum_facePts_sub_two {V : Finset (E n)} (hcp : ConvPos V)
    (h3 : dim (convexHull ℝ (V : Set (E n))) = 3) :
    ∑ G ∈ twoFinset V, ((facePts V G).card : ℤ) = 2 * (twoFinset V).card + 2 * V.card - 4 := by
  have h := sum_facePts_card hcp h3
  have he := euler3 hcp h3
  have h' : ∑ G ∈ twoFinset V, ((facePts V G).card : ℤ) = 2 * (edgeFinset V).card := by
    exact_mod_cast h
  rw [h']
  linarith

end Kalai5
