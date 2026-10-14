import Kalai5.Rigidity.Fan
import Kalai5.Euler.Relations

/-!
# Face facts for the symmetric triangulation

* `inter_mem_faces_of_nonempty`: the intersection of two faces is a face.
* `edge_eq_segment`: an edge is the segment between its two vertices.
* `subset_of_two_vertices`: a face containing two vertices of a `2`-face `G` that are not on a
  common edge contains `G`.
* `ncard_neighbours`: a vertex of a polygon has exactly two neighbours.
* `incid_eq_sum`: `incid P F i j = Σ_{j-faces G ⊆ F} cnt P G i`; `cnt_zero_eq_card`.
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

lemma one_le_dim_of_two_points {S : Set (E n)} {p q : E n} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) : 1 ≤ dim S := by
  by_contra h
  have h0 : dim S = 0 := by omega
  have hbot : vectorSpan ℝ S = ⊥ := Submodule.finrank_eq_zero.1 h0
  have hmem : p -ᵥ q ∈ vectorSpan ℝ S := vsub_mem_vectorSpan ℝ hp hq
  rw [hbot, Submodule.mem_bot, vsub_eq_sub, sub_eq_zero] at hmem
  exact hpq hmem

/-- **The intersection of two faces is a face.** -/
lemma inter_mem_faces_of_nonempty {P F G : Set (E n)} (hF : F ∈ faces P) (hG : G ∈ faces P)
    (hne : (F ∩ G).Nonempty) : F ∩ G ∈ faces P := by
  obtain ⟨l, hl⟩ := exists_functional hF
  obtain ⟨m, hm⟩ := exists_functional hG
  obtain ⟨z, hzF, hzG⟩ := hne
  have hlz : ∀ y ∈ P, l y ≤ l z := by rw [hl] at hzF; exact hzF.2
  have hmz : ∀ y ∈ P, m y ≤ m z := by rw [hm] at hzG; exact hzG.2
  have hzP : z ∈ P := face_subset hF hzF
  refine ⟨⟨z, hzF, hzG⟩, fun _ => ⟨l + m, ?_⟩⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, ContinuousLinearMap.add_apply]
  constructor
  · rintro ⟨hxF, hxG⟩
    have hxP := face_subset hF hxF
    have h1 : ∀ y ∈ P, l y ≤ l x := by rw [hl] at hxF; exact hxF.2
    have h2 : ∀ y ∈ P, m y ≤ m x := by rw [hm] at hxG; exact hxG.2
    exact ⟨hxP, fun y hy => add_le_add (h1 y hy) (h2 y hy)⟩
  · rintro ⟨hxP, hmax⟩
    have h := hmax z hzP
    have h1 := hlz x hxP
    have h2 := hmz x hxP
    refine ⟨?_, ?_⟩
    · rw [hl]; exact ⟨hxP, fun y hy => (hlz y hy).trans (by linarith)⟩
    · rw [hm]; exact ⟨hxP, fun y hy => (hmz y hy).trans (by linarith)⟩

/-- **An edge is the segment between its two vertices.** -/
lemma edge_eq_segment {V : Finset (E n)} {F : Set (E n)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E n)))) (hF1 : dim F = 1) {p q : E n}
    (hp : p ∈ (convexHull ℝ (V : Set (E n))).extremePoints ℝ)
    (hq : q ∈ (convexHull ℝ (V : Set (E n))).extremePoints ℝ) (hpq : p ≠ q) (hpF : p ∈ F)
    (hqF : q ∈ F) : F = convexHull ℝ {p, q} := by
  classical
  set T := V.filter (· ∈ F)
  have hFT : F = convexHull ℝ (T : Set (E n)) := face_eq_convexHull_filter hF
  have h2 := ncard_extremePoints_of_dim_one T (by rw [← hFT]; exact hF1)
  rw [← hFT] at h2
  have hpe : p ∈ F.extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset (face_subset hF) ⟨hpF, hp⟩
  have hqe : q ∈ F.extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset (face_subset hF) ⟨hqF, hq⟩
  have hext : F.extremePoints ℝ = {p, q} := by
    have hsub : ({p, q} : Set (E n)) ⊆ F.extremePoints ℝ := by
      rintro x (rfl | rfl); exacts [hpe, hqe]
    have hfin : (F.extremePoints ℝ).Finite := by rw [hFT]; exact extremePoints_finite T
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [h2, Set.ncard_pair hpq]) hfin).symm
  have := convexHull_extremePoints_eq T
  rw [← hFT, hext] at this
  exact this.symm

/-- A face containing two points of a segment face contains it. -/
lemma convexHull_pair_subset {F : Set (E n)} (hconv : Convex ℝ F) {p q : E n} (hp : p ∈ F)
    (hq : q ∈ F) : convexHull ℝ {p, q} ⊆ F :=
  convexHull_min (by rintro x (rfl | rfl); exacts [hp, hq]) hconv

/-- **A face containing two vertices of a `2`-face not on a common edge contains the `2`-face.** -/
lemma subset_of_two_vertices {V : Finset (E n)} {F G : Set (E n)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E n)))) (hG : G ∈ faces (convexHull ℝ (V : Set (E n))))
    (hG2 : dim G = 2) {p q : E n} (hpq : p ≠ q) (hpF : p ∈ F) (hqF : q ∈ F) (hpG : p ∈ G)
    (hqG : q ∈ G)
    (hnot : ¬ ∃ Ed ∈ faces (convexHull ℝ (V : Set (E n))), dim Ed = 1 ∧ p ∈ Ed ∧ q ∈ Ed) :
    G ⊆ F := by
  have hI := inter_mem_faces_of_nonempty hF hG ⟨p, hpF, hpG⟩
  by_cases hIG : F ∩ G = G
  · rw [← hIG]; exact Set.inter_subset_left
  exfalso
  have hIface : F ∩ G ∈ faces G := mem_faces_of_subset (face_subset hG) hI Set.inter_subset_right
  have hlt := dim_lt_of_mem_faces_ne hIface hIG
  have hge := one_le_dim_of_two_points (S := F ∩ G) ⟨hpF, hpG⟩ ⟨hqF, hqG⟩ hpq
  exact hnot ⟨F ∩ G, hI, by omega, ⟨hpF, hpG⟩, ⟨hqF, hqG⟩⟩

open Classical in
/-- **A vertex of a polygon has exactly two neighbours.** -/
theorem card_neighbours {W : Finset (E n)} (hcp : ConvPos W)
    (h2 : dim (convexHull ℝ (W : Set (E n))) = 2) {a : E n} (ha : a ∈ W) :
    (W.filter fun x => x ≠ a ∧ ∃ F ∈ faces (convexHull ℝ (W : Set (E n))), dim F = 1 ∧ a ∈ F ∧
      x ∈ F).card = 2 := by
  classical
  obtain ⟨σ⟩ := exists_vslice (hcp a ha)
  have hdimQ := σ.dim_Q_add_one (by omega)
  rw [σ.Q_eq', h2] at hdimQ
  have hext := ncard_extremePoints_of_dim_one σ.W (by omega)
  rw [← σ.Q_eq'] at hext
  set Nb := W.filter fun x => x ≠ a ∧ ∃ F ∈ faces (convexHull ℝ (W : Set (E n))), dim F = 1 ∧
    a ∈ F ∧ x ∈ F
  have hinj : Set.InjOn σ.e (Nb : Set (E n)) := by
    intro y hy y' hy' h
    obtain ⟨hyW, hya, -⟩ := Finset.mem_filter.1 hy
    obtain ⟨hy'W, hy'a, -⟩ := Finset.mem_filter.1 hy'
    exact σ.e_injOn hcp hyW hya hy'W hy'a h
  have himg : ((Nb.image σ.e : Finset (E n)) : Set (E n)) = σ.Q.extremePoints ℝ := by
    ext z
    rw [Finset.coe_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyW, hya, F, hF, hF1, haF, hyF⟩ := Finset.mem_filter.1 hy
      exact σ.e_extreme_of_edge hF hF1 haF hyW hya hyF
    · intro hz
      obtain ⟨y, hyW, hya, rfl, F, hF, hF1, haF, hyF⟩ := σ.extremePoints_Q hz
      exact ⟨y, Finset.mem_filter.2 ⟨hyW, hya, F, hF, hF1, haF, hyF⟩, rfl⟩
  rw [← Finset.card_image_of_injOn hinj, ← Set.ncard_coe_finset, himg, hext]

lemma finite_faces_below (V : Finset (E n)) (F : Set (E n)) (j : ℕ) :
    {G | G ∈ faces (convexHull ℝ (V : Set (E n))) ∧ G ⊆ F ∧ dim G = j}.Finite :=
  (faces_finite_convexHull V).subset fun _ hG => hG.1

/-- **Double counting below a face.** -/
lemma incid_eq_sum {V : Finset (E n)} (F : Set (E n)) (i j : ℕ) :
    incid (convexHull ℝ (V : Set (E n))) F i j =
      ∑ G ∈ (finite_faces_below V F j).toFinset, cnt (convexHull ℝ (V : Set (E n))) G i := by
  classical
  have hfin := faces_finite_convexHull V
  have hS : {GH : Set (E n) × Set (E n) | GH.1 ∈ faces (convexHull ℝ (V : Set (E n))) ∧
      GH.2 ∈ faces (convexHull ℝ (V : Set (E n))) ∧ GH.1 ⊆ GH.2 ∧
      GH.2 ⊆ F ∧ dim GH.1 = i ∧ dim GH.2 = j}.Finite :=
    (hfin.prod hfin).subset fun GH h => ⟨h.1, h.2.1⟩
  have hT := finite_faces_below V F j
  rw [incid, Set.ncard_eq_toFinset_card _ hS,
    Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := hT.toFinset)
      (fun GH hGH => by
        rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hGH
        rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        exact ⟨hGH.2.1, hGH.2.2.2.1, hGH.2.2.2.2.2⟩)]
  refine Finset.sum_congr rfl fun G hG => ?_
  have hG' := (Set.Finite.mem_toFinset _).1 hG
  rw [cnt, Set.ncard_eq_toFinset_card _ (hfin.subset fun H hH => hH.1)]
  refine Finset.card_nbij' Prod.fst (fun H => (H, G)) ?_ ?_ ?_ ?_
  · intro GH hGH
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset] at hGH
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    obtain ⟨⟨h1, -, h3, -, h5, -⟩, h⟩ := hGH
    exact ⟨h1, h ▸ h3, h5⟩
  · intro H hH
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hH
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hH.1, hG'.1, hH.2.1, hG'.2.1, hH.2.2, hG'.2.2⟩, rfl⟩
  · intro GH hGH
    rw [Finset.mem_coe, Finset.mem_filter] at hGH
    obtain ⟨-, h⟩ := hGH
    ext <;> simp [h]
  · intro H _; rfl

open Classical in
/-- The vertices of `P` in a face, counted as `0`-faces. -/
lemma cnt_zero_eq_card {V : Finset (E n)} (hcp : ConvPos V) {G : Set (E n)}
    (hG : G ∈ faces (convexHull ℝ (V : Set (E n)))) :
    cnt (convexHull ℝ (V : Set (E n))) G 0 = (V.filter (· ∈ G)).card := by
  classical
  rw [← fvec_face_eq_cnt hG 0]
  have hGT : G = convexHull ℝ ((V.filter (· ∈ G) : Finset (E n)) : Set (E n)) :=
    face_eq_convexHull_filter hG
  have hext : G.extremePoints ℝ = ((V.filter (· ∈ G) : Finset (E n)) : Set (E n)) := by
    apply Subset.antisymm
    · intro x hx
      rw [hGT] at hx
      exact extremePoints_convexHull_subset hx
    · intro x hx
      rw [Finset.coe_filter] at hx
      exact inter_extremePoints_subset_extremePoints_of_subset (face_subset hG) ⟨hx.2, hcp x hx.1⟩
  have h := fvec_zero_eq (V.filter (· ∈ G))
  rw [← hGT, hext, Set.ncard_coe_finset] at h
  exact h

end Kalai5
