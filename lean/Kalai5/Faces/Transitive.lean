import Kalai5.Faces.Basic

/-!
# Faces of faces of polytopes

For a polytope `P = conv V` and a face `F` of `P`, the faces of `F` are exactly the faces of `P`
contained in `F` (`mem_faces_face_iff`).  The nontrivial direction perturbs the functional of the
inner face by a large multiple of the functional of `F` (finitely many vertices).
Consequently a facet, viewed as a polytope on its own, has row `faceRow P F`.
-/

namespace Kalai5

open Set

variable {d : ℕ}

/-- A functional that is `≤ c` on a finite set `V` is `≤ c` on `conv V`, and the points where it
equals `c` lie in the hull of the points of `V` where it equals `c`. -/
lemma le_on_convexHull [DecidableEq (E d)] {V : Finset (E d)} (L : StrongDual ℝ (E d)) {c : ℝ}
    (hV : ∀ v ∈ V, L v ≤ c) {x : E d} (hx : x ∈ convexHull ℝ (V : Set (E d))) :
    L x ≤ c ∧ (L x = c →
      x ∈ convexHull ℝ ((V.filter fun v => L v = c : Finset (E d)) : Set (E d))) := by
  obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.1 hx
  have hLx : L x = ∑ v ∈ V, w v * L v := by
    conv_lhs => rw [← hwx]
    simp [map_sum, map_smul]
  have hsum : ∑ v ∈ V, w v * (c - L v) = c - L x := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, hLx]
  have hnn : ∀ v ∈ V, 0 ≤ w v * (c - L v) := fun v hv =>
    mul_nonneg (hw0 v hv) (sub_nonneg.2 (hV v hv))
  refine ⟨by linarith [Finset.sum_nonneg hnn], fun hcx => ?_⟩
  rw [hcx, sub_self] at hsum
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
  have hsupp : ∀ v ∈ V, w v ≠ 0 → L v = c := by
    intro v hv hwv
    rcases mul_eq_zero.1 (hzero v hv) with h | h
    · exact absurd h hwv
    · linarith
  refine Finset.mem_convexHull'.2 ⟨w, fun v hv => hw0 v (Finset.mem_filter.1 hv).1, ?_, ?_⟩
  · rw [Finset.sum_filter_of_ne fun v hv hwv => hsupp v hv hwv]; exact hw1
  · rw [Finset.sum_filter_of_ne fun v hv hwv => hsupp v hv fun h => hwv (by simp [h])]
    exact hwx

/-- **Faces of faces are faces** (for polytopes). -/
lemma faces_trans {V : Finset (E d)} {F G : Set (E d)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E d)))) (hG : G ∈ faces F) :
    G ∈ faces (convexHull ℝ (V : Set (E d))) := by
  classical
  set P := convexHull ℝ (V : Set (E d)) with hPdef
  have hPconv : Convex ℝ P := convex_convexHull ℝ _
  have hFconv : Convex ℝ F := face_convex hPconv hF
  have hGconv : Convex ℝ G := face_convex hFconv hG
  obtain ⟨l, hl⟩ := exists_functional hF
  obtain ⟨m, hm⟩ := exists_functional hG
  obtain ⟨g₀, hg₀⟩ := hG.1
  have hg₀F : g₀ ∈ F := face_subset hG hg₀
  have hg₀P : g₀ ∈ P := face_subset hF hg₀F
  set M := l g₀
  set a := m g₀
  have hlP : ∀ y ∈ P, l y ≤ M := by have := hg₀F; rw [hl] at this; exact this.2
  have hmF : ∀ y ∈ F, m y ≤ a := by have := hg₀; rw [hm] at this; exact this.2
  have hF_iff : ∀ y ∈ P, (y ∈ F ↔ l y = M) := by
    intro y hy; constructor
    · intro hyF; have := hyF; rw [hl] at this; exact le_antisymm (hlP y hy) (this.2 g₀ hg₀P)
    · intro hly; rw [hl]; exact ⟨hy, fun z hz => hly ▸ hlP z hz⟩
  have hG_iff : ∀ y ∈ F, (y ∈ G ↔ m y = a) := by
    intro y hy; constructor
    · intro hyG; have := hyG; rw [hm] at this; exact le_antisymm (hmF y hy) (this.2 g₀ hg₀F)
    · intro hmy; rw [hm]; exact ⟨hy, fun z hz => hmy ▸ hmF z hz⟩
  have hgap : ∀ v ∈ V, v ∉ F → 0 < M - l v := by
    intro v hv hvF
    have hvP : v ∈ P := subset_convexHull ℝ _ hv
    have hle := hlP v hvP
    rcases lt_or_eq_of_le hle with h | h
    · linarith
    · exact absurd ((hF_iff v hvP).2 h) hvF
  set N : ℝ := ∑ v ∈ V.filter (fun v => v ∉ F), (|m v - a| + 1) / (M - l v) with hNdef
  have hterm : ∀ v ∈ V.filter (fun v => v ∉ F), 0 ≤ (|m v - a| + 1) / (M - l v) := by
    intro v hv
    have := hgap v (Finset.mem_filter.1 hv).1 (Finset.mem_filter.1 hv).2
    positivity
  have hN0 : 0 ≤ N := Finset.sum_nonneg hterm
  have hN : ∀ v ∈ V, v ∉ F → m v - a < N * (M - l v) := by
    intro v hv hvF
    have hmem : v ∈ V.filter (fun v => v ∉ F) := Finset.mem_filter.2 ⟨hv, hvF⟩
    have hge : (|m v - a| + 1) / (M - l v) ≤ N := Finset.single_le_sum hterm hmem
    have hpos := hgap v hv hvF
    have : |m v - a| + 1 ≤ N * (M - l v) := by
      rwa [div_le_iff₀ hpos] at hge
    linarith [le_abs_self (m v - a)]
  set L : StrongDual ℝ (E d) := m + N • l
  have hLapp : ∀ y, L y = m y + N * l y := fun y => by
    simp [L, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hLv : ∀ v ∈ V, L v ≤ a + N * M := by
    intro v hv
    have hvP : v ∈ P := subset_convexHull ℝ _ hv
    rw [hLapp]
    by_cases hvF : v ∈ F
    · have := (hF_iff v hvP).1 hvF; have := hmF v hvF; rw [‹l v = M›]; linarith
    · have := hN v hv hvF; nlinarith
  have hLv_eq : ∀ v ∈ V, L v = a + N * M → v ∈ G := by
    intro v hv hLeq
    have hvP : v ∈ P := subset_convexHull ℝ _ hv
    rw [hLapp] at hLeq
    by_cases hvF : v ∈ F
    · have hlv := (hF_iff v hvP).1 hvF
      rw [hlv] at hLeq
      exact (hG_iff v hvF).2 (by linarith)
    · have := hN v hv hvF; nlinarith
  have hLg₀ : L g₀ = a + N * M := by rw [hLapp]
  refine ⟨hG.1, fun _ => ⟨L, ?_⟩⟩
  ext x; constructor
  · intro hx
    have hxF := face_subset hG hx
    have hxP := face_subset hF hxF
    have hLx : L x = a + N * M := by
      rw [hLapp, (hF_iff x hxP).1 hxF, (hG_iff x hxF).1 hx]
    exact ⟨hxP, fun y hy => hLx ▸ (le_on_convexHull L hLv hy).1⟩
  · rintro ⟨hxP, hmax⟩
    have hLx : L x = a + N * M :=
      le_antisymm (le_on_convexHull L hLv hxP).1 (hLg₀ ▸ hmax g₀ hg₀P)
    have hmem := (le_on_convexHull L hLv hxP).2 hLx
    exact convexHull_min (fun v hv => hLv_eq v (Finset.mem_filter.1 hv).1
      (Finset.mem_filter.1 hv).2) hGconv hmem

/-- A face of `P` contained in a face `F` is a face of `F`. -/
lemma mem_faces_of_subset {P F G : Set (E d)} (hFP : F ⊆ P) (hG : G ∈ faces P) (hGF : G ⊆ F) :
    G ∈ faces F := by
  obtain ⟨l, hl⟩ := exists_functional hG
  obtain ⟨g, hg⟩ := hG.1
  have hgmax : ∀ y ∈ P, l y ≤ l g := by have := hg; rw [hl] at this; exact this.2
  refine ⟨hG.1, fun _ => ⟨l, ?_⟩⟩
  ext x; constructor
  · intro hx
    have hx' := hx; rw [hl] at hx'
    exact ⟨hGF hx, fun y hy => hx'.2 y (hFP hy)⟩
  · rintro ⟨hxF, hmax⟩
    rw [hl]
    exact ⟨hFP hxF, fun y hy => le_trans (hgmax y hy) (hmax g (hGF hg))⟩

/-- **The faces of a face `F` of a polytope are the faces of the polytope inside `F`.** -/
lemma mem_faces_face_iff {V : Finset (E d)} {F G : Set (E d)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E d)))) :
    G ∈ faces F ↔ G ∈ faces (convexHull ℝ (V : Set (E d))) ∧ G ⊆ F :=
  ⟨fun hG => ⟨faces_trans hF hG, face_subset hG⟩,
    fun h => mem_faces_of_subset (face_subset hF) h.1 h.2⟩

/-- Counting faces of a face inside the big polytope. -/
lemma fvec_face_eq_cnt {V : Finset (E d)} {F : Set (E d)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E d)))) (k : ℕ) :
    fvec F k = cnt (convexHull ℝ (V : Set (E d))) F k := by
  unfold fvec cnt; congr 1; ext G
  simp only [Set.mem_setOf_eq, mem_faces_face_iff hF, and_assoc]

lemma flag2_face_eq_incid {V : Finset (E d)} {F : Set (E d)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E d)))) (i j : ℕ) :
    flag2 F i j = incid (convexHull ℝ (V : Set (E d))) F i j := by
  unfold flag2 incid; congr 1; ext ⟨G, H⟩
  simp only [Set.mem_setOf_eq, mem_faces_face_iff hF]
  constructor
  · rintro ⟨⟨hG, -⟩, ⟨hH, hHF⟩, hGH, hi, hj⟩; exact ⟨hG, hH, hGH, hHF, hi, hj⟩
  · rintro ⟨hG, hH, hGH, hHF, hi, hj⟩
    exact ⟨⟨hG, hGH.trans hHF⟩, ⟨hH, hHF⟩, hGH, hi, hj⟩

/-- **The row of a face, computed inside the face, equals its row computed in `P`.** -/
lemma rowOf_face {V : Finset (E d)} {F : Set (E d)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E d)))) :
    rowOf F = faceRow (convexHull ℝ (V : Set (E d))) F := by
  simp only [rowOf, faceRow, fvec_face_eq_cnt hF, flag2_face_eq_incid hF]

end Kalai5
