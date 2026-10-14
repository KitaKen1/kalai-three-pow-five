import Kalai5.Rigidity.FaceFacts
import Kalai5.Rigidity.Toric
import Kalai5.Faces.Counting
import Kalai5.Small.Model
import Kalai5.Polar.Relative
import Kalai5.Alexandrov.Poly3

/-!
# `WhiteleyCS` from the three-dimensional theorem

For a centrally symmetric 5-polytope `P`, the bar set `B` consists of the edges of `P` and, for
every `2`-face `G`, the diagonals of the fan triangulation of `G` from an apex `a_G`, the apexes
chosen antipodally (`a_{-G} = -a_G`).

* counts: `#B = f₁ + f₀₂ - 3 f₂`, and the same inside every facet (the fan of `G` has `k - 3`
  diagonals; a diagonal lies in no other `2`-face and on no edge);
* symmetry: `-B = B`, no bar `{p, -p}`;
* rigidity: every motion of `B` keeps the pairs inside each `2`-face (`braces_fan`), hence all
  pairs of vertices (`w5_of_w3`): `IsInfRigid`.

`IsCSPolytope5.whiteleyCS_of_w3 : WProp 3 → WhiteleyCS P`.
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- Two points on a common edge. -/
def OnEdge (R : Set E5) (p q : E5) : Prop := ∃ F ∈ faces R, dim F = 1 ∧ p ∈ F ∧ q ∈ F

open Classical in
/-- The points of `V` in `G`. -/
noncomputable def ptsIn (V : Finset E5) (G : Set E5) : Finset E5 := V.filter (· ∈ G)

lemma mem_ptsIn {V : Finset E5} {G : Set E5} {x : E5} : x ∈ ptsIn V G ↔ x ∈ V ∧ x ∈ G := by
  classical
  unfold ptsIn
  rw [Finset.mem_filter]

lemma filter_eq_ptsIn {V : Finset E5} {G : Set E5} [DecidablePred (· ∈ G)] :
    V.filter (· ∈ G) = ptsIn V G := by
  ext x
  rw [Finset.mem_filter, mem_ptsIn]

open Classical in
/-- The fan diagonals of `G` from `a`. -/
noncomputable def diagFan (R : Set E5) (V : Finset E5) (G : Set E5) (a : E5) : Finset (Sym2 E5) :=
  ((ptsIn V G).filter fun x => x ≠ a ∧ ¬ OnEdge R a x).image fun x => s(a, x)

lemma mem_diagFan {R : Set E5} {V : Finset E5} {G : Set E5} {a : E5} {b : Sym2 E5} :
    b ∈ diagFan R V G a ↔ ∃ x, x ∈ V ∧ x ∈ G ∧ x ≠ a ∧ ¬ OnEdge R a x ∧ b = s(a, x) := by
  classical
  unfold diagFan
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Finset.mem_filter, mem_ptsIn] at hx
    exact ⟨x, hx.1.1, hx.1.2, hx.2.1, hx.2.2, rfl⟩
  · rintro ⟨x, hxV, hxG, hxa, hxe, rfl⟩
    exact ⟨x, Finset.mem_filter.2 ⟨mem_ptsIn.2 ⟨hxV, hxG⟩, hxa, hxe⟩, rfl⟩

lemma ptsIn_hull {V : Finset E5} {G : Set E5} (hG : G ∈ faces (convexHull ℝ (V : Set E5))) :
    G = convexHull ℝ (ptsIn V G : Set E5) := by
  classical
  rw [← filter_eq_ptsIn]
  exact face_eq_convexHull_filter hG

lemma convPos_ptsIn {V : Finset E5} (hcp : ConvPos V) {G : Set E5}
    (hG : G ∈ faces (convexHull ℝ (V : Set E5))) : ConvPos (ptsIn V G) := by
  intro x hx
  rw [← ptsIn_hull hG]
  obtain ⟨hxV, hxG⟩ := mem_ptsIn.1 hx
  exact inter_extremePoints_subset_extremePoints_of_subset (face_subset hG) ⟨hxG, hcp x hxV⟩

/-- **The fan from `a` has `k - 3` diagonals.** -/
lemma card_diagFan {V : Finset E5} (hcp : ConvPos V) {G : Set E5}
    (hG : G ∈ faces (convexHull ℝ (V : Set E5))) (hG2 : dim G = 2) {a : E5} (haV : a ∈ V)
    (haG : a ∈ G) :
    (diagFan (convexHull ℝ (V : Set E5)) V G a).card + 3 = (ptsIn V G).card := by
  classical
  have hGW : G = convexHull ℝ (ptsIn V G : Set E5) := ptsIn_hull hG
  have hcpW : ConvPos (ptsIn V G) := convPos_ptsIn hcp hG
  have hdimW : dim (convexHull ℝ (ptsIn V G : Set E5)) = 2 := by rw [← hGW]; exact hG2
  have haW : a ∈ ptsIn V G := mem_ptsIn.2 ⟨haV, haG⟩
  have hnb := card_neighbours hcpW hdimW haW
  -- adjacency in `G` is adjacency in the polytope
  have hadj : ∀ x ∈ ptsIn V G, x ≠ a →
      ((∃ F ∈ faces (convexHull ℝ (ptsIn V G : Set E5)), dim F = 1 ∧ a ∈ F ∧ x ∈ F) ↔
        OnEdge (convexHull ℝ (V : Set E5)) a x) := by
    intro x hx hxa
    obtain ⟨hxV, hxG⟩ := mem_ptsIn.1 hx
    constructor
    · rintro ⟨F, hF, hF1, haF, hxF⟩
      rw [← hGW] at hF
      exact ⟨F, faces_trans hG hF, hF1, haF, hxF⟩
    · rintro ⟨F, hF, hF1, haF, hxF⟩
      have hFseg := edge_eq_segment hF hF1 (hcp a haV) (hcp x hxV) (Ne.symm hxa) haF hxF
      have hFG : F ⊆ G := by
        rw [hFseg]; exact convexHull_pair_subset (face_convex (convex_convexHull ℝ _) hG) haG hxG
      rw [← hGW]
      exact ⟨F, mem_faces_of_subset (face_subset hG) hF hFG, hF1, haF, hxF⟩
  have hNb : ((ptsIn V G).filter fun x => x ≠ a ∧ OnEdge (convexHull ℝ (V : Set E5)) a x).card
      = 2 := by
    refine Eq.trans ?_ hnb
    congr 1
    exact Finset.filter_congr fun x hx => and_congr_right fun hxa => (hadj x hx hxa).symm
  have hinj : Set.InjOn (fun x => s(a, x))
      ↑((ptsIn V G).filter fun x => x ≠ a ∧ ¬ OnEdge (convexHull ℝ (V : Set E5)) a x) := by
    intro x _ y _ h
    exact Sym2.congr_right.1 h
  have hA := Finset.card_filter_add_card_filter_not (s := (ptsIn V G).erase a)
    (fun x => OnEdge (convexHull ℝ (V : Set E5)) a x)
  rw [Finset.card_erase_of_mem haW] at hA
  have e1 : ((ptsIn V G).erase a).filter (fun x => OnEdge (convexHull ℝ (V : Set E5)) a x) =
      (ptsIn V G).filter fun x => x ≠ a ∧ OnEdge (convexHull ℝ (V : Set E5)) a x := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  have e2 : ((ptsIn V G).erase a).filter (fun x => ¬ OnEdge (convexHull ℝ (V : Set E5)) a x) =
      (ptsIn V G).filter fun x => x ≠ a ∧ ¬ OnEdge (convexHull ℝ (V : Set E5)) a x := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  rw [e1, e2, hNb] at hA
  have hW1 : 1 ≤ (ptsIn V G).card := Finset.card_pos.2 ⟨a, haW⟩
  unfold diagFan
  rw [Finset.card_image_of_injOn hinj]
  omega

open Classical in
/-- `WhiteleyCS` with **local rigidity**: the bars inside every facet and every 3-face brace its
vertices, a `k`-gon contains at most `2k - 3` bars, and a 3-face with `f₀` vertices contains
exactly `3 f₀ - 6` bars (a triangulated 2-sphere). -/
def WhiteleyCSLoc (P : Set E5) : Prop :=
  ∃ B : Finset (Sym2 E5),
    (∀ b ∈ B, ∀ p ∈ b, p ∈ P.extremePoints ℝ) ∧
    (∀ b ∈ B, b.map Neg.neg ∈ B ∧ b.map Neg.neg ≠ b) ∧
    (B.card : ℤ) = fvec P 1 + flag2 P 0 2 - 3 * fvec P 2 ∧
    (∀ F ∈ faces P, dim F = 4 → ((B.filter fun b => ∀ p ∈ b, p ∈ F).card : ℤ) =
      cnt P F 1 + incid P F 0 2 - 3 * cnt P F 2) ∧
    IsInfRigid (P.extremePoints ℝ) (B : Set (Sym2 E5)) ∧
    (∀ F ∈ faces P, dim F = 4 →
      Braces ((B.filter fun b => ∀ p ∈ b, p ∈ F : Finset (Sym2 E5)) : Set (Sym2 E5))
        (F.extremePoints ℝ)) ∧
    (∀ T ∈ faces P, dim T = 3 →
      Braces ((B.filter fun b => ∀ p ∈ b, p ∈ T : Finset (Sym2 E5)) : Set (Sym2 E5))
        (T.extremePoints ℝ)) ∧
    (∀ Q ∈ faces P, dim Q = 2 → (B.filter fun b => ∀ p ∈ b, p ∈ Q).card + 3 ≤ 2 * cnt P Q 0) ∧
    (∀ T ∈ faces P, dim T = 3 → (B.filter fun b => ∀ p ∈ b, p ∈ T).card + 6 = 3 * cnt P T 0)

lemma WhiteleyCSLoc.whiteleyCS {P : Set E5} (h : WhiteleyCSLoc P) : WhiteleyCS P := by
  obtain ⟨B, h1, h2, h3, h4, h5, -⟩ := h
  exact ⟨B, h1, h2, h3, h4, h5⟩

/-- **`WhiteleyCS` with local rigidity, from Alexandrov's theorem in dimension three.** -/
theorem IsCSPolytope5.whiteleyCSLoc_of_w3 {P : Set E5} (hP : IsCSPolytope5 P) (h3 : WProp 3) :
    WhiteleyCSLoc P := by
  classical
  obtain ⟨V0, hV0⟩ := hP.polytope
  subst hV0
  have hRV : convexHull ℝ (vertFinset V0 : Set E5) = convexHull ℝ (V0 : Set E5) :=
    convexHull_vertFinset V0
  have hcp : ConvPos (vertFinset V0) := convPos_vertFinset V0
  rw [← hRV] at hP ⊢
  set V := vertFinset V0
  set R := convexHull ℝ (V : Set E5) with hR
  have hvert : R.extremePoints ℝ = (V : Set E5) :=
    Subset.antisymm extremePoints_convexHull_subset (fun x hx => hcp x hx)
  have hVvert : ∀ {x : E5}, x ∈ V → x ∈ R.extremePoints ℝ := fun hx => hcp _ hx
  have hXV : ∀ {x : E5}, x ∈ R.extremePoints ℝ → x ∈ V := fun {x} hx => by
    rw [← Finset.mem_coe, ← hvert]; exact hx
  have hnegV : ∀ {x : E5}, x ∈ V → -x ∈ V := fun hx =>
    hXV (neg_mem_extremePoints hP.symm (hVvert hx))
  have hdimR : dim R = 5 := hP.dim_self
  have hRconv : Convex ℝ R := convex_convexHull ℝ _
  -- antipodal pairs never share a proper face
  have hne_neg : ∀ {p q : E5}, p ∈ V → (∃ F0 ∈ faces R, dim F0 ≤ 2 ∧ p ∈ F0 ∧ q ∈ F0) →
      s(-p, -q) ≠ s(p, q) := by
    rintro p q hpV ⟨F0, hF0, hF0d, hpF0, hqF0⟩ h
    rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
    · have hp0 : p = 0 := by
        have h2 : (2 : ℝ) • p = 0 := by
          rw [two_smul]; nth_rewrite 1 [← h1]; exact neg_add_cancel p
        rcases smul_eq_zero.1 h2 with h | h
        · norm_num at h
        · exact h
      subst hp0
      exact hP.zero_not_mem_extremePoints (hVvert hpV)
    · have hqF0' : -p ∈ F0 := by rw [h1]; exact hqF0
      have := hP.eq_of_mem_of_neg_mem hF0 hpF0 hqF0'
      rw [this, hdimR] at hF0d
      omega
  /- the edges -/
  have hE1fin := hP.kfaces_finite 1
  set E1 := hE1fin.toFinset with hE1
  have hE1mem : ∀ {F : Set E5}, F ∈ E1 ↔ F ∈ faces R ∧ dim F = 1 := fun {F} =>
    Set.Finite.mem_toFinset _
  have hends : ∀ F ∈ E1, ∃ pq : E5 × E5, pq.1 ∈ V ∧ pq.2 ∈ V ∧ pq.1 ≠ pq.2 ∧ pq.1 ∈ F ∧
      pq.2 ∈ F := by
    intro F hF
    have hF' := hE1mem.1 hF
    obtain ⟨p, q, hp, hq, hpq, hpF, hqF, -⟩ := exists_ends_of_edge hF'.1 hF'.2
    exact ⟨(p, q), hXV hp, hXV hq, hpq, hpF, hqF⟩
  choose! ends hends' using hends
  set edgeBar : Set E5 → Sym2 E5 := fun F => s((ends F).1, (ends F).2) with hedgeBar
  set EB := E1.image edgeBar with hEB
  have hseg : ∀ {F : Set E5}, F ∈ E1 → F = convexHull ℝ {(ends F).1, (ends F).2} := by
    intro F hF
    obtain ⟨h1, h2, h3', h4, h5⟩ := hends' F hF
    have hF' := hE1mem.1 hF
    exact edge_eq_segment hF'.1 hF'.2 (hVvert h1) (hVvert h2) h3' h4 h5
  have hends_eq : ∀ {F : Set E5}, F ∈ E1 → ∀ {p : E5}, p ∈ V → p ∈ F →
      p = (ends F).1 ∨ p = (ends F).2 := by
    intro F hF p hpV hpF
    have hF' := hE1mem.1 hF
    have hpe : p ∈ F.extremePoints ℝ :=
      inter_extremePoints_subset_extremePoints_of_subset (face_subset hF'.1) ⟨hpF, hVvert hpV⟩
    rw [hseg hF] at hpe
    have := extremePoints_convexHull_subset hpe
    simpa using this
  have hmemEB : ∀ b, b ∈ EB ↔ ∃ p ∈ V, ∃ q ∈ V, p ≠ q ∧ b = s(p, q) ∧ OnEdge R p q := by
    intro b
    constructor
    · intro hb
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hb
      obtain ⟨h1, h2, h3', h4, h5⟩ := hends' F hF
      have hF' := hE1mem.1 hF
      exact ⟨_, h1, _, h2, h3', rfl, F, hF'.1, hF'.2, h4, h5⟩
    · rintro ⟨p, hp, q, hq, hpq, rfl, F, hF, hF1, hpF, hqF⟩
      have hFE1 : F ∈ E1 := hE1mem.2 ⟨hF, hF1⟩
      refine Finset.mem_image.2 ⟨F, hFE1, ?_⟩
      show s((ends F).1, (ends F).2) = s(p, q)
      rcases hends_eq hFE1 hp hpF with hp' | hp' <;> rcases hends_eq hFE1 hq hqF with hq' | hq'
      · exact absurd (hp'.trans hq'.symm) hpq
      · rw [hp', hq']
      · rw [hp', hq', Sym2.eq_swap]
      · exact absurd (hp'.trans hq'.symm) hpq
  have hinjE : Set.InjOn edgeBar (E1 : Set (Set E5)) := by
    intro F hF F' hF' h
    rw [hseg hF, hseg hF']
    rcases Sym2.eq_iff.1 h with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · rw [e1, e2, Set.pair_comm]
  have hcardEB : EB.card = fvec R 1 := by
    rw [Finset.card_image_of_injOn hinjE, fvec, Set.ncard_eq_toFinset_card _ hE1fin]
  /- the `2`-faces and their apexes -/
  have hT2fin := hP.kfaces_finite 2
  set T2 := hT2fin.toFinset with hT2
  have hT2mem : ∀ {G : Set E5}, G ∈ T2 ↔ G ∈ faces R ∧ dim G = 2 := fun {G} =>
    Set.Finite.mem_toFinset _
  have hnegT2 : ∀ G ∈ T2, -G ∈ T2 := fun G hG =>
    hT2mem.2 ⟨neg_mem_faces hP.symm (hT2mem.1 hG).1, by rw [dim_neg]; exact (hT2mem.1 hG).2⟩
  have hneT2 : ∀ G ∈ T2, -G ≠ G := fun G hG h => by
    have hG' := hT2mem.1 hG
    have hGR := hP.eq_of_neg_eq hG'.1 h
    have h2 := hG'.2
    rw [hGR, hdimR] at h2
    omega
  obtain ⟨H, -, hHcov, hHdis, -⟩ := exists_half_of_involution (fun G : Set E5 => -G)
    (fun G => neg_neg G) T2.card T2 rfl hnegT2 hneT2
  have hpick : ∀ G ∈ T2, ∃ x, x ∈ V ∧ x ∈ G := fun G hG => by
    have hG' := hT2mem.1 hG
    obtain ⟨y, hy⟩ := hG'.1.1
    rw [ptsIn_hull hG'.1] at hy
    obtain ⟨x, hx⟩ := convexHull_nonempty_iff.1 ⟨y, hy⟩
    exact ⟨x, mem_ptsIn.1 hx⟩
  choose! pick hpickV hpickG using hpick
  set apex : Set E5 → E5 := fun G => if G ∈ H then pick G else -pick (-G) with hapexdef
  have hapex : ∀ G ∈ T2, apex G ∈ V ∧ apex G ∈ G := by
    intro G hG
    by_cases hGH : G ∈ H
    · simp only [hapexdef, if_pos hGH]; exact ⟨hpickV G hG, hpickG G hG⟩
    · simp only [hapexdef, if_neg hGH]
      have hnG := hnegT2 G hG
      exact ⟨hnegV (hpickV _ hnG), Set.mem_neg.1 (hpickG _ hnG)⟩
  have hapexneg : ∀ G ∈ T2, apex (-G) = -apex G := by
    intro G hG
    by_cases hGH : G ∈ H
    · have hnGH : -G ∉ H := hHdis G hGH
      simp only [hapexdef, if_pos hGH, if_neg hnGH, neg_neg]
    · have hnGH : -G ∈ H := (hHcov G hG).resolve_left hGH
      simp only [hapexdef, if_neg hGH, if_pos hnGH, neg_neg]
  set Dg : Set E5 → Finset (Sym2 E5) := fun G => diagFan R V G (apex G) with hDg
  set B := EB ∪ T2.biUnion Dg with hB
  -- diagonals are not edges, and lie in a single `2`-face
  have hdisj1 : Disjoint EB (T2.biUnion Dg) := by
    rw [Finset.disjoint_left]
    intro b hbE hbD
    obtain ⟨G, hG, hbG⟩ := Finset.mem_biUnion.1 hbD
    obtain ⟨x, -, -, -, hxe, rfl⟩ := mem_diagFan.1 hbG
    obtain ⟨p, -, q, -, -, hpq, hedge⟩ := (hmemEB _).1 hbE
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hxe; exact hxe hedge
    · rw [h1, h2] at hxe
      obtain ⟨F, hF, hF1, hpF, hqF⟩ := hedge
      exact hxe ⟨F, hF, hF1, hqF, hpF⟩
  have hdiag_sub : ∀ {G : Set E5}, G ∈ T2 → ∀ {F : Set E5}, F ∈ faces R → ∀ {x : E5},
      x ∈ V → x ∈ G → x ≠ apex G → ¬ OnEdge R (apex G) x → apex G ∈ F → x ∈ F → G ⊆ F := by
    intro G hG F hF x hxV hxG hxa hxe haF hxF
    have hG' := hT2mem.1 hG
    exact subset_of_two_vertices hF hG'.1 hG'.2 (Ne.symm hxa) haF hxF (hapex G hG).2 hxG hxe
  have hdisj2 : (T2 : Set (Set E5)).PairwiseDisjoint Dg := by
    intro G hG G' hG' hne
    show Disjoint (Dg G) (Dg G')
    rw [Finset.disjoint_left]
    intro b hb hb'
    obtain ⟨x, hxV, hxG, hxa, hxe, rfl⟩ := mem_diagFan.1 hb
    obtain ⟨y, hyV, hyG', hya, hye, hb''⟩ := mem_diagFan.1 hb'
    have hG'face := (hT2mem.1 hG').1
    have hGface := (hT2mem.1 hG).1
    rcases Sym2.eq_iff.1 hb'' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hG'a : apex G ∈ G' := by rw [h1]; exact (hapex G' hG').2
      have hG'x : x ∈ G' := by rw [h2]; exact hyG'
      have hGa : apex G' ∈ G := by rw [← h1]; exact (hapex G hG).2
      have hGy : y ∈ G := by rw [← h2]; exact hxG
      exact hne (Subset.antisymm (hdiag_sub hG hG'face hxV hxG hxa hxe hG'a hG'x)
        (hdiag_sub hG' hGface hyV hyG' hya hye hGa hGy))
    · have hG'a : apex G ∈ G' := by rw [h1]; exact hyG'
      have hG'x : x ∈ G' := by rw [h2]; exact (hapex G' hG').2
      have hGa : apex G' ∈ G := by rw [← h2]; exact hxG
      have hGy : y ∈ G := by rw [← h1]; exact (hapex G hG).2
      exact hne (Subset.antisymm (hdiag_sub hG hG'face hxV hxG hxa hxe hG'a hG'x)
        (hdiag_sub hG' hGface hyV hyG' hya hye hGa hGy))
  have hcardD : ∀ G ∈ T2, (Dg G).card + 3 = (ptsIn V G).card := fun G hG =>
    card_diagFan hcp (hT2mem.1 hG).1 (hT2mem.1 hG).2 (hapex G hG).1 (hapex G hG).2
  -- local rigidity: inside a face `F` of dimension `k`, the fans brace the `2`-faces, then `W_k`
  have hlocal : ∀ F ∈ faces R, ∀ k, dim F = k → WProp k →
      Braces ((B.filter fun b => ∀ p ∈ b, p ∈ F : Finset (Sym2 E5)) : Set (Sym2 E5))
        (F.extremePoints ℝ) := by
    intro F hF k hFk hWk
    have hFW := ptsIn_hull hF
    have hdimF : dim (convexHull ℝ (ptsIn V F : Set E5)) = k := by rw [← hFW]; exact hFk
    have hW4 := hWk 5 (ptsIn V F) hdimF
    rw [← hFW] at hW4
    have hFext : IsExtreme ℝ R F := hF.2.isExtreme
    intro u hu
    apply hW4 u
    intro b hb
    simp only [bars2, Set.mem_iUnion] at hb
    obtain ⟨G, ⟨hGF, hG2⟩, p, ⟨hpX, hpG⟩, q, ⟨hqX, hqG⟩, rfl⟩ := hb
    have hG : G ∈ faces R := faces_trans hF hGF
    have hGsub : G ⊆ F := face_subset hGF
    have hGT2 : G ∈ T2 := hT2mem.2 ⟨hG, hG2⟩
    have hGW := ptsIn_hull hG
    have hcpW := convPos_ptsIn hcp hG
    have hdimW : dim (convexHull ℝ (ptsIn V G : Set E5)) = 2 := by rw [← hGW]; exact hG2
    have haW : apex G ∈ ptsIn V G := mem_ptsIn.2 (hapex G hGT2)
    have hfan := braces_fan hcpW hdimW haW
    rw [← hGW] at hfan
    have hinF : ∀ {x y : E5}, x ∈ G → y ∈ G → ∀ z ∈ s(x, y), z ∈ F := by
      intro x y hx hy z hz
      rcases Sym2.mem_iff.1 hz with rfl | rfl
      · exact hGsub hx
      · exact hGsub hy
    have hmot : IsMotion (edgeBars (ptsIn V G : Set E5) G ∪ fanBars (apex G) (ptsIn V G : Set E5))
        u := by
      rintro b (⟨x, hx, y, hy, hxy, rfl, Ed, hE, hE1', hxE, hyE⟩ | ⟨y, hy, rfl⟩)
      · obtain ⟨hxV, hxG⟩ := mem_ptsIn.1 hx
        obtain ⟨hyV, hyG⟩ := mem_ptsIn.1 hy
        exact hu _ (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_union.2 (Or.inl
          ((hmemEB _).2 ⟨x, hxV, y, hyV, hxy, rfl, Ed, faces_trans hG hE, hE1', hxE, hyE⟩)),
          hinF hxG hyG⟩))
      · obtain ⟨hyV, hyG⟩ := mem_ptsIn.1 hy
        by_cases hya : y = apex G
        · rw [hya]; simp
        by_cases hye : OnEdge R (apex G) y
        · exact hu _ (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_union.2 (Or.inl
            ((hmemEB _).2 ⟨apex G, (hapex G hGT2).1, y, hyV, Ne.symm hya, rfl, hye⟩)),
            hinF (hapex G hGT2).2 hyG⟩))
        · exact hu _ (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_union.2 (Or.inr
            (Finset.mem_biUnion.2 ⟨G, hGT2, mem_diagFan.2 ⟨y, hyV, hyG, hya, hye, rfl⟩⟩)),
            hinF (hapex G hGT2).2 hyG⟩))
    have hpR : p ∈ R.extremePoints ℝ := hFext.extremePoints_subset_extremePoints hpX
    have hqR : q ∈ R.extremePoints ℝ := hFext.extremePoints_subset_extremePoints hqX
    have := hfan u hmot p (mem_ptsIn.2 ⟨hXV hpR, hpG⟩) q (mem_ptsIn.2 ⟨hXV hqR, hqG⟩)
    simpa using this

  refine ⟨B, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- endpoints are vertices
    intro b hb p hp
    rcases Finset.mem_union.1 hb with hb | hb
    · obtain ⟨p', hp', q', hq', -, rfl, -⟩ := (hmemEB b).1 hb
      rcases Sym2.mem_iff.1 hp with rfl | rfl
      · exact hVvert hp'
      · exact hVvert hq'
    · obtain ⟨G, hG, hbG⟩ := Finset.mem_biUnion.1 hb
      obtain ⟨x, hxV, -, -, -, rfl⟩ := mem_diagFan.1 hbG
      rcases Sym2.mem_iff.1 hp with rfl | rfl
      · exact hVvert (hapex G hG).1
      · exact hVvert hxV
  · -- symmetry
    intro b hb
    rcases Finset.mem_union.1 hb with hb | hb
    · obtain ⟨p, hp, q, hq, hpq, rfl, F, hF, hF1, hpF, hqF⟩ := (hmemEB b).1 hb
      rw [Sym2.map_mk]
      refine ⟨Finset.mem_union.2 (Or.inl ((hmemEB _).2 ⟨-p, hnegV hp, -q, hnegV hq,
        fun h => hpq (neg_injective h), rfl, -F, neg_mem_faces hP.symm hF,
        by rw [dim_neg]; exact hF1, Set.neg_mem_neg.2 hpF, Set.neg_mem_neg.2 hqF⟩)), ?_⟩
      exact hne_neg hp ⟨F, hF, by omega, hpF, hqF⟩
    · obtain ⟨G, hG, hbG⟩ := Finset.mem_biUnion.1 hb
      obtain ⟨x, hxV, hxG, hxa, hxe, rfl⟩ := mem_diagFan.1 hbG
      rw [Sym2.map_mk]
      refine ⟨Finset.mem_union.2 (Or.inr (Finset.mem_biUnion.2 ⟨-G, hnegT2 G hG, ?_⟩)), ?_⟩
      · rw [show -apex G = apex (-G) from (hapexneg G hG).symm]
        refine mem_diagFan.2 ⟨-x, hnegV hxV, Set.neg_mem_neg.2 hxG, ?_, ?_, rfl⟩
        · rw [hapexneg G hG]; exact fun h => hxa (neg_injective h)
        · rw [hapexneg G hG]
          rintro ⟨F, hF, hF1, haF, hxF⟩
          exact hxe ⟨-F, neg_mem_faces hP.symm hF, by rw [dim_neg]; exact hF1,
            Set.mem_neg.2 haF, Set.mem_neg.2 hxF⟩
      · exact hne_neg (hapex G hG).1 ⟨G, (hT2mem.1 hG).1, (hT2mem.1 hG).2.le, (hapex G hG).2, hxG⟩
  · -- the count
    rw [Finset.card_union_of_disjoint hdisj1, Finset.card_biUnion hdisj2, hcardEB]
    have hflag : flag2 R 0 2 = ∑ G ∈ T2, (ptsIn V G).card := by
      rw [hP.flag2_eq_sum 0 2]
      refine Finset.sum_congr rfl fun G hG => ?_
      rw [cnt_zero_eq_card hcp (hT2mem.1 hG).1, filter_eq_ptsIn]
    have hf2 : fvec R 2 = T2.card := by rw [fvec, Set.ncard_eq_toFinset_card _ hT2fin]
    have hsum : ∑ G ∈ T2, ((Dg G).card : ℤ) = ∑ G ∈ T2, (((ptsIn V G).card : ℤ) - 3) :=
      Finset.sum_congr rfl fun G hG => by have := hcardD G hG; omega
    rw [hflag, hf2]
    push_cast
    rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  · -- the count inside a facet
    intro F hF hF4
    have hFconv : Convex ℝ F := face_convex hRconv hF
    have hsplit : B.filter (fun b => ∀ p ∈ b, p ∈ F) =
        (E1.filter (· ⊆ F)).image edgeBar ∪ (T2.filter (· ⊆ F)).biUnion Dg := by
      ext b
      simp only [hB, Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion]
      constructor
      · rintro ⟨hb | hb, hbF⟩
        · obtain ⟨Ed, hE, rfl⟩ := Finset.mem_image.1 hb
          refine Or.inl ⟨Ed, ⟨hE, ?_⟩, rfl⟩
          rw [hseg hE]
          exact convexHull_pair_subset hFconv (hbF _ (Sym2.mem_mk_left _ _))
            (hbF _ (Sym2.mem_mk_right _ _))
        · obtain ⟨G, hG, hbG⟩ := hb
          obtain ⟨x, hxV, hxG, hxa, hxe, rfl⟩ := mem_diagFan.1 hbG
          exact Or.inr ⟨G, ⟨hG, hdiag_sub hG hF hxV hxG hxa hxe (hbF _ (Sym2.mem_mk_left _ _))
            (hbF _ (Sym2.mem_mk_right _ _))⟩, hbG⟩
      · rintro (⟨Ed, ⟨hE, hEF⟩, rfl⟩ | ⟨G, ⟨hG, hGF⟩, hbG⟩)
        · refine ⟨Or.inl (Finset.mem_image_of_mem _ hE), fun p hp => ?_⟩
          obtain ⟨-, -, -, h4, h5⟩ := hends' Ed hE
          rcases Sym2.mem_iff.1 hp with rfl | rfl
          · exact hEF h4
          · exact hEF h5
        · refine ⟨Or.inr ⟨G, hG, hbG⟩, fun p hp => ?_⟩
          obtain ⟨x, -, hxG, -, -, rfl⟩ := mem_diagFan.1 hbG
          rcases Sym2.mem_iff.1 hp with rfl | rfl
          · exact hGF (hapex G hG).2
          · exact hGF hxG
    have hdisj3 : Disjoint ((E1.filter (· ⊆ F)).image edgeBar) ((T2.filter (· ⊆ F)).biUnion Dg) :=
      hdisj1.mono (Finset.image_subset_image (Finset.filter_subset _ _))
        (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.filter_subset _ _))
    have hdisj4 : ((T2.filter (· ⊆ F) : Finset (Set E5)) : Set (Set E5)).PairwiseDisjoint Dg :=
      hdisj2.subset (Finset.coe_subset.2 (Finset.filter_subset _ _))
    have hinjE' : Set.InjOn edgeBar ((E1.filter (· ⊆ F) : Finset (Set E5)) : Set (Set E5)) :=
      hinjE.mono (Finset.coe_subset.2 (Finset.filter_subset _ _))
    rw [hsplit, Finset.card_union_of_disjoint hdisj3, Finset.card_biUnion hdisj4,
      Finset.card_image_of_injOn hinjE']
    -- the face counts below `F`
    have hc1 : cnt R F 1 = (E1.filter (· ⊆ F)).card := by
      rw [cnt, Set.ncard_eq_toFinset_card _ (finite_faces_below V F 1)]
      congr 1
      ext Ed
      rw [Set.Finite.mem_toFinset, Finset.mem_filter, hE1mem]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
      · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, h2, h3⟩
    have hc2 : cnt R F 2 = (T2.filter (· ⊆ F)).card := by
      rw [cnt, Set.ncard_eq_toFinset_card _ (finite_faces_below V F 2)]
      congr 1
      ext G
      rw [Set.Finite.mem_toFinset, Finset.mem_filter, hT2mem]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
      · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, h2, h3⟩
    have hi : incid R F 0 2 = ∑ G ∈ T2.filter (· ⊆ F), (ptsIn V G).card := by
      rw [incid_eq_sum]
      have e : (finite_faces_below V F 2).toFinset = T2.filter (· ⊆ F) := by
        ext G
        rw [Set.Finite.mem_toFinset, Finset.mem_filter, hT2mem]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
        · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, h2, h3⟩
      rw [e]
      refine Finset.sum_congr rfl fun G hG => ?_
      rw [cnt_zero_eq_card hcp (hT2mem.1 (Finset.mem_filter.1 hG).1).1, filter_eq_ptsIn]
    have hsum : ∑ G ∈ T2.filter (· ⊆ F), ((Dg G).card : ℤ) =
        ∑ G ∈ T2.filter (· ⊆ F), (((ptsIn V G).card : ℤ) - 3) :=
      Finset.sum_congr rfl fun G hG => by have := hcardD G (Finset.mem_filter.1 hG).1; omega
    rw [hc1, hc2, hi]
    push_cast
    rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  · -- rigidity
    have hW5 := w5_of_w3 h3 5 V hdimR
    have hbr : Braces (B : Set (Sym2 E5)) (R.extremePoints ℝ) := by
      intro u hu
      apply hW5 u
      intro b hb
      simp only [bars2, Set.mem_iUnion] at hb
      obtain ⟨G, ⟨hG, hG2⟩, p, ⟨hpX, hpG⟩, q, ⟨hqX, hqG⟩, rfl⟩ := hb
      have hGT2 : G ∈ T2 := hT2mem.2 ⟨hG, hG2⟩
      -- the fan of `G` is braced
      have hGW := ptsIn_hull hG
      have hcpW := convPos_ptsIn hcp hG
      have hdimW : dim (convexHull ℝ (ptsIn V G : Set E5)) = 2 := by rw [← hGW]; exact hG2
      have haW : apex G ∈ ptsIn V G := mem_ptsIn.2 (hapex G hGT2)
      have hfan := braces_fan hcpW hdimW haW
      rw [← hGW] at hfan
      have hmot : IsMotion (edgeBars (ptsIn V G : Set E5) G ∪ fanBars (apex G) (ptsIn V G : Set E5))
          u := by
        rintro b (⟨x, hx, y, hy, hxy, rfl, Ed, hE, hE1', hxE, hyE⟩ | ⟨y, hy, rfl⟩)
        · obtain ⟨hxV, -⟩ := mem_ptsIn.1 hx
          obtain ⟨hyV, -⟩ := mem_ptsIn.1 hy
          exact hu _ (Finset.mem_coe.2 (Finset.mem_union.2 (Or.inl ((hmemEB _).2
            ⟨x, hxV, y, hyV, hxy, rfl, Ed, faces_trans hG hE, hE1', hxE, hyE⟩))))
        · obtain ⟨hyV, hyG⟩ := mem_ptsIn.1 hy
          by_cases hya : y = apex G
          · rw [hya]; simp
          by_cases hye : OnEdge R (apex G) y
          · exact hu _ (Finset.mem_coe.2 (Finset.mem_union.2 (Or.inl ((hmemEB _).2
              ⟨apex G, (hapex G hGT2).1, y, hyV, Ne.symm hya, rfl, hye⟩))))
          · exact hu _ (Finset.mem_coe.2 (Finset.mem_union.2 (Or.inr (Finset.mem_biUnion.2
              ⟨G, hGT2, mem_diagFan.2 ⟨y, hyV, hyG, hya, hye, rfl⟩⟩))))
      have := hfan u hmot p (mem_ptsIn.2 ⟨hXV hpX, hpG⟩) q (mem_ptsIn.2 ⟨hXV hqX, hqG⟩)
      simpa using this
    have hne : (R.extremePoints ℝ).Nonempty := by
      rw [hvert]
      obtain ⟨x, hx⟩ := hP.nonempty
      exact convexHull_nonempty_iff.1 ⟨x, hx⟩
    have hspan : vectorSpan ℝ (R.extremePoints ℝ) = ⊤ := by
      have h1 : vectorSpan ℝ (R.extremePoints ℝ) = vectorSpan ℝ R := by
        rw [hvert, ← direction_affineSpan, ← direction_affineSpan, hR, affineSpan_convexHull]
      rw [h1]
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_euclideanSpace_fin]
      exact hdimR
    exact hbr.isInfRigid hne hspan
  · -- facets
    intro F hF hF4
    exact hlocal F hF 4 hF4 (w4_of_w3 h3)
  · -- three-faces
    intro T hT hT3
    exact hlocal T hT 3 hT3 h3
  · -- bars inside a `2`-face: its edges and the diagonals of its own fan
    intro Q hQ hQ2
    have hQconv : Convex ℝ Q := face_convex hRconv hQ
    have hQT2 : Q ∈ T2 := hT2mem.2 ⟨hQ, hQ2⟩
    have hsub : B.filter (fun b => ∀ p ∈ b, p ∈ Q) ⊆ (E1.filter (· ⊆ Q)).image edgeBar ∪ Dg Q := by
      intro b hb
      rw [Finset.mem_filter] at hb
      obtain ⟨hbB, hbQ⟩ := hb
      rcases Finset.mem_union.1 hbB with hbE | hbD
      · obtain ⟨Ed, hE, rfl⟩ := Finset.mem_image.1 hbE
        refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨Ed, Finset.mem_filter.2 ⟨hE, ?_⟩, rfl⟩)
        rw [hseg hE]
        exact convexHull_pair_subset hQconv (hbQ _ (Sym2.mem_mk_left _ _))
          (hbQ _ (Sym2.mem_mk_right _ _))
      · obtain ⟨G, hG, hbG⟩ := Finset.mem_biUnion.1 hbD
        obtain ⟨x, hxV, hxG, hxa, hxe, rfl⟩ := mem_diagFan.1 hbG
        have hGQ : G ⊆ Q := hdiag_sub hG hQ hxV hxG hxa hxe (hbQ _ (Sym2.mem_mk_left _ _))
          (hbQ _ (Sym2.mem_mk_right _ _))
        have hGeq : G = Q := by
          by_contra hne
          have hG' : G ∈ faces Q := (mem_faces_face_iff hQ).2 ⟨(hT2mem.1 hG).1, hGQ⟩
          have := dim_lt_of_mem_faces_ne hG' hne
          rw [(hT2mem.1 hG).2, hQ2] at this
          omega
        rw [hGeq] at hbG ⊢
        exact Finset.mem_union_right _ hbG
    have hcard := Finset.card_le_card hsub
    have h1 := Finset.card_union_le ((E1.filter (· ⊆ Q)).image edgeBar) (Dg Q)
    have hc1 : cnt R Q 1 = (E1.filter (· ⊆ Q)).card := by
      rw [cnt, Set.ncard_eq_toFinset_card _ (finite_faces_below V Q 1)]
      congr 1
      ext Ed
      rw [Set.Finite.mem_toFinset, Finset.mem_filter, hE1mem]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
      · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, h2, h3⟩
    have h2 : ((E1.filter (· ⊆ Q)).image edgeBar).card ≤ cnt R Q 1 := by
      rw [hc1]; exact Finset.card_image_le
    have h3' := hcardD Q hQT2
    have h4 : cnt R Q 1 = cnt R Q 0 := cnt_one_eq_cnt_zero hQ hQ2
    have h5 : (ptsIn V Q).card = cnt R Q 0 := by
      rw [cnt_zero_eq_card hcp hQ, filter_eq_ptsIn]
    omega
  · -- bars inside a 3-face: edges and fans of its 2-faces, `3 f₀ - 6` of them
    intro T hT hT3
    have hTconv : Convex ℝ T := face_convex hRconv hT
    have hsplit : B.filter (fun b => ∀ p ∈ b, p ∈ T) =
        (E1.filter (· ⊆ T)).image edgeBar ∪ (T2.filter (· ⊆ T)).biUnion Dg := by
      ext b
      simp only [hB, Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion]
      constructor
      · rintro ⟨hb | hb, hbT⟩
        · obtain ⟨Ed, hE, rfl⟩ := Finset.mem_image.1 hb
          refine Or.inl ⟨Ed, ⟨hE, ?_⟩, rfl⟩
          rw [hseg hE]
          exact convexHull_pair_subset hTconv (hbT _ (Sym2.mem_mk_left _ _))
            (hbT _ (Sym2.mem_mk_right _ _))
        · obtain ⟨G, hG, hbG⟩ := hb
          obtain ⟨x, hxV, hxG, hxa, hxe, rfl⟩ := mem_diagFan.1 hbG
          exact Or.inr ⟨G, ⟨hG, hdiag_sub hG hT hxV hxG hxa hxe (hbT _ (Sym2.mem_mk_left _ _))
            (hbT _ (Sym2.mem_mk_right _ _))⟩, hbG⟩
      · rintro (⟨Ed, ⟨hE, hET⟩, rfl⟩ | ⟨G, ⟨hG, hGT⟩, hbG⟩)
        · refine ⟨Or.inl (Finset.mem_image_of_mem _ hE), fun p hp => ?_⟩
          obtain ⟨-, -, -, h4, h5⟩ := hends' Ed hE
          rcases Sym2.mem_iff.1 hp with rfl | rfl
          · exact hET h4
          · exact hET h5
        · refine ⟨Or.inr ⟨G, hG, hbG⟩, fun p hp => ?_⟩
          obtain ⟨x, -, hxG, -, -, rfl⟩ := mem_diagFan.1 hbG
          rcases Sym2.mem_iff.1 hp with rfl | rfl
          · exact hGT (hapex G hG).2
          · exact hGT hxG
    have hdisj3 : Disjoint ((E1.filter (· ⊆ T)).image edgeBar) ((T2.filter (· ⊆ T)).biUnion Dg) :=
      hdisj1.mono (Finset.image_subset_image (Finset.filter_subset _ _))
        (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.filter_subset _ _))
    have hdisj4 : ((T2.filter (· ⊆ T) : Finset (Set E5)) : Set (Set E5)).PairwiseDisjoint Dg :=
      hdisj2.subset (Finset.coe_subset.2 (Finset.filter_subset _ _))
    have hinjE' : Set.InjOn edgeBar ((E1.filter (· ⊆ T) : Finset (Set E5)) : Set (Set E5)) :=
      hinjE.mono (Finset.coe_subset.2 (Finset.filter_subset _ _))
    rw [hsplit, Finset.card_union_of_disjoint hdisj3, Finset.card_biUnion hdisj4,
      Finset.card_image_of_injOn hinjE']
    -- the vertices of `T` and its own face lattice
    set W := ptsIn V T with hWdef
    have hTW : T = convexHull ℝ (W : Set E5) := ptsIn_hull hT
    have hcpW : ConvPos W := convPos_ptsIn hcp hT
    have hdimW : dim (convexHull ℝ (W : Set E5)) = 3 := by rw [← hTW]; exact hT3
    have hfacesT : ∀ G, G ∈ faces (convexHull ℝ (W : Set E5)) ↔ G ∈ faces R ∧ G ⊆ T := by
      intro G; rw [← hTW]; exact mem_faces_face_iff hT
    have hE : E1.filter (· ⊆ T) = edgeFinset W := by
      ext Ed
      rw [Finset.mem_filter, hE1mem, mem_edgeFinset, hfacesT]
      tauto
    have hF2 : T2.filter (· ⊆ T) = twoFinset W := by
      ext G
      rw [Finset.mem_filter, hT2mem, mem_twoFinset, hfacesT]
      tauto
    have hpts : ∀ G ∈ twoFinset W, (ptsIn V G).card = (facePts W G).card := by
      intro G hG
      congr 1
      ext x
      have hGT : G ⊆ T := ((hfacesT G).1 (mem_twoFinset.1 hG).1).2
      rw [mem_ptsIn, mem_facePts, mem_ptsIn]
      constructor
      · rintro ⟨hxV, hxG⟩; exact ⟨⟨hxV, hGT hxG⟩, hxG⟩
      · rintro ⟨⟨hxV, -⟩, hxG⟩; exact ⟨hxV, hxG⟩
    have hsumW := sum_facePts_sub_two hcpW hdimW
    have heul := euler3 hcpW hdimW
    have hc0 : cnt R T 0 = W.card := by rw [cnt_zero_eq_card hcp hT, filter_eq_ptsIn]
    rw [hc0, hE, hF2]
    have hsum : ∑ G ∈ twoFinset W, ((Dg G).card : ℤ) =
        ∑ G ∈ twoFinset W, (((facePts W G).card : ℤ) - 3) := by
      refine Finset.sum_congr rfl fun G hG => ?_
      have hGT2 : G ∈ T2 := (Finset.mem_filter.1 (hF2.symm ▸ hG)).1
      have h1 := hcardD G hGT2
      rw [hpts G hG] at h1
      omega
    have key : ((edgeFinset W).card : ℤ) + ∑ G ∈ twoFinset W, ((Dg G).card : ℤ) + 6 =
        3 * W.card := by
      rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hsumW]
      push_cast
      linarith
    exact_mod_cast key

/-- **`WhiteleyCS` from Alexandrov's theorem in dimension three.** -/
theorem IsCSPolytope5.whiteleyCS_of_w3 {P : Set E5} (hP : IsCSPolytope5 P) (h3 : WProp 3) :
    WhiteleyCS P :=
  (hP.whiteleyCSLoc_of_w3 h3).whiteleyCS

end Kalai5
