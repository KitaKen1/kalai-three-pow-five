import Kalai5.FullProd.TF18c

/-!
# A facet `Δ1 × Δ3` in a cs 5-polytope with eighteen vertices forces 60 edges

**Theorem** (`IsCSPolytope5.edges_ge_60_of_tRow`).  Count
`e ≥ 16 + 16 + #(side edges) + 2 #(edges at z)`: the opposite-sign candidates that are not edges
are covered by the candidates with `z` above at the corner (`CU`) and their mirrors; those give
two edges at `z` each (`adj_opp`); likewise for the same-sign candidates when `γ (oth s0) > 0`.
With `deg z ≥ 5` and the combinatorics (`comb_parallel`, `comb_concurrent`), `e ≥ 60`.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace T18

variable {P F : Set E5} (T : T18 P F)

section cs

variable (hP : IsCSPolytope5 P) (hF : F ∈ faces P) (h4 : dim F = 4)
include hP

omit hP in
lemma nxP (s : Fin 2) (k : Fin 4) (hP : IsCSPolytope5 P) : -T.x s k ∈ P := hP.symm _ (T.xP s k)

lemma nzext : -T.z ∈ P.extremePoints ℝ := hP.neg_mem_extremePoints T.zext

lemma nxext (s : Fin 2) (k : Fin 4) : -T.x s k ∈ P.extremePoints ℝ :=
  hP.neg_mem_extremePoints (T.ext s k)

include hF h4

lemma z_nmem_side (c : Fin 2 × Pr) : T.z ∉ T.side c := fun h => by
  rcases eq_of_extreme_mem_segment T.zext (T.xP _ _) (T.nxP _ _ hP) h with h1 | h1
  · exact T.x_ne_z _ _ h1.symm
  · exact T.nx_ne_z _ _ h1.symm

lemma nz_nmem_side (c : Fin 2 × Pr) : -T.z ∉ T.side c := fun h => by
  rcases eq_of_extreme_mem_segment (T.nzext hP) (T.xP _ _) (T.nxP _ _ hP) h with h1 | h1
  · exact T.x_ne_nz _ _ h1.symm
  · exact T.nx_ne_nz _ _ h1.symm

lemma z_nmem_sideS (p : Pr) : T.z ∉ T.sideS p := fun h => by
  rcases eq_of_extreme_mem_segment T.zext (T.xP _ _) (T.nxP _ _ hP) h with h1 | h1
  · exact T.x_ne_z _ _ h1.symm
  · exact T.nx_ne_z _ _ h1.symm

lemma nz_nmem_sideS (p : Pr) : -T.z ∉ T.sideS p := fun h => by
  rcases eq_of_extreme_mem_segment (T.nzext hP) (T.xP _ _) (T.nxP _ _ hP) h with h1 | h1
  · exact T.x_ne_nz _ _ h1.symm
  · exact T.nx_ne_nz _ _ h1.symm

lemma side_inj (c d : Fin 2 × Pr) (h : T.side c = T.side d) : c = d := by
  have h1 : T.x c.1 c.2.1.1 ∈ T.side d := h ▸ left_mem_segment ℝ _ _
  have h2 : -T.x (oth c.1) c.2.1.2 ∈ T.side d := h ▸ right_mem_segment ℝ _ _
  rcases eq_of_extreme_mem_segment (T.ext _ _) (T.xP _ _) (T.nxP _ _ hP) h1 with e1 | e1
  · rcases eq_of_extreme_mem_segment (T.nxext hP _ _) (T.xP _ _) (T.nxP _ _ hP) h2 with e2 | e2
    · exact absurd e2.symm (T.x_ne_nx hP hF h4 _ _ _ _)
    · have f1 := T.inj _ _ _ _ e1
      have f2 := T.inj _ _ _ _ (neg_injective e2)
      exact Prod.ext f1.1 (Subtype.ext (Prod.ext f1.2 f2.2))
  · exact absurd e1 (T.x_ne_nx hP hF h4 _ _ _ _)

lemma sideS_inj (p q : Pr) (h : T.sideS p = T.sideS q) : p = q := by
  have h1 : T.x T.s0 p.1.1 ∈ T.sideS q := h ▸ left_mem_segment ℝ _ _
  have h2 : -T.x T.s0 p.1.2 ∈ T.sideS q := h ▸ right_mem_segment ℝ _ _
  rcases eq_of_extreme_mem_segment (T.ext _ _) (T.xP _ _) (T.nxP _ _ hP) h1 with e1 | e1
  · rcases eq_of_extreme_mem_segment (T.nxext hP _ _) (T.xP _ _) (T.nxP _ _ hP) h2 with e2 | e2
    · exact absurd e2.symm (T.x_ne_nx hP hF h4 _ _ _ _)
    · have f1 := T.inj _ _ _ _ e1
      have f2 := T.inj _ _ _ _ (neg_injective e2)
      exact Subtype.ext (Prod.ext f1.2 f2.2)
  · exact absurd e1 (T.x_ne_nx hP hF h4 _ _ _ _)

lemma side_ne_sideS (c : Fin 2 × Pr) (p : Pr) : T.side c ≠ T.sideS p := fun h => by
  have h1 : T.x c.1 c.2.1.1 ∈ T.sideS p := h ▸ left_mem_segment ℝ _ _
  have h2 : -T.x (oth c.1) c.2.1.2 ∈ T.sideS p := h ▸ right_mem_segment ℝ _ _
  rcases eq_of_extreme_mem_segment (T.ext _ _) (T.xP _ _) (T.nxP _ _ hP) h1 with e1 | e1
  · rcases eq_of_extreme_mem_segment (T.nxext hP _ _) (T.xP _ _) (T.nxP _ _ hP) h2 with e2 | e2
    · exact T.x_ne_nx hP hF h4 _ _ _ _ e2.symm
    · have f1 := (T.inj _ _ _ _ e1).1
      have f2 := (T.inj _ _ _ _ (neg_injective e2)).1
      rw [f1] at f2
      exact oth_ne _ f2
  · exact T.x_ne_nx hP hF h4 _ _ _ _ e1

lemma zx_inj (a : Fin 2) (b : Fin 4) (a' : Fin 2) (b' : Fin 4)
    (h : segment ℝ T.z (T.x a b) = segment ℝ T.z (T.x a' b')) : (a, b) = (a', b') := by
  have h1 : T.x a b ∈ segment ℝ T.z (T.x a' b') := h ▸ right_mem_segment ℝ _ _
  rcases eq_of_extreme_mem_segment (T.ext _ _) T.zP (T.xP _ _) h1 with e | e
  · exact absurd e (T.x_ne_z _ _)
  · have := T.inj _ _ _ _ e; exact Prod.ext this.1 this.2

lemma znx_inj (a : Fin 2) (b : Fin 4) (a' : Fin 2) (b' : Fin 4)
    (h : segment ℝ T.z (-T.x a b) = segment ℝ T.z (-T.x a' b')) : (a, b) = (a', b') := by
  have h1 : -T.x a b ∈ segment ℝ T.z (-T.x a' b') := h ▸ right_mem_segment ℝ _ _
  rcases eq_of_extreme_mem_segment (T.nxext hP _ _) T.zP (T.nxP _ _ hP) h1 with e | e
  · exact absurd e (T.nx_ne_z _ _)
  · have := T.inj _ _ _ _ (neg_injective e); exact Prod.ext this.1 this.2

lemma zx_ne_znx (a : Fin 2) (b : Fin 4) (a' : Fin 2) (b' : Fin 4) :
    segment ℝ T.z (T.x a b) ≠ segment ℝ T.z (-T.x a' b') := fun h => by
  have h1 : -T.x a' b' ∈ segment ℝ T.z (T.x a b) := h ▸ right_mem_segment ℝ _ _
  rcases eq_of_extreme_mem_segment (T.nxext hP _ _) T.zP (T.xP _ _) h1 with e | e
  · exact T.nx_ne_z _ _ e
  · exact T.x_ne_nx hP hF h4 _ _ _ _ e.symm

end cs

end T18

lemma card_image_pair (U : Finset Pr) (s : Fin 2) (f : Pr → Fin 4) :
    (U.image fun p => (s, f p)).card = (U.image f).card := by
  have e : (U.image fun p => (s, f p)) = (U.image f).image fun k => (s, k) := by
    rw [Finset.image_image]; rfl
  rw [e, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)]

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **A `Δ1 × Δ3` facet in a cs 5-polytope with eighteen vertices forces 60 edges.** -/
theorem IsCSPolytope5.edges_ge_60_of_tRow (hv : fvec P 0 = 18) {F : Set E5} (hF : F ∈ faces P)
    (h4 : dim F = 4) (hrow : faceRow P F = tRow) : 60 ≤ fvec P 1 := by
  classical
  obtain ⟨T⟩ := hP.t18 hv hF h4 hrow
  have hdisj := T18.disj hP hF h4
  have isE_neg : ∀ G : Set E5, (-G ∈ faces P ∧ dim (-G) = 1) → (G ∈ faces P ∧ dim G = 1) :=
    fun G h => by
      have h1 := neg_mem_faces hP.symm h.1
      rw [neg_neg] at h1
      exact ⟨h1, by rw [← dim_neg]; exact h.2⟩
  -- the candidates that are edges, and those with `z` above
  set Eo := Finset.univ.filter
    (fun c : Fin 2 × Pr => T.side c ∈ faces P ∧ dim (T.side c) = 1) with hEo
  set Es := Finset.univ.filter (fun p : Pr => T.sideS p ∈ faces P ∧ dim (T.sideS p) = 1) with hEs
  set Uo := Finset.univ.filter
    (fun c : Fin 2 × Pr => T.CU c ∧ ¬ (T.side c ∈ faces P ∧ dim (T.side c) = 1)) with hUo
  have hcardo : 24 ≤ Eo.card + 2 * Uo.card := by
    have hsplit : Eo.card + (Finset.univ.filter
        (fun c : Fin 2 × Pr => ¬ (T.side c ∈ faces P ∧ dim (T.side c) = 1))).card = 24 := by
      rw [hEo, Finset.card_filter_add_card_filter_not]; rfl
    have hsub : Finset.univ.filter
        (fun c : Fin 2 × Pr => ¬ (T.side c ∈ faces P ∧ dim (T.side c) = 1)) ⊆
        Uo ∪ Uo.image T18.mir := by
      intro c hc
      have hne := (Finset.mem_filter.1 hc).2
      by_cases hu : T.CU c
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hu, hne⟩)
      · have hd : T.CD c := by
          by_contra hd
          exact hne (T.side_edge hP hF h4 c hu hd)
        rw [T.CD_iff] at hd
        have hne' : ¬ (T.side (T18.mir c) ∈ faces P ∧ dim (T.side (T18.mir c)) = 1) := by
          rw [T.side_mir]
          exact fun h => hne (isE_neg _ h)
        exact Finset.mem_union_right _ (Finset.mem_image.2
          ⟨T18.mir c, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd, hne'⟩, T18.mir_mir c⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le Uo (Uo.image T18.mir)
    have h3 : (Uo.image T18.mir).card ≤ Uo.card := Finset.card_image_le
    omega
  -- the edge families
  set E1 := {G : Set E5 | G ∈ faces P ∧ dim G = 1} with hE1
  set EF := {G : Set E5 | G ∈ faces P ∧ G ⊆ F ∧ dim G = 1} with hEF
  set EnF := {G : Set E5 | G ∈ faces P ∧ G ⊆ -F ∧ dim G = 1} with hEnF
  set ESo := T.side '' (Eo : Set (Fin 2 × Pr)) with hESo
  set ESs := T.sideS '' (Es : Set Pr) with hESs
  set EZ := {G : Set E5 | G ∈ faces P ∧ T.z ∈ G ∧ dim G = 1} with hEZ
  set EmZ := (fun G : Set E5 => -G) '' EZ with hEmZ
  have hfin : ∀ S : Set (Set E5), (∀ G ∈ S, G ∈ faces P) → S.Finite :=
    fun S hS => hP.faces_finite.subset hS
  -- `z` and `-z` on the edges at `z`
  have hnzEZ : ∀ G ∈ EZ, -T.z ∉ G := by
    rintro G ⟨hG, hzG, hG1⟩ hnz
    have hGP : G ≠ P := hP.ne_of_dim_ne (by rw [hG1]; norm_num)
    obtain ⟨c, -, hc⟩ := hP.exists_dual hG hGP
    have e1 := (hc _ T.zP).1 hzG
    have e2 := (hc _ (hP.symm _ T.zP)).1 hnz
    rw [inner_neg_left] at e2
    linarith
  have hnzEmZ : ∀ G ∈ EmZ, -T.z ∈ G := by
    rintro _ ⟨G, hG, rfl⟩
    exact Set.neg_mem_neg.2 hG.2.1
  have hzEmZ : ∀ G ∈ EmZ, T.z ∉ G := by
    rintro _ ⟨G, hG, rfl⟩ h
    exact hnzEZ G hG (by simpa using Set.neg_mem_neg.2 h)
  -- memberships
  have hESosub : ESo ⊆ E1 := by
    rintro _ ⟨c, hc, rfl⟩
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
  have hESssub : ESs ⊆ E1 := by
    rintro _ ⟨p, hp, rfl⟩
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
  have hEZsub : EZ ⊆ E1 := fun G hG => ⟨hG.1, hG.2.2⟩
  have hEmZsub : EmZ ⊆ E1 := by
    rintro _ ⟨G, hG, rfl⟩
    exact ⟨neg_mem_faces hP.symm hG.1, by rw [dim_neg]; exact hG.2.2⟩
  -- disjointness
  have hznF' : T.z ∉ -F := fun h => T.nznF (Set.mem_neg.1 h)
  have hnznF' : -T.z ∉ -F := fun h => T.znF (by simpa using Set.mem_neg.1 h)
  have d1 : Disjoint EF EnF := by
    rw [Set.disjoint_left]
    rintro G ⟨hG, hGF, -⟩ ⟨-, hGnF, -⟩
    obtain ⟨y, hy⟩ := hG.1
    exact hdisj y (hGF hy) (Set.mem_neg.1 (hGnF hy))
  have d2 : Disjoint (EF ∪ EnF) ESo := by
    rw [Set.disjoint_left]
    rintro G hG ⟨c, -, rfl⟩
    rcases hG with ⟨-, hGF, -⟩ | ⟨-, hGnF, -⟩
    · exact hdisj _ (T.memF _ _) (by simpa using hGF (right_mem_segment ℝ _ _))
    · exact hdisj _ (T.memF _ _) (Set.mem_neg.1 (hGnF (left_mem_segment ℝ _ _)))
  have d3 : Disjoint (EF ∪ EnF ∪ ESo) ESs := by
    rw [Set.disjoint_left]
    rintro G hG ⟨p, -, rfl⟩
    rcases hG with (⟨-, hGF, -⟩ | ⟨-, hGnF, -⟩) | ⟨c, -, hc⟩
    · exact hdisj _ (T.memF _ _) (by simpa using hGF (right_mem_segment ℝ _ _))
    · exact hdisj _ (T.memF _ _) (Set.mem_neg.1 (hGnF (left_mem_segment ℝ _ _)))
    · exact T.side_ne_sideS hP hF h4 c p hc
  have d4 : Disjoint (EF ∪ EnF ∪ ESo ∪ ESs) EZ := by
    rw [Set.disjoint_left]
    intro G hG hGZ
    have hz := hGZ.2.1
    rcases hG with ((⟨-, hGF, -⟩ | ⟨-, hGnF, -⟩) | ⟨c, -, rfl⟩) | ⟨p, -, rfl⟩
    · exact T.znF (hGF hz)
    · exact hznF' (hGnF hz)
    · exact T.z_nmem_side hP hF h4 c hz
    · exact T.z_nmem_sideS hP hF h4 p hz
  have d5 : Disjoint (EF ∪ EnF ∪ ESo ∪ ESs ∪ EZ) EmZ := by
    rw [Set.disjoint_left]
    intro G hG hGZ
    have hz := hnzEmZ G hGZ
    rcases hG with (((⟨-, hGF, -⟩ | ⟨-, hGnF, -⟩) | ⟨c, -, rfl⟩) | ⟨p, -, rfl⟩) | hG
    · exact T.nznF (hGF hz)
    · exact hnznF' (hGnF hz)
    · exact T.nz_nmem_side hP hF h4 c hz
    · exact T.nz_nmem_sideS hP hF h4 p hz
    · exact hnzEZ G hG hz
  -- cardinalities
  have hEFc : EF.ncard = 16 := congrArg Row.e hrow
  have hEnFc : EnF.ncard = 16 := by
    have h1 : EnF.ncard = cnt P (-F) 1 := rfl
    rw [h1, hP.cnt_neg]
    exact hEFc
  have hESoc : ESo.ncard = Eo.card := by
    rw [hESo, Set.InjOn.ncard_image (fun c _ d _ h => T.side_inj hP hF h4 c d h),
      Set.ncard_coe_finset]
  have hESsc : ESs.ncard = Es.card := by
    rw [hESs, Set.InjOn.ncard_image (fun p _ q _ h => T.sideS_inj hP hF h4 p q h),
      Set.ncard_coe_finset]
  have hEmZc : EmZ.ncard = EZ.ncard := by
    rw [hEmZ]
    exact Set.InjOn.ncard_image (fun G _ G' _ h => by simpa using h)
  have hEFfin : EF.Finite := hfin _ fun G hG => hG.1
  have hEnFfin : EnF.Finite := hfin _ fun G hG => hG.1
  have hESofin : ESo.Finite := (Finset.finite_toSet _).image _
  have hESsfin : ESs.Finite := (Finset.finite_toSet _).image _
  have hEZfin : EZ.Finite := hfin _ fun G hG => hG.1
  have hEmZfin : EmZ.Finite := hEZfin.image _
  have hE1fin : E1.Finite := hfin _ fun G hG => hG.1
  have hsub : EF ∪ EnF ∪ ESo ∪ ESs ∪ EZ ∪ EmZ ⊆ E1 := by
    refine Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
      (Set.union_subset ?_ ?_) hESosub) hESssub) hEZsub) hEmZsub
    · exact fun G hG => ⟨hG.1, hG.2.2⟩
    · exact fun G hG => ⟨hG.1, hG.2.2⟩
  have htot : (EF ∪ EnF ∪ ESo ∪ ESs ∪ EZ ∪ EmZ).ncard =
      32 + Eo.card + Es.card + 2 * EZ.ncard := by
    rw [Set.ncard_union_eq d5 ((((hEFfin.union hEnFfin).union hESofin).union hESsfin).union hEZfin)
        hEmZfin,
      Set.ncard_union_eq d4 (((hEFfin.union hEnFfin).union hESofin).union hESsfin) hEZfin,
      Set.ncard_union_eq d3 ((hEFfin.union hEnFfin).union hESofin) hESsfin,
      Set.ncard_union_eq d2 (hEFfin.union hEnFfin) hESofin,
      Set.ncard_union_eq d1 hEFfin hEnFfin, hEFc, hEnFc, hESoc, hESsc, hEmZc]
    ring
  have hle := Set.ncard_le_ncard hsub hE1fin
  rw [htot] at hle
  have hfv : fvec P 1 = E1.ncard := rfl
  -- the degree of `z`
  have hdeg : 5 ≤ EZ.ncard := hP.five_le_edges_at T.zext
  have hends : ∀ A B : Finset (Fin 2 × Fin 4),
      (∀ i ∈ A, segment ℝ T.z (T.x i.1 i.2) ∈ faces P ∧ dim (segment ℝ T.z (T.x i.1 i.2)) = 1) →
      (∀ i ∈ B, segment ℝ T.z (-T.x i.1 i.2) ∈ faces P ∧
        dim (segment ℝ T.z (-T.x i.1 i.2)) = 1) → A.card + B.card ≤ EZ.ncard := by
    intro A B hA hB
    set SA := (fun i : Fin 2 × Fin 4 => segment ℝ T.z (T.x i.1 i.2)) '' (A : Set (Fin 2 × Fin 4))
    set SB := (fun i : Fin 2 × Fin 4 => segment ℝ T.z (-T.x i.1 i.2)) '' (B : Set (Fin 2 × Fin 4))
    have hSA : SA.ncard = A.card := by
      rw [Set.InjOn.ncard_image (fun i _ j _ h => T.zx_inj hP hF h4 i.1 i.2 j.1 j.2 h),
        Set.ncard_coe_finset]
    have hSB : SB.ncard = B.card := by
      rw [Set.InjOn.ncard_image (fun i _ j _ h => T.znx_inj hP hF h4 i.1 i.2 j.1 j.2 h),
        Set.ncard_coe_finset]
    have hdAB : Disjoint SA SB := by
      rw [Set.disjoint_left]
      rintro _ ⟨i, -, rfl⟩ ⟨j, -, hj⟩
      exact T.zx_ne_znx hP hF h4 i.1 i.2 j.1 j.2 hj.symm
    have hsubZ : SA ∪ SB ⊆ EZ := by
      rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · exact ⟨(hA i hi).1, left_mem_segment ℝ _ _, (hA i hi).2⟩
      · exact ⟨(hB i hi).1, left_mem_segment ℝ _ _, (hB i hi).2⟩
    have := Set.ncard_le_ncard hsubZ hEZfin
    rw [Set.ncard_union_eq hdAB ((Finset.finite_toSet _).image _) ((Finset.finite_toSet _).image _),
      hSA, hSB] at this
    exact this
  -- the two sides of the opposite-sign candidates with `z` above
  set U0 := Finset.univ.filter (fun p : Pr => (T.s0, p) ∈ Uo) with hU0
  set U1 := Finset.univ.filter (fun p : Pr => (oth T.s0, p) ∈ Uo) with hU1
  have hUo : Uo.card = U0.card + U1.card := by
    have e : Uo = (U0.image fun p => (T.s0, p)) ∪ (U1.image fun p => (oth T.s0, p)) := by
      ext c
      obtain ⟨s, p⟩ := c
      simp only [Finset.mem_union, Finset.mem_image, hU0, hU1, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro hc
        by_cases hs : s = T.s0
        · subst hs; exact Or.inl ⟨p, hc, rfl⟩
        · have := eq_oth_of_ne hs; subst this; exact Or.inr ⟨p, hc, rfl⟩
      · rintro (⟨q, hq, he⟩ | ⟨q, hq, he⟩) <;> rw [← he] <;> exact hq
    rw [e, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)]
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hc1
    obtain ⟨q, -, hq⟩ := Finset.mem_image.1 hc2
    exact oth_ne T.s0 (Prod.mk.inj hq).1
  have hCU0 : ∀ p ∈ U0, T.CU (T.s0, p) ∧ ¬ (T.side (T.s0, p) ∈ faces P ∧ dim (T.side (T.s0, p)) = 1) :=
    fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).2).2
  have hCU1 : ∀ p ∈ U1, T.CU (oth T.s0, p) ∧
      ¬ (T.side (oth T.s0, p) ∈ faces P ∧ dim (T.side (oth T.s0, p)) = 1) :=
    fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).2).2
  -- the conflict for `ψ = Asm - Sabs`
  set ψ : Pr → ℝ := fun p => T.Asm p - T.Sabs p with hψ
  have hconf : ∀ p q : Pr, p.1.1 ≠ q.1.1 → p.1.2 ≠ q.1.2 → ψ p + ψ q ≤ 0 := by
    intro p q h1 h2
    have := psi_conflict T.Wc p q h1 h2
    simp only [hψ, T18.Asm, T18.Sabs]
    linarith
  set ξ := T.Zc (oth T.s0) with hξ
  have hA0 : ∀ p : Pr, T.Aop (T.s0, p) = -ξ + T.Asm p := by
    intro p; simp only [T18.Aop, T18.Asm, T.Zc_s0, hξ]; ring
  have hA1 : ∀ p : Pr, T.Aop (oth T.s0, p) = ξ + T.Asm p := by
    intro p; simp only [T18.Aop, T18.Asm, oth_oth, T.Zc_s0, hξ]; ring
  have h0 : ∀ p ∈ U0, 1 ≤ ψ p - ξ := by
    intro p hp
    have := (hCU0 p hp).1
    unfold T18.CU at this
    rw [hA0] at this
    simp only [hψ]
    linarith
  have h1 : ∀ p ∈ U1, 1 ≤ ψ p + ξ := by
    intro p hp
    have := (hCU1 p hp).1
    unfold T18.CU at this
    rw [hA1] at this
    simp only [hψ]
    linarith
  -- adjacency of the endpoints
  have hadj0 : ∀ p ∈ U0,
      (segment ℝ T.z (T.x T.s0 p.1.1) ∈ faces P ∧ dim (segment ℝ T.z (T.x T.s0 p.1.1)) = 1) ∧
      (segment ℝ T.z (-T.x (oth T.s0) p.1.2) ∈ faces P ∧
        dim (segment ℝ T.z (-T.x (oth T.s0) p.1.2)) = 1) :=
    fun p hp => T.adj_opp hP hF h4 (T.s0, p) (hCU0 p hp).1 (hCU0 p hp).2
  have hadj1 : ∀ p ∈ U1,
      (segment ℝ T.z (T.x (oth T.s0) p.1.1) ∈ faces P ∧
        dim (segment ℝ T.z (T.x (oth T.s0) p.1.1)) = 1) ∧
      (segment ℝ T.z (-T.x T.s0 p.1.2) ∈ faces P ∧ dim (segment ℝ T.z (-T.x T.s0 p.1.2)) = 1) := by
    intro p hp
    have := T.adj_opp hP hF h4 (oth T.s0, p) (hCU1 p hp).1 (hCU1 p hp).2
    simp only [oth_oth] at this
    exact this
  by_cases hγ : 0 < T.γ (oth T.s0)
  · -- concurrent: the same-sign candidates
    set Us := Finset.univ.filter
      (fun p : Pr => T.CUs p ∧ ¬ (T.sideS p ∈ faces P ∧ dim (T.sideS p) = 1)) with hUs
    have hcards : 12 ≤ Es.card + 2 * Us.card := by
      have hsplit : Es.card + (Finset.univ.filter
          (fun p : Pr => ¬ (T.sideS p ∈ faces P ∧ dim (T.sideS p) = 1))).card = 12 := by
        rw [hEs, Finset.card_filter_add_card_filter_not]; rfl
      have hsub : Finset.univ.filter
          (fun p : Pr => ¬ (T.sideS p ∈ faces P ∧ dim (T.sideS p) = 1)) ⊆
          Us ∪ Us.image Pr.swap := by
        intro p hp
        have hne := (Finset.mem_filter.1 hp).2
        by_cases hu : T.CUs p
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hu, hne⟩)
        · have hd : T.CDs p := by
            by_contra hd
            exact hne (T.sideS_edge hP hF h4 hγ p hu hd)
          rw [T.CDs_iff] at hd
          have hne' : ¬ (T.sideS p.swap ∈ faces P ∧ dim (T.sideS p.swap) = 1) := by
            rw [T.sideS_swap]
            exact fun h => hne (isE_neg _ h)
          refine Finset.mem_union_right _ (Finset.mem_image.2
            ⟨p.swap, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd, hne'⟩, ?_⟩)
          rfl
      have h1' := Finset.card_le_card hsub
      have h2' := Finset.card_union_le Us (Us.image Pr.swap)
      have h3' : (Us.image Pr.swap).card ≤ Us.card := Finset.card_image_le
      omega
    have hS : ∀ p ∈ Us, 1 ≤ ψ p - |ξ| := by
      intro p hp
      have := (Finset.mem_filter.1 hp).2.1
      unfold T18.CUs at this
      simp only [hψ, hξ]
      linarith
    have hcomb := comb_concurrent ψ ξ hconf U0 U1 Us h0 h1 hS
    -- the endpoints
    set A0 := U0.image fun p => (T.s0, p.1.1) with hA0d
    set B0 := U0.image fun p => (oth T.s0, p.1.2) with hB0d
    set A1 := U1.image fun p => (oth T.s0, p.1.1) with hA1d
    set B1 := U1.image fun p => (T.s0, p.1.2) with hB1d
    have hE0 : A0.card + B0.card ≤ EZ.ncard := by
      refine hends A0 B0 ?_ ?_
      · intro i hi
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
        exact (hadj0 p hp).1
      · intro i hi
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
        exact (hadj0 p hp).2
    have hE1' : A1.card + B1.card ≤ EZ.ncard := by
      refine hends A1 B1 ?_ ?_
      · intro i hi
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
        exact (hadj1 p hp).1
      · intro i hi
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
        exact (hadj1 p hp).2
    have cA0 : A0.card = (U0.image fun p => p.1.1).card := card_image_pair U0 T.s0 _
    have cB0 : B0.card = (U0.image fun p => p.1.2).card := card_image_pair U0 (oth T.s0) _
    have cA1 : A1.card = (U1.image fun p => p.1.1).card := card_image_pair U1 (oth T.s0) _
    have cB1 : B1.card = (U1.image fun p => p.1.2).card := card_image_pair U1 T.s0 _
    set M := max 5 (max ((U0.image fun p => p.1.1).card + (U0.image fun p => p.1.2).card)
        ((U1.image fun p => p.1.1).card + (U1.image fun p => p.1.2).card)) with hM
    have hMle : M ≤ EZ.ncard := by
      refine max_le hdeg (max_le ?_ ?_)
      · rw [← cA0, ← cB0]; exact hE0
      · rw [← cA1, ← cB1]; exact hE1'
    omega
  · -- parallel: `γ (oth s0) = 0`, hence `ξ = 0`
    have hγ0 : T.γ (oth T.s0) = 0 := le_antisymm (not_lt.1 hγ) (T.γnn _)
    have hξ0 : ξ = 0 := by simp only [hξ, T18.Zc, hγ0, zero_mul]
    have h0' : ∀ p ∈ U0, 1 ≤ ψ p := fun p hp => by have := h0 p hp; rw [hξ0] at this; linarith
    have h1' : ∀ p ∈ U1, 1 ≤ ψ p := fun p hp => by have := h1 p hp; rw [hξ0] at this; linarith
    have hcomb := comb_parallel ψ hconf U0 U1 h0' h1'
    set A := (U0.image fun p => (T.s0, p.1.1)) ∪ (U1.image fun p => (oth T.s0, p.1.1)) with hAd
    set B := (U0.image fun p => (oth T.s0, p.1.2)) ∪ (U1.image fun p => (T.s0, p.1.2)) with hBd
    have hE : A.card + B.card ≤ EZ.ncard := by
      refine hends A B ?_ ?_
      · intro i hi
        rcases Finset.mem_union.1 hi with hi | hi
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
          exact (hadj0 p hp).1
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
          exact (hadj1 p hp).1
      · intro i hi
        rcases Finset.mem_union.1 hi with hi | hi
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
          exact (hadj0 p hp).2
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
          exact (hadj1 p hp).2
    have hdisjA : Disjoint (U0.image fun p => (T.s0, p.1.1)) (U1.image fun p => (oth T.s0, p.1.1)) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hi1
      obtain ⟨q, -, hq⟩ := Finset.mem_image.1 hi2
      exact oth_ne T.s0 (Prod.mk.inj hq).1
    have hdisjB : Disjoint (U0.image fun p => (oth T.s0, p.1.2)) (U1.image fun p => (T.s0, p.1.2)) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hi1
      obtain ⟨q, -, hq⟩ := Finset.mem_image.1 hi2
      exact oth_ne T.s0 (Prod.mk.inj hq).1.symm
    have cA : A.card = (U0.image fun p => p.1.1).card + (U1.image fun p => p.1.1).card := by
      rw [hAd, Finset.card_union_of_disjoint hdisjA, card_image_pair, card_image_pair]
    have cB : B.card = (U0.image fun p => p.1.2).card + (U1.image fun p => p.1.2).card := by
      rw [hBd, Finset.card_union_of_disjoint hdisjB, card_image_pair, card_image_pair]
    set M := max 5 ((U0.image fun p => p.1.1).card + (U1.image fun p => p.1.1).card +
      (U0.image fun p => p.1.2).card + (U1.image fun p => p.1.2).card) with hM
    have hMle : M ≤ EZ.ncard := by
      refine max_le hdeg ?_
      have := hE
      rw [cA, cB] at this
      omega
    omega

end cs

end Kalai5
