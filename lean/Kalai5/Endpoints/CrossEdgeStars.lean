import Kalai5.Endpoints.PyramidApexEdges

namespace Kalai5
open Set
open scoped Classical

/-- Edges joining an apex to a prescribed set of other vertices. -/
def crossEdgeStar (P F a : Set E5) (U : Set (Set E5)) : Set (Set E5) :=
  {e | e ∈ edgeSet P F ∧ ∃ v ∈ U, vset P e = {a,v}}

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.cross_edge_star_lower {F a : Set E5} {U : Set (Set E5)}
    (haU : a ∉ U)
    (hjoin : ∀ v ∈ U, ∃ e, e ∈ edgeSet P F ∧ vset P e = {a,v}) :
    U.ncard ≤ (crossEdgeStar P F a U).ncard := by
  choose e he hve using hjoin
  let f : U → crossEdgeStar P F a U := fun v =>
    ⟨e v.val v.property,he v.val v.property,v.val,v.property,hve v.val v.property⟩
  have hinj : Function.Injective f := by
    intro v w heq
    have hew : e v.val v.property = e w.val w.property := congrArg Subtype.val heq
    have hv : v.val ∈ vset P (e w.val w.property) := by
      rw [← hew,hve v.val v.property]; exact Or.inr rfl
    rw [hve w.val w.property] at hv
    apply Subtype.ext
    exact hv.resolve_left (fun h => haU (h ▸ v.property))
  let hf : (crossEdgeStar P F a U).Finite := hP.faces_finite.subset fun e he => he.1.1
  letI := hf.fintype
  have hc := Nat.card_le_card_of_injective f hinj
  simpa only [Nat.card_coe_set_eq] using hc

theorem IsCSPolytope5.cross_edge_star_avoids_core {F T R a : Set E5} {U : Set (Set E5)}
    (haR : a ∉ vset P R) (hUT : ∀ v ∈ U, v ∉ vset P T) :
    Disjoint (edgeSet P T ∪ edgeSet P R) (crossEdgeStar P F a U) := by
  rw [Set.disjoint_left]
  rintro e he ⟨_,v,hv,hve⟩
  rcases he with he | he
  · apply hUT v hv
    apply vset_mono' he.2.1
    rw [hve]; exact Or.inr rfl
  · apply haR
    apply vset_mono' he.2.1
    rw [hve]; exact Or.inl rfl

theorem IsCSPolytope5.cross_edge_stars_disjoint {F R a b : Set E5} {U V : Set (Set E5)}
    (hab : a ≠ b) (haR : a ∉ vset P R) (hVR : V ⊆ vset P R) :
    Disjoint (crossEdgeStar P F a U) (crossEdgeStar P F b V) := by
  rw [Set.disjoint_left]
  rintro e ⟨_,u,_,heu⟩ ⟨_,v,hv,hev⟩
  have ha : a ∈ vset P e := by rw [heu]; exact Or.inl rfl
  rw [hev] at ha
  rcases ha with he | he
  · exact hab he
  · exact haR (he ▸ hVR hv)

/-- A fifteen-edge core and two disjoint cross-edge stars with three
and two edges force at least twenty edges. -/
theorem IsCSPolytope5.edges_twenty_of_cross_stars {F T R a b : Set E5}
    {U V : Set (Set E5)} (hTF : T ⊆ F) (hRF : R ⊆ F)
    (hcore : 15 ≤ (edgeSet P T ∪ edgeSet P R).ncard)
    (hUR : U ⊆ vset P R) (hVR : V ⊆ vset P R)
    (hUT : ∀ v ∈ U, v ∉ vset P T) (hVT : ∀ v ∈ V, v ∉ vset P T)
    (hU3 : 3 ≤ U.ncard) (hV2 : 2 ≤ V.ncard)
    (haR : a ∉ vset P R) (hbR : b ∉ vset P R) (hab : a ≠ b)
    (hjoinA : ∀ v ∈ U, ∃ e, e ∈ edgeSet P F ∧ vset P e = {a,v})
    (hjoinB : ∀ v ∈ V, ∃ e, e ∈ edgeSet P F ∧ vset P e = {b,v}) :
    20 ≤ cnt P F 1 := by
  let C := edgeSet P T ∪ edgeSet P R
  let D := crossEdgeStar P F a U
  let E := crossEdgeStar P F b V
  have hc : C.Finite := (hP.below_finite T 1).union (hP.below_finite R 1)
  have hd : D.Finite := hP.faces_finite.subset fun e he => he.1.1
  have he : E.Finite := hP.faces_finite.subset fun e he => he.1.1
  have hd3 := hP.cross_edge_star_lower (fun h => haR (hUR h)) hjoinA
  have he2 := hP.cross_edge_star_lower (fun h => hbR (hVR h)) hjoinB
  have hcd : Disjoint C D := hP.cross_edge_star_avoids_core haR hUT
  have hce : Disjoint C E := hP.cross_edge_star_avoids_core hbR hVT
  have hde : Disjoint D E := hP.cross_edge_stars_disjoint hab haR hVR
  have hsize : (C ∪ D ∪ E).ncard = C.ncard + D.ncard + E.ncard := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨hce,hde⟩) (hc.union hd) he,
      Set.ncard_union_eq hcd hc hd]
  have hs : C ∪ D ∪ E ⊆ edgeSet P F := by
    rintro e ((he | he) | he)
    · rcases he with he | he
      · exact ⟨he.1,he.2.1.trans hTF,he.2.2⟩
      · exact ⟨he.1,he.2.1.trans hRF,he.2.2⟩
    · exact he.1
    · exact he.1
  have hl := Set.ncard_le_ncard hs (hP.below_finite F 1)
  change (C ∪ D ∪ E).ncard ≤ cnt P F 1 at hl
  change U.ncard ≤ D.ncard at hd3
  change V.ncard ≤ E.ncard at he2
  change 15 ≤ C.ncard at hcore
  omega

end Kalai5
