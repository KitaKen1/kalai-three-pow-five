import Kalai5.Endpoints.FacetEdgeBudget
import Kalai5.Endpoints.PyramidVertexDegree
import Kalai5.Endpoints.PolygonPyramid

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Edges through a fixed vertex inject into their other endpoints. -/
theorem IsCSPolytope5.edge_star_endpoint_bound {D U : Set (Set E5)} {v : Set E5}
    (hU : U.Finite) (hvU : v ∉ U)
    (hD : ∀ e ∈ D, e ∈ faces P ∧ dim e = 1 ∧ v ∈ vset P e ∧
      vset P e ⊆ insert v U) : D.ncard ≤ U.ncard := by
  have hf : D.Finite := hP.faces_finite.subset fun e he => (hD e he).1
  have other : ∀ e ∈ D, ∃ w ∈ U, vset P e = {v,w} := by
    intro e he
    obtain ⟨heF,he1,hve,hsub⟩ := hD e he
    obtain ⟨w,hw,hwv⟩ := exists_ne_of_ncard_eq_two (hP.edge_vertex_card heF he1) hve
    have hwU : w ∈ U := (hsub hw).resolve_left hwv
    refine ⟨w,hwU,?_⟩
    apply (Set.eq_of_subset_of_ncard_le (by
      rintro x (rfl | rfl)
      · exact hve
      · exact hw) _ (hP.vset_finite e)).symm
    rw [hP.edge_vertex_card heF he1,Set.ncard_pair hwv.symm]
  choose w hwU hwe using other
  let f : D → U := fun e => ⟨w e.val e.property,hwU e.val e.property⟩
  have hi : Function.Injective f := by
    intro e g heq
    have hw : w e.val e.property = w g.val g.property := congrArg Subtype.val heq
    apply Subtype.ext
    have hvs : vset P e.val = vset P g.val := by
      rw [hwe e.val e.property,hwe g.val g.property,hw]
    exact hP.eq_of_subset_of_dim_le (hD e.val e.property).1 (hD g.val g.property).1
      (hP.subset_of_vset (hD e.val e.property).1 (hD g.val g.property).1 hvs.subset)
      (by rw [(hD e.val e.property).2.1,(hD g.val g.property).2.1])
  letI := hU.fintype
  have hle := Nat.card_le_card_of_injective f hi
  simpa only [Nat.card_coe_set_eq] using hle

/-- The apex of a square pyramid is joined by an edge to every base vertex. -/
theorem IsCSPolytope5.square_pyramid_apex_edge {Y Q a v : Set E5}
    (hY : Y ∈ faces P) (hY3 : dim Y = 3) (hy : tri3 P Y = (5,8,5))
    (hQ : Q ∈ faces P) (hQY : Q ⊆ Y) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (ha : a ∈ vset P Y) (haQ : a ∉ vset P Q)
    (hvs : vset P Y = insert a (vset P Q)) (hv : v ∈ vset P Q) :
    ∃ e, e ∈ edgeSet P Y ∧ vset P e = {a,v} := by
  by_contra hn
  let D : Set (Set E5) := {e | e ∈ faces P ∧ a ⊆ e ∧ e ⊆ Y ∧ dim e = 1}
  have hd : 4 ≤ D.ncard := hP.four_le_vdeg_pyramid_apex hY hY3 hy hQ hQY hQ2 hQ4
    ha.1 ha.2.1 ha.2.2 (fun h => haQ ⟨ha.1,h,ha.2.2⟩)
  have hb : D.ncard ≤ (vset P Q \ {v}).ncard := hP.edge_star_endpoint_bound
    (hP.vset_finite Q).sdiff (fun h => haQ h.1) (by
      intro e he
      have hae : a ∈ vset P e := ⟨ha.1,he.2.1,ha.2.2⟩
      refine ⟨he.1,he.2.2.2,hae,?_⟩
      intro w hw
      have hwY := vset_mono' he.2.2.1 hw
      rw [hvs] at hwY
      rcases hwY with rfl | hwQ
      · exact Or.inl rfl
      · refine Or.inr ⟨hwQ,?_⟩
        intro hwv
        have hwv' : w = v := hwv
        subst w
        apply hn
        refine ⟨e,⟨he.1,he.2.2⟩,?_⟩
        apply (Set.eq_of_subset_of_ncard_le (by
          rintro x (rfl | rfl)
          · exact hae
          · exact hw) _ (hP.vset_finite e)).symm
        rw [hP.edge_vertex_card he.1 he.2.2.2,Set.ncard_pair (by
          intro heq; exact haQ (heq ▸ hv))])
  rw [Set.ncard_sdiff_singleton_of_mem hv,← cnt_eq_vset,hQ4] at hb
  omega

end Kalai5
