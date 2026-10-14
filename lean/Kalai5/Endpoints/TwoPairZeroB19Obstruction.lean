import Kalai5.Endpoints.TwoPairZeroB19Apices
import Kalai5.Endpoints.PolygonEdges

/-! Apex incidence forces an impossible triangle in the quadrilateral base. -/
namespace Kalai5
open Set
open scoped Classical
variable {P F : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem B19Shell.common_apex_ridge (s : B19Shell P F) (a : B19Apices s)
    (hF : F ∈ faces P) (h4 : dim F=4) (hr8 : cnt P F 3=8) :
    ∃ T,T ∈ faces P ∧ T ⊆ F ∧ dim T=3 ∧ a.c ⊆ T ∧ a.d ⊆ T ∧ ¬ s.Q ⊆ T := by
  have hQC : s.S ⊆ s.C := s.hSI ▸ inter_subset_left
  have hQD : s.S ⊆ s.D := s.hSI ▸ inter_subset_right
  have hcC : a.c ∈ vset P s.C := by rw [a.verticesC]; exact Or.inl rfl
  have hdD : a.d ∈ vset P s.D := by rw [a.verticesD]; exact Or.inl rfl
  have hc := hP.apex_count hF h4 s.pent.1 s.pent.2.1 s.pent.2.2.1
    s.hC.1 s.hC.2.1 s.hC.2.2.1 hQC s.hD.1 s.hD.2.1 s.hD.2.2.1 hQD s.hCD hcC
    (by rw [a.verticesC])
  have hd := hP.apex_count hF h4 s.pent.1 s.pent.2.1 s.pent.2.2.1
    s.hD.1 s.hD.2.1 s.hD.2.2.1 hQD s.hC.1 s.hC.2.1 s.hC.2.2.1 hQC s.hCD.symm hdD
    (by rw [a.verticesD])
  rw [s.pent.2.2.2] at hc hd
  let U := {T | T ∈ faces P ∧ a.c ⊆ T ∧ T ⊆ F ∧ dim T=3}
  let V := {T | T ∈ faces P ∧ a.d ⊆ T ∧ T ⊆ F ∧ dim T=3}
  have huf : U.Finite := hP.faces_finite.subset fun T hT => hT.1
  have hvf : V.Finite := hP.faces_finite.subset fun T hT => hT.1
  have hu : (U ∪ V).ncard ≤ 8 := by
    have hs : U ∪ V ⊆ {T | T ∈ faces P ∧ T ⊆ F ∧ dim T=3} := by
      rintro T (hT | hT) <;> exact ⟨hT.1,hT.2.2⟩
    have hh := Set.ncard_le_ncard hs (hP.below_finite F 3)
    change (U ∪ V).ncard ≤ cnt P F 3 at hh
    rwa [hr8] at hh
  have hadd := Set.ncard_union_add_ncard_inter U V huf hvf
  have hcommon : 4 ≤ (U ∩ V).ncard := by
    change 5+1 ≤ U.ncard at hc
    change 5+1 ≤ V.ncard at hd
    omega
  have hQA : s.Q ⊆ s.A := s.hQI ▸ inter_subset_left
  have hQB : s.Q ⊆ s.B := s.hQI ▸ inter_subset_right
  have hp : ({s.A,s.B} : Set (Set E5)) ⊆ U ∩ V := by
    rintro T (rfl | rfl)
    · exact ⟨⟨s.hA.1,a.cQ.2.1.trans hQA,s.hA.2.1,s.hA.2.2.1⟩,
        ⟨s.hA.1,a.dQ.2.1.trans hQA,s.hA.2.1,s.hA.2.2.1⟩⟩
    · exact ⟨⟨s.hB.1,a.cQ.2.1.trans hQB,s.hB.2.1,s.hB.2.2.1⟩,
        ⟨s.hB.1,a.dQ.2.1.trans hQB,s.hB.2.1,s.hB.2.2.1⟩⟩
  have hdiff : ((U ∩ V) \ {s.A,s.B}).ncard≠0 := by
    rw [Set.ncard_sdiff hp (by simp),Set.ncard_pair s.hAB]
    omega
  obtain ⟨T,hT⟩ := Set.nonempty_of_ncard_ne_zero hdiff
  refine ⟨T,hT.1.1.1,hT.1.1.2.2.1,hT.1.1.2.2.2,hT.1.1.2.1,hT.1.2.2.1,?_⟩
  intro hQT
  have htwo := hP.twoface_in_facet hF h4 s.quad.1 s.quad.2.1 s.quad.2.2.1
  have he : ({s.A,s.B} : Set (Set E5))=
      {R | R ∈ faces P ∧ s.Q ⊆ R ∧ R ⊆ F ∧ dim R=3} :=
    Set.eq_of_subset_of_ncard_le
      (by rintro R (rfl | rfl)
          · exact ⟨s.hA.1,hQA,s.hA.2.1,s.hA.2.2.1⟩
          · exact ⟨s.hB.1,hQB,s.hB.2.1,s.hB.2.2.1⟩)
      (by rw [htwo,Set.ncard_pair s.hAB])
      (hP.faces_finite.subset fun R hR => hR.1)
  apply hT.2
  rw [he]
  exact ⟨hT.1.1.1,hQT,hT.1.1.2.2⟩

theorem B19Shell.impossible (s : B19Shell P F)
    (hF : F ∈ faces P) (h4 : dim F=4) (h8 : cnt P F 0=8) (hr8 : cnt P F 3=8) : False := by
  obtain ⟨a⟩ := s.apices hP h8
  obtain ⟨x,hx⟩ := Set.ncard_eq_one.1 (s.vertex_cover hP h8).2.1
  have hxm : x ∈ vset P s.Q ∩ vset P s.S := by rw [hx]; exact Set.mem_singleton x
  have hxc : x≠a.c := by intro he; exact a.cS (he ▸ hxm.2)
  have hxd : x≠a.d := by intro he; exact a.dS (he ▸ hxm.2)
  have inter_vertices (R v : Set E5) (hvQ : v ∈ vset P s.Q)
      (hR : vset P R=insert v (vset P s.S)) :
      vset P (s.Q ∩ R)={x,v} := by
    rw [vset_inter',hR]
    ext w
    constructor
    · rintro ⟨hwQ,hw | hwS⟩
      · exact Or.inr hw
      · exact Or.inl (Set.mem_singleton_iff.1 (hx ▸ ⟨hwQ,hwS⟩))
    · rintro (rfl | rfl)
      · exact ⟨hxm.1,Or.inr hxm.2⟩
      · exact ⟨hvQ,Or.inl rfl⟩
  have vC := inter_vertices s.C a.c a.cQ a.verticesC
  have vD := inter_vertices s.D a.d a.dQ a.verticesD
  have not_base (R v : Set E5) (hxv : x≠v) (hv : vset P (s.Q ∩ R)={x,v}) :
      ¬ s.Q ⊆ R := by
    intro hsub
    have hi : s.Q ∩ R=s.Q := Set.inter_eq_left.2 hsub
    have hn := s.quad.2.2.2
    rw [cnt_eq_vset,← hi,hv,Set.ncard_pair hxv] at hn
    omega
  have hxcI : x ∈ vset P (s.Q ∩ s.C) := by rw [vC]; simp
  have hcI : a.c ∈ vset P (s.Q ∩ s.C) := by rw [vC]; simp
  have hxdI : x ∈ vset P (s.Q ∩ s.D) := by rw [vD]; simp
  have hdI : a.d ∈ vset P (s.Q ∩ s.D) := by rw [vD]; simp
  obtain ⟨hE1,hE11,vE1⟩ := hP.polygon_inter_edge s.quad.1 s.quad.2.2.1 s.hC.1
    (not_base s.C a.c hxc vC) hxc hxcI hcI
  obtain ⟨hE2,hE21,vE2⟩ := hP.polygon_inter_edge s.quad.1 s.quad.2.2.1 s.hD.1
    (not_base s.D a.d hxd vD) hxd hxdI hdI
  obtain ⟨T,hT,_,hT3,hcT,hdT,hnot⟩ := s.common_apex_ridge hP a hF h4 hr8
  obtain ⟨hE3,hE31,vE3⟩ := hP.polygon_inter_edge s.quad.1 s.quad.2.2.1 hT hnot a.cd
    ⟨a.cQ.1,subset_inter a.cQ.2.1 hcT,a.cQ.2.2⟩
    ⟨a.dQ.1,subset_inter a.dQ.2.1 hdT,a.dQ.2.2⟩
  have h12 : s.Q ∩ s.C≠s.Q ∩ s.D := by
    intro he
    have hm := he ▸ hcI
    rw [vE2] at hm
    rcases hm with hm | hm
    · exact hxc hm.symm
    · exact a.cd hm
  have h13 : s.Q ∩ s.C≠s.Q ∩ T := by
    intro he
    have hm := he ▸ hxcI
    rw [vE3] at hm
    exact hm.elim hxc hxd
  have h23 : s.Q ∩ s.D≠s.Q ∩ T := by
    intro he
    have hm := he ▸ hxdI
    rw [vE3] at hm
    exact hm.elim hxc hxd
  exact hP.quadrilateral_no_triangle_edges s.quad.1 s.quad.2.2.1 s.quad.2.2.2
    hE1 inter_subset_left hE11 hE2 inter_subset_left hE21 hE3 inter_subset_left hE31
    h12 h13 h23 hxc hxd a.cd vE1 vE2 vE3

end Kalai5

