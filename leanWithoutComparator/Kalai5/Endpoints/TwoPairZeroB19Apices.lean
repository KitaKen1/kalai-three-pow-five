import Kalai5.Endpoints.TwoPairZeroB19Cover

/-! The four pyramid apices lie in opposite bases and are pairwise distinct. -/
namespace Kalai5
open Set
open scoped Classical

structure B19Apices {P F : Set E5} (s : B19Shell P F) where
  a : Set E5
  b : Set E5
  c : Set E5
  d : Set E5
  aS : a ∈ vset P s.S
  bS : b ∈ vset P s.S
  cQ : c ∈ vset P s.Q
  dQ : d ∈ vset P s.Q
  aQ : a ∉ vset P s.Q
  bQ : b ∉ vset P s.Q
  cS : c ∉ vset P s.S
  dS : d ∉ vset P s.S
  ab : a≠b
  cd : c≠d
  verticesA : vset P s.A=insert a (vset P s.Q)
  verticesB : vset P s.B=insert b (vset P s.Q)
  verticesC : vset P s.C=insert c (vset P s.S)
  verticesD : vset P s.D=insert d (vset P s.S)

variable {P F : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem B19Shell.apices (s : B19Shell P F) (h8 : cnt P F 0=8) :
    Nonempty (B19Apices s) := by
  have hcover := (s.vertex_cover hP h8).1
  have hA5 : cnt P s.A 0=5 := congrArg Prod.fst s.hA.2.2.2
  have hB5 : cnt P s.B 0=5 := congrArg Prod.fst s.hB.2.2.2
  have hC6 : cnt P s.C 0=6 := congrArg Prod.fst s.hC.2.2.2
  have hD6 : cnt P s.D 0=6 := congrArg Prod.fst s.hD.2.2.2
  have hQ4 := s.quad.2.2.2
  have hS5 := s.pent.2.2.2
  obtain ⟨a,ha,haQ,hva⟩ := hP.polygon_pyramid_apex
    (show s.Q ⊆ s.A from s.hQI ▸ inter_subset_left) (by omega : cnt P s.A 0=cnt P s.Q 0+1)
  obtain ⟨b,hb,hbQ,hvb⟩ := hP.polygon_pyramid_apex
    (show s.Q ⊆ s.B from s.hQI ▸ inter_subset_right) (by omega : cnt P s.B 0=cnt P s.Q 0+1)
  obtain ⟨c,hc,hcS,hvc⟩ := hP.polygon_pyramid_apex
    (show s.S ⊆ s.C from s.hSI ▸ inter_subset_left) (by omega : cnt P s.C 0=cnt P s.S 0+1)
  obtain ⟨d,hd,hdS,hvd⟩ := hP.polygon_pyramid_apex
    (show s.S ⊆ s.D from s.hSI ▸ inter_subset_right) (by omega : cnt P s.D 0=cnt P s.S 0+1)
  have haS : a ∈ vset P s.S := by
    have hm := vset_mono' s.hA.2.1 ha
    rw [← hcover] at hm
    exact hm.resolve_left haQ
  have hbS : b ∈ vset P s.S := by
    have hm := vset_mono' s.hB.2.1 hb
    rw [← hcover] at hm
    exact hm.resolve_left hbQ
  have hcQ : c ∈ vset P s.Q := by
    have hm := vset_mono' s.hC.2.1 hc
    rw [← hcover] at hm
    exact hm.resolve_right hcS
  have hdQ : d ∈ vset P s.Q := by
    have hm := vset_mono' s.hD.2.1 hd
    rw [← hcover] at hm
    exact hm.resolve_right hdS
  have hab : a≠b := by
    intro he
    have hm : a ∈ vset P (s.A ∩ s.B) := by rw [vset_inter']; exact ⟨ha,he ▸ hb⟩
    exact haQ (s.hQI ▸ hm)
  have hcd : c≠d := by
    intro he
    have hm : c ∈ vset P (s.C ∩ s.D) := by rw [vset_inter']; exact ⟨hc,he ▸ hd⟩
    exact hcS (s.hSI ▸ hm)
  exact ⟨⟨a,b,c,d,haS,hbS,hcQ,hdQ,haQ,hbQ,hcS,hdS,hab,hcd,hva,hvb,hvc,hvd⟩⟩

theorem B19Apices.distinct (s : B19Shell P F) (a : B19Apices s) :
    a.a≠a.c ∧ a.a≠a.d ∧ a.b≠a.c ∧ a.b≠a.d := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro h
  · exact a.aQ (h ▸ a.cQ)
  · exact a.aQ (h ▸ a.dQ)
  · exact a.bQ (h ▸ a.cQ)
  · exact a.bQ (h ▸ a.dQ)

end Kalai5

