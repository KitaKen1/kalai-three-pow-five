import Kalai5.Endpoints.TwoPairZeroB19Shell
import Kalai5.Endpoints.FourSetCover

/-! Equality in the four-set bound fixes the vertex overlap of the two bases. -/
namespace Kalai5
open Set
open scoped Classical

variable {P F : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem B19Shell.vertex_cover (s : B19Shell P F) (h8 : cnt P F 0=8) :
    vset P s.Q ∪ vset P s.S=vset P F ∧
      (vset P s.Q ∩ vset P s.S).ncard=1 ∧
      cnt P (s.A ∩ s.C) 0=3 ∧ cnt P (s.A ∩ s.D) 0=3 ∧
      cnt P (s.B ∩ s.C) 0=3 ∧ cnt P (s.B ∩ s.D) 0=3 := by
  have hA5 : cnt P s.A 0=5 := congrArg Prod.fst s.hA.2.2.2
  have hB5 : cnt P s.B 0=5 := congrArg Prod.fst s.hB.2.2.2
  have hC6 : cnt P s.C 0=6 := congrArg Prod.fst s.hC.2.2.2
  have hD6 : cnt P s.D 0=6 := congrArg Prod.fst s.hD.2.2.2
  have hS5 := s.pent.2.2.2
  have hSC : s.S ⊆ s.C := s.hSI ▸ inter_subset_left
  have hSD : s.S ⊆ s.D := s.hSI ▸ inter_subset_right
  have hAC := hP.polygon_pyramid_inter_small_ridge s.hC.1 s.hC.2.2.1
    s.pent.1 hSC s.pent.2.2.1 (by omega) s.hA.1 s.hA.2.2.1 (by omega)
  have hAD := hP.polygon_pyramid_inter_small_ridge s.hD.1 s.hD.2.2.1
    s.pent.1 hSD s.pent.2.2.1 (by omega) s.hA.1 s.hA.2.2.1 (by omega)
  have hBC := hP.polygon_pyramid_inter_small_ridge s.hC.1 s.hC.2.2.1
    s.pent.1 hSC s.pent.2.2.1 (by omega) s.hB.1 s.hB.2.2.1 (by omega)
  have hBD := hP.polygon_pyramid_inter_small_ridge s.hD.1 s.hD.2.2.1
    s.pent.1 hSD s.pent.2.2.1 (by omega) s.hB.1 s.hB.2.2.1 (by omega)
  let v : Set E5 → Finset (Set E5) := fun X => (hP.vset_finite X).toFinset
  have card (X : Set E5) : (v X).card=cnt P X 0 :=
    (Set.ncard_eq_toFinset_card _ (hP.vset_finite X)).symm
  have mono {X Y : Set E5} (h : X ⊆ Y) : v X ⊆ v Y := by
    intro a ha
    simp only [v,Set.Finite.mem_toFinset] at ha ⊢
    exact vset_mono' h ha
  have inter (X Y : Set E5) : v X ∩ v Y=v (X ∩ Y) := by
    ext a
    simp only [v,Finset.mem_inter,Set.Finite.mem_toFinset,vset_inter',Set.mem_inter_iff]
  have icard (X Y : Set E5) : (v X ∩ v Y).card=cnt P (X ∩ Y) 0 := by
    rw [inter,card]
  obtain ⟨he,hac,had,hbc,hbd⟩ := four_set_double_cover (v F) (v s.A) (v s.B) (v s.C) (v s.D)
    (mono s.hA.2.1) (mono s.hB.2.1) (mono s.hC.2.1) (mono s.hD.2.1)
    (by rw [card,h8]) (by rw [card,hA5]) (by rw [card,hB5])
    (by rw [card,hC6]) (by rw [card,hD6])
    (by rw [icard]; exact hAC) (by rw [icard]; exact hAD)
    (by rw [icard]; exact hBC) (by rw [icard]; exact hBD)
  rw [inter,inter,s.hQI,s.hSI] at he
  have hcover : vset P s.Q ∪ vset P s.S=vset P F := by
    have hh := congrArg (fun X : Finset (Set E5) => (X : Set (Set E5))) he
    simpa only [Finset.coe_union,v,Set.Finite.coe_toFinset] using hh
  have hsum := Set.ncard_union_add_ncard_inter (vset P s.Q) (vset P s.S)
    (hP.vset_finite s.Q) (hP.vset_finite s.S)
  rw [hcover,← cnt_eq_vset,← cnt_eq_vset,← cnt_eq_vset] at hsum
  rw [icard] at hac had hbc hbd
  exact ⟨hcover,by have := s.quad.2.2.2; have := s.pent.2.2.2; omega,hac,had,hbc,hbd⟩

end Kalai5
