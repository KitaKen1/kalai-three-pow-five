import Kalai5.Cube3.NormalFamilies
import Kalai5.Cube3.NoFive

/-! Four segment fibres cannot have only eighteen facets and no extra full normal. -/

namespace Kalai5.Cube3
open Set FullPrism

variable {x : Fin 8 → E5} {C : Config x}

theorem SegmentData.no_eighteen (S : SegmentData C) {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (hno : ¬ C.ExtraPM) : False := by
  have hnt := S.no_triple_parallel hP hrange hh hno
  obtain ⟨i,j,hij,hpar⟩ := S.exists_parallel hP hrange hh
  obtain ⟨τ,h0,h1⟩ := order_pair i j hij
  have h01 : det2 (S.direction (τ 0)) (S.direction (τ 1))=0 := by rwa [h0,h1]
  obtain ⟨h02,h03⟩ := S.pair_transverse hno hnt τ h01
  obtain ⟨A⟩ := S.double_normal_family hno hnt
    (fun he => (by decide : (0 : Fin 4) ≠ 1) (τ.injective he)) h01
  by_cases h23 : det2 (S.direction (τ 2)) (S.direction (τ 3))=0
  · obtain ⟨B⟩ := S.double_normal_family hno hnt
      (fun he => (by decide : (2 : Fin 4) ≠ 3) (τ.injective he)) h23
    have h22 := A.two_facets B hP hrange h02
    norm_num [EightNormalIndex,Fintype.card_sum] at h22
    omega
  · obtain ⟨B⟩ := S.single_normal_family hP hrange (τ 2)
    obtain ⟨D⟩ := S.single_normal_family hP hrange (τ 3)
    have h22 := A.three_facets B D hP hrange h02 h03 h23
    norm_num [EightNormalIndex,Fintype.card_sum,Fintype.card_prod] at h22
    omega

theorem Config.not_all_two {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (hno : ¬ C.ExtraPM) : ¬(∀ j,(C.cls j).card=2) := by
  intro hs
  obtain ⟨S⟩ := C.segments_of_size_two hs
  exact S.no_eighteen hP hrange hh hno

theorem Config.three_size_patterns {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM) :
    ∃ τ : Equiv.Perm (Fin 4),
    ((C.cls (τ 0)).card=4 ∧ (C.cls (τ 1)).card=2 ∧
      (C.cls (τ 2)).card=1 ∧ (C.cls (τ 3)).card=1) ∨
    ((C.cls (τ 0)).card=3 ∧ (C.cls (τ 1)).card=3 ∧
      (C.cls (τ 2)).card=1 ∧ (C.cls (τ 3)).card=1) ∨
    ((C.cls (τ 0)).card=3 ∧ (C.cls (τ 1)).card=2 ∧
      (C.cls (τ 2)).card=2 ∧ (C.cls (τ 3)).card=1) := by
  obtain ⟨τ,h | h | h | h⟩ := C.four_size_patterns hP hrange hh
  · exact ⟨τ,Or.inl h⟩
  · exact ⟨τ,Or.inr (Or.inl h)⟩
  · exact ⟨τ,Or.inr (Or.inr h)⟩
  · apply (C.not_all_two hP hrange hh hno).elim
    intro j
    obtain ⟨j,rfl⟩ := τ.surjective j
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2

end Kalai5.Cube3
