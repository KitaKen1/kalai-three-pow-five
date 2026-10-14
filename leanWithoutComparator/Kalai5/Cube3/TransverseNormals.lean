import Kalai5.Cube3.MixedDirections
import Kalai5.Cube3.SegmentFibreRays

/-! At most two unit normals are orthogonal to a given nonzero segment direction. -/
namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

lemma SegmentFibre.transverse_normals_card {j : Fin 4} (S : SegmentFibre C j)
    (N : Finset (E 2)) (hN : ∀ n ∈ N,‖n‖=1) :
    N.card ≤ (N.filter fun n => ⟪n,S.direction⟫ ≠ 0).card+2 := by
  classical
  have hsub : (N.filter fun n => ⟪n,S.direction⟫=0) ⊆ {S.normal,-S.normal} := by
    intro n hn
    obtain ⟨hn,horth⟩ := Finset.mem_filter.1 hn
    have he := unit_common_orthogonal (hN n hn) S.normal_unit S.direction_ne_zero
      horth S.normal_orthogonal
    simpa only [Finset.mem_insert,Finset.mem_singleton] using he
  have hcard : (N.filter fun n => ⟪n,S.direction⟫=0).card≤2 := by
    apply (Finset.card_le_card hsub).trans
    simpa using Finset.card_insert_le S.normal {-S.normal}
  have hsum := Finset.card_filter_add_card_filter_not (s := N) (fun n => ⟪n,S.direction⟫=0)
  simp only [ne_eq] at *
  omega

lemma SegmentFibre.transverse_normals_card_of_no_opposite {j : Fin 4} (S : SegmentFibre C j)
    (N : Finset (E 2)) (hN : ∀ n ∈ N,‖n‖=1) (hop : ∀ n ∈ N,∀ m ∈ N,n ≠ -m) :
    N.card ≤ (N.filter fun n => ⟪n,S.direction⟫ ≠ 0).card+1 := by
  classical
  have hcard : (N.filter fun n => ⟪n,S.direction⟫=0).card≤1 := by
    apply Finset.card_le_one.2
    intro n hn m hm
    obtain ⟨hn,hnorth⟩ := Finset.mem_filter.1 hn
    obtain ⟨hm,hmorth⟩ := Finset.mem_filter.1 hm
    rcases unit_common_orthogonal (hN n hn) (hN m hm) S.direction_ne_zero hnorth hmorth with he | he
    · exact he
    · exact (hop n hn m hm he).elim
  have hsum := Finset.card_filter_add_card_filter_not (s := N) (fun n => ⟪n,S.direction⟫=0)
  simp only [ne_eq] at *
  omega

end Kalai5.Cube3
