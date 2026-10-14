import Kalai5.Cube3.PositiveSigma

/-! Distinct nonopposite edge normals give a family of actual polar vertices. -/
namespace Kalai5.Cube3
open Set FullPrism
variable {x : Fin 8 → E5} (C : Config x)

theorem Config.exists_fibre_normals {j : Fin 4} (h3 : 3 ≤ (C.cls j).card) :
    ∃ N : Finset (E 2),(∀ n ∈ N,LemmaB.IsEdgeNormal (fibre C.c C.k j) n) ∧ (C.cls j).card≤N.card := by
  obtain ⟨N,hN,hcard⟩ := LemmaB.exists_edgeNormals (C.convpos_fibre j) (C.dim_fibre_eq_two h3)
  exact ⟨N,hN,by rwa [C.card_fibre] at hcard⟩

theorem Config.edge_normals_family {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (j : Fin 4) (N : Finset (E 2))
    (hN : ∀ n ∈ N,LemmaB.IsEdgeNormal (fibre C.c C.k j) n)
    (hop : ∀ n ∈ N,∀ m ∈ N,n ≠ -m) :
    ∃ F : PositiveFamily C (Σ _ : N,Unit),∀ k,F.normal k=k.1.val := by
  classical
  have hex (n : N) : ∃ G : PositiveFamily C Unit,∀ i,G.normal i=n.val :=
    C.edge_positive_family hP hrange j (hN n.val n.property)
  choose G hG using hex
  have hne : ∀ n m : N,n ≠ m → ∀ a b,(G n).normal a ≠ (G m).normal b := by
    intro n m hnm a b he
    rw [hG,hG] at he
    exact hnm (Subtype.ext he)
  have hopp : ∀ n m : N,∀ a b,(G n).normal a ≠ -(G m).normal b := by
    intro n m a b
    rw [hG,hG]; exact hop n.val n.property m.val m.property
  exact ⟨PositiveFamily.sigma G hne hopp,fun k => hG k.1 k.2⟩

end Kalai5.Cube3
