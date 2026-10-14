import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Functor
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Embedding
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Star
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.SProd
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic

/-!
# The combinatorics of the prism facet

Abstract incidence data: vertices `X`, facets `𝒢`, incidence `inc`, adjacency `adj`.  Suppose

* every vertex misses exactly two facets;
* every vertex has at least four neighbours, and neighbours share at least three facets;
* every facet misses two or four vertices, sixteen misses in all.

Then every vertex misses exactly one facet that misses two vertices (`miss_side_card`): the
"sides" miss disjoint pairs of vertices covering all vertices.  (A neighbour of `y` must miss one
of the two facets missed by `y`, so `y` has at most `d_a + d_b - 2` neighbours; hence some missed
facet is a "base" (`d = 4`); there are two bases with eight misses in all, one for each vertex.)
-/

namespace Kalai5.FullPrism

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Facets missed by a vertex. -/
def missF (𝒢 : Finset β) (inc : α → β → Prop) [DecidableRel inc] (y : α) : Finset β :=
  𝒢.filter fun G => ¬ inc y G

/-- Vertices missed by a facet. -/
def outV (X : Finset α) (inc : α → β → Prop) [DecidableRel inc] (G : β) : Finset α :=
  X.filter fun y => ¬ inc y G

lemma double_count (X : Finset α) (𝒢 : Finset β) (r : α → β → Prop) [DecidableRel r] :
    ∑ y ∈ X, (𝒢.filter (r y)).card = ∑ G ∈ 𝒢, (X.filter (r · G)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem miss_side_card (X : Finset α) (𝒢 : Finset β) (inc : α → β → Prop) [DecidableRel inc]
    (adj : α → α → Prop) [DecidableRel adj]
    (hmiss : ∀ y ∈ X, (missF 𝒢 inc y).card = 2)
    (hnb : ∀ y ∈ X, 4 ≤ (X.filter fun z => z ≠ y ∧ adj y z).card)
    (hcommon : ∀ y ∈ X, ∀ z ∈ X, z ≠ y → adj y z →
      3 ≤ (𝒢.filter fun G => inc y G ∧ inc z G).card)
    (hout : ∀ G ∈ 𝒢, (outV X inc G).card = 2 ∨ (outV X inc G).card = 4)
    (h𝒢 : 𝒢.card = 6) (hX : X.card = 8) :
    ∀ y ∈ X, ((missF 𝒢 inc y).filter fun G => (outV X inc G).card = 2).card = 1 := by
  classical
  -- a neighbour misses one of the facets missed by `y`
  have hnbmiss : ∀ y ∈ X, ∀ z ∈ X, z ≠ y → adj y z → (missF 𝒢 inc y ∩ missF 𝒢 inc z).Nonempty := by
    intro y hy z hz hzy hadj
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hc := hcommon y hy z hz hzy hadj
    have hsub : (𝒢.filter fun G => inc y G ∧ inc z G) ⊆ 𝒢 \ (missF 𝒢 inc y ∪ missF 𝒢 inc z) := by
      intro G hG
      simp only [Finset.mem_filter] at hG
      simp only [Finset.mem_sdiff, Finset.mem_union, missF, Finset.mem_filter, not_or, not_and,
        not_not]
      exact ⟨hG.1, fun _ => hG.2.1, fun _ => hG.2.2⟩
    have h1 := Finset.card_le_card hsub
    have h2 : (missF 𝒢 inc y ∪ missF 𝒢 inc z) ⊆ 𝒢 := by
      intro G hG
      rcases Finset.mem_union.1 hG with h | h <;> exact (Finset.mem_filter.1 h).1
    rw [Finset.card_sdiff_of_subset h2, Finset.card_union_of_disjoint
      (Finset.disjoint_iff_inter_eq_empty.2 hemp), hmiss y hy, hmiss z hz, h𝒢] at h1
    omega
  -- so `y` has at most `d_a + d_b - 2` neighbours, and some missed facet misses four vertices
  have hbase : ∀ y ∈ X, ∃ G ∈ missF 𝒢 inc y, (outV X inc G).card = 4 := by
    intro y hy
    by_contra hno
    push_neg at hno
    have hsmall : ∀ G ∈ missF 𝒢 inc y, (outV X inc G).card = 2 := by
      intro G hG
      rcases hout G (Finset.mem_filter.1 hG).1 with h | h
      · exact h
      · exact absurd h (hno G hG)
    obtain ⟨a, b, hab, hmy⟩ := Finset.card_eq_two.1 (hmiss y hy)
    have ha : a ∈ missF 𝒢 inc y := by rw [hmy]; simp
    have hb : b ∈ missF 𝒢 inc y := by rw [hmy]; simp
    have hsub : (X.filter fun z => z ≠ y ∧ adj y z) ⊆ (outV X inc a ∪ outV X inc b).erase y := by
      intro z hz
      simp only [Finset.mem_filter] at hz
      obtain ⟨G, hG⟩ := hnbmiss y hy z hz.1 hz.2.1 hz.2.2
      rw [Finset.mem_inter] at hG
      have hGy := hG.1
      rw [hmy] at hGy
      have hGz := (Finset.mem_filter.1 hG.2).2
      refine Finset.mem_erase.2 ⟨hz.2.1, ?_⟩
      rcases Finset.mem_insert.1 hGy with rfl | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hz.1, hGz⟩)
      · rw [Finset.mem_singleton] at h
        subst h
        exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hz.1, hGz⟩)
    have hyU : y ∈ outV X inc a ∪ outV X inc b :=
      Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hy, (Finset.mem_filter.1 ha).2⟩)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hyU] at h1
    have h2 := Finset.card_union_le (outV X inc a) (outV X inc b)
    have h3 : y ∈ outV X inc a ∩ outV X inc b := Finset.mem_inter.2
      ⟨Finset.mem_filter.2 ⟨hy, (Finset.mem_filter.1 ha).2⟩,
        Finset.mem_filter.2 ⟨hy, (Finset.mem_filter.1 hb).2⟩⟩
    have h4 := Finset.card_union_add_card_inter (outV X inc a) (outV X inc b)
    have h5 : 1 ≤ (outV X inc a ∩ outV X inc b).card := Finset.card_pos.2 ⟨y, h3⟩
    have := hnb y hy
    rw [hsmall a ha, hsmall b hb] at h4
    omega
  -- the bases miss eight vertices in all
  set bases := 𝒢.filter fun G => (outV X inc G).card = 4 with hbases
  have hdouble : ∑ y ∈ X, ((missF 𝒢 inc y).filter fun G => (outV X inc G).card = 4).card =
      ∑ G ∈ bases, (outV X inc G).card := by
    have h1 : ∀ y, (missF 𝒢 inc y).filter (fun G => (outV X inc G).card = 4) =
        𝒢.filter (fun G => ¬ inc y G ∧ (outV X inc G).card = 4) := by
      intro y; rw [missF, Finset.filter_filter]
    simp only [h1]
    rw [double_count X 𝒢 (fun y G => ¬ inc y G ∧ (outV X inc G).card = 4), hbases,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun G _ => ?_
    split_ifs with h
    · simp only [h, and_true]; exact h
    · simp [h]
  -- double counting all misses: sixteen; so there are exactly two bases
  have htotal : ∑ y ∈ X, (missF 𝒢 inc y).card = ∑ G ∈ 𝒢, (outV X inc G).card :=
    double_count X 𝒢 (fun y G => ¬ inc y G)
  have hsum16 : ∑ G ∈ 𝒢, (outV X inc G).card = 16 := by
    rw [← htotal, Finset.sum_congr rfl hmiss, Finset.sum_const, hX]; rfl
  have hbcard : bases.card = 2 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not 𝒢 (fun G => (outV X inc G).card = 4)
      (fun G => (outV X inc G).card)
    have hb4 : ∑ G ∈ bases, (outV X inc G).card = 4 * bases.card := by
      rw [Finset.sum_congr rfl fun G hG => (Finset.mem_filter.1 hG).2, Finset.sum_const,
        smul_eq_mul, mul_comm]
    have hs2 : ∑ G ∈ 𝒢.filter (fun G => ¬ (outV X inc G).card = 4), (outV X inc G).card =
        2 * (𝒢.filter fun G => ¬ (outV X inc G).card = 4).card := by
      rw [Finset.sum_congr rfl fun G hG => ?_, Finset.sum_const, smul_eq_mul, mul_comm]
      rcases hout G (Finset.mem_filter.1 hG).1 with h | h
      · exact h
      · exact absurd h (Finset.mem_filter.1 hG).2
    have hc := Finset.card_filter_add_card_filter_not (s := 𝒢)
      (p := fun G => (outV X inc G).card = 4)
    rw [← hbases] at hsplit hc
    rw [hb4, hs2, hsum16] at hsplit
    omega
  have h8 : ∑ G ∈ bases, (outV X inc G).card = 8 := by
    rw [Finset.sum_congr rfl fun G hG => (Finset.mem_filter.1 hG).2, Finset.sum_const, hbcard]
    rfl
  -- each vertex misses exactly one base, hence exactly one side
  have hone : ∀ y ∈ X, ((missF 𝒢 inc y).filter fun G => (outV X inc G).card = 4).card = 1 := by
    have hge : ∀ y ∈ X, 1 ≤ ((missF 𝒢 inc y).filter fun G => (outV X inc G).card = 4).card := by
      intro y hy
      obtain ⟨G, hG, h4⟩ := hbase y hy
      exact Finset.card_pos.2 ⟨G, Finset.mem_filter.2 ⟨hG, h4⟩⟩
    have hs : ∑ y ∈ X, ((missF 𝒢 inc y).filter fun G => (outV X inc G).card = 4).card = 8 := by
      rw [hdouble, h8]
    by_contra hne
    push_neg at hne
    obtain ⟨y0, hy0, hne0⟩ := hne
    have hlt : 1 < ((missF 𝒢 inc y0).filter fun G => (outV X inc G).card = 4).card :=
      lt_of_le_of_ne (hge y0 hy0) (Ne.symm hne0)
    have : ∑ y ∈ X, 1 < ∑ y ∈ X, ((missF 𝒢 inc y).filter fun G => (outV X inc G).card = 4).card :=
      Finset.sum_lt_sum (fun y hy => hge y hy) ⟨y0, hy0, hlt⟩
    rw [hs, Finset.sum_const, hX] at this
    simp at this
  intro y hy
  have hsplit := Finset.card_filter_add_card_filter_not (s := missF 𝒢 inc y)
    (p := fun G => (outV X inc G).card = 4)
  have heq : ((missF 𝒢 inc y).filter fun G => ¬ (outV X inc G).card = 4) =
      (missF 𝒢 inc y).filter fun G => (outV X inc G).card = 2 := by
    apply Finset.filter_congr
    intro G hG
    rcases hout G (Finset.mem_filter.1 hG).1 with h | h <;> simp [h]
  rw [heq, hone y hy, hmiss y hy] at hsplit
  omega

end Kalai5.FullPrism
