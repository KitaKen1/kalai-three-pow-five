import Kalai5.LemmaB.Types
import Kalai5.LemmaB.Assemble

/-!
# Lemma B: the core claim

`coreClaim`: a rank-three configuration without a fourth `±1`-functional has at least `243`
nonempty faces.  Relabel the classes by decreasing size (a configuration for the same points);
the sizes are then `(5,1,1)`, `(4,2,1)`, `(3,3,1)` or `(3,2,2)`, and each type is counted in
`Kalai5.LemmaB.Types`.
-/

namespace Kalai5.LemmaB

open Set Module LemmaA

/-- **Lemma B (core).** -/
theorem coreClaim : CoreClaim := by
  intro x C hX
  obtain ⟨τ, hτ1, hτ2⟩ := Config.exists_perm_antitone (fun j => (C.cls j).card)
  have hX' : ¬ (C.perm τ.symm).ExtraPM := fun h => hX (C.extraPM_of_perm τ.symm h)
  have hcls : ∀ j, ((C.perm τ.symm).cls j).card = (C.cls (τ j)).card := fun j => by
    rw [C.cls_perm, Equiv.symm_symm]
  have hsum := (C.perm τ.symm).sum_card_cls
  rw [hcls, hcls, hcls] at hsum
  have hp0 := Finset.card_pos.2 ((C.perm τ.symm).cls_nonempty 0)
  have hp1 := Finset.card_pos.2 ((C.perm τ.symm).cls_nonempty 1)
  have hp2 := Finset.card_pos.2 ((C.perm τ.symm).cls_nonempty 2)
  rw [hcls] at hp0 hp1 hp2
  obtain h | h | h | h : ((C.cls (τ 0)).card = 5 ∧ (C.cls (τ 1)).card = 1 ∧
        (C.cls (τ 2)).card = 1) ∨
      ((C.cls (τ 0)).card = 4 ∧ (C.cls (τ 1)).card = 2 ∧ (C.cls (τ 2)).card = 1) ∨
      ((C.cls (τ 0)).card = 3 ∧ (C.cls (τ 1)).card = 3 ∧ (C.cls (τ 2)).card = 1) ∨
      ((C.cls (τ 0)).card = 3 ∧ (C.cls (τ 1)).card = 2 ∧ (C.cls (τ 2)).card = 2) := by
    omega
  · exact (C.perm τ.symm).count_511 (by rw [hcls]; exact h.1) (by rw [hcls]; exact h.2.1)
      (by rw [hcls]; exact h.2.2)
  · exact (C.perm τ.symm).count_421 hX' (by rw [hcls]; exact h.1) (by rw [hcls]; exact h.2.1)
      (by rw [hcls]; exact h.2.2)
  · exact (C.perm τ.symm).count_331 hX' (by rw [hcls]; exact h.1) (by rw [hcls]; exact h.2.1)
      (by rw [hcls]; exact h.2.2)
  · exact (C.perm τ.symm).count_322 hX' (by rw [hcls]; exact h.1) (by rw [hcls]; exact h.2.1)
      (by rw [hcls]; exact h.2.2)

end Kalai5.LemmaB
