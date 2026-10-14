import Kalai5.Cube3.Fibres

/-!
# Relabeling cube classes while retaining the offset relation

The Klein four permutations act transitively and preserve Balanced (possibly
reversing its two sides). An arbitrary permutation is never presumed valid.
-/

namespace Kalai5.Cube3

open Set

def classPerm (j : Fin 4) : Equiv.Perm (Fin 4) :=
  ![Equiv.refl _, (Equiv.swap 0 1).trans (Equiv.swap 2 3),
    (Equiv.swap 0 2).trans (Equiv.swap 1 3),
    (Equiv.swap 0 3).trans (Equiv.swap 1 2)] j

lemma classPerm_zero (j : Fin 4) : classPerm j 0 = j := by
  fin_cases j <;> decide

lemma classPerm_balanced (j : Fin 4) (a : Fin 4 → ℝ) (ha : Balanced a) :
    Balanced (fun k => a ((classPerm j).symm k)) := by
  change a 0 + a 3 = a 1 + a 2 at ha
  fin_cases j <;> simp [classPerm,Balanced,Equiv.swap_apply_def] <;> linarith

variable {x : Fin 8 → E5} (C : Config x)

namespace Config

noncomputable def relabel (τ : Equiv.Perm (Fin 4))
    (hτ : ∀ a, Balanced a → Balanced (fun j => a (τ.symm j))) : Config x where
  c := fun v => τ.symm (C.c v)
  k := C.k
  surj := by
    intro j
    obtain ⟨v,hv⟩ := C.surj (τ j)
    exact ⟨v,by change τ.symm (C.c v) = j; rw [hv,τ.symm_apply_apply]⟩
  inj := by
    intro v w hc hk
    exact C.inj v w (τ.symm.injective hc) hk
  convpos := by
    intro v
    have hf : fibre (fun w => τ.symm (C.c w)) C.k (τ.symm (C.c v)) =
        fibre C.c C.k (C.c v) := by
      unfold fibre
      congr 1
      ext w
      simp
    rw [hf]
    exact C.convpos v
  real := by
    intro a ha b
    exact C.real (fun j => a (τ.symm j)) (hτ a ha) b
  faithful := by
    intro a ha b hb
    exact C.faithful (fun j => a (τ.symm j)) (hτ a ha) b hb

lemma relabel_cls (τ : Equiv.Perm (Fin 4))
    (hτ : ∀ a, Balanced a → Balanced (fun j => a (τ.symm j))) (j : Fin 4) :
    (C.relabel τ hτ).cls j = C.cls (τ j) := by
  ext v
  simp [cls,relabel,Equiv.symm_apply_eq]

end Config
end Kalai5.Cube3
