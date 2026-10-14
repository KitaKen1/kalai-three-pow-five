import Kalai5.Cube3.PositiveFamilies

/-! Combine variable-size vertex families on distinct, nonopposite normal rays. -/

namespace Kalai5.Cube3.PositiveFamily
open Set
variable {x : Fin 8 → E5} {C : Config x} {ι κ : Type*}

noncomputable def reindex (F : PositiveFamily C ι) (e : κ → ι) (he : Function.Injective e) :
    PositiveFamily C κ where
  point k := F.point (e k)
  inj := F.inj.comp he
  extreme k := F.extreme (e k)
  normal k := F.normal (e k)
  unit k := F.unit (e k)
  ray k := F.ray (e k)
  noOpposite i j := F.noOpposite (e i) (e j)

noncomputable def sigma {κ : ι → Type*} (F : ∀ i,PositiveFamily C (κ i))
    (hne : ∀ i j,i ≠ j → ∀ a b,(F i).normal a ≠ (F j).normal b)
    (hop : ∀ i j,∀ a b,(F i).normal a ≠ -(F j).normal b) :
    PositiveFamily C (Sigma κ) where
  point k := (F k.1).point k.2
  inj := by
    rintro ⟨i,a⟩ ⟨j,b⟩ he
    by_cases hij : i=j
    · subst j
      exact congrArg (Sigma.mk i) ((F i).inj he)
    · exfalso
      have hh := congrArg planar he
      obtain ⟨s,hs,ha⟩ := (F i).ray a
      obtain ⟨t,ht,hb⟩ := (F j).ray b
      rw [ha,hb] at hh
      exact hne i j hij a b (unit_ray_eq ((F i).unit a) ((F j).unit b) hs ht hh)
  extreme k := (F k.1).extreme k.2
  normal k := (F k.1).normal k.2
  unit k := (F k.1).unit k.2
  ray k := (F k.1).ray k.2
  noOpposite a b := hop a.1 b.1 a.2 b.2

end Kalai5.Cube3.PositiveFamily
