import Kalai5.Cube3.PolarModel
import Kalai5.Cube3.FibreLift
import Kalai5.Cube3.Fibres

/-!
# Removing three singleton fibres

The distinguished fibre is class 0. The other classes have planar points q₀,
q₁,q₂. Their unique compatible displacement in class 0 is q₀+q₁-q₂.
The resulting polar has a cube coordinate and a three-dimensional auxiliary
body. No arbitrary permutation of the balanced offsets is assumed.
-/

namespace Kalai5.Cube3

open Set

noncomputable def anchor (q : Fin 3 → E 2) : E 2 := q 0 + q 1 - q 2

noncomputable def dot2 (p : E5) (k : E 2) : ℝ := p 3 * k 0 + p 4 * k 1

noncomputable def singletonMap (q : Fin 3 → E 2) : E5 →ₗ[ℝ] E5 where
  toFun p := (WithLp.equiv 2 (Fin 5 → ℝ)).symm
    ![p 0 + p 1 + p 2 - dot2 p (anchor q),
      p 0 - dot2 p (q 0), p 1 - dot2 p (q 1), p 3, p 4]
  map_add' := by
    intro p t; ext i; fin_cases i <;> simp [dot2] <;> ring
  map_smul' := by
    intro a p; ext i; fin_cases i <;> simp [dot2] <;> ring

lemma singletonMap_injective (q : Fin 3 → E 2) : Function.Injective (singletonMap q) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro p hp
  have h0 := congrArg (fun t : E5 => t 0) hp
  have h1 := congrArg (fun t : E5 => t 1) hp
  have h2 := congrArg (fun t : E5 => t 2) hp
  have h3 := congrArg (fun t : E5 => t 3) hp
  have h4 := congrArg (fun t : E5 => t 4) hp
  simp [singletonMap] at h3 h4
  simp [singletonMap, dot2, h3, h4] at h0 h1 h2
  ext i; fin_cases i <;> simp [h1, h2, h3, h4] <;> linarith

noncomputable def singletonEquiv (q : Fin 3 → E 2) : E5 ≃ₗ[ℝ] E5 :=
  LinearEquiv.ofInjectiveEndo (singletonMap q) (singletonMap_injective q)

noncomputable def cubePart (p : E5) : E 3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![p 0, p 1, p 2]

noncomputable def auxPart (p : E5) : E 3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![p 0 + p 1 + p 2, p 3, p 4]

def cubeBox : Set (E 3) := {u | ∀ i, |u i| ≤ 1}

variable {x : Fin 8 → E5} (C : Config x)

namespace Config

/-- Singleton class cardinalities provide the points required by the shear. -/
lemma singleton_points
    (hsize : ∀ i : Fin 3, (C.cls (![1,2,3] i)).card = 1) :
    ∃ q : Fin 3 → E 2, ∀ i : Fin 3, ∀ v,
      C.c v = (![1,2,3] i : Fin 4) → C.k v = q i := by
  classical
  choose v hv using fun i => Finset.card_eq_one.1 (hsize i)
  refine ⟨fun i => C.k (v i), ?_⟩
  intro i w hw
  have hmem : w ∈ C.cls (![1,2,3] i) := by simp [cls, hw]
  rw [hv i, Finset.mem_singleton] at hmem
  rw [hmem]

lemma singleton_value (q : Fin 3 → E 2) (p : E5) (v : Fin 8) :
    C.value (singletonEquiv q p) v =
      ![p 0 + p 1 + p 2 + dot2 p (C.k v - anchor q),
        p 0 + dot2 p (C.k v - q 0), p 1 + dot2 p (C.k v - q 1),
        -p 2 + dot2 p (C.k v - q 2)] (C.c v) := by
  rw [C.value_eq]
  generalize C.c v = j
  fin_cases j <;> simp [singletonEquiv, LinearEquiv.coe_ofInjectiveEndo,
    singletonMap, offsets, dot2, anchor] <;> ring

/-- The only constraints involving the large fibre. -/
def singletonAux (q : Fin 3 → E 2) : Set (E 3) :=
  {y | ∀ v, C.c v = 0 →
    |y 0 + y 1 * (C.k v - anchor q) 0 + y 2 * (C.k v - anchor q) 1| ≤ 1}

def singletonModel (q : Fin 3 → E 2) : Set E5 :=
  {p | cubePart p ∈ cubeBox ∧ auxPart p ∈ C.singletonAux q}

/-- Exact H-description, with all three singleton constraints retained. -/
theorem singleton_mem_iff (q : Fin 3 → E 2)
    (hsingle : ∀ i : Fin 3, ∀ v, C.c v = (![1,2,3] i : Fin 4) → C.k v = q i)
    (p : E5) : singletonEquiv q p ∈ C.polarModel ↔ p ∈ C.singletonModel q := by
  constructor
  · intro hp
    constructor
    · intro i
      obtain ⟨v, hv⟩ := C.surj (![1,2,3] i)
      have hk := hsingle i v hv
      have h := hp v
      rw [C.singleton_value, hv, hk] at h
      fin_cases i <;> simpa [cubePart, dot2] using h
    · intro v hv
      have h := hp v
      rw [C.singleton_value, hv] at h
      simpa [auxPart, dot2, add_assoc] using h
  · rintro ⟨hc, hd⟩ v
    rw [C.singleton_value]
    generalize hv : C.c v = j
    fin_cases j
    · simpa [auxPart, dot2, add_assoc] using hd v hv
    · have hk := hsingle 0 v hv
      simpa [hk, dot2, cubePart] using hc 0
    · have hk := hsingle 1 v hv
      simpa [hk, dot2, cubePart] using hc 1
    · have hk := hsingle 2 v hv
      simpa [hk, dot2, cubePart] using hc 2

lemma singletonModel_image (q : Fin 3 → E 2)
    (hsingle : ∀ i : Fin 3, ∀ v, C.c v = (![1,2,3] i : Fin 4) → C.k v = q i) :
    singletonEquiv q '' C.singletonModel q = C.polarModel := by
  ext p
  obtain ⟨p, rfl⟩ := (singletonEquiv q).surjective p
  rw [(singletonEquiv q).injective.mem_set_image, C.singleton_mem_iff q hsingle]

/-- The graph description is precisely a fibre product, not a projection or relaxation. -/
theorem singleton_fibreProduct (q : Fin 3 → E 2) :
    (fun p : E5 => (auxPart p, cubePart p)) '' C.singletonModel q =
      fibreProduct (C.singletonAux q) cubeBox (fun y => y 0) (fun u => ∑ i, u i) := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨hp.2, hp.1, ?_⟩
    simp [auxPart, cubePart, Fin.sum_univ_three]
  · rintro ⟨hy, hu, he⟩
    let p : E5 := (WithLp.equiv 2 (Fin 5 → ℝ)).symm ![z.2 0, z.2 1, z.2 2, z.1 1, z.1 2]
    have hu' : cubePart p = z.2 := by ext i; fin_cases i <;> rfl
    have hy' : auxPart p = z.1 := by
      ext i; fin_cases i
      · simpa [auxPart, p, Fin.sum_univ_three] using he.symm
      · rfl
      · rfl
    refine ⟨p, ?_, ?_⟩
    · exact ⟨hu' ▸ hu, hy' ▸ hy⟩
    · exact Prod.ext hy' hu'

end Config
end Kalai5.Cube3
