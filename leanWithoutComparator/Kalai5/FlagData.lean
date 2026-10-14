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
# The global reduction (MAIN_PROOF §1–2), as pure arithmetic

`FlagData` collects the face and flag numbers of a (putative) centrally symmetric 5-polytope.
`FlagData.Valid` lists the facts the geometric foundations have to supply:

* Euler's relation, the four summed-Euler flag identities, antipodal parity of faces and flags;
* nonnegativity of the polygon excess `A` and of `B = 2f₁₃ - 3f₀₃`, `C = 2f₁₃ - 3f₁₄`;
* the centrally symmetric toric bounds `G, G* ≥ 0` (Sanyal–Werner–Ziegler);
* the incidence bound `2 f₀₄ ≤ f₀ f₄` (a facet contains at most one vertex of each antipodal pair).

From these alone we prove (`global_reduction`): a counterexample with `14 ≤ f₀ ≤ f₄` has
`(f₀, f₄)` in the explicit fifteen-element `ledger`.
-/

namespace Kalai5

/-- Face and flag numbers. `v e p r h` are `f₀ … f₄`; `I = f₀₄`, `x = f₀₂`, `y = f₂₄`. -/
structure FlagData where
  v : ℕ
  e : ℕ
  p : ℕ
  r : ℕ
  h : ℕ
  I : ℕ
  x : ℕ
  y : ℕ
  f03 : ℕ
  f13 : ℕ
  f14 : ℕ
  f024 : ℕ

namespace FlagData

variable (D : FlagData)

/-- `t = f₁ + f₃`. -/
def t : ℕ := D.e + D.r

/-- `s = f₀ + f₄`. -/
def s : ℕ := D.v + D.h

/-- Number of nonempty faces, including the polytope itself. -/
def total : ℕ := D.v + D.e + D.p + D.r + D.h + 1

/-- Polygon excess `A = Σ_Q (f₀(Q) - 3)(f₀(P/Q) - 3) = f₀₂₄ - 3f₀₂ - 3f₂₄ + 9f₂`. -/
def A : ℤ := D.f024 - 3 * D.x - 3 * D.y + 9 * D.p

/-- `B = 2 f₁₃ - 3 f₀₃` (degree excess in 3-faces). -/
def B : ℤ := 2 * D.f13 - 3 * D.f03

/-- `C = 2 f₁₃ - 3 f₁₄` (the polar counterpart of `B`). -/
def C : ℤ := 2 * D.f13 - 3 * D.f14

/-- Centrally symmetric toric slack `G = g₂ - 5 = f₁ + f₀₂ - 3f₂ - 5f₀ + 10`. -/
def G : ℤ := D.e + D.x - 3 * D.p - 5 * D.v + 10

/-- The polar slack `G*`. -/
def Gs : ℤ := D.r + D.y - 3 * D.p - 5 * D.h + 10

/-- The facts the foundations layer has to supply for a centrally symmetric 5-polytope. -/
structure Valid : Prop where
  euler : (D.v : ℤ) - D.e + D.p - D.r + D.h = 2
  even_v : Even D.v
  even_e : Even D.e
  even_p : Even D.p
  even_r : Even D.r
  even_h : Even D.h
  even_I : Even D.I
  even_x : Even D.x
  even_y : Even D.y
  f03_eq : (D.f03 : ℤ) = D.I + D.x - 2 * D.e
  f14_eq : (D.f14 : ℤ) = D.I + D.y - 2 * D.r
  f13_eq : (D.f13 : ℤ) = D.I + D.x + D.y - 2 * (D.e + D.r)
  f024_eq : (D.f024 : ℤ) = 2 * D.I + 2 * D.x + 2 * D.y - 4 * (D.e + D.r)
  A_nonneg : 0 ≤ D.A
  B_nonneg : 0 ≤ D.B
  C_nonneg : 0 ≤ D.C
  G_nonneg : 0 ≤ D.G
  Gs_nonneg : 0 ≤ D.Gs
  incidence : 2 * D.I ≤ D.v * D.h

variable {D}

/-- Total face count: `#faces = 2t + 3`. -/
lemma total_eq (hD : D.Valid) : (D.total : ℤ) = 2 * D.t + 3 := by
  have := hD.euler
  simp only [total, t]; push_cast; linarith

/-- `A + B + C = 9 f₂ - 6 t`. -/
lemma ABC_identity (hD : D.Valid) : D.A + D.B + D.C = 9 * D.p - 6 * D.t := by
  simp only [A, B, C, t]
  rw [hD.f024_eq, hD.f13_eq, hD.f03_eq, hD.f14_eq]; push_cast; ring

/-- `G + G* + A = 2 f₀₄ - 8 s + 26`. -/
lemma GGA_identity (hD : D.Valid) : D.G + D.Gs + D.A = 2 * D.I - 8 * D.s + 26 := by
  have := hD.euler
  simp only [G, Gs, A, s]
  rw [hD.f024_eq]; push_cast; linarith

/-- Consequence of `A + B + C ≥ 0`: `t ≥ 3s - 6`. -/
lemma three_s_le (hD : D.Valid) : 3 * (D.s : ℤ) ≤ D.t + 6 := by
  have h1 := ABC_identity hD
  have := hD.A_nonneg; have := hD.B_nonneg; have := hD.C_nonneg
  have := hD.euler
  simp only [s, t] at *; push_cast at *; linarith

end FlagData

/-- The fifteen endpoint pairs `(f₀, f₄)`, `f₀ ≤ f₄`, left after the global reduction. -/
def ledger : List (ℕ × ℕ) :=
  [(14, 16), (14, 18), (14, 20), (14, 22), (14, 24), (14, 26),
   (16, 16), (16, 18), (16, 20), (16, 22), (16, 24),
   (18, 18), (18, 20), (18, 22), (20, 20)]

/-- The ledger is exactly the set of even pairs `14 ≤ v ≤ h`, `v + h ≤ 40`,
`(v-8)(h-8) ≥ 40` (the last condition removes only `(14,14)`). -/
lemma ledger_spec :
    ledger = ((List.range 41).flatMap fun v => (List.range 41).map fun h => (v, h)).filter
      fun q => 14 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.1 % 2 = 0 ∧ q.2 % 2 = 0 ∧ q.1 + q.2 ≤ 40 ∧
        40 ≤ (q.1 - 8) * (q.2 - 8) := by
  decide +kernel

/-- Pure arithmetic core of the global reduction. -/
theorem ledger_of_arith (v e p r h I : ℕ)
    (heul : (v : ℤ) - e + p - r + h = 2)
    (hev : Even v) (hee : Even e) (heh : Even h) (her : Even r) (heI : Even I)
    (h9 : (0 : ℤ) ≤ 9 * p - 6 * (e + r))
    (hI : (0 : ℤ) ≤ 2 * I - 8 * (v + h) + 26)
    (hinc : 2 * I ≤ v * h)
    (htot : v + e + p + r + h + 1 < 243)
    (hv : 14 ≤ v) (hh : 14 ≤ h) (hvh : v ≤ h) :
    (v, h) ∈ ledger := by
  obtain ⟨v', rfl⟩ := hev
  obtain ⟨h', rfl⟩ := heh
  obtain ⟨e', rfl⟩ := hee
  obtain ⟨r', rfl⟩ := her
  obtain ⟨I', rfl⟩ := heI
  have hs : v' + h' ≤ 20 := by omega
  have hv1 : 7 ≤ v' := by omega
  have hh1 : 7 ≤ h' := by omega
  have hv2 : v' ≤ 13 := by omega
  have hh2 : h' ≤ 13 := by omega
  interval_cases v' <;> interval_cases h' <;> first | omega | simp [ledger]

namespace FlagData

variable {D : FlagData}

/-- **Global reduction.** A counterexample (fewer than 243 faces) with `14 ≤ f₀ ≤ f₄` has
`(f₀, f₄)` in the fifteen-element `ledger`. -/
theorem global_reduction (hD : D.Valid) (hlt : D.total < 243)
    (hv : 14 ≤ D.v) (hh : 14 ≤ D.h) (hvh : D.v ≤ D.h) : (D.v, D.h) ∈ ledger := by
  refine ledger_of_arith D.v D.e D.p D.r D.h D.I hD.euler hD.even_v hD.even_e hD.even_h
    hD.even_r hD.even_I ?_ ?_ hD.incidence hlt hv hh hvh
  · have h1 := ABC_identity hD
    have := hD.A_nonneg; have := hD.B_nonneg; have := hD.C_nonneg
    simp only [t] at h1; push_cast at h1; linarith
  · have h1 := GGA_identity hD
    have := hD.A_nonneg; have := hD.G_nonneg; have := hD.Gs_nonneg
    simp only [s] at h1; push_cast at h1; linarith

/-- In particular `(14,14)` is impossible (MAIN_PROOF §2). -/
theorem not_fourteen_fourteen (hD : D.Valid) (hlt : D.total < 243) :
    ¬ (D.v = 14 ∧ D.h = 14) := by
  rintro ⟨hv, hh⟩
  have := global_reduction hD hlt (by omega) (by omega) (by omega)
  rw [hv, hh] at this
  simp [ledger] at this

end FlagData

end Kalai5
