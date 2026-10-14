import Kalai5.LemmaB.Eight.Pattern
import Kalai5.LemmaB.Classes

/-!
# Lemma B at sixteen vertices: rank-three configurations

In the rank-three case, after choosing representatives `x_v` (`v < 8`) of the vertex pairs, every
vertex position `q(x_v) = (u₁, u₂, u₃)(x_v)` is one of three independent classes `p_j` (with sign
`+` after normalizing the representatives), and two more coordinates `k_v ∈ ℝ²` complete the
picture.  The counting only uses:

* `real`: for all `a ∈ ℝ³`, `b ∈ ℝ²`, some linear form takes the value `a_{c v} + ⟪b, k_v⟫` at
  `x_v` (octahedral coordinates);
* convex position of each fibre `K_j = {k_v : c v = j}`, injectivity within fibres, nonempty
  fibres, and the spanning of the fibre differences (full dimension).

`ExtraPM`: a fourth `±1`-functional with `b ≠ 0`; it hands the case to Lemma A.
-/

namespace Kalai5.LemmaB.Eight

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The fibre of class `j`. -/
noncomputable def fibre (c : Fin 8 → Fin 3) (k : Fin 8 → E 2) (j : Fin 3) : Finset (E 2) :=
  (Finset.univ.filter fun v => c v = j).image k

/-- A rank-three configuration for the representatives `x`. -/
structure Config (x : Fin 8 → E5) where
  /-- the class of `x_v` -/
  c : Fin 8 → Fin 3
  /-- the planar coordinates of `x_v` -/
  k : Fin 8 → E 2
  /-- octahedral coordinates are realized by linear forms -/
  real : ∀ (a : Fin 3 → ℝ) (b : E 2), ∃ z : E5, ∀ v, ⟪z, x v⟫ = a (c v) + ⟪b, k v⟫
  /-- every class occurs -/
  surj : Function.Surjective c
  /-- points of a fibre are distinct -/
  inj : ∀ v w, c v = c w → k v = k w → v = w
  /-- each point is a vertex of its fibre polygon -/
  convpos : ∀ v, k v ∈ (convexHull ℝ (fibre c k (c v) : Set (E 2))).extremePoints ℝ
  /-- the fibre differences span the plane -/
  span : ∀ b : E 2, (∀ v w, c v = c w → ⟪b, k v⟫ = ⟪b, k w⟫) → b = 0

/-- A fourth `±1`-functional. -/
def Config.ExtraPM {x : Fin 8 → E5} (C : Config x) : Prop :=
  ∃ (a : Fin 3 → ℝ) (b : E 2), b ≠ 0 ∧
    ∀ v, a (C.c v) + ⟪b, C.k v⟫ = 1 ∨ a (C.c v) + ⟪b, C.k v⟫ = -1

end Kalai5.LemmaB.Eight
