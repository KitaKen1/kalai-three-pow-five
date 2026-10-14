import Mathlib.Tactic

/-! A kernel-checked obstruction for a labelled B19 boundary.
The geometric labelling/transfer is a separate obligation; this file alone
does not exclude any actual polytope. Bit i denotes vertex i (0 <= i < 8).
-/
namespace Kalai5.B19Boundary

def squareA : List Nat :=
  [0,1,2,3,4,6,8,9,12,15,16,17,18,19,20,22,24,25,28]
def squareB : List Nat :=
  [0,1,2,3,4,6,8,9,12,15,32,33,34,35,36,38,40,41,44]
def pentC : List Nat :=
  [0,1,2,3,16,17,18,19,32,33,34,35,64,66,80,82,128,130,160,162,192,194,241]
def pentD : List Nat :=
  [0,1,8,9,16,17,24,25,32,33,40,41,64,72,80,88,128,136,160,168,192,200,241]

def maskCard (m : Nat) : Nat := ((List.range 8).filter (fun i => m.testBit i)).length

def compatible (t : Fin 256) : Prop :=
  maskCard t.val=4 ∧ t.val ≠ 15 ∧ (t.val &&& 31) ∈ squareA ∧
    (t.val &&& 47) ∈ squareB ∧ (t.val &&& 243) ∈ pentC ∧ (t.val &&& 249) ∈ pentD

instance (t : Fin 256) : Decidable (compatible t) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def candidates : List Nat := [86,92,166,172,198,204]
def boundary : List Nat := [22,28,38,44,82,88,162,168,194,200]

def covers (a b c d : Nat) : Prop :=
  ∀ q ∈ boundary,(q &&& a)=q ∨ (q &&& b)=q ∨ (q &&& c)=q ∨ (q &&& d)=q

instance (a b c d : Nat) : Decidable (covers a b c d) :=
  inferInstanceAs (Decidable (∀ q ∈ boundary,_))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem compatible_iff : ∀ t : Fin 256,compatible t ↔ t.val ∈ candidates := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem catalogue_no_cover : ∀ a ∈ candidates,∀ b ∈ candidates,∀ c ∈ candidates,
    ∀ d ∈ candidates,¬ covers a b c d := by decide +kernel

/-- Four compatible labelled tetrahedra cannot cover the ten boundary triangles.
Distinctness is unnecessary, so repeated tetrahedra cannot evade the check. -/
theorem no_four_tetrahedra (a b c d : Fin 256)
    (ha : compatible a) (hb : compatible b) (hc : compatible c) (hd : compatible d) :
    ¬ covers a.val b.val c.val d.val :=
  catalogue_no_cover a.val ((compatible_iff a).1 ha) b.val ((compatible_iff b).1 hb)
    c.val ((compatible_iff c).1 hc) d.val ((compatible_iff d).1 hd)

end Kalai5.B19Boundary
