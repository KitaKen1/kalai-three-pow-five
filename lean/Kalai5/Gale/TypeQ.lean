import Kalai5.Gale.CombX

/-!
# Type-level check: the free sum of two triangles

`qDualRow = (6,15,18,9; 36)` is the row of the free sum `Δ2 ⊕ Δ2` (the polar of the product of two
triangles).  `Tab.checkQ` is `Tab.check` with the row test replaced by: either the row is not
`qDualRow`, or the facet masks are exactly the sets meeting some 3-set `U` in two points and its
complement in two points (`Tab.qOK`).
-/

namespace Kalai5

/-- Row of the free sum of two triangles, the polar of the product of two triangles. -/
def qDualRow : Row := ⟨6, 15, 18, 9, 36⟩

namespace Gale

/-- The subsets meeting `U` in two elements and its complement in two elements. -/
def famQ (n U : ℕ) : ℕ :=
  maskOf (2 ^ n) fun S => popc n (S &&& U) == 2 && popc n (S &&& cmask n U) == 2

/-- The facet masks are the `2 + 2` sets for some 3-set `U`. -/
def Tab.qOK (T : Tab) (fv : ℕ) (rk : ℕ × ℕ × ℕ) : Bool :=
  (List.range (2 ^ T.n)).any fun U => popc T.n U == 3 && T.dimV fv rk 3 == famQ T.n U

/-- The type check for one sorted code sequence. -/
def Tab.checkQ (T : Tab) (cs : List ℕ) : Bool :=
  if min (nlines cs) 2 != T.n - 5 then true
  else
    let circ := circuits cs
    let cands := candidates cs
    if (List.range T.n).all (fun j => covered circ (T.co j)) then
      (T.covV circ ||| T.farV cands) == T.full &&
        (decide (T.row (T.faceV circ) (T.rk (nzMask cs) ((List.range (nlines cs)).map (lineMask cs)))
            ≠ qDualRow) ||
          T.qOK (T.faceV circ) (T.rk (nzMask cs) ((List.range (nlines cs)).map (lineMask cs))))
    else (List.range T.n).any fun j => !covered circ (T.co j) && farkas cands (T.co j)

/-- All completions of the prefix `pre` pass the type check. -/
def checkFromQ (T : Tab) (k last nl : ℕ) (pre : List ℕ) : Bool :=
  (gen k last nl).all fun cs => T.checkQ (pre ++ cs)

theorem checkQ_of_prefixes (T : Tab) (a b last nl : ℕ)
    (h : ∀ p ∈ gen a last nl, checkFromQ T b (lastOf last p) (nlOf nl p) p = true) :
    ∀ cs ∈ gen (a + b) last nl, T.checkQ cs = true := by
  intro cs hcs
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_gen_append a b last nl cs hcs
  have := h p hp
  unfold checkFromQ at this
  rw [List.all_eq_true] at this
  exact this q hq

set_option maxRecDepth 100000

-- run the kernel checks one at a time (parallel elaboration multiplies the kernel caches)
set_option Elab.async false

theorem chkQ6_0 : checkFromQ (tab 6) 4 0 0 [0, 0] = true := by decide +kernel
theorem chkQ6_1 : checkFromQ (tab 6) 4 1 1 [0, 1] = true := by decide +kernel
theorem chkQ6_2 : checkFromQ (tab 6) 4 2 1 [0, 2] = true := by decide +kernel
theorem chkQ6_3 : checkFromQ (tab 6) 4 1 1 [1, 1] = true := by decide +kernel
theorem chkQ6_4 : checkFromQ (tab 6) 4 2 1 [1, 2] = true := by decide +kernel
theorem chkQ6_5 : checkFromQ (tab 6) 4 3 2 [1, 3] = true := by decide +kernel
theorem chkQ6_6 : checkFromQ (tab 6) 4 4 2 [1, 4] = true := by decide +kernel
theorem chkQ6_7 : checkFromQ (tab 6) 4 2 1 [2, 2] = true := by decide +kernel
theorem chkQ6_8 : checkFromQ (tab 6) 4 3 2 [2, 3] = true := by decide +kernel
theorem chkQ6_9 : checkFromQ (tab 6) 4 4 2 [2, 4] = true := by decide +kernel

lemma gen2_eq_6' : gen 2 0 0 = [[0, 0], [0, 1], [0, 2], [1, 1], [1, 2], [1, 3], [1, 4], [2, 2],
    [2, 3], [2, 4]] := by
  decide +kernel

theorem checkQ6 : ∀ cs ∈ gen 6 0 0, (tab 6).checkQ cs = true := by
  refine checkQ_of_prefixes (tab 6) 2 4 0 0 ?_
  intro p hp
  rw [gen2_eq_6'] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact chkQ6_0
  · exact chkQ6_1
  · exact chkQ6_2
  · exact chkQ6_3
  · exact chkQ6_4
  · exact chkQ6_5
  · exact chkQ6_6
  · exact chkQ6_7
  · exact chkQ6_8
  · exact chkQ6_9

end Gale

end Kalai5
