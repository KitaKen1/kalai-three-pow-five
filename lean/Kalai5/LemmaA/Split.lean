import Kalai5.LemmaA.Cert

/-!
# Lemma A: assembling split kernel checks

The certificate of a family is checked in small pieces (facet-record chunks and subtrees, each by
`decide +kernel` in its own declaration, which keeps the kernel's caches small); these lemmas put
the pieces together.
-/

namespace Kalai5.LemmaA.Family

variable {F : Family}

theorem walk_branch_of {facts : List (ℕ × ℤ)} {p : ℕ} {n z q : Node}
    (h0 : (factOf facts p).isNone = true) (hn : F.walk ((p, -1) :: facts) n = true)
    (hz : F.walk ((p, 0) :: facts) z = true) (hq : F.walk ((p, 1) :: facts) q = true) :
    F.walk facts (.branch p n z q) = true := by
  simp only [walk, h0, hn, hz, hq, Bool.and_self]

theorem check_of (h1 : F.facets.all F.recOK = true) (h2 : F.walk [] F.tree = true) :
    F.check = true := by
  simp only [check, h1, h2, Bool.and_self]

end Kalai5.LemmaA.Family
