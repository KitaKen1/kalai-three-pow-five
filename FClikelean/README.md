# Formal Conjectures submission draft

[Kalai.lean](Kalai.lean) records the general conjecture and three dimension
ranges. Its four `sorry` bodies are statement placeholders, not proofs.

| Declaration in `namespace Kalai` | Scope | Draft category |
|---|---|---|
| `three_pow` | General dimension | `research open` |
| `three_pow_le_four` | Dimension at most four | `research solved`, by Sanyal–Werner–Ziegler |
| `three_pow_five` | Dimension five | `research solved`, with an external Lean proof |
| `three_pow_ge_six` | Dimension at least six | `research open` |

The dimension-five signature is identical to the proof candidate in
[../lean/Kalai5/FormalConjectures.lean](../lean/Kalai5/FormalConjectures.lean), the Comparator reference in
[../lean/Challenge.lean](../lean/Challenge.lean), and the original public
bridge in [../leanWithoutComparator/Kalai5/FormalConjectures.lean](../leanWithoutComparator/Kalai5/FormalConjectures.lean).
No proof imports this draft.

The dimension-five `formal_proof` link identifies the prior verified archive
at a fixed commit in `KitaKen1/kalai-three-pow-five-lean`. It does not claim
a public run for this FC package has succeeded. Private CI passed; see
[receipts](../verification/private-ci/README.md). After public CI succeeds,
the link can be updated to that public proof commit.

The FC draft, proof candidate and Comparator reference use the same Lean
`v4.33.1` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
The FC checkout is fixed to `ef4943a77f7caad81e63e3b4c68b36151af2fc65`.
The historical proof link uses rc3; it is not a new FC-version CI result.

```sh
cd FClikelean
lake build Kalai
```

Four warnings for the statement placeholders are expected. Compilation is
not a proof of the statements. The new copy, including its proof-link
attribute, should be compiled in the target FC environment before submission.
No upstream acceptance or submission is claimed by this local package.
