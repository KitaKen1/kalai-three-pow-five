# Local FC smoke checks

Lean `v4.33.1` and FC Mathlib were used for the three foundation modules
and the two API compatibility modules listed in [smoke-checks.json](smoke-checks.json).
The command exit codes were zero. The logs are retained here; an empty
ProfileCount log means compilation produced no messages.

These are partial checks. They do not establish the complete final theorem,
Comparator acceptance or CI success on this version. A broader exploratory
build found the two compatibility errors, and was interrupted after those
errors were diagnosed. Both corrected modules were then checked separately.
The reference Challenge also compiled successfully, with its expected
placeholder warning. This is a statement check. These records describe the initial local checks. The later complete FC archive,
Comparator and fresh replay passed in [private CI](../private-ci/README.md).
