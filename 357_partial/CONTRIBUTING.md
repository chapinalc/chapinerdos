# Contributing

Corrections, simplifications, and independent checks are welcome.

Please open an issue before making a substantial mathematical change.
Any change to a formal theorem should be reflected in the manuscript,
and any change to the manuscript's formal claims should be checked
against the Lean statement.

Contributions must:

- build with the pinned Lean and mathlib versions;
- introduce no `sorry`, `admit`, user-declared axiom, or unsafe
  declaration;
- preserve the distinction between the finite formal theorem and the
  human-written asymptotic optimization; and
- include an explanation of the mathematical effect of the change.

Run `./scripts/static_check.sh`, `lake build`, and
`./scripts/build_paper.sh` before opening a pull request.
