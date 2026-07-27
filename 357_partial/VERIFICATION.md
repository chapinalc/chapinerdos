# Verification record

This file separates confirmations that were completed while packaging
the repository from checks that require the eventual public CI run.

## Completed during packaging

- The Lean source was normalized to UTF-8 text and audited statically.
- The source contains no line matching the repository's forbidden-code
  patterns for `sorry`, `admit`, a user-declared `axiom`, or an
  `unsafe` declaration.
- The Lake dependency manifest was pinned to mathlib v4.27.0, tag
  commit `a3a10db0e9d66acbebf76c5e6a135066525ac900`.
- The manuscript was rebuilt from the included TeX source.
- Every rendered PDF page was visually inspected.
- The archive was tested after creation and its extracted file hashes
  were compared with the source directory.

Exact hashes and PDF inspection details are recorded below by the
packaging process.

<!-- VERIFICATION_RESULTS_BEGIN -->
- Packaging date: 2026-07-26.
- Lean source: 1,841 lines.
- Final Lean source SHA-256:
  `1d80799caa6f05ac8a1cd8845a74fb28cb1822dd974a40c0e754ec5e2aa4652e`.
- Supplied Lean source SHA-256:
  `3fa83347189397e96b5aae5c0f2dc4e35a6c28a9f93d39bccfe4895b0b5d5d30`.
  The only changes to that source are the copyright/license wording and
  replacing “kernel-checks” with the more precise “formalizes” in a
  module comment; no Lean declaration or proof term was changed.
- TeX source SHA-256:
  `6d13924830d424f02e56328a2e5ad9e0e4383856d6ba957ebe9643958202c988`.
- PDF SHA-256:
  `a39757318fc089dad8d61ced5f9c2fb41a523e5cf37aff11148b8254daac5267`.
- Lake manifest SHA-256:
  `175685f72c4862fc45586ee8a3c5b84aeb4b2a4f20fc73c7b856678692c125cb`.
- Static forbidden-code scan: PASS.
- JSON/YAML parsing: PASS.
- `CITATION.cff` structural validation against the official CFF schema:
  PASS. Its deliberately fictional draft URLs were not treated as
  release metadata.
- Every pinned manifest revision/configuration target was fetched
  successfully from its upstream GitHub repository.
- LaTeX build: PASS with no unresolved citations, references, overfull
  boxes, underfull boxes, or package warnings.
- PDF inspection: 8 US-letter pages, all listed fonts embedded, no
  encryption, forms, JavaScript, or suspect objects.
- Visual inspection: PASS for all 8 rendered pages.
- Draft-release guard: PASS; `release_check.sh` exits nonzero while the
  author, affiliation, license, and repository placeholders remain.
<!-- VERIFICATION_RESULTS_END -->

## Not completed in the packaging sandbox

A fresh Lean kernel run could not be executed in the packaging sandbox:
the installed Lean runtime resolves its executable through
`/proc/self/exe`, and that read is blocked by the sandbox policy. This
is an environment restriction, not a Lean diagnostic and not evidence
that the file succeeds or fails.

Therefore a green GitHub Actions run is mandatory before the
formalization is described as freshly kernel-checked. The CI workflow:

1. installs the toolchain from `lean-toolchain`;
2. restores the pinned mathlib dependency;
3. runs `lake build`;
4. runs the repository's static audit; and
5. invokes the additional checker exposed by `leanprover/lean-action`.

Before release, replace this section with the public commit hash and
successful CI run URL, while retaining an accurate record of what was
checked.
