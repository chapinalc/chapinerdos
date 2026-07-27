# An adaptive packing bound for Erdős Problem 357

This repository contains a Lean 4 development and an accompanying
manuscript for a finite adaptive-packing inequality concerning distinct
consecutive sums.

## Result

Let \(f(n)\) be the maximum \(k\) for which there are integers
\(1 \le a_1 < \cdots < a_k \le n\) whose nonempty consecutive sums are
all distinct. The manuscript proves

\[
f(n) \le \frac n2 + \frac{9}{2^{7/3}}n^{2/3} + O(n^{1/3}).
\]

In particular, \(f(n) \le (1/2+o(1))n\). This is meaningful progress on
[Erdős Problem 357](https://www.erdosproblems.com/357), but it does
**not** resolve the conjecture \(f(n)=o(n)\).

The central finite statement is formalized in
[`Erdos357AdaptiveBound.lean`](Erdos357AdaptiveBound.lean). The formal
file also proves the convenient integral specialization

\[
2f(n) \le n+8m^2+4 \qquad (n\le m^3).
\]

## Release status

This bundle is a **draft that requires personalization and a green
GitHub Actions run before public release**. Search for `REPLACE` and
follow [`RELEASE_CHECKLIST.md`](RELEASE_CHECKLIST.md). In particular:

- replace the author, affiliation, and repository placeholders;
- choose the manuscript license in [`paper/LICENSE.md`](paper/LICENSE.md);
- have a human author check every mathematical and novelty claim; and
- require both CI jobs to pass before citing the formalization as
  kernel-checked.

The cautious novelty statement is “to the best of our knowledge.” A
literature search cannot prove absence from all unpublished or
unindexed work.

## Reproduce the checks

The project pins Lean 4.27.0 and mathlib v4.27.0.

```bash
./scripts/static_check.sh
lake build
./scripts/build_paper.sh
```

For a prospective release, after replacing all placeholders, run:

```bash
./scripts/release_check.sh
```

GitHub Actions uses the official
[`leanprover/lean-action`](https://github.com/leanprover/lean-action),
builds the Lake target, runs an additional Lean checker, and rebuilds
the paper. See [`VERIFICATION.md`](VERIFICATION.md) for exactly what
was and was not confirmed while this archive was prepared.

## Repository contents

- `Erdos357AdaptiveBound.lean` — formal development.
- `lakefile.lean`, `lake-manifest.json`, `lean-toolchain` — pinned Lean
  project.
- `paper/Erdos357AdaptiveBoundPaper.tex` — manuscript source.
- `paper/Erdos357AdaptiveBoundPaper.pdf` — built manuscript.
- `.github/workflows/ci.yml` — automated Lean and LaTeX checks.
- `scripts/` — local static, paper, and release checks.
- `CITATION.cff` and `.zenodo.json` — citation and archiving metadata.
- `LITERATURE_REVIEW.md` — search scope, prior bounds, and the cautious
  novelty assessment.
- `RELEASE_CHECKLIST.md` — required steps before publication.

## Relationship to the official formal statement

The local definition is designed to use the same finite-index,
strict-monotonicity, range, and order-connected-finset data as the
Formal Conjectures entry. The upstream source cited by this draft is
pinned to commit
[`c252a41054125b5fd9c8356e2137cd9b55337657`](https://github.com/google-deepmind/formal-conjectures/blob/c252a41054125b5fd9c8356e2137cd9b55337657/FormalConjectures/ErdosProblems/357.lean).

## Uploading to GitHub

Create an empty repository named `Erdos357AdaptiveBound`, extract this
archive, and run:

```bash
git init
git add .
git commit -m "Initial release candidate"
git branch -M main
git remote add origin https://github.com/REPLACE_ME/Erdos357AdaptiveBound.git
git push -u origin main
```

Then open the Actions tab and confirm that the Lean and paper jobs are
green. Do not describe this as a solution to Problem 357; describe it
as a new upper bound or partial result.

## Citation

After replacing the metadata placeholders, GitHub will expose
[`CITATION.cff`](CITATION.cff) through its “Cite this repository”
interface. For a durable scholarly record, create a tagged GitHub
release and archive that release with Zenodo to obtain a DOI.

## Licensing

The Lean source and repository scripts are licensed under Apache-2.0;
see [`LICENSE`](LICENSE). The manuscript is explicitly excluded from
that grant until the author selects a paper license; see
[`paper/LICENSE.md`](paper/LICENSE.md).
