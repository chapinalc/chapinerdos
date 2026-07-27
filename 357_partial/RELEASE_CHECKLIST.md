# Release checklist

This result improves an upper bound but does not solve Erdős Problem
357. Complete every item before announcing it publicly.

## Identity and metadata

- [ ] Replace every `REPLACE_ME`, `REPLACE BEFORE RELEASE`, `AUTHOR
      NAME`, and `AFFILIATION` placeholder.
- [ ] Add the public repository URL to the manuscript once it exists.
- [ ] Add ORCID identifiers only if they are correct and controlled by
      the named authors.
- [ ] Validate `CITATION.cff`, for example with the Citation File Format
      validator or GitHub's rendered citation panel.
- [ ] Review `.zenodo.json` before enabling Zenodo archiving.

## Mathematical review

- [ ] Have at least one knowledgeable human independently read the
      finite proof and optimization.
- [ ] Check that the manuscript theorem agrees exactly with
      `finite_adaptive_bound_int`.
- [ ] Check that the manuscript clearly distinguishes the stronger
      human-derived asymptotic bound from the coarser cube-scale Lean
      corollary.
- [ ] Recheck the novelty claim immediately before submission. Use “to
      the best of our knowledge,” not an absolute claim.
- [ ] Describe the work as partial progress or a new upper bound, never
      as a solution of \(f(n)=o(n)\).

## Machine verification

- [ ] Run `./scripts/release_check.sh` successfully in a normal local
      environment.
- [ ] Push to GitHub and require the Lean job to be green.
- [ ] Require the additional checker in the Lean job to be green.
- [ ] Require the paper-build job to be green.
- [ ] Record the release commit and CI URL in `VERIFICATION.md`.
- [ ] Recompute `SHA256SUMS` after the final edits.

## Rights and disclosure

- [ ] Replace the author in `paper/LICENSE.md` and deliberately choose
      the manuscript's license.
- [ ] Confirm that every named author accepts responsibility for the
      paper.
- [ ] Revise the AI-assistance disclosure to satisfy the target
      journal, repository, and institution policies.
- [ ] Confirm permission for any text or code not written by the
      authors.

## Release and communication

- [ ] Tag the reviewed commit (for example, `v0.1.0`).
- [ ] Create a GitHub release containing the PDF and source archive.
- [ ] Archive the GitHub release with Zenodo and add the DOI to the
      README, manuscript, and `CITATION.cff`.
- [ ] Send the public paper/repository link to the Erdős Problems
      maintainers as a claimed improvement, not a solution.
- [ ] Consider an arXiv submission and an additive-combinatorics or
      formal-mathematics venue after expert review.
