# Literature and novelty review

Review date: 2026-07-26

## Question reviewed

For the extremal function \(f(n)\) in Erdős Problem 357, has the bound

\[
f(n) \le \frac n2 + O(n^{2/3})
\]

or the parameterized adaptive inequality in the manuscript already
appeared in the accessible literature?

## Sources checked

The review covered the problem database and its references, bibliographic
and full-text searches for the problem's characteristic phrases, forward
and backward reference trails around the main known bounds, the current
Formal Conjectures entry, and the corresponding OEIS record. The most
relevant located sources were:

1. [Erdős Problem 357](https://www.erdosproblems.com/357), including its
   historical notes and known-bound summary.
2. P. Erdős, “Problems and results on combinatorial number theory III”
   (1977), [author-hosted PDF](https://www.renyi.hu/~p_erdos/1977-27.pdf).
3. N. Hegyvári, “On consecutive sums in sequences” (1986),
   [DOI](https://doi.org/10.1007/BF01949064).
4. D. Coppersmith and S. Phillips, “On a question of Erdős on
   subsequence sums” (1996),
   [DOI](https://doi.org/10.1137/S0895480193244139).
5. J. Konieczny, “On consecutive sums in permutations” (2021),
   [DOI](https://doi.org/10.4310/JOC.2021.v12.n3.a3).
6. A. Beker, “On a problem of Erdős and Graham about consecutive sums
   in strictly increasing sequences” (2024),
   [DOI](https://doi.org/10.1112/blms.13098).
7. The [Formal Conjectures Problem 357 source](https://github.com/google-deepmind/formal-conjectures/blob/c252a41054125b5fd9c8356e2137cd9b55337657/FormalConjectures/ErdosProblems/357.lean),
   pinned at commit `c252a41054125b5fd9c8356e2137cd9b55337657`.
8. [OEIS A364132](https://oeis.org/A364132), which records initial
   inverse-extremal values.

## Findings

- The finite problem is attributed to Erdős and Harzheim. Erdős's 1977
  paper asks a related infinite-density question; it should not be
  described as the identical finite formulation.
- The problem database records the construction lower bound
  \(f(n)\ge(2+o(1))\sqrt n\).
- Hegyvári's upper bound concerns the variant without monotonicity.
- Coppersmith and Phillips imply the previously recorded linear bound
  \[
  f(n)\le\left(\frac23-\frac1{512}\right)n+O(\log n).
  \]
- The Konieczny and Beker papers study nearby consecutive-sum
  questions, but not the requirement that every consecutive sum of the
  increasing sequence be distinct in the form used here.
- No checked source was found containing the manuscript's adaptive
  choice \(r_i=\lceil n/(2a_i)\rceil\), its four-way
  good/small/boundary/bad decomposition, the displayed finite
  parameterized inequality, or the resulting leading constant \(1/2\).

## Assessment

The result appears genuinely novel relative to the accessible sources
checked. The appropriate claim is:

> To the best of our knowledge, neither the adaptive finite inequality
> nor the resulting \(1/2\) leading constant has appeared previously.

This is evidence of novelty, not proof of it. Unpublished work,
non-digitized sources, differently worded results, or recent work not
yet indexed can be missed. Before journal submission, the author should
repeat forward-citation and recent-preprint searches and ask at least
one specialist familiar with Erdős Problem 357.
