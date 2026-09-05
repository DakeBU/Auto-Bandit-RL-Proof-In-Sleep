# Independent review: Textbook Part IV Chapter 15 minimax lower-bounds spine

> Historical review of the 2026-08-17 dependency snapshot. Its statements
> that Lemma 15.1 and Theorem 15.2 were blocked were superseded by later
> compiled work. See the 2026-09-04 closure audit for the current boundary.

Date: 2026-08-17

Scope: Chapter 15 production Lean, typed canary, source/task/DAG/export
artifacts, directly connected Chapter 13--14 status text, and the Part IV
website spine. The reviewer was run in an external read-only Codex process.
After applying the source-edition correction, a fresh independent read-only
reviewer rechecked only the affected metadata and status boundary.

## Findings

### P0--P2

No actionable finding.

### P3: source editions were conflated in page labels

The initial artifacts called author-online page labels 198--205 "printed"
pages. CUP's first-edition metadata instead places Chapter 15 at print
pp. 170--176, while the free author edition explicitly says its page numbers
do not match the print edition. The author edition labels Chapter 15
pp. 198--205 and those pages occur at physical PDF pp. 207--214.

Resolution:

- CUP print, author-online page labels, and physical PDF pages are now separate
  fields throughout the Chapter 15 task, conversion window, textbook cards,
  readings, and site.
- Lemma 15.1 is mapped to CUP pp. 170--171 / author-online pp. 198--199 /
  physical PDF pp. 207--208.
- Theorem 15.2 is mapped to CUP pp. 171--173 / author-online pp. 199--201 /
  physical PDF pp. 208--210.
- The incorrect site title for §15.3 was replaced by the official title
  "Notes"; §§15.4--15.5 are separately named Bibliographic Remarks and
  Exercises.
- The same edition-label correction was applied to the visible Chapter 13--17
  spine metadata without promoting the planned Chapter 16--17 routes.

Primary evidence:

- CUP book and chapter metadata:
  <https://www.cambridge.org/core/books/bandit-algorithms/8E39FD004E6CE036680F90DD0C6F09FC>
  and <https://doi.org/10.1017/9781108571401.020>.
- CUP table of contents:
  <https://assets.cambridge.org/97811084/86828/toc/9781108486828_toc.pdf>.
- Official free author edition:
  <https://tor-lattimore.com/downloads/book/book.pdf>.

## Mathematical and evidence checks

- The exact Lemma 15.1 direction remains
  `D(P_nu^pi,P_nu'^pi)` with expected pulls under `nu` and one common possibly
  randomized nonanticipating policy.
- Theorem 15.2 retains `k > 1`, `n >= k - 1`, unit variance, means in
  `[0,1]^k`, the `1/27` constant, and `sqrt((k-1)n)` order.
- The Gaussian log-density, RN/LLR, integrability, KL, changed-arm KL, and gap
  tuning declarations are consistent with their typed canary.
- No Chapter 15 source terminal, stochastic-policy history law, or conditional
  kernel-KL integral is presented as compiled.
- The test-only root-import stabilization does not alter a production theorem
  or weaken the lower-bound target.
- The Chapter 15 production/canary files contain no `sorry`, `admit`, `axiom`,
  or `postulate`; public axiom reports are baseline-only.

## Residual boundary

Lemma 15.1 and Theorem 15.2 remain blocked on the documented conditional
composition-product KL integral and canonical stochastic-policy history-law
interface. This is an accepted partial dependency slice, not a completed source
terminal.

## Verdict

The follow-up reviewer confirmed that the original P3 is closed and found no
unresolved P0--P3 issue. It independently confirmed the CUP, author-online,
and physical-PDF page ranges, the §15.3--§15.5 titles, and the retained
blocked status of Lemma 15.1 and Theorem 15.2. Heavyweight gates were not part
of that read-only follow-up; the local gate evidence above remains the
repository's execution record.

## Remote evidence

- PR #13 passed the required build check in run `31958097793`, job
  `95191765312`, and was merged as
  `5620329617a573bd59ad18b7988841e58de0f1bd` without a direct push to
  `main`.
- Authoritative-main run `31959217761` passed. Build job `95194514824`
  completed the full Lean/Tests and site gates in 22m38s; Pages deployment
  job `95197261026` passed in 23s.
- The live Chapter 15 page was inspected at 1280x720 and 390x844. It serves
  the `2026-08-16T17:01:13+00:00` build, keeps the chapter `PARTIAL`, renders
  the corrected three-way source pagination, exposes the compiled Gaussian
  and tuning leaves, keeps both source terminals blocked, and has zero broken
  images or document-level horizontal overflow.

This evidence accepts the scoped dependency slice. It does not close or
weaken the residual mathematical blockers recorded above.
