# Independent review: Chapter 16 Gaussian equality and one-arm information extension

Date: 2026-08-22

Scope: the current twenty-declaration Chapter 16 dependency record, production
Lean, the root-import canary, task/conversion/obligation artifacts, generated
retrieval and Blueprint snapshots, anonymous claim-ledger boundary, and the
desktop/mobile textbook page. The independent reviewer was read-only: it did
not edit files or start a Lean build.

## Findings and resolutions

No Blocking or High finding was identified.

Two Medium evidence/presentation findings were resolved before this record was
accepted:

1. The 2026-08-17 review covered only the older consistency and candidate
   `d_inf` slice. This record supersedes it for the exact Gaussian equality and
   one-arm event-information extension; the old record remains historical.
2. The anonymous supplement builder previously copied the Chapter 16 result
   records without a chapter-specific fail-closed boundary. It now requires
   exactly the frozen twenty unique compiled declarations and independently
   requires the source-terminal record to remain `blocked` with zero
   declarations. Negative regression tests cover both failure modes.

The mobile Lean-correspondence table was also widened inside its already
focusable, labelled local scroll region. At a 390-pixel viewport it now uses a
704-pixel table, keeps the document itself at viewport width, and reduces the
tallest correspondence row from the earlier roughly 192--288 pixel range to
about 125 pixels.

## Mathematical and evidence checks

- The compiled record contains exactly twenty named declarations: the eleven
  older analytic/`d_inf` dependencies plus nine new Gaussian-equality,
  one-arm-history, majority-event, Bretagnolle--Huber, and scalar declarations.
- `unitGaussianDivergenceInfimum_eq` states the strict-suboptimal unit-variance
  formula `d_inf = (muStar-mu)^2/2`; the strict boundary and original-to-
  alternative KL direction match Table 16.1.
- The same randomized nonanticipating `HistoryAlgorithm` appears under both
  stationary environments. The history KL and expected pull count are under
  the original environment, and only the changed arm contributes.
- `oneArmMajorityPullEvent` is `2*T_i > lastRound+1`, exactly the repository's
  inclusive-horizon form of the source event `T_i(n)>n/2`.
- The Bretagnolle--Huber scale retains the source factor `1/2`; the deterministic
  two-regret assembly retains the resulting factor `1/4`.
- The compiled logarithmic theorem is only a scalar consumer. It does not
  manufacture the original- and changed-environment expected-pseudo-regret
  bounds required by Lemma 16.3.
- Lemma 16.3, Theorem 16.2, and Theorem 16.4 remain `blocked`, have no local
  terminal declaration, and remain absent from the anonymous claim-ledger's
  verified endpoints.

The source comparison used Lattimore--Szepesvári, *Bandit Algorithms* (2020),
official author PDF, §16.1--§16.2 (author-online pp. 207--210; physical PDF
pp. 216--219): <https://tor-lattimore.com/downloads/book/book.pdf>.

## Local verification evidence

- Focused root/canary build: 8,828 jobs, success.
- New theorem axiom reports: only `propext`, `Classical.choice`, and
  `Quot.sound`; no `sorryAx`.
- `python tools/bandit.py check`: `lake build` 8,848 jobs, ProofGraph export,
  197 Python tests with four platform skips, final `check passed`.
- `python website/scripts/build_site.py --lean-verified`: 580 modules, 7,739
  declarations, 90 highlights, 73 milestones, zero placeholders.
- `python website/scripts/check_site.py`: 609 pages, 16,728 Lean source links,
  valid internal links/anchors, MathJax fallbacks, and Pages workflow.
- Browser inspection: desktop and 390x844 layouts have no document-level
  overflow; the mobile drawer retains `inert`/`aria-hidden`, focus trapping,
  Escape closure, and focus return; the Lean table scrolls only inside its
  labelled region.
- Anonymous supplement: 15 builder tests pass; a fresh proof graph has 14,322
  project nodes and 695,626 edges; the deterministic 704-file archive passes
  its packaged verifier and reports no target-drift results.

## Residual boundary and verdict

The source-general event-to-regret producers, finite-time Lemma 16.3 terminal,
Theorem 16.2 zero/finite/infinite-`d_inf` and `liminf` branches, and Theorem
16.4 aggregation remain open. The current extension has no unresolved local
Blocking, High, or Medium review finding. PR #38 passed its Lean/documentation
and lifecycle checks and merged as `359fb6a`; authoritative-main run
`32546802426` passed Lean, Tests, the site build/check, artifact upload, and
Pages deployment. The live manifest points to the same clean Lean-verified
commit, and desktop/mobile plus merge-pinned source-link checks passed. These
remote gates verify the bounded dependency slice only and do not promote any
of the three blocked source terminals.
