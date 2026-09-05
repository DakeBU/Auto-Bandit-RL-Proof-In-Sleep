# Chapter 14 full-body acceptance

## Decision and scope

The frozen required body (author pp.186-191, before Notes, including boxed
assertions and source proof steps) is accepted as **compiled with explicit
source/model qualifications**. This is not a claim that every literal sentence
of the book is true in every coding convention, or that all Notes/Exercises
are formalized. The task, conversion window and evidence matrix define the
same boundary. No Lean source or theorem assumptions change in this acceptance.

## Verified publication evidence

- PR #106 merged at c48b98ac16be9589a7dbe37425577547bff6045a on
  2026-09-05T09:53:41Z; its tree equals the independently reviewed 6632b77 tip.
- Main workflow 33959196451 passed: build job 101287945232 and Pages deploy
  job 101291397123. Python: 400 tests in 88.762s, 3 platform skips.
- Public site-manifest.json reports that exact clean commit, lean_verified=true,
  generated_at=2026-09-05T18:22:09+08:00, 661 modules, 8666 declarations,
  zero placeholders. Static QA passed: 715 HTML pages, 9495 Lean source links.
- Live desktop Chapter 14 page at 1280x720: readable navigation, heading and
  claim boundary; document scroll width 1265 matches its client area.
- Keyboard activation of commonDensityOverlap_le_testingError opens the exact
  declaration and its source link at this merge commit, line 155. The displayed
  statement quantifies over arbitrary measurable events and keeps both AC
  premises and the common sigma-finite dominating measure.
- Mobile viewport 390x844: chapter and arithmeticBlockCode_payload_interval
  declaration pages have client/scroll widths 375/375. Inspected screenshots
  show readable reflow, no page-level horizontal overflow, and a contained
  statement panel. Keyboard theorem navigation works. Viewport reset afterward.
- The deployed page still displays the pre-acceptance partial badge. This
  record validates the proofs and publication at c48b98a; publishing the
  acceptance metadata is a separate subsequent change, not retroactive evidence.

URLs: https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pull/106
and https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/actions/runs/33959196451.
Live chapter: https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/textbook-spine/chapter-14-information-theory/.

## Mathematical and presentation gates

Independent full-body source review passed after cf3ed1f repaired the arbitrary-
event overlap step. Its complete local gate passed; both current-main
integrations were independently reviewed with no remaining finding. Subsequent
PR and main compiler gates passed. See the independent-source-route,
main-integration and evidence-matrix records for exact canaries and snapshots.
The Markdown/LaTeX export contains the same mathematical terminals. Acceptance
metadata was rebuilt with TeX Live: three pages, no overfull boxes or LaTeX
errors. All pages were rendered and inspected; after the final status sentence
correction, reflowed pages 2-3 were rendered again. No clipping/overlap was found.
Final latest.tex SHA256:
D333A8868746A3EE56900169B1500BA8EEDCFF5C2498AD4754BF7D31661BEC92.
The wrapper/PDF are scratch verification artifacts, not a requested publication.

Acceptance-metadata QA: local site build/static check passed (715 pages,
9495 Lean source links); displayed chapter counts are two compiled and three
partial. A direct validator regression check accepts Chapters 13/14 and rejects
premature compiled status for each of Chapters 15/16/17. The site checker now
guards three key Chapter 14 declarations, the qualification strings and obsolete
pending-status wording. Independent bounded metadata review PASS after clearing
stale status sentences; no remaining actionable finding. This is presentation
regression evidence, not a substitute for the mathematical compiler gates above.

## Qualifications retained by acceptance

1. BinaryPrefixCode uses nonempty words, including a one-bit singleton.
2. Uniform fixed-length optimality is proved for power-of-two cardinalities.
   For three symbols, 0,10,11 has mean length 5/3 < 2, so the unrestricted
   source reading is explicitly refuted, not silently proved under new premises.
3. Arithmetic coding is classical exact-real, not executable finite precision;
   the named family retains payload containment, zero-mass escape and +3 overhead.
4. Cross-entropy differences are unrounded and assume support compatibility.
5. Finite KL iff AC is finite-alphabet-only; general finiteness also requires
   integrability. Gaussian variance is positive. BH is unconditional with
   exp(-infinity)=0 and KL direction P to Q.

Optional Notes, Bibliographic Remarks and Exercises are not completion claims;
the separately compiled full Exercise 14.10 is an additional result. Adaptive
bandit-history KL belongs to Chapter 15.
