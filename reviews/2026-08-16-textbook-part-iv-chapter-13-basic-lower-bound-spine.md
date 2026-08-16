# Evidence review: Textbook Part IV Chapter 13 lower-bound basic ideas spine

Task: `TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE`

Date: 2026-08-16

Mode: independent read-only Codex review of the maintained Chapter 13 source
contract, Lean module, typed canary, proof obligations, proof export, and site
data. Generated retrieval indexes and unrelated repository content were
explicitly excluded. This is an independent model review, not a human review.

## Decision

`ACCEPT LOCALLY`. P0: none. P1: none. P2: none. P3: none unresolved.

The source-stated unit-variance Gaussian minimax lower bound in Theorem 13.1
is not accepted as a local Lean theorem. The accepted scope consists only of
the Chapter 13 semantic and deterministic leaves; the same-policy history-law
information bridge remains planned for Chapter 14 and the caller-free
Gaussian minimax terminal remains planned for Chapter 15.

## Review trail

The independent reviewer found and closed the following evidence-consistency
issues before acceptance:

- removed two conceptual regret/pull-count declarations from the compiled
  result's hard `depends_on` list because the Chapter 13 module does not import
  or consume them;
- added `le_minimaxExpectedRegret` and
  `alternativeExpectedPullBudget_le` to the task's public declaration list;
- added `le_minimaxExpectedRegret` to the site correspondence table;
- added a typed `le_minimaxExpectedRegret` application and completed the
  canary's axiom print over all twelve public declarations.

Read-only review sessions were `01a00a0b-02fc-75c2-a72b-402c3e6d55c9`,
`01a00a0e-cbcf-7703-bfaa-a44371c4f00a`,
`01a00a11-f6bd-7b60-ad4c-ecc883d06da9`, and the final closure check
`01a00a13-f90a-79a0-9fae-599a43ed8680`. The final reviewer conclusion was:
"No unresolved P0-P3 finding remains."

## Statement fence

- Worst-case regret is an `ENNReal` supremum over an explicit environment
  subtype; minimax regret is an `ENNReal` infimum over an explicit policy
  subtype. Empty-class complete-lattice values are documented, and meaningful
  consumers retain an explicit nonemptiness obligation.
- The source's one-based alternative arms `2,...,k` map bijectively to
  `i.succ` for `i : Fin m`. The averaging result exposes `0 < m`, coordinate
  nonnegativity, and the exact total expected-pull identity.
- The deterministic transport interface assumes
  `baseFirstExpectedPulls - changedFirstExpectedPulls <= error` and concludes
  the direction-correct bound `Delta * (n-error) / 2 <= max B C` under
  `0 <= Delta`. It never identifies expectations from different laws.
- No local claim is made for a likelihood ratio, KL chain rule, binary-event
  inequality, absolute continuity, policy consistency, Gaussian
  construction, minimax packing, or asymptotic lower bound.
- Chapter 13 remains `partial`: its twelve scoped declarations are compiled,
  while Theorem 13.1 remains `planned`.

## Deterministic evidence

- The production module and public canary were compiled through the root
  import. A nondegenerate three-arm vector `(4,1,1)` exercises the exact pull
  budget and a nonzero transport error exercises the quantitative algebra.
- The final standalone canary typecheck after review closure exited zero from
  the short-path gate worktree.
- All twelve `#print axioms` reports contain only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Before review-only canary expansion, `python3 tools/bandit.py check` passed
  completely: the root library, `Tests`, and 42 CLI tests all passed. The full
  gate is rerun on the final Chapter 13 commit before remote acceptance.
- The lean-verified site build/check and desktop plus 390-pixel mobile browser
  inspections passed before review closure; both site commands and browser
  checks are repeated against the final committed artifacts.

Remote PR, Actions, Pages deployment, and live-page verification are separate
acceptance gates and are not implied by this local decision.
