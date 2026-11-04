# Contribute a BanditRLBench family

Read the repository `AGENTS.md` and `CONTRIBUTING.md`. Propose a bounded family
before adding many near-duplicate questions. A proposal should explain:

1. The mathematical skill, task statement, assumptions, interesting difficulty
   and failure modes. Current library-application warmups are not frontier-hard
   agent tasks, and their count is not a capability result.
2. The immutable source commit/version and exact anchor, rights and original
   restatement; preserve the question contract and source-repair distinction.
3. The correct answer, criterion rubric, counterexamples and reviewer rationale.
   Arrange independent mathematical admission and formal alignment review.
4. The exact Lean Graph declaration/module IDs, source versus contextual relation,
   and which dependencies are actually measured from a compiled proof.
5. For formal tasks, exact imports/signature, a reference proof, environment and
   axiom policy, positive/no-op/incorrect/placeholder controls, and isolation status.
6. Family and solution aliases kept together. No random row split that leaks
   equivalent proofs into evaluation. All current rows remain public `dev`.

Use a personal branch and contribution manifest. Preserve transcript, task and
prediction hashes, model/agent/configuration, access mode, resource budget and
raw verdicts for experiments. Do not add a leaderboard score before the evaluation
protocol and expert gold have passed review. A formal subtarget cannot certify
the full NL solution or promote an unrelated source theorem.

## Expert review workflow

Prepare prompts with `tools/banditrlbench.py prepare`. After collecting responses,
use `review-pack` to generate reviewer-only data. Fill each criterion with 0, 1 or
2, a reason and reviewer identity, then use `assess`. The response SHA-256 binds
the judgment to the actual answer. Preserve substantive mathematical failures in
the reasons; a fluent answer is not evidence of correctness. Report criterion
judgments rather than a calibrated automatic correctness claim. Human agreement
and independent gold admission are still open.
