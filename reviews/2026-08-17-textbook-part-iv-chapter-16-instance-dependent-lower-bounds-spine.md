# Independent review: Textbook Part IV Chapter 16 instance-dependent lower-bounds spine

Date: 2026-08-17

Scope: Chapter 16 production Lean, typed public canary, task/conversion/DAG,
textbook and Mathlib cards, proof export, result/highlight records, Part IV
website content, and the generated desktop/mobile page. The reviewer ran in an
ephemeral read-only Codex process and did not modify files or run builds.

## Findings

### P0--P2

No actionable finding.

### P3: Definition 16.1 status wording was internally inconsistent

The conversion-window status fence originally said that all four source
endpoints were uncompiled, although the same artifact, production Lean, and
website correctly marked Definition 16.1's generic consistency interface as
compiled through `IsConsistentRegret` and `IsConsistentPolicyOver`.

Resolution:

- the fence now says that Definition 16.1's generic interface is compiled;
- Theorem 16.2, Lemma 16.3, and Theorem 16.4 remain uncompiled and blocked;
- the generated blueprint was refreshed from the corrected task/conversion
  sources.

## Mathematical and evidence checks

- Definition 16.1 preserves one policy, every environment in the class, and
  every positive real exponent; regret nonnegativity remains an explicit
  caller obligation rather than a hidden field.
- Theorem 16.2 remains restricted to an unstructured Cartesian product of
  per-arm law classes with finite means. The KL direction is original
  `P_i` to confusing alternative `P_i'`, strict improvement is
  `muStar < mean(P_i')`, and pull expectations are under the original
  environment.
- The source event remains `A={T_i(n)>n/2}` and the history bridge requires
  one common possibly randomized nonanticipating policy. No deterministic
  policy substitution or reversed KL appears in a compiled claim.
- `d_inf` is represented in `ENNReal`; empty, zero, finite, and infinite
  branches remain visible obligations. The compiled Gaussian result is only
  a perturbed-alternative upper bound, not the exact Gaussian infimum formula.
- Theorem 16.2 retains a `liminf`; the compiled power/log leaves stop before
  the history information inequality and final asymptotic extraction.
- Lemma 16.3 retains the original gap, alternative optimality margin, exact
  regret-sum logarithm, original-to-alternative arm KL denominator, and the
  finite-positive-KL branch requirement.
- Theorem 16.4 retains unit variance, nonempty selected horizon set, `C>0`,
  `0<p<1`, `0<epsilon<=1`, factor `2/(1+epsilon)^2`, and a positive part over
  the entire displayed per-gap quotient.
- Reserved theorem names and source/theorem cards are marked blocked or route
  evidence only. No local declaration is claimed for Theorem 16.2, Lemma
  16.3, or Theorem 16.4.

## Local verification evidence

- `lake build BanditRLProof.LowerBounds.InstanceDependent`: passed.
- `lake build BanditRLProof`: passed, 4182 jobs.
- `lake build Tests.TextbookPartIVChapter16Canary`: passed; all six printed
  axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build Tests.Basic`: passed, 4184 jobs.
- `lake build Tests`: passed, 4195 jobs.
- `python3 tools/bandit.py check`: passed; 42 Python tests, one expected skip.
- `python3 website/scripts/build_site.py --lean-verified`: passed with 562
  modules, 7405 declarations, and zero placeholders.
- `python3 website/scripts/check_site.py`: passed with 590 pages, 14 Mermaid
  blocks, and 16012 Lean source links.
- Browser inspection at 1280x720 and 390x844 found the Chapter 16 page
  `PARTIAL`, the compiled/blocked split intact, source pagination and chapter
  links present, zero broken images, and no document-level horizontal overflow.

## Residual boundary

The exact Gaussian `d_inf` equality and its extended-real branch audit remain
partial. The same-policy stochastic history KL / original-law expected-pull
bridge remains blocked on Chapter 15's conditional kernel-KL integral and
canonical stochastic-policy history law. Theorem 16.2's per-arm and regret
`liminf` terminals, Lemma 16.3, and Theorem 16.4 therefore remain blocked.

## Verdict

The P3 is corrected and no unresolved P0--P3 issue remains in the scoped local
dependency slice. This accepts the local partial slice only; PR, Actions,
Pages deployment, and live-page evidence remain pending, and no source
terminal is promoted.
