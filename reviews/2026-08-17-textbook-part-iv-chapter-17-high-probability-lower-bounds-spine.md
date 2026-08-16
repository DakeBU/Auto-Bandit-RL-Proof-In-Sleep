# Independent review: Textbook Part IV Chapter 17 high-probability lower-bounds spine

Date: 2026-08-17

Scope: Chapter 17 production Lean, typed public canary, task/conversion/DAG,
textbook and paper cards, proof export, result/highlight records, Part IV
website content, and the generated desktop page. The reviewer ran in an
ephemeral read-only Codex process and did not modify files or run builds.

## Findings

### P0--P2

No actionable finding.

### P3: Corollary 17.2 reserved terminal was absent from the website mapping

The first review found that the website's Chapter 17 `lean_correspondence`
listed the blocked Theorem 17.1, Corollary 17.3, and Theorem 17.4 reserved
names but omitted the reserved Corollary 17.2 terminal.

Resolution: the website now includes
`gaussianRandomPseudoRegret_ge_corollary17_2` as `blocked`, explicitly saying
that no declaration is claimed.

### P3: typed canary did not lock the complete threshold/public surface

The first review found that only the Theorem 17.1 threshold had a direct
shape canary. Corollary 17.2 and Theorem 17.4 constants and logarithm arguments
were therefore not independently pinned at the public root.

Resolution: the canary now directly checks `tailAtLeast`, the generic and CDF
first-moment interfaces, event subtraction, all three exact threshold shapes,
the quarter-horizon algebra, and the Eq. (17.8) conditional transfer.

The independent read-only re-review found no unresolved P0--P3 after these
two changes.

## Mathematical and evidence checks

- Theorem 17.1 retains one common possibly randomized nonanticipating policy,
  a uniform expected-regret premise, original-to-alternative history KL,
  original-law pull expectations, the outer factor `1/4`, and probability at
  least `delta`.
- Corollary 17.2 retains its horizon-confidence side condition, the factor
  `1/2` inside the square root, and the outer factor `1/4`.
- Corollary 17.3 retains one policy over every horizon, confidence level, and
  environment, a real exponent in `(0,1)`, and the strict `< delta` tail.
- Stochastic random pseudo-regret, adversarial random regret, and deterministic
  expected regret are never interchanged.
- Theorem 17.4 remains a deterministic bounded reward-matrix existence target.
  Claim 17.5 alone is compiled; the random hard law and average-tail premise
  are not supplied by that theorem.
- The Claim 17.6 construction preserves shared within-round Gaussian noise and
  IID time coordinates for each arm; no across-arm independence is assumed.
- Claims 17.6--17.7 and construction-level Eq. (17.8) remain blocked. The
  compiled event subtraction and quarter-horizon algebra are dependency leaves.
- Textbook and external-paper cards remain source/route evidence. No card is
  treated as a local proof.

## Local verification evidence

- `lake build BanditRLProof.LowerBounds.HighProbability`: passed, 2654 jobs.
- The public root and expanded typed canary compile through the worktree's
  `X:` short-path mapping. Five printed axiom reports contain only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `python3 tools/bandit.py check` reaches the full `lake build` but is blocked
  locally by Windows MAX_PATH while creating an existing unrelated long-named
  RL `.olean`. This is not a Chapter 17 compiler error; authoritative Linux CI
  remains the required full Lean/Tests gate.
- Focused placeholder scanning found no `sorry`, `admit`, `axiom`, or
  `postulate`; the only `axiom` tokens are the canary's `#print axioms` lines.
- JSON parsing and `git diff --check`: passed.
- `python3 website/scripts/build_site.py --lean-verified`: passed with 563
  modules, 7415 declarations, and zero placeholders.
- `python3 website/scripts/check_site.py`: passed with 591 pages, 14 Mermaid
  blocks, and 16037 Lean source links.
- Browser inspection at 1280x720 found the Chapter 17 page `PARTIAL`, all seven
  MathJax displays rendered, the compiled/blocked boundary intact, and no
  document-level horizontal overflow. Long MathJax, table, and Lean-code
  elements have local horizontal scrolling.
- The browser security policy rejected a synthetic 390px iframe viewport and
  prohibited an alternate browser workaround. Mobile rendering was therefore
  deferred to the supported native remote/live viewport gate recorded below.

## Residual boundary

The stochastic branch remains blocked on a canonical same-policy adaptive
history law and Lemma 15.1's conditional kernel-KL integral/decomposition.
The adversarial branch remains blocked on the correlated clipped-normal law,
Claim 17.6, construction-level Eq. (17.8), Claim 17.7, and the final tuning and
deterministic-witness assembly. Theorem 17.1, Corollaries 17.2--17.3, and
Theorem 17.4 are not local declarations.

## Verdict

The local Chapter 17 dependency slice has no unresolved P0--P3 review finding
and passed authoritative Linux and remote/live gates. It is not a
source-terminal completion.

## Remote evidence

- PR #17 passed the required build check in run `31975031469`, job
  `95233089033`, and was merged as
  `eb41d9607cc5a46aa208572e3a6f05f291c82798` without a direct push to
  `main`.
- Authoritative-main run `31976153611` passed. Build job `95235875154`
  completed the full Lean/Tests and site gates in 22m24s; Pages deployment
  job `95238317293` passed in 12s.
- The live Chapter 17 page was inspected at 1280x720 and through the browser's
  native 390x844 viewport. It serves the `2026-08-16T22:44:25+00:00` build,
  keeps the chapter `PARTIAL`, renders seven MathJax displays, exposes the
  compiled Claim 17.5 and reusable dependency leaves, keeps Theorem 17.1,
  Corollaries 17.2--17.3, and Theorem 17.4 blocked, and has zero broken images
  or document-level horizontal overflow. At 390x844 the document client and
  scroll widths are both 375 CSS pixels; the mobile TOC/sidebar and long
  MathJax displays retain intentional local horizontal scrolling.

This evidence accepts the scoped dependency slice. It does not close or
weaken the residual mathematical blockers recorded above.
