# Textbook Part IV Chapter 15 minimax lower-bounds spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-15-MINIMAX-LOWER-BOUNDS-SPINE`

Kind: `theoremFormalization`

Status: `accepted`

Harness: `hierarchical`

## Goal

Formalize the source-faithful finite-armed minimax lower-bound route in
Lattimore--Szepesvári, *Bandit Algorithms* (2020), Chapter 15. The exact
terminals are the same-policy adaptive-history divergence decomposition of
Lemma 15.1 and the unit-variance Gaussian minimax lower bound of Theorem 15.2.
Lemma 15.1 now compiles for the repository's kernel-valued randomized history
policy and canonical trajectory law.  Theorem 15.2 remains a separate target:
compiled information and Gaussian leaves must not be reported as that minimax
terminal until its regret/event bridge and final existence statement compile.

## Source

- Authors: Tor Lattimore and Csaba Szepesvári.
- Book: *Bandit Algorithms*, Cambridge University Press, 2020.
- DOI: <https://doi.org/10.1017/9781108571401>.
- Formal author version: <https://tor-lattimore.com/downloads/book/book.pdf>.
- Placement: Part IV, Chapter 15, CUP print pp. 170--176; author-online
  page labels 198--205; physical PDF pp. 207--214.
- Lemma 15.1: §15.1, CUP print pp. 170--171 / author-online pp. 198--199 /
  physical PDF pp. 207--208, Eq. (15.1).
- Theorem 15.2: §15.2, CUP print pp. 171--173 / author-online pp. 199--201 /
  physical PDF pp. 208--210.
- Further source mapping: §15.3 Notes, CUP print pp. 173--174 /
  author-online pp. 201--203 / physical PDF pp. 210--212; §15.4
  Bibliographic Remarks, CUP print p. 174 / author-online p. 203 / physical
  PDF p. 212; §15.5 Exercises, CUP print pp. 174--176 / author-online
  pp. 203--205 / physical PDF pp. 212--214.
- Textbook card: `TXT-LATTIMORE-SZEPESVARI-2020`.
- Scenario card: `SCN-STOCHASTIC-FINITE`.

The author PDF records that its free online edition has the same mathematical
content as the print edition, apart from corrected minor typos and typography,
and explicitly warns that the page numbers do not match. CUP first-edition
print pages, author-online page labels, and physical PDF pages are therefore
recorded separately above.

## Frozen source targets

Let `nu=(P_1,...,P_k)` and `nu'=(P'_1,...,P'_k)` be two `k`-armed
environments, and run the **same possibly randomized nonanticipating policy**
`pi` for `n` rounds. Write `P_nu^pi` and `P_nu'^pi` for the canonical laws of
the complete action/reward history, and `T_i(n)` for the pull count of arm `i`.
Lemma 15.1 is

```text
D(P_nu^pi, P_nu'^pi)
  = sum_i E_nu^pi[T_i(n)] * D(P_i, P'_i).                 (15.1)
```

The direction is `nu` to `nu'`; the expectation and pull counts are under
`nu`; and the policy kernel is identical under both environments.

Theorem 15.2 says that for `k > 1`, `n >= k - 1`, and every admissible policy
`pi`, there exists `mu in [0,1]^k` such that the unit-variance Gaussian bandit
`nu_mu` satisfies

```text
R_n(pi, nu_mu) >= (1/27) * sqrt((k - 1) * n).
```

Consequently the minimax regret over this Gaussian class has the same lower
bound. The source proof uses the base mean vector `(Delta,0,...,0)`, changes a
least-explored arm `i>1` to mean `2*Delta`, applies Theorem 14.2 to
`{T_1(n) <= n/2}`, invokes Lemma 15.1 and
`D(N(0,1),N(2*Delta,1))=2*Delta^2`, then chooses
`Delta=sqrt((k-1)/(4*n))`.

## Lean target and status fence

Target files:

- `BanditRLProof/LowerBounds/ConditionalKernelKL.lean`;
- `BanditRLProof/LowerBounds/BanditHistoryKL.lean`;
- `BanditRLProof/LowerBounds/Minimax.lean`.

Expected public dependency declarations:

```lean
LowerBounds.log_gaussianPDFReal_div_gaussianPDFReal_one
LowerBounds.llr_gaussianReal_one_ae
LowerBounds.integrable_llr_gaussianReal_one
LowerBounds.klDiv_gaussianReal_one
LowerBounds.gaussianMinimaxGap
LowerBounds.gaussianMinimaxGap_informationExponent_eq_half
LowerBounds.gaussianMinimaxGap_le_half
LowerBounds.klDiv_compProd_same_left_eq_lintegral_klDiv_of_measurable
LowerBounds.canonicalBanditHistoryMeasure
LowerBounds.canonicalRealizedExpectedPullCountThrough
LowerBounds.banditHistoryRelativeEntropy_eq_expectedPulls_sum
```

Compiled source terminal:

```lean
LowerBounds.banditHistoryRelativeEntropy_eq_expectedPulls_sum
```

Remaining reserved source terminals:

```lean
LowerBounds.exists_gaussianBandit_expectedRegret_ge_one_div_twentySeven
LowerBounds.gaussianBanditMinimaxExpectedRegret_ge_one_div_twentySeven
```

The history decomposition is a local proof of Lemma 15.1, not a theorem-card
adapter. The Gaussian and numeric tuning declarations remain dependency leaves
only and do not by themselves prove Theorem 15.2. The chapter stays `partial`
while the minimax existence terminal remains blocked.

## Exact regularity contract

- `k > 1` and `n >= k - 1` for Theorem 15.2.
- Each arm law is a probability measure on one measurable reward space.
- The compiled source terminal allows arbitrary Markov arm laws on one
  countably generated reward space. Singular arms and infinite KL are handled
  explicitly; zero-probability arms use the standard `ENNReal` convention
  `0 * infinity = 0`, with no support condition silently inferred.
- Policies are stochastic kernels from past histories to actions, may use
  private randomization, are measurable/nonanticipating, and are identical
  under `nu` and `nu'`.
- The local `lastRound` index is inclusive, so its history contains
  `lastRound + 1` action/reward observations.  The source's positive `n`-round
  display is obtained with `lastRound = n - 1`; this conversion must remain
  explicit wherever `T_i(n)` is compared with a local pull count.
- KL direction is `P_nu^pi` to `P_nu'^pi`; expected pulls are under the first
  law. Reversing either is a different statement.
- Gaussian laws have variance exactly one. Their means lie in `[0,1]` after
  the source tuning, using `n >= k - 1` to obtain `Delta <= 1/2`.
- Regret is expected pseudo-regret under the corresponding history law.
- Lemma 15.1 is a deterministic-horizon identity. Exercise 15.7's stopping-
  time extension is not silently substituted for it.

## Current semantic boundary

The former Lemma 15.1 blocker is resolved locally.  The project supplements
`InformationTheory.klDiv_compProd_eq_add` with a measurable conditional-KL
integral, including singular fibres; instantiates the existing kernel-valued
`Thompson.HistoryAlgorithm`; builds the canonical finite history law; and proves
that its policy-mass recurrence is exactly the lower integral of the realized
pull count.  The remaining Chapter 15 blocker is downstream: connect this
identity to the least-explored Gaussian alternative, the exact testing event
and regret identities, and the caller-free `1/27` Theorem 15.2 terminal.

## Proof obligations

- [x] Official edition, DOI, stable author PDF, chapter/section and dual page
  references are recorded.
- [x] Lemma 15.1 and Theorem 15.2 are conservatively restated with direction,
  quantifiers, Gaussian class, constant, and horizon/arm conditions.
- [x] Existing policy/history-law and installed Mathlib KL APIs are audited.
- [x] Exact unit-variance Gaussian likelihood-ratio, integrability, and KL
  dependency leaves compile.
- [x] Conditional composition-product KL integral compiles.
- [x] A canonical stochastic-policy finite-history law and pull-count function
  compile with probability/measurability instances.
- [x] Lemma 15.1 compiles for the source finite-arm policy class.
- [x] The source gap choice, information exponent `1/2`, and unit-cube upper
  bound compile as numeric dependency leaves.
- [ ] Regret/event identities connect the compiled tuning to Theorem 15.2.
- [ ] The minimax corollary compiles through the Chapter 13 semantic surface.
- [x] Root import, focused canary, Tests, scans, full harness, export, evidence
  indexes, documentation, and website build/check pass.
- [x] Local desktop/mobile checks pass for the extension snapshot.
- [x] Independent read-only mathematical and repository review passed with no
  unresolved Blocking, High, or Medium finding.
- [ ] PR, main Actions, Pages deployment, and live desktop/mobile checks pass.

## Lemma 15.1 extension local verification (2026-08-19)

- Two ordinary cold-cache attempts reached Mathlib and then stopped with the
  Windows infrastructure error `failed to create thread`; neither emitted a
  Lean source error.  A temporary `weakLeanArgs := #["-j", "1"]` retry in the
  root and Mathlib package files completed `lake build BanditRLProof Tests`
  successfully with 8843 jobs.  Both temporary settings were then restored;
  the root and dependency `lakefile.lean` files have no working or staged diff.
- After restoration, the focused standard-configuration build of
  `ConditionalKernelKL`, `BanditHistoryKL`, and the Chapter 15 canary completed
  successfully with 8824 jobs.
- `#print axioms` for the source-facing Lemma 15.1 terminal reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- `python tools/bandit.py check` passed: the complete Lean gate rebuilt 8842
  jobs, ProofGraph export passed, and all 132 tool tests passed with three
  expected skips.
- `python website/scripts/build_site.py --lean-verified` passed with 605 HTML
  pages, 576 modules, 7581 scanner declarations, 83 highlights, and 70
  milestones.  `python website/scripts/check_site.py` then passed all internal
  links and anchors, 16397 Lean source links, MathJax readable fallbacks, 14
  Mermaid blocks, README links, and the Pages workflow.
- The retrieval index contains 7487 source declarations; the two new modules
  contribute 42 scanner declarations with unique full names.  All changed JSON
  sources parse successfully.
- Independent source/Lean review rechecked the official PDF direction
  `nu -> nu'`, first-law expectation, shared randomized policy, singular and
  infinite-KL branches, and the inclusive-index conversion.  It found no
  unresolved Blocking, High, or Medium issue.  Theorem 15.2 remains blocked.
- Independent local browser review at 1440x1000 and 390x844 confirmed zero
  document-level horizontal overflow.  The Chapter 15 callout and Roadmap
  milestone remain inside the 390px viewport, long declaration names wrap, the
  formula stays in its scrollable region, the drawer remains keyboard/ARIA
  operable, and the five-step desktop proof flow uses the available row width.

## Prior dependency-slice verification (2026-08-16)

- Commit `23120d8` passed the complete harness in detached short-path
  worktree `C:\abrl-p4-ch15-final-6c8be3d`. The short path is required because
  Windows cannot create one unrelated existing RL `.olean` under the long
  Codex worktree path; the Chapter 15 module itself built successfully in both
  attempts.
- `lake build BanditRLProof.LowerBounds.Minimax`: passed, 3452 jobs.
- `lake build BanditRLProof`: passed, 4181 jobs.
- `lake build Tests.TextbookPartIVChapter15Canary`: passed, 4181 jobs; public
  axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build Tests.Basic`: passed, 4183 jobs. Importing the Gaussian module
  made one old numeric test close earlier and increased typeclass search cost
  in two old stochastic-trajectory examples; the test-only scripts were made
  robust without changing any production theorem or lower-bound target.
- `lake build Tests`: passed, 4194 jobs.
- `python3 tools/bandit.py check`: passed; 42 Python tests, one expected skip,
  and the complete Lean gate passed.
- `python3 website/scripts/build_site.py --lean-verified`: passed with 561
  modules, 7394 declarations, 74 highlights, 56 milestones, and five Part IV
  textbook-spine chapters.
- `python3 website/scripts/check_site.py`: passed across 589 HTML pages, 14
  Mermaid blocks, 15984 Lean source links, MathJax fallbacks, internal links,
  anchors, and the Pages workflow.
- Real-browser review passed at 1280x720 and 390x844. The Chapter 15 page has
  no document-level horizontal overflow or broken images; its long MathJax
  theorem is contained by a mobile horizontal scroller. Compiled Gaussian and
  tuning leaves remain visually distinct from the blocked Lemma 15.1 and
  Theorem 15.2 terminals.

## Remote verification evidence

- PR #13 passed `Lean and documentation / build` in run `31958097793`, job
  `95191765312` (22m27s), and was merged without a direct push to `main`.
- Merge commit: `5620329617a573bd59ad18b7988841e58de0f1bd`.
- Authoritative-main run `31959217761` passed: build job `95194514824`
  completed Lean, Tests, the lean-verified site, site checks, and Pages
  artifact upload in 22m38s; deployment job `95197261026` passed in 23s.
- Live page:
  <https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/textbook-spine/chapter-15-minimax-lower-bounds/>.
  Desktop 1280x720 and mobile 390x844 inspections confirmed the new
  `2026-08-16T17:01:13+00:00` build, overall `PARTIAL` chapter status, the
  corrected CUP/author-online/PDF page mapping, compiled Gaussian/tuning
  declarations, blocked Lemma 15.1 and Theorem 15.2 terminals, zero broken
  images, and no document-level horizontal overflow.

That remote acceptance applies only to the earlier Gaussian KL and tuning
dependency slice.  The 2026-08-19 Lemma 15.1 extension requires its own local,
PR, Actions, Pages, and live-page acceptance evidence before it is public.

## Mathlib-ready leaf contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| Gaussian unit-variance KL | `gaussianReal`, `rnDeriv_gaussianReal`, `integral_id_gaussianReal`, `klDiv_of_ac_of_integrable` | identify the RN ratio, integrate its affine log | variance `1`; mutual AC via volume | compiled project leaf, Mathlib candidate |
| conditional kernel KL | `klDiv_compProd_eq_add`, kernel RN derivative, `compProd_withDensity` | identify the conditional KL term as an integral; split singular fibres through measurable conditional KL | finite base law, Markov kernels, countably generated target, measurable pointwise KL | compiled local/Mathlib candidate |
| stochastic history law | `HistoryAlgorithm`, `Kernel`, `trajMeasure`, measurable prefix equivalences | policy kernel followed by chosen-arm reward kernel | measurable/nonanticipating common randomized policy; probability kernels | compiled project-local semantic interface |
| divergence decomposition | conditional kernel KL plus same-policy cancellation | induction over inclusive history; regroup finite action masses and identify realized pull-count lower integrals | KL direction and first-law expectation fixed; arbitrary Markov arm laws | compiled source terminal, Lemma 15.1 |
| least-explored arm | `exists_leastExploredAlternative` | reuse Chapter 13 finite averaging | nonnegative pulls, sum equals horizon | compiled dependency |
| testing step | Chapter 14 `bretagnolleHuber` | apply to `T_1(n)<=n/2` | event measurability and common policy | compiled measure theorem; bandit bridge blocked |
| source tuning | real square root and field algebra | set `Delta=sqrt(m/(4n))`; prove exponent `1/2` and `Delta<=1/2` | positive real counts/horizon; `m<=n` | compiled project leaf |
| Gaussian minimax terminal | all above plus regret identities and real algebra | source base/alternative construction and `Delta` tuning | `k>1`, `n>=k-1`, means in unit cube | blocked source terminal |

## Retrieval cards

- Mathlib route evidence:
  `InformationTheory.klDiv_compProd_eq_add`,
  `InformationTheory.klDiv_compProd_left`,
  `gaussianReal_absolutelyContinuous`,
  `gaussianReal_absolutelyContinuous'`,
  `rnDeriv_gaussianReal`, `integral_id_gaussianReal`, and
  `memLp_id_gaussianReal`.
- Local compiled dependencies: Chapter 13 `exists_leastExploredAlternative`
  and Chapter 14 `bretagnolleHuber`.
- Textbook: `TXT-LATTIMORE-SZEPESVARI-2020`.
- Scenario: `SCN-STOCHASTIC-FINITE`.
- LML: none promoted.
- Route evidence only: `WEAPON-KL-CHANGE-OF-MEASURE`.

## Nonclaims and failure policy

- The Gaussian KL leaf alone is not Lemma 15.1 or Theorem 15.2; the separately
  compiled randomized-history declaration is the Lemma 15.1 evidence.
- A deterministic policy specialization alone would not cover the source's
  policy class; the compiled terminal instead uses a common Markov policy
  kernel on each visible finite history.
- A theorem carrying Eq. (15.1) as a premise is a conditional algebraic leaf,
  not a compiled proof of Eq. (15.1).
- The imported Mathlib chain rule alone is route evidence; the local conditional
  integral, canonical history recursion, and realized-count bridge provide the
  compiled source-terminal evidence.
- If the exact terminal remains blocked, preserve it and publish the smallest
  compiled general leaves plus the exact blocker. Do not weaken KL direction,
  add a deterministic-policy restriction, or conceal regularity assumptions.
