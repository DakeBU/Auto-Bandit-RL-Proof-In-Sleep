# Proof Obligations: Textbook Part IV Chapter 17 high-probability lower bounds

Task id: `TEXTBOOK-PART-IV-CHAPTER-17-HIGH-PROBABILITY-LOWER-BOUNDS-SPINE`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`

Scenario cards: `SCN-STOCHASTIC-FINITE`, `SCN-ADVERSARIAL-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `CH17-SOURCE-FENCE` | exact Theorem 17.1 / Corollaries 17.2--17.3 / Theorem 17.4 / Claims 17.5--17.7 / Eq. (17.8) | official source | evidence artifacts | textbook/paper cards | freeze regret notion, all quantifiers, event direction, constants, and pages | three editions distinct | source evidence | repository artifacts | source review | mapped |
| `CH17-TAIL-EVENT` | `{quantity>=threshold}` | sets/order | set comprehension | `MLIB-ORDER-ALGEBRA` | literal source event direction | no probability law hidden | project-local | `tailAtLeast` | focused Lean | compiled |
| `CH17-THM-17-1-THRESHOLD` | outer `1/4` times exact minimum | log/sqrt/min | real special functions | `MLIB-REAL-LOG-SQRT` | literal transcription with `alternativeArms=k-1` | terminal supplies positivity | project-local | `stochasticHighProbabilityThreshold` | focused Lean | compiled |
| `CH17-COR-17-2-THRESHOLD` | exact Eq. (17.7) threshold | log/sqrt/min | real special functions | `MLIB-REAL-LOG-SQRT` | retain `1/2` inside sqrt and outer `1/4` | terminal supplies side condition | project-local | `stochasticMinimaxHighProbabilityThreshold` | focused Lean | compiled |
| `CH17-THM-17-4-THRESHOLD` | `c sqrt(nk log(1/(2delta)))` | log/sqrt | real special functions | `MLIB-REAL-LOG-SQRT` | literal transcription | terminal supplies `c,C,n,k,delta` conditions | project-local | `adversarialHighProbabilityThreshold` | focused Lean | compiled |
| `CH17-FIRST-MOMENT` | average tail gives one point | probability measure | `exists_integral_le` | `MLIB-MEASURE-INTEGRAL` | first moment method | probability law and integrability | Mathlib-composed | `exists_tailMass_ge_of_integral_ge` | focused Lean | compiled |
| `CH17-CLAIM-17-5` | `E_Q[1-F_X(u)]>=delta` gives deterministic `x` | first-moment leaf | Bochner integral | textbook card | specialize tail mass to `1-F_x(u)` | integrability explicit | exact source claim | `exists_cdfTail_ge_of_integral_ge` | focused Lean | compiled |
| `CH17-EVENT-SUBTRACTION` | pull-small `2delta`, clipping-bad `delta` imply good `delta` | finite measure | `le_measureReal_diff` | `MLIB-MEASURE-INTEGRAL` | outer-measure difference plus linear arithmetic | no measurable-set premise needed | Mathlib-composed | `measureReal_diff_ge_delta` | focused Lean | compiled |
| `CH17-EQ-17-8-EXPRESSION` | exact RHS count expression | natural casts/order | real arithmetic | `MLIB-ORDER-ALGEBRA` | define source lower expression | construction semantics separate | project-local | `adversarialRegretLowerExpression` | focused Lean | compiled |
| `CH17-EQ-17-8-QUARTER` | count bounds leave `Delta n/4` | previous expression | ordered multiplication | `MLIB-ORDER-ALGEBRA` | subtract half and quarter, multiply by nonnegative gap | nonnegative gap | project-local | `adversarialRegretLowerExpression_ge_quarter` | focused Lean | compiled |
| `CH17-EQ-17-8-TRANSFER` | source comparison implies random-regret threshold | previous leaf | order transitivity | textbook card | compose with explicit construction premise | Eq. (17.8) remains premise | project-local conditional | `randomRegret_ge_quarter_of_clippingDecomposition` | focused Lean | compiled |
| `CH17-HISTORY` | original-law expected-pull/history information | Ch15 Lemma 15.1 | stochastic policy/history | KL chain-rule route | change one Gaussian arm | same randomized policy; first-law pulls | connected blocker | none | focused Lean | blocked |
| `CH17-THM-17-1` | exact stochastic tail lower bound | history, BH, least arm, tuning | Ch13--15 | source card | choose gap, one-arm change, sum two tail events | exact `n,k,B,delta` and class | source terminal | reserved | focused Lean | blocked |
| `CH17-COR-17-2` | exact Eq. (17.7) | Theorem 17.1 | expectation/tail bound | source card | contradiction and choose source `B` | Eq. (17.6) exact | source terminal | reserved | focused Lean | blocked |
| `CH17-COR-17-3` | no single all-confidence policy | Theorem 17.1 | layer-cake/tail integral | `MLIB-MEASURE-INTEGRAL` | integrate tail and contradict Theorem 17.1 | real `p in (0,1)`, strict `<delta` | source terminal/local analytic gap | reserved | focused Lean | blocked |
| `CH17-CLIPPED-NORMAL` | reward-matrix hard family and interaction law | Gaussian/clipping/kernels | distribution maps | probability cards | preserve within-round dependence and across-time IID | Borel bounded matrix; same policy | semantic interface gap | none | focused Lean | blocked |
| `CH17-CLAIM-17-6` | `P_Qi(T_i<n/2)>=2delta` | hard family and history KL | Chapter 14--15 route | textbook/paper route | least arm plus entropy calculation | exact `Delta`; same policy | connected blocker | reserved | focused Lean | blocked |
| `CH17-EQ-17-8` | construction-level pathwise regret comparison | clipped reward coordinates | finite sums/indicators | textbook/paper route | show chosen arm reward dominates except pull/clipping rounds | exact clipping map | source terminal | reserved | focused Lean | blocked |
| `CH17-CLAIM-17-7` | clipping count tail at most `delta` | clipped Gaussian tails | concentration/finite union | `MLIB-PROBABILITY-SUBGAUSSIAN` | tail each boundary hit and sum/count | exact constants and horizon condition | missing concentration result | reserved | focused Lean | blocked |
| `CH17-THM-17-4` | deterministic reward-matrix witness | Claims 17.5--17.7 and Eq. (17.8) | first moment and tuning | source/paper route | good-event subtraction, calibrate `Delta`, extract witness | universal constants and CDF law | source terminal | reserved | focused Lean | blocked |
| `CH17-CANARY` | root-import typed applications and axiom reports | compiled slice | `BanditRLProof` root | local declarations | instantiate nontrivial threshold and probability leaves | no placeholders | project-local | `Tests/TextbookPartIVChapter17Canary.lean` | Tests | verified on Linux PR/main |
| `CH17-SITE-REVIEW` | synchronized evidence/site and independent audit | all above | build/check/browser | repository | compare informal and Lean statements | no terminal promotion | repository | evidence artifacts | full/local | site, desktop/mobile, Linux, and review passed |
| `CH17-REMOTE` | PR, authoritative-main Actions, Pages, and live page | accepted local slice | GitHub workflow | repository | merge through PR and inspect deployed artifact | source terminals remain blocked; PR #17; merge `eb41d96`; main run `31976153611`; deploy `95238317293`; live desktop/mobile | repository | remote evidence | deployment | verified |

## Failure classification

The stochastic source-terminal failure is a `connected blocker`: Chapter 15's
conditional kernel-KL integral and canonical stochastic-policy history law are
absent. Corollary 17.3 also has a `local Lean lemma gap` for its exact tail
integral. The adversarial route has a `semantic interface gap` for the
clipped-normal reward-matrix/history law and a `missing regularity contract`
and concentration result for Claim 17.7. No theorem target is weakened in
response.

## Reviewer notes

- Compare random pseudo-regret, random regret, and expected regret exactly.
- Check Theorem 17.1's uniform premise, outer factor `1/4`, KL direction, and
  probability `>=delta`.
- Check Corollary 17.2's Eq. (17.6), the factor `1/2` inside the square root,
  and the same outer quarter.
- Check Corollary 17.3's single-policy quantifiers, real exponent, and strict
  `<delta` direction.
- Check Theorem 17.4's deterministic bounded reward matrix, CDF argument,
  `log(1/(2delta))`, and horizon condition.
- Check that Claim 17.5 is compiled only with explicit integrability and that
  Claims 17.6--17.7 remain blocked.
- Check within-round arm dependence and across-time IID in the hard family.
- Do not promote the NeurIPS paper, theorem cards, open-problem proposals, or
  conditional algebra to compiled terminal evidence.
