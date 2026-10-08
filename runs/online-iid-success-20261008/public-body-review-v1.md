# IID-success actual BODY review v1

Verdict: accepted-with-explicit-delta for the four actual public proof bodies and the bounded canary validation only. Actor /root/source_reviewer is reused from CONTRACT and previous staged reviews. Requested GPT-6 Astra/medium is not runtime attestation; no absolute blindness, human or external review is claimed.

All 128 fixed BODY raw rows and all 88 original CONTRACT raw rows match independently before/after. All four frozen exact header strings occur unchanged in the actual public module. Pinned PDF freshly hashes to cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Source physical13/14/16 text was reread against the unchanged source pixels directly viewed in CONTRACT. No fresh pixel or final reader acceptance is implied. Source equations1.1/1.2 and derived Theorem1.3 applications retain their attribution.

Actual full public bodies and whole new canary module were inspected, with relevant complete old IID and private-seed fixture producers and prior shared proof dependencies. The following seven slots retain the exact CONTRACT analysis and are checked against each actual body.

## S001

- **Objects:** Arbitrary total:Nat->Real and fixed real c.
- **Quantifiers:** For every total and c, equivalence of two atTop assertions.
- **Assumptions:** No sign, monotonicity, A0=0, c=0, stochastic or convergence premise.
- **Terminal:** Centered total little-o(T) iff average total minus c tends to zero.
- **Constants/normalization:** Real-cast natural denominator; signed centered residual; little-o controls magnitude.
- **Information structure:** No algorithm or probability model is asserted.
- **Boundary/delta:** Use eventual T>0; at T0 quotient-minus-c=-c while residual=A0. No pointwise identity at zero is required.

Actual proof: Actual eventually_gt_atTop produces nonzero real T. normalized_excess supplies eventual quotient equality; isLittleO_iff_tendsto and tendsto_congr prove the iff. No A0/c restriction or assumed convergence.

## S002

- **Objects:** Arbitrary measurable Omega and Seed, probability mu, one infinite real target process and one seed-history policy.
- **Quantifiers:** Universal data/hypotheses then let-defined actual prediction; all-T nonnegativity and two iff statements.
- **Assumptions:** Measurable same-law a.s.unit targets, joint IID, measurable seed independent of WHOLE stream, jointly measurable policy feasible for every seed on legal histories only.
- **Terminal:** Nonnegative expected fixed regret; little-o iff average loss minus variance tends0 iff average integrated squared deviation from population mean tends0. It does not assert arbitrary-policy convergence.
- **Constants/normalization:** Unnormalized expected cumulative loss minus min of expected fixed loss; denominator T in limits, variance and mean of Y0.
- **Information structure:** Actual strict-past tuple plus private tape, same process/policy across horizons; no current Yt or law oracle input.
- **Boundary/delta:** T0 lower bound valid; normalized sequences may differ at T0. Explicit private-seed model does not represent every kernel/completed-information/AE-factorized strategy.

Actual proof: Actual seeded causal expectedFixed_excess supplies both finite nonnegativity and MSE sum; expectedFixedMinimum_eq_variance and S001 prove first iff; the second uses eventual positive-horizon division of the produced equality. Same let-bound prediction throughout; no arbitrary-policy success assertion.

## S003

- **Objects:** Same-law a.s.unit measurable process and actual initial-half meanPredict on its histories.
- **Quantifiers:** Every such process and every natural T>0.
- **Assumptions:** Probability, all-time measurability/same-law/a.s.support; NO independence premise.
- **Terminal:** One-sided expected fixed regret <=4+4logT, a derived integrated application of Theorem1.3.
- **Constants/normalization:** Natural logarithm, positive real-cast horizon, unnormalized signed excess; initial output1/2.
- **Information structure:** Strict past only; population mean is analysis comparator, not learner input; no horizon-dependent rerun.
- **Boundary/delta:** No T0 formula assertion or nonnegativity without IID. Must derive integrability and use empirical minimum <= population-comparator loss before integration; no E/min swap.

Actual proof: AE-all support is assembled, prediction and target MemLp2 are genuinely derived, then both finite sums are integrable. Pathwise theorem_1_3 and empiricalMean_minimizes give loss-minus-fixed-population-mean upper in the correct inequality direction. integral_mono_ae/integral_sub are applied only after integrability. Same-law decomposition and actual fixed minimum turn this into the frozen endpoint without independence or exchanging min and expectation.

## S004

- **Objects:** Joint-IID version of S003 and same actual meanPredict.
- **Quantifiers:** For every fixed infinite process, ordinary normalized zero limit AND little-o atTop.
- **Assumptions:** Add joint independence to measurable same-law probability/a.s.support; no assumed convergence.
- **Terminal:** Actual algorithm success for expected fixed regret, not an equivalence alone.
- **Constants/normalization:** Division by real T, zero ordinary limit and magnitude little-o; upper rate follows from 4+4logT.
- **Information structure:** Same strict-past unknown-law learner, source round1=Lean0; seed/general strategy not asserted.
- **Boundary/delta:** Finite initial T0 irrelevant to limits; IID lower bound and positive-horizon upper are both needed. No a.s./high-probability/minimax or full-source strategy-class closure.

Actual proof: Actual meanPredict_expectedFixed_excess supplies nonnegative lower; actual S003 supplies eventual upper after division. Existing real inverse/log-over-x limits compose with Nat.cast; squeeze_zero gives ordinary normalized convergence. S001 is a genuine second consumer at c=0, proving little-o. Neither limit is assumed; no horizon-dependent learner.

## Canary and evidence findings

All fourteen named test proofs and two fixture definitions are meaningful. The infinite product fair-coin model is an actual probability law; the mean predictor has positive two-round excess 1/4 and variance 1/4 while invoking S004 for asymptotic success and S003 for the upper. The independent private seed is used through a measurable, globally feasible bit policy. Its actual excess is T/4, normalized limit1/4, and limit uniqueness proves not little-o; the new S002 iff is genuinely used to reject success. This validates the criterion/convergence distinction rather than assuming the desired counterexample.

The correlated stream repeats one fair coordinate. S003 applies without independence; actual two-round excess is -1/4, so its upper cannot be promoted to IID nonnegativity or absolute convergence. The zero-horizon test displays average loss minus variance=-1/4 while regret/0=0. The generic total5+3T test genuinely invokes S001 with nonzero initial total and nonzero centering. Borrowed fixture laws/support/independence/means/variance are actual producers, not simulation values or unsupported test axioms.

The actual selected kernel log has 45 unique named axiom records, each using only propext/Classical.choice/Quot.sound, no sorryAx. The supplied audit source instantiates all four public theorem VALUES at arbitrary universes, in addition to four neutral whole-Prop and three whole-definition identities. The compiled TEST-environment graph has45 selected nodes and3325 direct TYPE/VALUE occurrences; all14 specified pairs were independently found in value_dependencies. This is a selected graph, not a full-library export, and counts are not semantic acceptance.

Actual focused public builds report3374 jobs and the canary build3435 jobs, with replay/cache work included. Successful final public S004 and canary exits are0; kernel audit records actual exit0. The two S003 failed builds remain: integral_sub could not match unapplied Pi subtraction, then a guessed sq_zero identifier failed. The successful repair adds Pi.sub_apply simplification and ordinary simp for the zero-square expression; hypotheses/header/route are unchanged. Earlier API, writer and concatenated-universe diagnostics remain historical, not successful target proofs. No new root/Tests/full-harness/site gate is claimed here.

## Bounded future integration decision

The explicit scope JSON is acceptable only as prospective permission within the existing task: append exactly one public-root import and one Tests import; one own source-qualified four-target card and four own notes; own C1 boundary/links while preserving every old object/ID/status/result; one own schema2 contribution manifest; task-only native rows and own docs updates with prior raw prefixes preserved. The current public and canary bytes, all prior mathematics/pins, source objects and global SGB remain immutable. Native acceptance and publication are not approved as already executed by this BODY verdict.

Before modifying any fixed live root/reader/task metadata, save exact immutable baseline bytes and explicitly resolve this receipt's original bindings to those snapshots. Do not silently refresh hashes or treat a prefix check as proof of semantic ownership. Actual changed suffixes/fields and current reader must be audited at FINAL. No rewrite of old cards/notes is allowed by the append scope; any broader layout need requires a separately versioned scope review. All current combined gates, registry preservation, actual pixels, FINAL and delivery remain required.

No mathematical or current binding blocker was found. The source deltas remain: S001 general signed adapter; S002 explicit measurable private-tape model only; S003 derived dependent same-law upper; S004 actual expected success of this learner. Universal kernel/completed-information/AE-factorization coverage is still required. Original sixteen source objects/null proof total, five old module audits, C1/C2, Chapters3–16 and appendices stay open; total Goal remains active.

## Exact mandatory future reader requirements

- **R1:** Display source equations (1.1) and (1.2) and Theorem 1.3 with source round 1 = Lean time 0; label S001 as a generic adapter and S003/S004 as derived applications, not new numbered source results.

- **R2:** Keep minimization over the expected loss of one fixed comparator outside expectation; explain the feasible population mean and do not substitute expected hindsight minimum.

- **R3:** State one infinite probability process with measurable same-law a.s. [0,1] targets; S002/S004 require joint IID, whereas S003 does not; derive integrability rather than strengthen to pointwise support.

- **R4:** For S002 state seed independence from the whole target stream, joint measurability, every-seed feasibility only on legal strict-past histories, and the actual composed prediction; equivalences do not make every policy successful.

- **R5:** Show the actual unknown-law meanPredict with initial 1/2 and strict-past empirical mean; population mean is a proof comparator, not algorithm input, and horizons do not select different learners.

- **R6:** Distinguish ordinary expected normalized zero convergence and magnitude little-o from adversarial eventual-upper-epsilon NoRegret; state eventual T>0 and the possible generic T0 discrepancy.

- **R7:** Present complete exact headers and definitions, a displayed proof explanation and actual compiled dependencies only when available; preserve existing registry IDs/URLs/hashes and verify current formulas/pixels after applicable combined gates.

- **R8:** Keep full randomization/kernel/completed-information/AE-factorization coverage, five old module audits, original sixteen source objects with null proof total, full C1/C2, Chapters3–16 and necessary appendices required; no chapter/Goal/main/live completion.

All eight remain pending; none is discharged by BODY acceptance. No source-package, FINAL, chapter, Goal, merge or main/live acceptance is issued.
