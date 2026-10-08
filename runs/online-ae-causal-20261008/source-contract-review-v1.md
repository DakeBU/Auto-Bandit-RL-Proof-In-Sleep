# AE causal source contract review v1

Verdict: **accepted-with-explicit-delta**, for source/type stabilization only. No blocking mathematical or metadata repair was found. All 118 indexed raw inputs matched independently before and after review; the cached original PDF also matched its pinned SHA. The three raw header hashes and whitespace-normalized statement fingerprints independently matched. The intended production file does not yet exist. Draft type elaboration and API checks do not certify a theorem body.

The reviewer is /root/source_reviewer, a reused distinct staged automated actor with prior source-review history. GPT-6 Astra / medium are requested settings, not runtime-attested facts. This is not an absolute-blind, external or human review. The decoder reconstruction is separately scoped and does not establish source acceptance.

## Source and API scrutiny

I personally viewed the bound original-detail PDF13 and PDF15 images and read the corresponding source text. Printed page 1 motivates the IID variance/fixed expected-loss benchmark; printed page 3 imposes strict-past prediction and distinguishes hindsight from FTL. These are three derived formalization targets, not three printed theorems. Source pathwise unit feasibility is extended to AE feasibility explicitly, without silently claiming source-wide equivalence.

The actual AEStronglyMeasurable definition uses ambient mu and an F-measurable representative equal almost everywhere. The factorization API accepts arbitrary input measurable spaces and a real standard-Borel output; it does not require a standard-Borel seed. L1 can select a representative at each time, lift through the subordinate comap, factor through seed/history, clip globally to the unit interval and use countable AE intersection. This is a viable proposed proof route, not a compiled proof. It produces one all-time event, not off-null equality or an executable unknown-law policy constructor.

The existing private-seed parent really derives joint seed/past versus current independence from joint target independence and independence of seed from the whole stream. L2 can use a measurable version and IndepFun.congr without bounds or identical laws. L3 can derive ambient AE measurability and square integrability, invoke L2, and use the actual attained expected fixed minimum/variance and cumulative decomposition parents. The reused benchmark is min of expected fixed-comparator loss, not expected hindsight minimum. No consumer oracle is smuggled into the target premises.

## Per-target seven-slot comparison

### L1 — BanditRL.OnlineLearning.ae_predictable_exists_bounded_history_policy

Contract verdict: accepted-with-explicit-delta.

- **objects:** Arbitrary measurable Omega and Seed, arbitrary ambient measure mu, one real prediction process and time-indexed sigma fields; no probability, target measurability or seed measurability premise.

- **assumptions:** For each t, F_t is below the comap of (S, strict past Y), prediction is AE strongly measurable relative to F_t under ambient mu, and unit-valued almost everywhere.

- **quantifiers:** One policy family exists before all horizons, measurable and unit-valued for every input; one common full-measure event gives equality for every natural t. Countable intersection, not merely a separate horizon-dependent witness.

- **information structure:** Only seed and Finset.range t history enter the policy. At t=0 the history is empty and seed remains. No monotonicity of the supplied F family is needed.

- **conclusion:** A globally bounded measurable representative policy reproduces the original process almost everywhere simultaneously in time; original off-null equality is not asserted.

- **normalization and boundaries:** No regret or horizon normalization. Arbitrary measure includes degenerate measures; real output is nonempty. No standard-Borel assumption on Seed is needed by the actual factorization API, whose regularity requirement is on real output.

- **source delta:** Derived law-relative AE representation infrastructure. Source pathwise feasible guessing is generalized to AE feasibility. Classical measurable factorization and clipping are not a newly designed executable unknown-law learner or a representation theorem for every completed filtration/kernel.

### L2 — BanditRL.OnlineLearning.ae_predictable_private_seed_independent

Contract verdict: accepted-with-explicit-delta.

- **objects:** Measurable private seed and measurable jointly independent real target stream on a probability space; one time and one real prediction.

- **assumptions:** Seed is independent of the entire infinite stream; F is subordinate to seed plus strict past; prediction is AE strongly measurable relative to F. No same-law, support, boundedness or prediction integrability premise.

- **quantifiers:** For every chosen t, F and P satisfying these premises, IndepFun P (Y t) mu. Current independence is the conclusion, not an input.

- **information structure:** A measurable version factors through the permitted sigma field; the existing genuine seed/past independence producer and AE congruence apply. Pairwise seed-target independence alone is not substituted for whole-stream independence.

- **conclusion:** Independence of the original prediction and current target, unchanged under AE replacement.

- **normalization and boundaries:** No sum, normalization or positive-time restriction; seed-only time zero is included. No hidden boundedness may be introduced during implementation.

- **source delta:** Derived probabilistic causal-information lemma, not a separately printed theorem. Ambient-measure AE hypothesis is explicit and is not automatically all completed-information models.

### L3 — BanditRL.OnlineLearning.ae_predictable_private_seed_expectedFixed_excess

Contract verdict: accepted-with-explicit-delta.

- **objects:** Same infinite original prediction and IID measurable target stream, private seed independent of the entire stream, probability measure and subordinate F_t.

- **assumptions:** Joint target independence, identical distribution with Y0, AE unit support of all targets and predictions, seed and target measurability, and relative AE strong measurability. No supplied current-independence, regret bound, minimizer or convergence assumption.

- **quantifiers:** For every natural T on the same fixed process, exact expectedFixedRegret identity and nonnegativity. Neither a seed-dependent comparator nor a horizon-dependent replacement process is introduced.

- **information structure:** L2 supplies current independence. Ambient measurability follows from F_t below the measurable seed/past comap; AE boundedness on a probability space supplies L2 integrability. Population mean appears only in analysis.

- **conclusion:** Expected fixed-comparator regret equals the sum of integrals of squared prediction-minus-population-mean deviations, and is nonnegative. Parent expected minimum is the infimum of expected fixed unit-comparator losses, not expectation of a pathwise minimum.

- **normalization and boundaries:** Finite cumulative identity, no division by T. T=0 is included via empty sums and the attained fixed benchmark zero. No rate, ordinary limit, little-o, pathwise or high-probability conclusion.

- **source delta:** A derived AE/private-seed specialization supporting printed IID variance benchmark. All-time process identity is preserved. Full stochastic-kernel/completion coverage and broader source-program conclusions remain separate mandatory work.

## Scope and evidence limits

The exact future-proof scope is approved as copied into the receipt: only these three frozen bodies and necessary scoped helpers in OnlineGuessingAECausal.lean; existing parent bodies remain unchanged. L3 follows actual L2 focused success. Root/site integration waits for distinct BODY review. This does not authorize header weakening, pin upgrades, replacing the active SGB frontier, or unrelated edits.

The six original R1–R6 reader requirements remain future mandatory obligations, copied verbatim below and in the receipt; none is discharged by this contract verdict. Required later evidence includes the genuine AE-only/non-pointwise canary, actual bodies and VALUE edges, kernel/fence checks, combined project gates, readable reader/registry/pixels, distinct FINAL, native acceptance and scoped draft delivery.

The retrieval-scope diagnostic candidly records an earlier generated_at-versus-generated guard failure and that its raw stdout was not saved. This is an evidence limitation, not a mathematical proof failure; the current contract does not rely on an invented raw transcript. A read-only reviewer lookup initially used the wrong run-relative targets path; the actual indexed docs/contracts path was then read and verified. No input was edited.

Original 16 source objects and null proof total remain. Completed-information augmentation, universal stochastic-kernel representation, all remaining Chapter 1/2, Chapters 3–16 and required appendices remain required. Prior PR197 evidence is a bounded historical dependency, not a fresh recursive acceptance or merge claim. Whole Goal remains active; no chapter, source-package, BODY, FINAL, native or publication acceptance is issued here.

## Future reader requirements, unchanged

R1: Source-qualified Orabona v10 printed1/PDF13 and strict-past printed3/PDF15; three derived formalization targets, not three printed theorems. Preserve original16 source objects/null unknown proof total and whole-book active boundary.

R2: AE strongly measurable relative to F_t uses ambient mu. One same-process all-time AE representation, globally unit-valued chosen policy, no off-null original equality, no asserted completion or universal kernel identity. Classical law-relative representation is not an executable unknown-law algorithm design.

R3: Actual independence derives from measurable representatives, joint target independence and seed independent of entire infinite target stream; no supplied current-independence premise. L2 needs no support/same law; L1 needs no probability/IID/ambient S/Y measurability.

R4: L3 exact original prediction for every natural T, actual expectedFixedRegret against minimum of expected fixed unit losses outside expectation; population mean analysis-only, T0 empty endpoint. No rate, convergence or high-probability upgrade.

R5: Exact frozen whole public headers/proof VALUE checks, genuine AE-only noncausal-on-null canary, actual positive-variance/random-seed and nonzero excess, focused/root/Tests/harness/axiom/shadow gates. API and type-only checks are not proof compilation.

R6: Separate readable formula proof, assumption delta, folded exact Lean/dependencies and remaining boundary; same shared registry/old links preserved, applicable local site gate and real original pixel inspection. No generated _site hand edit, source correction, main/live/merge/deploy or chapter/Goal completion claim. Native commands enforce named checks only; remaining role/scope conventions require separate inspection.
