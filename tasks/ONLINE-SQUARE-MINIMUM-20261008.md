# Produce squared-loss hindsight minimum and actual FTL best regret

Task id: `ONLINE-SQUARE-MINIMUM-20261008`
Kind: `lean`
Status: `planned`
Harness: `hierarchical`

## Goal

State the bandit/RL theorem, definition, or literature-port target.

## Source

- Paper or repository:
- Theorem/lemma/section:
- Existing Lean declaration:
- Textbook/source card:
- Scenario card:

## Lean Target

```lean
-- target declaration names here
```

Target file: `BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret`

## Proof Obligations

- [ ] Natural-language statement is mapped to Lean symbols.
- [ ] Required model assumptions are explicit.
- [ ] Probability, measurability, concentration, and stopping-time contracts are recorded.
- [ ] Reusable theorem cards are identified before proof search.
- [ ] Each active leaf has local APIs, intended proof route, and regularity contracts.
- [ ] General leaves are classified as `mathlib-candidate`, `project-local`, or `theorem-card-only`.
- [ ] `lake build && lake build Tests` passes.

## Mathlib-Ready Leaf Contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| root | TBD | TBD | TBD | project-local |

## Retrieval Cards

- LML cards:
- Mathlib cards:
- Textbook cards:
- Scenario cards:

## Trial Logging

```bash
python3 tools/bandit.py trial-log --task ONLINE-SQUARE-MINIMUM-20261008 --role lower --kind attempt --status running --notes "..."
python3 tools/bandit.py trial-summary
```


## Draft exact square-minimum contract v1

# Version1 draft: actual squared hindsight minimum

Source Orabona1912.13213v10/2026-06-21 pinned PDF SHAcef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Printed2/PDF14 square-game best-fixed regret, printed3/PDF15 actual empirical-mean argmin, printed4/PDF16 Theorem1.3, printed5/PDF17 sharp initial1/4 and positive-round tail. ROOT directly read/viewed current copied cached source14-16 against the unchanged pinned PDF; caches are provenance-preserving copies, not a claimed fresh rerender. Page17 cache follows separate copy/read before stabilization.

Six exact frozen prospective headers in targets-v1; public-context-v1 contains one genuine literal minimum definition. No target body yet. At every finite T with y_t in[0,1] for t<T, produce mean feasibility/minimization. ForT0, empty sum/minimum are0 and defaultmean0 is feasible; this is an explicit library extension, not uniqueness/source1/T atzero. ForpositiveT use actual existing mean_minimizes/mem. Real sInf over nonempty image is proved attained with actual source mean, no totalized-inf or assumed minimizer certificate. Same losses, predictor, comparator and horizon in shared comparatorRegret. Generic provided prediction equality/order need not be feasible or causal and are representation generalizations, not algorithm existence. Actual endpoints use meanPredict (first1/2, later strict-prefix mean) and existing theorem1.3/refined bodies; arbitrary initialization not given sharpquarter guarantee. Source1..T=Lean0..T-1; refined source2..T=Lean t0..T-2 denominator t+2. Signed pathwise best regret may be negative; do not inherit expected-excess nonnegativity.

No IID/expectation/probability/min-expectation exchange theorem here. Printed1-2 expected fixed minimum and causal variance benchmark remain REQUIRED next, never inferred from this pathwise minimum. No generic argmin for arbitrary losses/carriers and no sublinear/ordinary-limit claim. Four derived representation/order results and two actual-guarantee adapters are not six printed book theorems or new regret-rate mathematics. Proposed meaningful terminal is literal minimum now produced, rather than assumed, and actual FTL guarantee expressed against it.

Distinct required decoder/reviewer before stabilization/proving; same requestedAstra-medium and history disclosed. Sourcecard/fingerprints/DAG/API checks/review receipts required. Future root/Tests/harness/axiom/canary/sharedregistry/reader/site/FINAL/native/PR gates separate. Only bounded square minimum hinge may close; full C1, IID benchmark, five main-relative source-module audits, Chapter2,3-16/appendices remain required. Original16C1items/proof-totalnull, GoalACTIVE, PR192 OPENdraft stack. No main/live/merge/deploy/retirement.

Frozen prospective headers: 6f845210c292f01803e3842002ebcc3795359e7878f3094d5452c582eb62cc01; no source/body acceptance yet.


## Stabilized version1; first finite proving leaf

Distinct source/type CONTRACT review accepted with explicit scope. Six terminal headers and one definition frozen unchanged. R1-R8 remain future reader requirements. First leaf M001 produces empirical-mean feasibility and minimization using actual imported APIs; no target body, package, chapter or Goal acceptance at stabilization.


## Six actual compiled square-minimum terminals; BODY candidate

M001 produces actual mean feasibility/minimization on the same finite interval-target prefix; T0 is only an explicit empty-prefix extension without uniqueness. M002 constructs IsLeast, including actual membership and lower bounds, then imports mathlib IsLeast.csInf_eq. The comparator-loss image is generally infinite, not asserted finite; its actual least element is produced, not supplied as a certificate. M003/M004 retain signed same-trace regret and any supplied real prediction without claiming generic causality/feasibility. M005/M006 use the actual first1/2 strict-past meanPredict and existing theorem1.3/refined proofs; source rounds1..T and tail2..T map to rangeT and range(T-1) denominator real t+2. Six are derived producers/representations/adapters, not six printed results or new rate mathematics.

Actual focused six-body/public20canary builds,38 named standard-axiom kernel checks,6 neutral-to-draft and6 draft-to-actual public closed-Prop identities,20 actual canary type identities,6 whole scoped/fixture identities,26 native header guards and16 actual compiler VALUE pairs pass separately. Safe-verify scans headers/tokens and does not compile. Actual canaries produce T0 minimum/regret0 without uniqueness; varying0/1 data has T2 mean1/2/minimum1/2 and positive-horizon unique mean; actual strategy gives first1/2,next0,then1/2 and regrets1/4,3/4. Fixed time-only alternating prediction and matching fixed targets produce signed regret -1/2 atT2, independently of losses/comparator. Nonbinary1/4,3/4 data gives T2 mean1/2/minimum1/8. Actual endpoint calls preserve log and sharp quarter/tail. These are validation instances, not universal theorem substitutes.

Distinct source/type CONTRACT review accepted-with-explicit-delta and decoder only reconstructed. Source BODY, combined root/Tests/full harness, scoped shadow, contributor, shared source-qualified registry/readers/site/pixels, FINAL, native acceptance and draft PR remain pending. Exact original R1-R8 stay future requirements. No min/expectation exchange: printed1-2 minimum of expected fixed loss and causal cumulative IID variance benchmark remain REQUIRED next. Five older main-relative module audits unwaived; original16C1items/proof-totalnull/fullC1open/C2incomplete/C3-16unenumerated/necessaryappendicesrequired/totalGoalACTIVE. Exact OPENdraft/unmerged PR192base2aa08b9e1f5da4d0c7d7dcbe9ddeadd1fbfc34e3 is a stack, not main/live. Requested Astra/medium and prior staged role history disclosed, no absolute-blind/human/external/runtime attestation. No single runtime enforces the whole workflow.


## Actual bounded package accepted; draft PR delivery pending

ONLINE-SQUARE-MINIMUM-20261008 C1 pathwise square-minimum hinge only: actual empirical-mean feasibility/minimization and attained real interval infimum; signed same-process best-fixed/comparator identity and order; existing actual first1/2 strict-past FTL log and sharp-quarter-tail guarantees expressed against that minimum. Six derived producer/representation/adapters and one definition, not six printed source theorems or new rate mathematics. T0 empty extension without uniqueness; positiveT performance restrictions; arbitrary supplied traces algebra only. Original16C1source items/proof-totalnull/fullC1open, expected FIXED-loss minimum and causal IID cumulative variance REQUIRED next; five older main-relative Foundations/History/IID/Information/Stochastic audits unwaived. Chapter2incomplete, Chapters3–16unenumerated, necessaryappendices required, totalGoalACTIVE. No min/expectation interchange or generic causal learner; exact OPENdraft/unmergedPR192base2aa08b9e1f5da4d0c7d7dcbe9ddeadd1fbfc34e3 stack, no main/live/merge/deploy/retirement. Actual38kernel/26nativeguards/16VALUEpairs,20namedcanaries2fixtures, 6neutral->draft+6draft->actual+20canary types and6wholedefinition identities. Root9096/Tests9251/harness472skip7; actual committed5productionpaths1contract gate supersedes initialvacuous0/0. Clean47c6a03 localLeanverifiedsite/10906oldsharedIDsURLsHashes+7newnodes/12currentimages independently viewed. Distinct reused staged decoder/source reviewer CONTRACT/BODY/FINAL accepted with exact R1–R8; requestedAstra-medium/no human/external/runtime attestation. Frozen6terminal contract progresses6->0 only; original helper/ownership/whitespace/clean-tail failures retained and rawbytes preserved.
