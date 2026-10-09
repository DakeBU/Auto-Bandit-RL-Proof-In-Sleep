# Proof Obligations: source-loss and actual source-update transport

Task id: `ONLINE-CH2-PRESCIENT-SOURCE-20261010`
Source card: docs/contracts/online-ch2-prescient-source-v1/source-card-v1.json
Scenario: required Chapter2 prescient forward dependency, not Chapter15 acceptance.

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| proper | proper from source domain | nonempty finite witness | EReal.coe_toReal | actual retrieval receipts | choose feasible point | arbitrary E, no-bottom globally | project encoding, potentially upstream adapter | lower | OnlineConvex.sourceProper_of_domain | focused + public canary | draft-open |
| strict | penalized objective strict | finitePart convex | StrictConvexOn, canonical divergence | retrieval-source-API-v1 | affine cancellation, positive inverse | real inner-product E; no completeness | project integration | lower | OnlinePrescientBregman.penalized_strictConvex | focused + public canary | draft-open |
| unique | exact selected minimizer | strict + finitePart minimum | advance, eq_of_isMinOn | same | selected minimum equality | complete E, supplied feasible actual minimum | project integration | lower | OnlinePrescientBregman.advance_eq_some_of_minimizer | focused + public canary | draft-open |
| identity | exact source trajectory | unique | iterate | same | induction through T | current-loss argmin updates, not hseq input | project integration | lower | OnlinePrescientBregman.iterate_eq_of_source_updates | focused + public canary | draft-open |
| fixed | source printed fixed bound | proper + identity + iterate_fixed_regret | existing cumulative chain | same | actual source-to-recursion transport | finite-dimensional source, T>=0, interior states | source terminal | lower | OnlinePrescientBregman.source_fixed_regret | full package gates | draft-open |
| variable | source printed finite-MAX bound | proper + identity + iterate_variable_regret | same | same | source transport with previous-state maximum | finite-dimensional source, T>0, positive nonincreasing played steps | source terminal | lower | OnlinePrescientBregman.source_variable_regret | full package gates | draft-open |

## Failure Classification

Draft probe v2 actual1: named namespace syntax error; v3 explicit namespace ends actual0, same headers. No theorem proof authored. Read-only retrieval mistakes retained in retrieval-failures-v1.json. Any body/compiler/semantic failure must be recorded and repaired without terminal weakening.

## Reviewer Notes

All six open. No native/runtime claim of complete method enforcement. Blind reconstruction complete; independent source contract verdict pending. No universal attainment inference from strictness/closedness. Eight required source forward containers remain open pending their own exact source reconciliation and gates. Whole Chapters1-16 Goal active, Chapter2 partial/null. No merge/live assertion.

Integrated candidate: Six frozen source-loss/actual-source-update proof terminals and two complete8/6conjunct canaries have focused/public VALUE, standard-only axioms, frozen native fences and distinct CONTRACT/BODY/publication acceptance. The source codomain/domain assumptions now produce properness; strict penalized objectives identify supplied actual minima with the same classical selector; induction identifies the supplied valid source trajectory with the actual Option recursion. Both printed fixed and decreasing-step bounds are derived, not assumed. All six proof bodies and both full canaries passed combined root/Tests/full harness with actual markers/hashes in inspected receipts. Selected8public/8total nodes,1431coalesced directTYPE_VALUE presences,20requiredVALUEpairs and two individually selected numeric Eq.mpr branches retaining their specific new source endpoints. This is conditional valid-run source transport, not universal attained minima or automatic interior preservation. Six Lean proofs are not six printed source results. All eight Chapter2 source forward containers remain required/open pending dedicated reconciliation; Chapter2 partial/null, Ch3-16 unenumerated/null, persistent Chapters1-16 Goal ACTIVE. Shared registry/site/browser/original-pixel/FINAL/native/delivery gates pending. Stacked unmerged PR212 exact 547137ea02c59c24424e2fb448174875845fadb4. No main/live/merge/deploy/CI/retirement claim.
