# Private seed and predictable strict-past IID guessing variance benchmark

Task id: `ONLINE-RANDOMIZED-IID-20261008`
Kind: `lean`
Status: `draft`
Harness: `hierarchical`

## Goal

Produce current-target independence and cumulative expected-fixed excess for independent private tape and measurable strict-past predictions. Frozen exact prospective headers in `docs/contracts/online-randomized-iid-v1/targets-v2.json`; source contract review pending, no body accepted. Total Chapters1–16 Goal ACTIVE.

## Source

Orabona arXiv1912.13213v10/2026-06-21, printed1–2/PDF13–14, SHAcef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Source card `docs/contracts/online-randomized-iid-v1/source-card-v2.json`; scenario private tape independent WHOLE IID stream, subordinate pre-reveal information.

## Lean Target

Target file: `BanditRLProof/OnlineGuessingRandomizedIID.lean`

- `BanditRL.OnlineLearning.independent_private_seed_pair` (R001): Joint-seed regrouping lemma; pairwise independence does not suffice.
- `BanditRL.OnlineLearning.private_seed_past_independent` (R002): Derive joint seed+strict-past current independence from natural whole-process seed independence and target IID.
- `BanditRL.OnlineLearning.privateSeedPastInformation_monotone` (R003): Actual generated pre-reveal information grows with the history; no stochastic hypotheses needed.
- `BanditRL.OnlineLearning.predictable_private_seed_independent` (R004): Any measurable prediction in subordinate information inherits independence; current independence is not supplied.
- `BanditRL.OnlineLearning.randomized_history_policy_independent` (R005): Actual jointly measurable policy of seed and finite strict past; empty initial history may use seed.
- `BanditRL.OnlineLearning.predictable_private_seed_expectedFixed_excess` (R006): General predictable-information actual causal lower producer; derive ambient measurability and L2 from information/support.
- `BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess` (R007): Concrete seed+finite-history producer instantiates the general information endpoint; feasible only on legal histories.

## Boundaries

Probability/measurable/a.s.unit targets, same laws/joint IID, whole-process seed independence. Legal history cube only; general predictions a.s.feasible. Minimum of expected FIXED loss outside integration; no E[min], future inputs, supplied current independence, full kernel representation or asymptotic claim. t0 extension; source1..T=Lean0..T−1. Original16/null, C1C2open, remaining asymptotic/oldfive/3–16/appendices required. OPENdraftPR194 exactb08 stack, not main/live.

## Mathlib-Ready Leaf Contract

Cards MLIB-PROBABILITY-INDEPENDENCE/MLIB-MEASURE-INTEGRAL/MLIB-PROBABILITY-VARIANCE. R001 mathlib-candidate (not upstream); R002–R007 project-local. Exact typed API evidence in runs/online-randomized-iid-20261008/draft-types-and-API-v2.log; staged ROOT director/architect and single lower route. Distinct mandatory semantic roundtrip before proving. Focused build/public canary/axiom/fences/root/Tests/fullharness/site and semantic reviewer all separate before acceptance.


## Stabilized v2; first dependency-ready proving leaf R001

Actual distinct CONTRACT accepted-with-explicit-delta, exact seven headers/one context frozen. R002 typed tuple route uses iIndepFun.indepFun_finset and comp, old scalar API is an indirect search lead. R1–R7 remain future body/canary/reader/gate requirements. R001 joint-law regrouping first; no package/chapter/Goal accepted at stabilization.


## Seven frozen actual causal private-seed terminals: BODY candidate

Actual R001 regrouping produces (seed,past)/current independence from independent WHOLE blocks; actual R002 extracts finite tuples from the whole jointly IID process using iIndepFun.indepFun_finset. R003 proves monotone generated comap. R004 inherits independence for measurable predictions in subordinate pre-reveal information. R005 is an actual jointly measurable seed+strict-history policy. R006 derives ambient measurability/L2/current independence and cumulative expected-fixed excess. R007 instantiates R006 with the actual joint policy trajectory, producing legal histories from countable a.s. support. The same stream and prefix are used. No supplied current independence/stability certificate. Arbitrary measurable private tape may be used at t0, with an empty past.

Keep probability, measurable targets, same-law/joint independence/a.s.unit support. Policy feasibility only on legal unit histories for EVERY seed; general predictions only a.s.feasible. Benchmark is min of expected FIXED loss OUTSIDE integration, reusing actual PR194 minimum. R006 accepts a supplied prediction trace measurable in the subordinate information; R007 supplies the explicit real policy representation. No universal stochastic-kernel representation, completed/augmented-field or AE-factorization theorem. Finite lower producer only, not an unknown-law learning rate, high-probability or asymptotic guarantee. Source rounds1..T=Lean0..T-1; T0 is a disclosed empty extension.

Actual seven public proofs/one definition compile with the exact v2 context/headers. Twenty-nine named canary proofs/nine whole fixtures/two probability proofs/two actual anonymous measurable instances compile: a fair private bit times an INFINITE joint IID target law, same laws/a.s.support/mean1/2/variance1/4, actual legal policy first-private-bit then latest past. Two-round expected-fixed excess1/2, separate subordinate-information/R006 wiring, zero horizon, and a proof current Y0 cannot be measured in private-only information. A four-atom XOR law has X,Y,seed each pair independent but (seed,X) not independent of Y; the whole-seed premise cannot be replaced by pairwise independence. The same off-cube-unbounded policy is covered on legal histories. These are actual endpoint instantiations and falsifying boundaries, not substitutes for general declarations.

Actual 55 selected kernel checks: compiler kinds42theorem/13definition, including probability/measurable class proof values. Standard axioms only, no sorryAx. Seven arbitrary-universe public proof VALUE instantiations, seven draft/neutral Prop identities, three complete benchmark/information definition identities;29 closed canary Prop identities/nine whole fixture identities/two probability types/two actual class identities. Thirty-six native header fences/safe scans and26 actual compiled direct VALUE pairs separately pass. All original failures and exact proof-only repairs retained; audit generator duplicate-definition repair changes no source, public or canary. Safe-verify is not compilation. Seven are derived producer/interface results, not seven printed results or a new rate.

Distinct CONTRACT review accepted-with-explicit-delta; BODY, combined root/Tests/full harness, own shadow, nonvacuous contributor, shared registry/source-qualified readers/site/pixels/FINAL/native/draft PR still separate gates. Original R1-R7 remain future FINAL reader requirements. Universal-kernel/completed-field source coverage and source asymptotic-success equivalence remain unproved/required for full coverage audit. Original16 C1 source items/proof-totalnull/five older main-relative source-module audits unwaived/C1C2open/3-16unenumerated/necessaryappendicesrequired/totalGoalACTIVE. OPENdraft unmerged PR194 exact b08 stack, canonical cleanmain6847; no main/live/merge/deploy/retirement. Distinct staged reused automated actors, requested Astra/medium; no absolute-blind/human/external/runtime setting attestation or single-runtime-enforces-all-workflow claim.


## Bounded private-tape producer accepted; draft PR pending

ONLINE-RANDOMIZED-IID-20261008 Independent private tape and subordinate strict-past information finite IID producer only: whole-process tape independence, jointly IID measurable a.s.unit targets, same-law expected fixed benchmark, derived current independence and L2, real jointly measurable policy feasible for every seed only on legal histories. Seven derived proofs and one information definition; same-prefix excess identity and nonnegativity, not a new rate or seven printed results. Universal-kernel/completed-information/AE-factorization full-source coverage audit and source asymptotic-success equivalence REQUIRED; original16 C1 source items/proof-totalnull/five old main-relative source-module audits unwaived/C1C2open/3-16unenumerated/necessaryappendicesrequired/GoalACTIVE. OPENdraft/unmerged PR194 exact b08 stack; no main/live/merge/deploy/retirement. Actual55kernel/42theorem13definition/26VALUEpairs/36nativeguards, 29namedcanaries9fixtures2probabilityproofs2anonymousclassvalues; arbitrary-universe exact public/canary/whole-definition types. Root9098/Tests9255/fullharness472skip7/currentcommittedcontributor5productionpaths1contract. Clean f8c25ea9e5e43841410c0449cb226650cdb057cb v3localLeanverifiedsite;10923oldregistryIDsURLsHashes+8newnodes;13currentoriginalimages viewed by ROOT and distinct FINAL reviewer. Decoder reconstruction recorded; distinct CONTRACT1143/BODY1582/FINAL1822 source reviews accepted-with-explicit-delta with exactR1-R7; no human/external/absolute-blind/model-runtime attestation. Only frozen seven terminals progress7->0. Raw failed attempts/tracking-only/parser/weak historical guessed-hash OR-prefix guard/reader corrections retained. Fullunexcluded whitespaceexit2/scopedpass/exactfiveSHA-boundRAWstdoutexceptions/noexecutablehelper exemption. Actual native acceptance and PR delivery remain separate, performed below with versioned evidence.
