# Prescient affine foundation — source/contract review

Verdict: accepted-with-explicit-delta, CONTRACT stabilization only; no blocking repair. Reused distinct automated source reviewer /root/source_reviewer, requested GPT-6 Astra / medium; no absolute-blind, human/external or runtime-model attestation.

All34 indexed RAW inputs were independently hashed before/after. Pinned v10 PDF SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17 matches. I personally viewed all three current original-detail images PDF26/277/278 and read their extracted text. Source printed14 gives a forward observation; Algorithm15.8 on printed265 receives the current loss before choosing the point. Theorem15.30 and printed266 use negative Bregman movement; the constant-step statement left as an exercise remains mandatory. This package is a necessary, reusable affine/quadratic foundation, not completion of that full result or container.

The actual Domain/project context supplies a nonempty closed convex carrier and classical nearest-point selection in a complete real inner-product space. Finite Euclidean spaces specialize; infinite-dimensional completeness is an explicit mathematical extension. Affine losses are finite everywhere, so X=E, initial x0 arbitrary ambient, and every produced later point feasible are consistent. The four full definitions fix update, recursion, updated prediction, and signed cumulative fixed-comparator regret. No new target proof body exists or was reviewed. The actual successful Lean retrieval is #check of existing APIs only; neutral prose headers are not a compiled new theorem/type file. Decoder reconstruction covers seven types and four definitions, with source/proof verdict deliberately unassessed.

Anti-anchoring checks: with p=project(x-eta*g), actual variational characterization gives eta<g,p-u> <= <x-p,p-u>; the three-point norm identity gives exactly the frozen sharp inequality. Hence proximal comparison and same-run telescope have a legitimate producer route. No future-informed existence or supplied one-step bound premise occurs. Uniqueness is not asserted by the minimizer header. Prefix equality holds with fixed parameters and inclusive indices only. At T=0 the sharp bound is equality0, while the source-form bound merely has nonnegative initial-distance RHS. Zero/negative eta are allowed only by algebra/feasibility/prefix helpers.

The proposed bounded-domain check is arithmetically sound: V=[-1,1], x0=1, eta=1/2, vectors6,-1 yields predictions-1,-1/2, regret-11/2, terminal square1/4, movement17/4, sharp RHS-7/2. Negating ordinary gradient energy would instead give-17/2 and falsely bound the regret. The unconstrained trajectory gives-21/2 and equality in the sharp identity. These are mathematical checks, not compiled canary evidence.

## 1. BanditRL.OnlinePrescientLinear.advance_sharp_bound

- objects: Actual projected update and fixed feasible comparator
- quantifiers: forall V,eta>0,g,x,u with u in V
- assumptions: Complete real Hilbert space; nonempty closed convex V; x arbitrary ambient
- conclusion: sharp one-step inequality
- normalization: 2eta; both negative distance and movement retained
- information: same g read before scoring updated point
- boundary_and_proof_route: Projection VI yields eta<g,p-u> <= <x-p,p-u>; norm identity gives result, no supplied bound oracle

## 2. BanditRL.OnlinePrescientLinear.advance_proximal_minimizer

- objects: Same update with affine offset b
- quantifiers: forall V,eta>0,g,x,b and every feasible comparison u
- assumptions: No x feasibility or sign of b required
- conclusion: membership AND attained proximal objective minimum
- normalization: squared movement/(2eta); b cancels
- information: defined update independent of b and u
- boundary_and_proof_route: One-step plus nonnegative comparator distance yields objective comparison; no uniqueness or numerical implementation claim

## 3. BanditRL.OnlinePrescientLinear.prediction_mem

- objects: Recursive updated prediction
- quantifiers: forall V,eta,g,x0,t
- assumptions: eta arbitrary real; x0 need not feasible
- conclusion: prediction belongs to V
- normalization: t=0 already projects; no initial-state membership claim
- information: current-inclusive update
- boundary_and_proof_route: Projection membership alone; weaker assumptions than performance endpoints legitimate

## 4. BanditRL.OnlinePrescientLinear.prediction_prefix

- objects: Two same-parameter runs
- quantifiers: forall g,gprime,t; equality for all s<=t
- assumptions: same V,eta,x0; eta arbitrary
- conclusion: equal predictions at t
- normalization: inclusive s<=t, not s<t
- information: current vector allowed, future vectors excluded for fixed parameters
- boundary_and_proof_route: Induction on actual recursion; parameters must remain fixed, no external parameter-selection causality guarantee

## 5. BanditRL.OnlinePrescientLinear.regret_eq_loss_difference

- objects: Signed fixed-comparator affine regret
- quantifiers: forall V,eta,g,b,x0,u,T
- assumptions: u need not feasible; eta arbitrary
- conclusion: exact affine loss-difference sum
- normalization: rangeT, offset cancellation, emptyT0
- information: same actual generated predictions
- boundary_and_proof_route: Pure algebra; not best-comparator regret or expectation

## 6. BanditRL.OnlinePrescientLinear.regret_sharp_bound

- objects: Same actual trajectory
- quantifiers: forall V,eta>0,g,x0,u,T with u feasible
- assumptions: No boundedness/gradient bound/positive horizon
- conclusion: sharp finite regret with terminal AND movement residuals
- normalization: state0=x0; stateT=last prediction for T>0; T0 RHS=0
- information: known-current vectors, constant eta throughout
- boundary_and_proof_route: Telescope actual one-step inequalities; no invented gradient-square sign replacement

## 7. BanditRL.OnlinePrescientLinear.regret_source_bound

- objects: Same actual trajectory and fixed comparator
- quantifiers: same universals as sharp bound
- assumptions: positive eta and comparator feasibility
- conclusion: source-form finite movement bound
- normalization: T0 RHS initialdistance/(2eta)>=0
- information: same current-inclusive trajectory
- boundary_and_proof_route: Drop only nonpositive terminal residual; specialization of constant-step15.30, not full source closure

## Frozen future scope

Approve versioned stabilization of the exact seven hashes and four definitions. Initially permit ONLY the new BanditRLProof/OnlinePrescientLinear.lean context and advance_sharp_bound proof, plus scoped OWN task/contract/run metadata. Its actual compiled proof and frozen statement guard must precede dependent lowering; no target weakening or changed header without a new review. Protect all4168 old baseline files, already independently rehashed here. Before intended metadata appends, preserve exact immutable prior input bytes and explicit suffix resolution; do not later claim changed live journals remain raw-identical.

No roots/Tests/readers/global SGB/index/generated site/old package edits are authorized now. Separate exact publication plan and canary header review remain required. No Chapter15 expansion, new library, package/body/combined/site/native acceptance, Chapter2 fraction, whole Goal completion, merge/deploy or retirement is authorized. Seven terminals serve one chain, not seven source results. Whole Goal ACTIVE and chapter proof total null remain.

Future reader obligations follow with stable IDs:

- R1: Identify the package as a complete-Hilbert extension of an affine-loss quadratic/Euclidean foundation, not the full prescient source container or seven printed results.
- R2: State receive-current-loss BEFORE prediction; prediction t=state(t+1), source round t+1; contrast ordinary strict-past OGD without conflating its loss evaluation.
- R3: State nonempty closed convex domain, arbitrary ambient initial center, fixed positive eta for performance/minimizer, and no bounded domain/gradient assumption.
- R4: Display negative movement energy and final residual correctly; do not substitute negative ordinary gradient-square energy on constrained domains.
- R5: Explain actual projection/proximal minimizer and same-run telescope producers, not assumptions of an argmin/one-step regret oracle; classical projection is not a numerical sampler.
- R6: Preserve full quantifiers, all natural horizons including0, finite signed fixed-comparator cumulative loss, offset cancellation, and weaker feasibility/prefix/algebra assumptions.
- R7: Keep general convex/subdifferentiable/Bregman/time-varying15.30 and the full Chapter2 prescient source container required/open; source constant-step exercise remains mandatory.
- R8: Future canary headers require separate roundtrip review; roots/Tests/readers need exact byte publication scope and combined/kernel/site/registry/pixel/FINAL/native/delivery gates before any package acceptance.
