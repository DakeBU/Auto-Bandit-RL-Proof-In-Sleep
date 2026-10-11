# Adaptive OSD algorithm CONTRACT review

Verdict: accepted-with-explicit-delta. Context, recurrence, prefix and parent-terminal contracts are favorable within the explicit source and information boundaries. No blocking repairs. This is not a BODY or algorithm acceptance.

The reused distinct staged automated source reviewer has related history. Requested Astra/medium is not runtime attested; no human/external review or absolute blindness is claimed. All 46 indexed RAW inputs were independently hashed before/after. The decoder's adjacent API comments/declarations and one proof-line exposure remain disclosed. Its first API hashes followed an initial lookup, rather than preceding every access; matching final snapshots do not change that history. Both complete reconstructions were read and checked against the actual context.

## Source and actual definitions

The original PDF51 was personally viewed at original detail this round; PDF52 reuses the personally viewed unchanged original from the immediately preceding minimum review. Source Eq4.3 uses inclusive observed support energy and skips zero feedback; Eq4.4 gives the 3/2 coefficient, and Theorem4.14 gives sqrt(2) with the rescaled step. The min/infimum correction is separately mathematically approved, not a newly compiled benchmark, source alteration or assumption permitting future knowledge. The earlier missing-/2 allegation remains rejected and withdrawn.

The eight definitions are actual state, history, energy, output, selected, eta, LegalFeedback and regret. state is a Nat.rec whose initial pair is singleton x1 and zero; each transition evaluates the fixed policy on the finite past losses, its actual history and the current loss, then appends one actual action and adds the selected squared norm. history/energy are state projections; output is its last entry. selected repeats the same policy call on this actual state. eta uses inclusive energy. LegalFeedback concerns selected global supports only at played points. regret uses these pre-update actions and one fixed comparator. No desired trajectory, stability inequality or regret bound is supplied to the recursion.

The shared Domain is nonempty/closed/convex and projection is the actual nearest-point construction. Finite dimensionality supplies the real Euclidean setting. SourceSubdifferential is a global ambient support inequality; SubdifferentiableOn includes properness and support existence on the carrier. Properness rules out bottom and provides a finite witness; a support at a feasible point then rules out top there. Consequently the future performance proof can justify both played/comparator toReal conversions once feasibility is proved. Totalized toReal alone is not this justification.

Omitting explicit global convexity is a valid stated support-sufficient generalization for this comparison, not a claim that arbitrary nonconvex losses satisfy the assumptions. The global supports already provide the required loss-difference inequality. The source-convex specialization and a canonical lawful-policy adapter remain explicit future obligations.

## Anti-anchored checks and constants

For fixed V,alpha,D,x1,p, state at time t reads only losses strictly before t. Induction under equality of those complete functions gives equal earlier state, equal current support on the next consumed round, and equal appended state. No agreement of separately supplied step schedules is needed because eta is computed internally. A p closure or external D chosen afresh using each full future stream is not covered; neither the interface nor the theorem gives that stronger assertion.

For D>0, the proposed nonzero-step projection inequality has potential weight sqrt(S_(t+1))/(2alpha D). The already reviewed weighted-potential bound with C=D² yields D sqrt(S_T)/(2alpha) minus the displayed terminal term. The energy summation contributes alpha D sqrt(S_T), giving exactly 1/(2alpha)+alpha. Zero selected feedback must be handled separately: action and potential stay unchanged, and the global zero support makes that round's loss difference nonpositive, even if previous energy is positive. No division by a possibly zero step is justified on that branch.

D=0 forces all feasible points to coincide, so the feasible trajectory and comparator coincide despite possibly nonzero feedback; regret and terminal distance vanish. T=0 gives empty regret/zero energy. Zero total energy forces every played support to vanish, yielding nonpositive regret, not necessarily equality or constant losses. These checks reveal no counterexample to the frozen parent terminal. They are contract plausibility/source checks, not its Lean BODY proof. Alpha1 and alpha=sqrt(2)/2 yield the stated coefficients only for their respective same-parameter runs; they do not identify trajectories across alpha.

## Seven slots per target

### state_succ

- objects/model: Finite-dimensional real inner-product E; nonempty closed convex Domain and actual Nat.rec history-energy state.
- quantifiers: For all V, alpha,D,loss,x1,p,t with identical arguments throughout.
- hypotheses: No positivity, feasibility, legality or regularity assumptions.
- conclusion: Exact full pair equality: append zero-skip or projection update and add actual selected norm squared.
- constants/indices/boundaries: History length t+1 becomes t+2; denominator is sqrt(previous energy+current norm squared).
- information: Current action exists before loss t; p sees strict-past full losses, actual history, current whole loss; update produces next action.
- source/evidence delta: Total division and zero skip preserve arbitrary definition inputs; equality is structural, not performance or legal-policy existence.

### state_prefix

- objects/model: Two loss streams on the same E, Domain and common fixed external parameters/policy.
- quantifiers: Universal streams and natural t; one common p rather than two independently selected policies.
- hypotheses: Equality of complete ambient loss functions for each s<t; no equality of eta required.
- conclusion: Equality of whole finite history and cumulative energy at t.
- constants/indices/boundaries: At t0 premise vacuous; no condition on loss t or later, and no conclusion about current support or state t+1.
- information: Strict-past structural causality holds for fixed V,alpha,D,x1,p. Reselection or future information encoded in changing parameters is outside this comparison.
- source/evidence delta: No legality/finite loss/feasibility or sign conditions needed; full-function equality is stronger than EqOn V and is appropriate because p reads whole functions.

### regret_bound

- objects/model: Same actual generated trajectory, actual EReal losses, fixed feasible comparator, selected supports and cumulative energy.
- quantifiers: All T>=0; alpha>0, D>=0; every actual-prefix legal policy satisfying displayed source regularity.
- hypotheses: Feasible initial/comparator; proper loss plus global supports at every feasible point; selected support legal at played point; diameter bound on entire carrier.
- conclusion: Same-run regret <= (1/(2alpha)+alpha)D sqrt(S_T) - norm(x_T-u)^2 sqrt(S_T)/(2alpha D).
- constants/indices/boundaries: Source rounds1..T map range T; x_T is after T updates; terminal energy includes exactly T supports. T0/D0/zeroenergy retained.
- information: No supplied desired one-step bound, exogenous eta, future-energy optimizer, probability or expectation. Prefix legality is conditional, not an existence certificate.
- source/evidence delta: Support-sufficient generalization omits explicit global convexity; properness/supports yield finite values. Negative terminal is a strengthening of printed bound. Source specialization and full algorithm proof remain required.

## Probe and precise conditional proof window

The v1 scratch probe failed to synthesize Decidable for equality in the generic E; its failed output, including the error placeholder, is not proof evidence. Contextv2 adds the local classical DecidableEq without changing theorem premises. The v2 full recurrence/regret Prop probe and the separate full prefix Prop probe actually exit0; their unused-variable warnings are retained. These compile definitions and proposition types, not theorem bodies.

Stabilize the exact contextv2 and three SHA-bound headers. Permit only create-only BanditRLProof/OnlineAdaptiveOSD.lean containing those eight exact definitions/context and exact state_succ with its BODY, followed by an actual focused build. Only after that build succeeds may the same file append exact state_prefix and its BODY, preserving prior definitions/state_succ bytes and performing its own focused build. No additional public declarations, altered imports/context or parent regret BODY are authorized. The parent stays frozen and required; energy/feasibility/finite-support/zero/one-step/summation dependencies need their own reviewed readiness before it can be lowered.

No root, Tests, reader, registry, pins, old library or global state edits are authorized by this contract review. No package, source-container, Chapter2 or whole-Goal closure. Whole Goal remains active.
