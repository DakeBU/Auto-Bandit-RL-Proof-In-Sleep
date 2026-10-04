# Blind mathematical reconstruction: 21 target declarations

## Scope and provenance

This report decodes only `blind-packet-v3.md` from this run directory. I read no other files, source texts, target proofs, prior reports, or prior verdicts. It is a distinct automated decoder's reconstruction, not an external human or external-model review. All target headers and the two imported theorem headers are supplied statements without proof bodies. Nothing here certifies compilation, correctness of proofs, or acceptance against an original source.

Independently computed raw-byte packet SHA-256:
`652d0efc210cf8f2e26e5d822095e7df7128cae7899fc432f627b315333c41f2`.

## Shared mathematical context and notation

All 21 targets are parametrized by an arbitrary finite-dimensional real inner-product space E, with its compatible normed additive commutative group structure. No positive dimension is required. A domain V consists of a nonempty, closed, convex subset C of E. Boundedness is not part of this domain structure. Write P_C(z) for the supplied choice of metric projection. The supplied, unproved projection header states that P_C(z) belongs to C and its distance from z equals the infimum of distances from z to members of C. This is not a projection algorithm or a supplied proof of that property.

The losses f_t map E to the extended real line, with values possibly +∞ or −∞ unless hypotheses exclude them. Properness is exactly

\[
\mathrm{Proper}(f)\iff (\forall z\in E, f(z)\ne-\infty)
\ \land\ (\exists z\in E\ \exists r\in\mathbb R, f(z)=r).
\]

The finite-value witness need not initially be in C. The subdifferential is the all-query support relation

\[
\partial f(x)=\{g\in E:\forall y\in E,\ f(x)+\iota(\langle g,y-x\rangle)\le f(y)\},
\]

where ι is the embedding of real numbers in EReal. Queries are not restricted to C or to a finite effective domain. Define

\[
S_C(f)\iff\mathrm{Proper}(f)\land\forall x\in C,\ \partial f(x)\ne\varnothing.
\]

This definition does not explicitly add a global convexity assumption on f. It does impose global properness and the existence of globally supporting vectors at every point of C. Properness together with a supporting vector at a point forces its value to be finite: −∞ is excluded by properness; +∞ would violate support at the properness witness. In particular S_C(f) produces finite values throughout C. The supplied toReal operation sends both infinities to zero and a finite real value to itself; thus an unrestricted toReal loss difference is not automatically an actual finite loss difference.

A fixed policy p is a family of maps

\[
p_t:(E\to\overline{\mathbb R})^{\{0,\ldots,t-1\}}
\times E^{\{0,\ldots,t\}}\times(E\to\overline{\mathbb R})\to E.
\]

It receives the t past loss functions, a history of t+1 outputs, and the currently observed whole loss function. At t=0 the first input is empty. There is no future loss argument and no comparator argument. The whole current function is available; this is not merely scalar feedback at the played point. The type alone does not certify that the output is a subgradient.

For a schedule η:ℕ→ℝ, loss sequence f, initialization a (called x₁ in the packet despite time starting at zero), and common fixed p, define H_t, x_t, and g_t recursively:

\[
H_0=(a),\qquad x_t=H_t(t),\qquad
 g_t=p_t((f_s)_{s<t},H_t,f_t),\qquad
 H_{t+1}=H_t\mathbin{\|}\big(P_C(x_t-\eta_t g_t)\big).
\]

Here the last operation appends a single vector, retaining all existing coordinates. Hence x₀=a and x_{t+1}=P_C(x_t−η_t g_t). Indices are zero based: T losses are f₀ through f_{T−1}, with terminal output x_T.

The optional universal oracle law O_C(p) says: for every t, every tuple of past loss functions, every output tuple h of length t+1, and every current function f, if S_C(f) and h(t)∈C, then p_t(past,h,f)∈∂f(h(t)). Earlier coordinates of h need not be feasible; the tuples need not describe a generated trajectory. In contrast, L_T means only

\[
L_T(C,\eta,f,a,p)\iff\forall t<T,\quad g_t\in\partial f_t(x_t)
\]

for the actual generated run. It constrains neither other histories nor later rounds. The regret definition is

\[
R_T(u)=\sum_{t=0}^{T-1}\big(\operatorname{toReal}(f_t(x_t))-
\operatorname{toReal}(f_t(u))\big).
\]

Write Δ_t(u) for this summand and A_t(u)=‖x_t−u‖². All occurrences of x_t and g_t below belong to the schedule specified for that particular claim; changing η generally changes the run. All quantifiers are deterministic. No probability, expectation, high-probability qualification, filtration, or independence assumption is supplied.

The canonical policy chooses c(f,x) from ∂f(x) by classical choice when that set is nonempty, and returns 0 when it is empty. Its value is pᶜ_t(past,h,f)=c(f,h(t)); it ignores the past-loss input and all history coordinates except the last. Define the imported iteration z₀=a, z_{t+1}=P_C(z_t−η_t c(f_t,z_t)). No computational availability or continuity of the choice is claimed.

For boundedness context, the extended diameter is the supremum of extended distances between all pairs of members of C, and diam(C) is its ENNReal.toReal value. The supplied second imported theorem header equates boundedness with that extended diameter being different from +∞. Thus the boundedness assumption in target 16 matters when interpreting diam(C) as a finite distance bound; the real-valued conversion alone would not establish finiteness of the extended diameter.

## Result 1 — initial history

1. **Objects/spaces:** E, C, η, f, a, p, and the one-coordinate history H₀ as defined above.
2. **Quantifiers/order:** For every such domain, schedule, losses, initialization, and fixed policy; equality is of functions on the one-element index set Fin 1.
3. **Assumptions:** Only the shared space/domain structure and well-typed inputs.
4. **Exact conclusion:** H₀(i)=a for its sole index i; equivalently H₀ is the constant function with value a.
5. **Constants:** Time 0 and history length 1.
6. **Probability/information:** Deterministic; no loss is consulted to initialize the history.
7. **Boundary/exclusions:** a may be outside C; neither feedback legality nor positive steps is required. This is only the initialization identity.

## Result 2 — history recursion

1. **Objects/spaces:** The same run and H_t,H_{t+1},x_t,g_t,η_t.
2. **Quantifiers/order:** Universally for the shared inputs and every natural t.
3. **Assumptions:** No additional restrictions on a, losses, steps, or p.
4. **Exact conclusion:** H_{t+1}=H_t appended with P_C(x_t−η_t g_t), as equality of functions with t+2 coordinates. Old coordinates are retained in order.
5. **Constants:** One appended coordinate; time increments from t to t+1.
6. **Probability/information:** Deterministic; g_t can use f_t, but no later loss is an input to this update.
7. **Boundary/exclusions:** t=0 and zero or negative steps are included. This identity alone asserts no loss or regret inequality.

## Result 3 — initial output

1. **Objects/spaces:** The run's output x₀ and initialization a.
2. **Quantifiers/order:** For every shared input tuple.
3. **Assumptions:** No extra assumptions.
4. **Exact conclusion:** x₀=a.
5. **Constants:** Time zero; the source parameter name x₁ does not shift the summation indices.
6. **Probability/information:** Deterministic; the first play is independent of supplied loss arguments with a and p fixed.
7. **Boundary/exclusions:** No membership a∈C is imposed. This does not project the initialization.

## Result 4 — output recursion

1. **Objects/spaces:** The run's consecutive outputs and selected vector.
2. **Quantifiers/order:** For all shared inputs and t∈ℕ.
3. **Assumptions:** No extra feasibility, positivity, or legality assumption.
4. **Exact conclusion:** x_{t+1}=P_C(x_t−η_t g_t).
5. **Constants:** A single step with scalar η_t, not a different schedule or a shifted step index.
6. **Probability/information:** Deterministic; current feedback is selected after x_t and used for x_{t+1}.
7. **Boundary/exclusions:** Arbitrary real η_t and arbitrary policy vectors are allowed. The formula does not claim that g_t is supporting.

## Result 5 — feasibility of every history coordinate

1. **Objects/spaces:** H_t and its coordinate i∈{0,…,t} in E, with domain C.
2. **Quantifiers/order:** For every shared run initialized feasibly, every t, and every i∈Fin(t+1).
3. **Assumptions:** a∈C, in addition to the domain/space structure.
4. **Exact conclusion:** H_t(i)∈C.
5. **Constants:** History has exactly t+1 coordinates.
6. **Probability/information:** Deterministic; no oracle law or legal-feedback premise is used.
7. **Boundary/exclusions:** Includes the initial coordinate and t=0. No positivity or finite-loss premise is needed; an infeasible initialization is excluded by this statement.

## Result 6 — feasibility of outputs

1. **Objects/spaces:** The output x_t of a run on C.
2. **Quantifiers/order:** Every shared run with a∈C, and every natural t.
3. **Assumptions:** a∈C only beyond shared typing/structure.
4. **Exact conclusion:** x_t∈C.
5. **Constants:** No numerical bound; all times including zero.
6. **Probability/information:** Deterministic; arbitrary p and losses are allowed.
7. **Boundary/exclusions:** The assertion covers all t without any finite horizon. It does not infer subgradient legality from feasibility.

## Result 7 — strict-past causality of histories

1. **Objects/spaces:** Two runs on the same C, same a, and exactly the same fixed function p, but schedules η,η′ and losses f,f′.
2. **Quantifiers/order:** For every t, if η_s=η′_s and f_s=f′_s for every s<t, the histories agree at t. Equality of losses means equality of whole functions on E.
3. **Assumptions:** The stated strict-prefix equalities; no requirements on times s≥t or on feasibility.
4. **Exact conclusion:** H_t(C,η,f,a,p)=H_t(C,η′,f′,a,p), including every coordinate.
5. **Constants:** The cutoff is strictly less than t, not less than or equal to t.
6. **Probability/information:** Deterministic nonanticipation conditional on common fixed p and a. The current loss f_t and current step η_t need not agree. This does not assert invariance if p or initialization is changed based on the loss sequence; a function closure with external choices is held fixed in the comparison.
7. **Boundary/exclusions:** At t=0 both prefix premises are vacuous. Equality of selected vectors g_t is not asserted when current losses differ. Schedules are arbitrary inputs; no general predictability theorem about how a schedule was chosen is included.

## Result 8 — strict-past causality of played outputs

1. **Objects/spaces:** The paired runs and shared C,a,p of result 7.
2. **Quantifiers/order:** Every t, under equality of both schedules and whole loss functions at all s<t.
3. **Assumptions:** Exactly those strict-prefix equalities; no oracle or feasibility hypothesis.
4. **Exact conclusion:** x_t(C,η,f,a,p)=x_t(C,η′,f′,a,p).
5. **Constants:** Strict cutoff t; it permits different data at t itself.
6. **Probability/information:** Deterministic causality for the current play with p and initialization held fixed. Current loss may affect selected feedback and the next output, without affecting x_t.
7. **Boundary/exclusions:** Includes t=0; does not compare different policies, different initializations, or arbitrary sequences of steps whose earlier values already encode different future data.

## Result 9 — universal oracle law supplies actual legal feedback

1. **Objects/spaces:** A run, finite horizon T, O_C(p), and L_T for that run.
2. **Quantifiers/order:** For every shared run and natural T, if the universal law holds and S_C(f_t) for every t<T, legality follows at every t<T.
3. **Assumptions:** a∈C, O_C(p), and the per-round S_C(f_t) premise on the horizon. No step positivity is assumed.
4. **Exact conclusion:** L_T(C,η,f,a,p), namely g_t∈∂f_t(x_t) for all t<T.
5. **Constants:** Horizon indices 0,…,T−1.
6. **Probability/information:** Deterministic. The universal law quantifies over arbitrary off-trajectory histories; the conclusion only concerns this trajectory. This is an implication, not an equivalence.
7. **Boundary/exclusions:** T=0 is allowed and yields vacuous legality. Behavior after T and converses from actual legality to the universal law are not asserted.

## Result 10 — finite played and comparator loss values

1. **Objects/spaces:** f_t, the actual x_t, and comparator u∈C.
2. **Quantifiers/order:** Every run, any t, and any feasible comparator u.
3. **Assumptions:** a∈C, S_C(f_t), and u∈C. No assumption is made on earlier losses, p's legality, or positive steps.
4. **Exact conclusion:** Both equalities hold in EReal:
   \[f_t(x_t)=\iota(\operatorname{toReal}f_t(x_t)),\qquad
     f_t(u)=\iota(\operatorname{toReal}f_t(u)).\]
   Thus both displayed values are actual finite real values.
5. **Constants:** No loss magnitude bound or numeric constant.
6. **Probability/information:** Deterministic; no random or oracle event. Finiteness follows from the mathematical premises rather than the toReal conversion by itself.
7. **Boundary/exclusions:** ±∞ at these two points is excluded by the conclusion. Values outside C may still be +∞. The declaration does not claim uniform bounds or finiteness everywhere in E.

## Result 11 — two one-step inequalities

1. **Objects/spaces:** One run, time t, selected g_t, consecutive x_t,x_{t+1}, and u∈C.
2. **Quantifiers/order:** Universally for these inputs, with hypotheses at the specified round t.
3. **Assumptions:** η_t>0; S_C(f_t); actual membership g_t∈∂f_t(x_t); u∈C. Notably no a∈C premise is present, and no legality at other rounds is required.
4. **Exact conclusion:** A conjunction of inequalities, retaining the intermediate inner product:
   \[
   \eta_t\Delta_t(u)\le\eta_t\langle g_t,x_t-u\rangle,
   \quad
   \eta_t\langle g_t,x_t-u\rangle\le
   \tfrac12 A_t(u)-\tfrac12 A_{t+1}(u)
     +\tfrac12\eta_t^2\|g_t\|^2.
   \]
5. **Constants:** Exact coefficients 1/2; the feedback term uses η_t squared and ‖g_t‖ squared.
6. **Probability/information:** Deterministic, with support legality only at the actual point for this step. Properness plus that membership also gives finite f_t(x_t), even when x_t was not assumed feasible; f_t(u) is finite by S_C(f_t) and u∈C.
7. **Boundary/exclusions:** Zero/negative η_t are excluded. No norm bound, bounded domain, universal oracle law, or feasibility of the initialization is required by this header.

## Result 12 — divided one-step loss bound

1. **Objects/spaces:** The same one-step objects as result 11.
2. **Quantifiers/order:** Every run, time t, and feasible comparator satisfying the listed local premises.
3. **Assumptions:** η_t>0; S_C(f_t); g_t∈∂f_t(x_t); u∈C. Again there is no a∈C premise.
4. **Exact conclusion:**
   \[
   \Delta_t(u)\le\frac{A_t(u)-A_{t+1}(u)}{2\eta_t}
       +\frac{\eta_t}{2}\|g_t\|^2.
   \]
5. **Constants:** Denominator 2η_t and coefficient η_t/2; the terminal squared distance has a negative sign.
6. **Probability/information:** Deterministic actual-feedback statement at t only. The loss difference is finite under properness and support at x_t plus feasibility of u.
7. **Boundary/exclusions:** No full-horizon legality is needed. η_t=0 is excluded even though a totalized formal division operation exists; no alternative zero-step bound is stated.

## Result 13 — fixed-step regret with terminal residual

1. **Objects/spaces:** A run whose schedule is the constant η, horizon T, and comparator u∈C.
2. **Quantifiers/order:** Every η>0, every such run, every natural T, and each feasible u, under the horizon assumptions.
3. **Assumptions:** a∈C, S_C(f_t) for all t<T, L_T for the constant-η run, and u∈C. No universal O_C(p) is required.
4. **Exact conclusion:**
   \[
   R_T(u)\le\frac{\|a-u\|^2}{2\eta}
      +\frac\eta2\sum_{t=0}^{T-1}\|g_t\|^2
      -\frac{\|x_T-u\|^2}{2\eta}.
   \]
5. **Constants:** Exact initial term and negative terminal term, both divided by 2η; exact gradient-energy coefficient η/2.
6. **Probability/information:** Deterministic, actual trajectory legality sufficient; all losses at played and comparator points are finite under the premises. All outputs and feedback are from this same constant-step run.
7. **Boundary/exclusions:** T=0 is included; the empty sum and matching initial/terminal terms cancel. No domain diameter or gradient magnitude bound is required. Nonpositive η is excluded.

## Result 14 — fixed-step regret after dropping terminal residual

1. **Objects/spaces:** The same constant-step run, T, and u as in result 13.
2. **Quantifiers/order:** Universally over those inputs and all natural T.
3. **Assumptions:** η>0, a∈C, horizon S_C(f_t), horizon L_T for that run, u∈C.
4. **Exact conclusion:**
   \[
   R_T(u)\le\frac{\|a-u\|^2}{2\eta}
      +\frac\eta2\sum_{t=0}^{T-1}\|g_t\|^2.
   \]
5. **Constants:** 1/(2η) and η/2. There is no terminal residual in this conclusion; it is a weaker upper bound than result 13.
6. **Probability/information:** Deterministic; neither universal oracle behavior nor stochastic averaging is required.
7. **Boundary/exclusions:** T=0 allowed. No boundedness or gradient bound is assumed; η must remain strictly positive.

## Result 15 — nonincreasing-step regret with supplied diameter bound

1. **Objects/spaces:** A variable-step run, positive horizon T, real D, comparator u∈C, and all pairwise distances in C.
2. **Quantifiers/order:** Every such run and D satisfying ∀x∈C ∀y∈C, ‖x−y‖≤D; every feasible u.
3. **Assumptions:** a∈C; T>0; η_t>0 for t<T; η_{t+1}≤η_t whenever t+1<T; S_C(f_t) and actual L_T on t<T; the pairwise D bound; u∈C. There is no separately written D>0 premise, although nonemptiness and the pairwise bound imply D≥0.
4. **Exact conclusion:**
   \[
   R_T(u)\le\frac{D^2}{2\eta_{T-1}}
     +\sum_{t=0}^{T-1}\frac{\eta_t}{2}\|g_t\|^2
     -\frac{\|x_T-u\|^2}{2\eta_{T-1}}.
   \]
5. **Constants:** Both distance terms use the last played step η_{T−1}, not η_T. The gradient term retains the individual η_t/2 weights.
6. **Probability/information:** Deterministic actual-feedback bound on the same variable-step run. The header does not require an online rule for selecting η; it treats the schedule as given.
7. **Boundary/exclusions:** T=0 is excluded. For T=1 monotonicity is vacuous. D=0 is permitted for a singleton domain. No restrictions on steps at t≥T, and no uniform gradient bound, are imposed.

## Result 16 — nonincreasing-step regret using metric diameter

1. **Objects/spaces:** The variable-step run and metric diameter d=diam(C), with bounded domain C.
2. **Quantifiers/order:** Every bounded domain, every run and positive horizon meeting the conditions, and every u∈C.
3. **Assumptions:** a∈C; T>0; positive steps t<T; η_{t+1}≤η_t for t+1<T; horizon S_C(f_t) and L_T; boundedness of C; u∈C.
4. **Exact conclusion:**
   \[
   R_T(u)\le\frac{d^2}{2\eta_{T-1}}
      +\sum_{t=0}^{T-1}\frac{\eta_t}{2}\|g_t\|^2
      -\frac{\|x_T-u\|^2}{2\eta_{T-1}}.
   \]
5. **Constants:** The finite metric diameter is squared. Both denominators use 2η_{T−1}; the negative terminal contribution is retained exactly.
6. **Probability/information:** Deterministic; the imported boundedness/extended-diameter header explains why the real diameter represents a finite pairwise bound here. This report does not certify that header's proof.
7. **Boundary/exclusions:** Unbounded C and T=0 are excluded. Diameter zero is allowed. No global oracle law or gradient bound is assumed.

## Result 17 — horizon-tuned bound for one comparator

1. **Objects/spaces:** Positive reals D,G, positive natural horizon T, comparator u, and the run with constant step η*=D/(G√T), where T is coerced to ℝ inside √T.
2. **Quantifiers/order:** For every such D,G,T and run, every u∈C with ‖a−u‖≤D, provided the actual selected vectors of this tuned run obey the specified bound.
3. **Assumptions:** a∈C; T>0; D>0; G>0; S_C(f_t) for t<T; L_T specifically for η*; u∈C; ‖a−u‖≤D; ‖g_t‖≤G for t<T specifically on that same η* run.
4. **Exact conclusion:**
   \[R_T(u;\eta^*)\le DG\sqrt T.\]
5. **Constants:** η*=D/(G√T) and regret coefficient exactly 1 in front of DG√T. D bounds initial comparator distance, not necessarily domain diameter.
6. **Probability/information:** Deterministic and horizon-tuned. The horizon may be known when this schedule is chosen. Legality and gradient bounds from a different schedule cannot be substituted. No future-loss access is an input to p's interface.
7. **Boundary/exclusions:** D=0, G=0, and T=0 are excluded by explicit strict positivity; no limiting convention is asserted. No bounded-domain assumption is needed. The claim is comparator-specific and does not assert an anytime guarantee across T on one fixed schedule.

## Result 18 — horizon-tuned bound uniformly over comparators

1. **Objects/spaces:** The same η*=D/(G√T) construction, with D now bounding every pairwise domain distance.
2. **Quantifiers/order:** After fixing C,f,a,p,T,D,G and their hypotheses, the conclusion holds for every u∈C, on the same tuned run. There is no choice of a new policy or new trajectory for each u.
3. **Assumptions:** a∈C; T,D,G strictly positive; horizon S_C(f_t); actual L_T for η*; ∀x∈C ∀y∈C, ‖x−y‖≤D; and ‖g_t‖≤G for every t<T on the same η* run.
4. **Exact conclusion:**
   \[\forall u\in C,\quad R_T(u;\eta^*)\le DG\sqrt T.\]
5. **Constants:** Exact tuning D/(G√T), exact DG√T upper bound, and strictly positive D,G.
6. **Probability/information:** Deterministic simultaneous comparator statement. Feedback need only be legal on the actual trajectory. It is not an expected-regret or probability-qualified conclusion.
7. **Boundary/exclusions:** Zero horizon or zero tuning parameters excluded. The pairwise bound is required here, unlike result 17. It does not claim a realized minimizer exists, nor does it assert a single horizon-independent schedule achieving every bound.

## Result 19 — canonical policy satisfies the universal law

1. **Objects/spaces:** Domain C and pᶜ, defined by the classical subgradient chooser c.
2. **Quantifiers/order:** For every C, O_C(pᶜ). Expanded: for every t,past,h,f, if S_C(f) and h(t)∈C, then pᶜ_t(past,h,f)∈∂f(h(t)).
3. **Assumptions:** Only the shared domain/space structure outside the universal implication; S_C(f) and last-point membership are inside its antecedent.
4. **Exact conclusion:** The canonical policy obeys the full oracle law, including at histories that are not generated by any run.
5. **Constants:** Canonical fallback is vector 0 when ∂f(h(t)) is empty; the law's antecedent excludes that emptiness.
6. **Probability/information:** Deterministic classical selection. The policy uses current f and the last output, ignoring past losses and earlier output coordinates. No uniqueness or implementability of the selected vector is asserted.
7. **Boundary/exclusions:** No schedule, initialization, or horizon is present. The law makes no claim for current functions failing S_C(f) or last points outside C, even if the chooser happens to be legal there.

## Result 20 — canonical output agrees with imported iteration

1. **Objects/spaces:** Canonical-policy run x_tᶜ and imported sequence z_t defined in the shared context.
2. **Quantifiers/order:** Every C, arbitrary η,f,a, and every t∈ℕ.
3. **Assumptions:** No feasibility, step positivity, properness, or feedback-law premise is required.
4. **Exact conclusion:** x_tᶜ=z_t, where z₀=a and z_{s+1}=P_C(z_s−η_s c(f_s,z_s)).
5. **Constants:** Same initialization and same index t; no time shift or alternative step size.
6. **Probability/information:** Deterministic identity of two recursively specified trajectories using the same choice function.
7. **Boundary/exclusions:** Includes t=0, arbitrary losses, and empty-subdifferential cases through the zero fallback. This is an identity, not a new regret guarantee or a computational execution claim.

## Result 21 — canonical feedback agrees at the imported iterate

1. **Objects/spaces:** Canonical selected feedback g_tᶜ, current f_t, and imported iterate z_t.
2. **Quantifiers/order:** Every C,η,f,a and natural t.
3. **Assumptions:** No extra hypotheses on feasibility, losses, or steps.
4. **Exact conclusion:** g_tᶜ=c(f_t,z_t), the imported current-subgradient choice at that iterate.
5. **Constants:** Current index t on both loss and iterate; fallback vector zero remains part of c's definition.
6. **Probability/information:** Deterministic equality; current f_t is an explicit input to the feedback selector, after the play at t. It does not imply g_t itself is strict-past invariant under changes to f_t.
7. **Boundary/exclusions:** With ∂f_t(z_t) empty the equality still applies and identifies the selected vector as zero, without declaring that vector a subgradient. Legality needs separate hypotheses such as those in result 9 or the oracle antecedent.

## Limits of the reconstruction

The supplied definitions fix the relevant indexing, finite-history input types, EReal conversion, properness, all-query support condition, diameter convention, and distinction between arbitrary oracle histories and actual feedback. I find no remaining ambiguity in the mathematical statements on those points. Causality is precisely the paired-run invariance stated with common p and a and common strict-past schedule; it is not a theorem that arbitrary externally chosen p, initialization, or schedules cannot encode outside information. The target and imported theorem headers remain unproved data for this review. No original source, proof term, compiler, or independent acceptance procedure has been consulted.
