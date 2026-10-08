# Source CONTRACT and separate proposed correction review

Verdict: **accepted-with-explicit-delta**, source/type stabilization only. All189 fixed RAW bindings independently match before/after. Reused distinct staged automated source reviewer, requested Astra/medium; no human/external/absolute-blind or runtime attestation.

Read pinned v10 printed2/4/6 texts. Cached PDF SHA matches cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. All three copied source PNGs were compared byte-for-byte to the images I personally viewed in the preceding FTL-limit source review. Those actual original-pixel views are explicitly reused, not claimed freshly rendered or freshly viewed here.

Source printed2 writes an ordinary lim while explaining at-most-sublinear fixed-comparator regret. Printed4 Theorem1.3 uses initialhalf then strict-past mean and proves a finite-horizon best-comparator upper bound. Printed6 discusses its sublinear guarantee and running summary. The four present targets are derived reconciliation results, not four printed theorems. The source bound is not contradicted by signed oscillating fixed-comparator regret.

## Per-target seven-slot audit

### D1 — BanditRL.OnlineLearning.meanPredict_limitNoRegret_iff_mean_converges

- objects: One unit observation stream, actual initial-half strict-past meanPredict, shared signed regret and literal LimitNoRegret
- quantifiers: For all y with all-time unit support: comparator-wise finite nonpositive limits iff there exists ONE feasible m with empiricalMean tending m
- assumptions: Only all-time y in closed unit interval; mean convergence is RHS conclusion, not additional premise
- metric: Exact ordinary-limit iff, not upper-epsilon iff or every comparator limit equal zero
- normalization: Natural prefixes t<T; totalized T0 has no asymptotic effect
- information_probability: Deterministic same causal predictor; limiting m is analysis-only
- boundary: Derived converse plus prior sufficiency; no universal bounded-stream convergence claim

Necessity can use actual u=0 and u=1 limits via prior fixedRegret_limit_iff: squared distances converge, their difference equals1-2mean. The recovered limit is in[0,1] by closedness and actual prefix feasibility. Sufficiency is prior conditional producer. No circular limit premise.

### D2 — BanditRL.OnlineLearning.dyadicObservation_unit

- objects: Complete fixed real-valued dyadicObservation recursion
- quantifiers: Every natural t
- assumptions: No support oracle; recursion alone
- metric: Pointwise membership in closed[0,1]
- normalization: d0=0; d(n+1)=1-d(floor(n/2)), not floor((n+1)/2)
- information_probability: Single exogenous horizon-independent deterministic sequence
- boundary: Feasibility producer; binary strengthening plausible but not claimed by header

Well-founded halved-predecessor recursion strictly decreases; strong induction gives values0/1 and hence unit membership. Whole definition including base and recursive index is fixed.

### D3 — BanditRL.OnlineLearning.dyadic_empiricalMean_subsequences

- objects: Same dyadic stream and two actual empirical-mean subsequences
- quantifiers: Conjunction of two atTop limits with no supplied convergence assumptions
- assumptions: Only fixed definitions
- metric: First horizon4^(n+1)-1 limit2/3; second2*4^n-1 limit1/3
- normalization: Natural subtraction; n0 horizons3 and1, positive and diverging; prefix excludes endpoint
- information_probability: Same infinite stream for both subsequences; no random/adaptive stopping
- boundary: Must produce prefix count and diverging subsequence maps; not assumed oscillation or numerical experiment

At horizon4^(n+1)-1, alternating binary-tree blocks give sum2*(4^(n+1)-1)/3 and mean exactly2/3. At2*4^n-1, sum2*(4^n-1)/3 gives limit1/3. These are reviewer mathematical checks, not compiled theorem bodies.

### D4 — BanditRL.OnlineLearning.dyadic_meanPredict_obstruction

- objects: Same unit dyadic stream, actual FTL, upper NoRegret, feasible-best and fixed-zero regrets
- quantifiers: Closed four-part conjunction; no real a gives a fixed-zero ordinary limit; upper condition forall feasible u/epsilon with dependent threshold
- assumptions: None externally: support/upper/best limit must be derived
- metric: Upper NoRegret AND best/T tends0 AND no finite-real fixed-zero limit AND not literal LimitNoRegret
- normalization: Signed regret/natural horizon; T0 totalized; subsequence limits would be -4/9 and -1/9
- information_probability: Deterministic actual initial-half strict-past learner, no future/mean input
- boundary: Counterexample to ordinary-limit existence inference, not to source logarithmic upper bound; no stochastic/minimax/all-algorithm conclusion

Prior unit-stream upper guarantee and best-average limit apply after D2. F4 criterion at u0 turns an assumed fixed-regret limit into a square-mean limit; D3 yields distinct4/9 and1/9, contradiction. Thus literal failure follows at feasible0 without assuming its sign.

## Complete definition and reconstruction

The owned dyadic definition fixes d0=0 and d(n+1)=1-d(n/2) with natural floor division and explicit termination. Initial blocks are0;1,1;four0s;eight1s. This is one all-time exogenous sequence, not a horizon-selected witness. The neutral decoder reconstructs all four Props with these exact horizons and signed quantifiers. Its output is reconstruction, not source acceptance. Actual draft/proposition probes only elaborate types; they do not prove any new terminal. No consumer assumes the desired regret, support, mean convergence or nonexistence conclusions.

## Separate proposed source-correction verdict

Accepted-with-explicit-delta as a PROPOSAL and contract for future verification. Eventual comparator-wise upper-epsilon (equivalently limsup≤0 in the appropriate extended-real sense) does not require ordinary-limit existence. The pinned lim display and literal LimitNoRegret stay preserved. For this specific squared FTL, an explicit empirical-mean convergence hypothesis restores the literal statement; D1 aims to prove it necessary as well. The proposal itself expressly requires the concrete obstruction and iff to be proved and separately reviewed first. No source-wide algorithm claim or current theorem-body acceptance follows.

## Future reader obligations

R1 — mandatory future, not discharged: Pinned source ordinary-lim display, existing upper NoRegret and proposed correction remain separate; four DERIVED terminals, not four printed results.

R2 — mandatory future, not discharged: Same actual initial-half strict-past meanPredict; one fixed all-time observation stream, no horizon/future/mean algorithm oracle.

R3 — mandatory future, not discharged: D1 exact iff for all unit comparators versus existence of one convergent empirical mean inunit; necessity uses actual comparator0/1 limits, not a convergence premise.

R4 — mandatory future, not discharged: D2 explicit binary well-founded dyadic recursion and D3 two empirical-mean subsequences with distinct2/3 and1/3 limits; exact prefix counts and subsequence divergence produced, not assumed.

R5 — mandatory future, not discharged: D4 same bounded source-FTL pathwise upper NoRegret and best/T0 together with nonexistence of any ordinary real limit at the fixed comparator0 and failure of literal all-comparator LimitNoRegret. Signed negative subsequence limits allowed; no stochastic/minimax claim.

R6 — mandatory future, not discharged: All four public endpoints instantiated by nondegenerate exact finite-prefix public canaries; focused/rootTests/harness/axioms/fences/nonempty committed-HEAD contributor/site/registry/pixels/semantic gates separately recorded.

R7 — mandatory future, not discharged: Only four derived obligations may close; original16/null/historical overlays and other required C1C2/C3-16/appendices remain. Full Chapter1 reconciliation/gate still required; GoalACTIVE, PR201stackedunmerged, main/live unchanged.

## Exact future scope and remaining boundary

Approve only the unchanged contract-mutable-scope-v1.json copied into the receipt: frozen four headers and complete context, scoped production/proof helpers, canary contract review before canary bodies, own task appendices/evidence/native records. Terminal edits require a new contract review; root/reader/registry/contribution integration requires separate BODY review. No such edits or native actions were performed by this reviewer.

No blocking mathematical or metadata repair found. Actual bodies, independent canary review, kernel/combined/site/pixels/FINAL/native/delivery remain pending. Only four derived obligations are in scope. Original16 source objects/null unknown proof total, other required C1/C2/C3–16 and appendices remain required; Goal ACTIVE, PR201 unmerged. This does not close the whole Chapter1 reconciliation or book.
