# Read-only next-source dependency audit

After Example2.15, required source Definition2.16 and Examples2.17/2.19 concern extended-real closedness and properness. Existing shared OnlineConvexExtended.extendedIndicator is the exact zero-on-set/top-outside function; reuse it, not ordinary Set.indicator.

Pinned mathlib Topology/Semicontinuity/Basic.lean provides lowerSemicontinuous_iff_isClosed_preimage (line196) and lowerSemicontinuous_iff_isOpen_preimage (line174). Their thresholds range over the entire codomain. The source closedness definition only quantifies real thresholds for an EReal-valued function. Directly renaming the mathlib property without proving finite-cut equivalence would miss a semantic obligation, especially the bottom sublevel. EReal.exists_between_coe_real (Data/EReal/Basic.lean423) supports writing the open superlevel above bottom as a union of real-threshold superlevels; top superlevel is empty. No properness or no-bottom assumption belongs in this equivalence.

Definition2.18 then introduces properness separately: nowhere bottom and finite somewhere. For extendedIndicator, this should be equivalent to nonempty feasible set. This is read-only retrieval and intended DAG only, not a frozen Lean terminal or a completed source result. Huber acceptance/current-main integration comes first.
