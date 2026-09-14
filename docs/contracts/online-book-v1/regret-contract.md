# Regret semantics v1

Source p2: comparator regret is difference of cumulative losses. Comparator is not an input to prediction. NoRegret uses the precise eventual upper-sublinear formulation (limsup average <=0), without requiring regret nonnegativity or a limit to exist. When the displayed source limit exists this agrees with its <=0 condition. This is an explicit formal interpretation of upper sublinearity, not a claim that all regret sequences converge. Empty horizon definition gives zero; division at zero is irrelevant to atTop.

The generic vanishing-bound lemma is an adapter, not the actual FTL regret theorem, which has already been proved separately. Concrete FTL asymptotic instantiation remains required. Edit scope is this new module and evidence; existing theorem contracts unchanged.
