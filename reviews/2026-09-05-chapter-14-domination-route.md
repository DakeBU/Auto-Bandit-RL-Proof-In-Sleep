# Common domination and finite-alphabet KL

Source author pp.188-189: finite KL iff atom support is compatible on a finite
alphabet, and P+Q is a common sigma-finite dominating measure for probability
laws. Existing finite_eq_top_iff already proves the complementary endpoint
claim. Expose its exact less-than-infinity/AC form as a source adapter.
For domination, addition has zero mass only when both summands have zero
mass; the sum of finite measures is finite, hence sigma-finite. Preserve the
finite alphabet condition, which cannot be dropped from AC iff finite KL.

Focused result: CommonDomination builds (2672 jobs). The finite dominating
measure is explicitly P+Q; the sigma-finite corollary derives its instance
from finiteness. The KL iff is a thin adapter of the already proved finite
atom-support dichotomy, not a second analytic proof. UniformCoding and
CommonDomination are now aggregate-imported with canaries, but are outside
the running d325147 full gate.

Typed probability-law canary passed; all three axiom audits contain only
propext/Classical.choice/Quot.sound. Retrieval/task memory/blueprint refreshed.
