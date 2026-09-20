# Actual intervention sampling and concentration bridge

Target: the repeated-sampling part of Algorithm 2 / Theorem 3 in the frozen
2016 causal contract. This is a required producer, not the simple-regret endpoint.

Each round first draws an intervention label from the covered allocation and
then draws the complete assignment from the already constructed intervened DAG
law. A finite product measure over these actual rounds gives a fixed-budget
history. Projection to reward parents and the binary reward must recover the
mixture paired law proved in CausalImportance, rather than postulating iid
reward-parent observations. Weighted truncation is a function of that projection
and the known parent laws, not of the unknown reward table.

Reuse decision: adapt_existing. Reuse GraphModel.mixture_parent_joint,
weightedBit_mean/second_le/bounds, designCost, Mathlib's finite product measure,
measurePreserving_eval and iIndepFun_pi. For concentration reuse
HeavyTail.bounded_centering_mgf and independent_sum_mgf. No new generic
probability library or dependency update is intended.

Owning modules: CausalSampling and the subsequent Causal concentration module.
Expected consumers are the tuned source confidence producer and actual
recommendation regret. Finite product factorization supplies independence;
integral transport supplies the moments required by the shared MGF interface.
The fixed tilt 1/(2B) and full tuning are recorded in
CAUSAL-CONCENTRATION-ROUTE.md and remain required.

Publication: add the exact sampling/interface statements with the actual proof
once compiled, update the producer ledger, and retain topic_complete=false.
Lean Graph gains actual producer edges. Overview gains partial causal progress.
Functor Hypergraph has no new certified transport claim. Shared topic mapping
and whole-topic acceptance wait for the complete performance chain.

Semantic plan: distinct blind reconstruction of the compiled sampling/producer
interface, followed by source/repair review against the frozen contract. The
source reviewer independently checks tuning and regret assembly while this
producer is implemented. Compilation alone will not close the source contract.

2026-09-20 scope repair: the initial all-Bool candidate was superseded after
independent source review. Sampling, MGF, confidence and recommendation now use
`GraphModel V n` for arbitrary finite inhabited `V`, with `rewardBit : V → Bool`.
The full assignment remains V-valued; only the observed reward is projected.
The reward kernel in moment proofs is the pushforward of the node table. These
modules pass focused builds, including the actual reward integral identity and
the pathwise recommendation bound. This is a common finite alphabet model;
no heterogeneous-domain transport theorem is claimed yet.

Next route: integrate the pathwise bound with the bad-event indicator under the
actual product law, using regret in [0,1], the proved probability bound 1/T,
and `integral_indicator_one`. Retain the residual 1/T. Simplify the source
tuning to coefficient 2*sqrt(2)+7; do not copy the smaller printed coefficient
or absorb 1/T using the false universal inequality 1/T <= sqrt(m*L/T).
The prior Bool-only review hashes are historical and do not accept this packet.

The seven-module packet now additionally proves the actual expected-regret
bound with residual, its cap by one, the explicit constant 3*sqrt(2)+7 rate,
and actual-law uniform/optimal allocation corollaries. Focused build:
`lake build BanditRLProof.Algorithms.CausalAllocationRegret`, 3602 jobs.
Independent blind reconstruction SHA256
48438a0333a3d120e9fef12fe9c7396071e846bc19928f57a24164163eb3fb06 and
source-semantic review SHA256
cb4abe279e0227ba10d7638f43fa774c2f3f7275230b9c5698605f4385c11bc9 bind
the seven module hashes. Verdict: accepted-with-explicit-delta for the common
finite alphabet chain, partial relative to the frozen contract. These reviews
do not accept a heterogeneous-domain transport, parallel design or canary.

`Tests/CausalNoisyGraphCanary.lean` constructs the frozen noisy three-node DAG,
proves actual joint factorization, derives means 1/2, 3/10, 7/10 from the actual
reward integrals, and instantiates the uniform all-horizon bound. Focused build
3603 jobs and printed axiom checks pass. Its separate semantic review is pending.
Concentrated allocation m=8/3, biases, conditional-observational distinction,
the tuned T=1 exact regret, uncovered diagnostic and parallel witness remain
open. Shared root/Tests integration is now being checked; no global acceptance,
main merge, site deployment or ICLR evidence completion is claimed.

Validation update: separate partial-canary source review accepted the exact
joint law, means and uniform instance (report SHA256
e4f22b8310a9db2b917bd8d786ee2e535b893bb6bd34fcb3fe1f758d6cdd4a51).
Shared root 9024 jobs and Tests 9124 jobs passed. Full harness rerun passed
437 Python tests with 7 skips in 153.828 seconds. The initial packaging error
was caused by new untracked Lean files; tracking those files fixed it.
The local site builds with a fresh Lean gate and passes its checker. Twelve
production declaration links are bound to reviewed hashes; their scope has
20 nodes and 22 edges, with all generated destinations verified. Test-only
declarations remain in Tests and the reader, outside the public declaration
registry. The production/review and validation JSON receipts are in
`runs/extended-topics-20260919/causal-sampling-{review,validation}.json`.
The research worktree remains active. All frozen gaps listed above remain
mandatory; this is neither causal-topic completion nor all-ten-topic completion.
