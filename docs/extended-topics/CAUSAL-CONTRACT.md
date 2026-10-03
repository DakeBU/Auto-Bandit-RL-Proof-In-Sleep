# Causal intervention learning: frozen representative contract

Frozen 2026-09-18. Status: source-qualified contract and mathematical derivation;
no causal-topic Lean endpoint, independent review or acceptance yet.

## Source and scope

Lattimore, Lattimore and Reid, *Causal Bandits: Learning Good Interventions via
Causal Inference*, NIPS 2016: general-graph Algorithm 2 and Theorem 3, uniform
allocation Proposition 4, optimal allocation, and its parallel-model bridge
(supplement Proposition 8; arXiv v1 Proposition 9). Exact files and hashes are
in `CAUSAL-SOURCE-AUDIT.md` and `causal-source-hashes.json`.

The representative line is general-graph, known intervention parent laws,
fixed-budget simple regret. Parallel Algorithm 1 and its unknown-marginal
Theorems 1–2 are separate background results, not substituted endpoints.
Unknown graph learning, latent confounding, cumulative regret and intervention
costs are outside this line. This does not exempt any of the ten topics.

## Primitive model and actual algorithm

Use a finite DAG with finite nonempty value types, a binary reward node Y,
and primitive conditional probability tables. Construct the full joint law
in topological order. An action replaces the tables of intervened non-reward
nodes with the specified point masses. Prove normalization and the truncated
factorization; do not assume arbitrary action-indexed distributions constitute
a causal graph. Marginalize to the reward parents Z and prove
P_a(Z=z,Y=1)=P_a(z) r(z), where the unchanged reward table r is common to all
actions. Reward observations are fresh and noisy. The learner knows P_a on Z,
but does not receive the unknown reward table.

Let A be finite nonempty, K=|A|, and T>=1. An allocation eta is a probability
vector on A. Define Q(z)=sum_a eta(a) P_a(z). Require coverage: P_a(z)>0 implies
Q(z)>0 for every a,z. Define R_a(z)=P_a(z)/Q(z) on positive Q and zero elsewhere.
Zero allocation weights are allowed when this mixture still covers every
action's support. Totalized division must not erase uncovered mass.

Define m(eta)=max_a sum_z P_a(z)^2/Q(z), with the zero convention only off the
union support. Prove 1<=m. Put L=log(2TK), B=sqrt(m T/L). Independently on each
round draw an actual action from eta, then fresh full feedback from that
action's interventional law. Derive the marginal iid (Z,Y) mixture law.
Compute muhat_a=T^(-1) sum_t Y_t R_a(Z_t) 1{R_a(Z_t)<=B}; choose an actual
maximizer with a fixed total-order tie rule. The recommendation must be
constructed from observed history, not supplied as a performance premise.

## Required performance chain

For W_a=Y R_a(Z)1{R_a<=B}, derive from the constructed laws:

1. 0<=W_a<=B and E_Q W_a^2<=m, hence Var(W_a)<=m.
2. E_Q W_a=mu_a-beta_a, with 0<=beta_a<=m/B.
3. Independent-sum Bernstein from primitive bounded variables gives the
   simultaneous error event with failure probability <=1/T and radius
   epsilon=sqrt(2mL/T)+3BL/T. No supplied tail or confidence premise.
4. On that event, argmax comparison gives
   mu_* - mu_I <= epsilon_*+epsilon_I+beta_*.
5. Integrate the actual recommendation regret, using its [0,1] range, to prove
   R_T <= (2 sqrt(2)+7) sqrt(m log(2TK)/T)+1/T, as well as R_T<=1.
   Derive the source O(sqrt(m log(2TK)/T)) endpoint with an explicit constant.

The coefficient and probability direction repairs are disclosed in the audit.
This is not a claim that the smaller printed coefficient is impossible.

## Allocation results are mandatory

Prove uniform allocation covers all supports and gives m<=K. Prove convexity
of m on the covered simplex and existence of an optimal covered allocation;
do not assume an optimizer or a solved design program. A possible existence
proof uses the compact m<=K sublevel set: its positive-coordinate lower
bounds keep Q away from zero on the finite union support, so the objective
is continuous there. This route remains a proof obligation.

For the parallel binary-root graph with N>=2 and the source m(q), prove the
rare-action count bound. Give each rare atomic intervention weight 1/(2m(q));
if their total is D<=1/2, give the empty intervention weight 1-D. Prove
normalization, coverage, and m(eta)<=2m(q), then transfer to the optimum.
Handle deterministic coordinates and zero parent probabilities explicitly.
The empty-action normalization is a source repair, not an unmarked formula
transcription.

## Frozen nondegenerate canaries

Use the observed DAG X->W, X->Y, W->Y with X~Bernoulli(1/2),
P(W=1|X=0)=1/4, P(W=1|X=1)=3/4 and
P(Y=1|X,W)=(1+X+2W)/5. A={empty, do(W=0), do(W=1)}. Derive the three
means 1/2, 3/10, 7/10 from the full table construction. In particular,
E[Y|W=1]=3/4 differs from E[Y|do(W=1)]=7/10.

Allocation eta(empty)=1 covers all four parent states despite two zero
action weights and gives m=8/3. At diagnostic truncation B=2, the biases for
do(W=0), do(W=1) are respectively 1/5, 3/10. For the actual tuned T=1
algorithm, 1<B<4/3; tie order empty first implies recommendation empty for
both possible rewards and expected simple regret 1/5. These are arithmetic
targets, not existing Lean theorems. Also construct an uncovered allocation
diagnostic, a repaired parallel-design witness, and an actual all-horizon
performance instantiation. Finite enumeration supports but never replaces
the symbolic producer and endpoint proofs.

## Acceptance

All producers, allocation results, canaries and endpoint must live in the
existing BanditRLProof library and public root. Acceptance requires independent
semantic review of the actual source-to-code chain, declaration audit, joint
root/Tests/full harness, shared registry/site checks, and the all-topic ICLR
reuse/transfer/failure evidence. No isolated project, supplied concentration
consumer or contract-only milestone closes this topic.
