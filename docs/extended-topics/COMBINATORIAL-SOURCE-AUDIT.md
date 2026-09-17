# Combinatorial bandits: source audit in progress

Follow-up: the full triggered CUCB contract is now frozen in CUCB-CONTRACT.md (81a1998). A normalized analysis-charge repair is under implementation; this historical audit records the evidence leading to that decision. It is not independent acceptance.

Date: 2026-09-17. This is a source-selection and proof-obligation audit, **not a frozen contract, Lean implementation, or accepted topic**. All ten topics remain mandatory; accepted topics remain 0/10. The current CUCB candidate must not be presented as a full-bandit result.

## Version fence

| Source | Exact primary artifact | SHA256 |
| --- | --- | --- |
| Chen, Wang, Yuan, ICML 2013 | [main PDF](https://proceedings.mlr.press/v28/chen13a.pdf) | `7e554c1320dea2c05b6606430e0337ec7dd226bd90c230d3ca0fee4e057ed40c` |
| Same paper, complete supplementary file | [supplement](https://proceedings.mlr.press/v28/chen13a-supp.pdf) | `be1ca019cd6b8d2a488d646add31ce180c048427c4174b176b00c830d479751d` |
| Chen, Wang, Yuan, Wang, JMLR 2016 | [journal PDF](https://jmlr.org/papers/volume17/14-298/14-298.pdf) | `6a29fc188cd1490c53864eb4f839e572551c171388fc27ba256a7e61424e856c` |
| Ye, Wang, Liu, Li, CMOSS | [arXiv 2508.06247v2](https://arxiv.org/pdf/2508.06247v2), 2025-12-28 | `951b7fcc133295f7ac22c3f0346b65b5b1c792fe1fe6236a48f1b9d77d0b82d7` |

Reading depth: the 2013 model, algorithm, Theorems 1/2, main coarse proof and supplementary Section A proofs were read. Supplementary extensions and application proofs were not fully audited. The 2016 model, Algorithm 1 and Section 3.1 proofs of Theorems 1/2 were read; remaining applications were not fully audited. CMOSS model, algorithm, theorem statement and start of semi-bandit analysis were read; its full proof is **not audited**. Rendered original pages checked: 2013 supplement pp. 5–6 and 2016 pp. 22, 24. Reading is not independent semantic acceptance.

## Scope distinction that affects the contract

The JMLR extension explicitly corrects the earlier influence-maximization application: probabilistic triggering requires additional modeling and analysis (2016, p. 4). The two versions also differ in initialization: 2013 plays an arm-covering initialization schedule; 2016 starts all counts at zero and uses clipped optimistic indices. Do not mix those algorithms or claim the 2013 no-trigger bound for general triggered feedback.

The representative candidate remains **CUCB with a general feasible super-arm family, a randomized approximation oracle, and nonlinear mean-based rewards**. Both the refined gap-dependent integral bound and the polynomial-smoothness distribution-independent bound are under consideration. The coarse global-minimum-gap bound alone would not close this candidate. The choice between the original direct-observation model and the extended triggering model is not yet frozen. Selection must state its mathematical scope rather than silently omit triggering assumptions.

CMOSS v2 Section 3.2 uses linear reward and the family of all subsets of cardinality at most k, hence a top-k selection problem. It is useful recent context, not a substitute for a general constrained family with an approximate oracle. Its logarithmic factors have boundary cases k=1 and m-k=1 requiring verification before quoting an all-parameter guarantee. This is a scope/boundary question, not a claimed refutation of the paper. Do not mix v1 search snippets with v2.

## Verified proof details and repairs

1. **Integer counting (2013 supplement, pp. 4–5).** The prose bounds the number of integers in a real interval by its length, which is false in general: (1.8, 2.1] contains one integer but has length 0.3. This does **not** refute the displayed weighted aggregate in Eq. (27). A correct floor-and-summation argument proves that aggregate. The 2016 paper already supplies this argument in Eqs. (30)–(31), p. 22; it is not a new ABRL discovery.
2. **Gap index (2013 supplement, p. 6).** The printed Case (2) selects the first gap greater than the cutoff and immediately uses the opposite inequality. The 2016 p. 24 definition uses the first gap at most the cutoff. Preserve the corrected order and existence argument, or avoid this index entirely using the pathwise envelope below.
3. **Hoeffding premises.** The isolated 2013 supplementary lemma omits independence. Its intended per-arm sampling context supplies iid observations; the 2016 Fact 1 states this explicitly. A reusable Lean theorem must carry the actual independence/conditional-MGF producer.
4. **Oracle success.** The input is adaptive. An oracle kernel must meet its success guarantee for every input, with fresh oracle randomness, so the unconditional failure bound follows by integration. An asserted per-round failure estimate is not the algorithm construction.
5. **Adaptive feedback.** Fresh round outcomes may have within-round dependence. The selected-arm observation count is random; a fixed-size concentration theorem cannot simply be applied conditional on that count. Derive the concentration event for the actual policy, retaining the observation mask and filtration.
6. **Inverse domain.** Strict increase alone is not surjectivity onto every positive gap. A freeze must specify the domain and range of f and prove that each inverse argument is in range, or label an explicit strengthening. The journal adds continuity and f(0)=0; it does not justify an arbitrary total inverse on all positive reals by itself.
7. **Empty families and horizon.** Define zero contributions for arms in no bad super-arm, handle no bad actions, state arm coverage for the 2013 initialization, and separately account for horizons within initialization. Do not silently define a minimum of an empty positive-gap set.
8. **Actual reward.** Approximation regret uses the signed comparator n alpha beta opt minus expected reward. Prove the actual-to-mean reward identity from the constructed round law. Nonnegative reward is needed for the oracle-failure cancellation; replacing this comparator by a positive-part gap is not an equality.

### A pathwise proof of the weighted count bound

This derivation is ordinary mathematical work, not yet Lean-checked. It also explains why the incorrect interval-length prose need not change the final constant.

Let d1 >= ... >= dK > 0 and 0=L0 <= L1 <= ... <= LK, with Lj = ell(dj). For one arm, each positive pre-increment counter q is charged at most once. If an under-sampled charge has gap dl and q <= Ll, place q in the unique nonempty interval (L(j-1), Lj]. Then j <= l and dl <= dj. Thus its total cost is at most

    sum_j (floor(Lj) - floor(L(j-1))) dj
      = floor(LK) dK + sum_{j<K} floor(Lj) (dj-d(j+1))
      <= LK dK + sum_{j<K} Lj (dj-d(j+1)).

All coefficients of the floors in the middle expression are nonnegative. This is an aggregate argument, not a termwise replacement of each floor difference by a real difference. If ell is decreasing, each Lj (dj-d(j+1)) is bounded by the integral of ell over [d(j+1),dj]. This yields the refined integral bound without rounding loss. Repeated gaps give empty intervals and zero differences, so strict sorting is unnecessary. A counter starting at zero adds at most d1 for its unique zero charge; the 2013 counter starts at one after separately charged initialization.

### A direct pathwise route to the polynomial endpoint

For ell(d) = 6 log(n) (gamma/d)^(2/omega), set a=omega/2 in (0,1/2]. An under-sampled positive counter q obeys

    d <= gamma (6 log(n))^a q^(-a).

For a terminal counter N, positive charged counters are distinct members of {1,...,N-1}. Monotonicity gives

    sum_{q=1}^{N-1} q^(-a) <= integral_0^N x^(-a) dx
                            = N^(1-a)/(1-a).

The singular integral is finite because a<1; N=0 is treated separately. Hence the arm's under-sampled cost is at most

    (2 gamma/(2-omega)) (6 log(n))^(omega/2) N^(1-omega/2),

plus its zero-counter charge if that initialization convention is used. Applying finite concavity to the terminal counters, whose sum is at most n, gives the source coefficient

    (2 gamma/(2-omega)) (6 m log(n))^(omega/2) n^(1-omega/2).

This holds pathwise, so it needs no conditioning on a possibly null event of prescribed terminal counters. It still requires the full statistical bound for sufficiently sampled bad rounds, the signed-regret decomposition and oracle cancellation; it is not an algorithm-performance theorem by itself.

## Journal triggering proof: additional unresolved audit item

In the 2016 Lemma 4 proof, p. 18, the claimed equality ell_n(d,pi) pi / ps = ell_n(d,ps) must be checked against the piecewise threshold when pi=1 but ps<1. The deterministic branch has coefficient 6 while the probabilistic branch has a max with coefficients 12 and 24. That equality is not a general algebraic identity across the branches. This observation concerns an intermediate proof step; no counterexample to the final regret theorem has been established. Before adopting the full triggering endpoint, resolve this step, including whether the counter selection or subsequent event bound needs a different argument. Do not add the step as a hypothesis or weaken the final bound without disclosure.

## Remaining before implementation

- Resolve the source model/version choice and inverse-domain contract, then freeze exact algorithm, endpoints and every required producer.
- Complete the relevant recent-source comparison without upgrading abstract screening to full proof review.
- Build the actual reward/feedback/oracle trajectory and adaptive concentration; prove both refined counting and terminal bounds.
- Include a genuinely combinatorial, noisy, non-singleton canary; a scalar UCB wrapper is insufficient.
- After implementation: combined root, Tests, full harness, axiom/semantic review, shared mappings and all-topic evidence. No combinatorial Lean gate was run for this documentation-only audit.
