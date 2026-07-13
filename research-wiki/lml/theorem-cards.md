# LML Theorem Cards

Source: [LeanMachineLearning/LML](https://github.com/LeanMachineLearning/LML)

Seed commit: `19dc3ab132c2a7539f5944503d1114eac4c5bb74` (2026-06-24).

Status rule: every entry below is a theorem card until ABRL imports or ports
the declaration and passes the local Lean gate.

| Card id | LML declaration | Module | ABRL use | Status |
| --- | --- | --- | --- | --- |
| `LML-BANDIT-REGRET-GAP` | `Bandits.regret_eq_sum_gap` | `LeanMachineLearning.Online.Bandit.Regret` | regret as sum of gaps | theorem-card |
| `LML-BANDIT-REGRET-PULLCOUNT` | `Bandits.regret_eq_sum_pullCount_mul_gap` | `LeanMachineLearning.Online.Bandit.Regret` | pull-count regret decomposition | theorem-card |
| `LML-ETC-REGRET` | `Bandits.ETC.regret_le` | `LeanMachineLearning.Online.Bandit.Algorithms.ETC` | Explore-Then-Commit expected regret | theorem-card |
| `LML-UCB-REGRET` | `Bandits.UCB.regret_le` | `LeanMachineLearning.Online.Bandit.Algorithms.UCB` | UCB logarithmic regret route | theorem-card |
| `LML-TS-POSTERIOR-ACTION` | `Bandits.TS.hasCondDistrib_action` | `LeanMachineLearning.Online.Bandit.Algorithms.TS` | posterior best-action identity | theorem-card |
| `LML-TS-BAYES-REGRET` | `Bandits.integral_regret_le` | `LeanMachineLearning.Online.Bandit.Algorithms.Regret.BayesRegretTS` | Bayesian regret upper bound | theorem-card |

## LML-ETC-REGRET Exact Seed Contract

At seed `19dc3ab132c2a7539f5944503d1114eac4c5bb74`, the upstream theorem is:

```lean
theorem Bandits.ETC.regret_le
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R (etcAlgorithm hK m) (stationaryEnv nu) P)
    (hnu : forall a, HasSubgaussianMGF
      (fun x => x - (nu a)[id]) sigma2 (nu a))
    (hm : Not (m = 0)) (n : Nat) (hn : K * m <= n) :
    P[regret nu A n] <=
      Finset.univ.sum (fun a => gap nu a *
        (m + (n - K * m) *
          Real.exp (-(m : Real) * gap nu a ^ 2 / (4 * sigma2))))
```

Implicitly, `nu : Kernel (Fin K) Real` is Markov, `P` is a probability
measure, and `A`/`R` are an arbitrary action/reward process satisfying the
algorithm-environment sequence contract. The proof uses a per-arm expected
pull-count bound and then sums by arm gaps.

Current exact LML theorem status remains `card-only`; ABRL does not import LML.
The local route now compiles the native Real concentration, exact per-arm
expected-count producer, stationary-kernel gap identities, complete finite-sum
regret bound, finite exploration-prefix transport, and scheduled
initial/successor conditional-law transport. The action-dependent source
adapter
`ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_actionDependent_actionRewardHistory_condDistrib`
also accepts the upstream-shaped selected feedback laws and maps them to that
native Real exact theorem. The downstream least-encoded action endpoint also
proves the local fold equals the `Nat.find` least-`Encodable.encode` selector
and assembles round-robin exploration, commit, and persistence, so no caller-
supplied horizon action equality remains. The downstream history-score adapter
also mirrors `pullCount'`/`sumRewards'`/`empMean'`, proves the finite-history
score equality, and accepts the history-shaped commit law directly. It adds no
`StandardBorelSpace Omega`, full trajectory-law equality, independence
assumption, or stronger infinite-horizon premise. The local
`ETC.RealStationaryETCSequence` bundle and
`ETC.regret_le_of_realStationaryETCSequence` theorem now compile the faithful
field-consumer surface. Remaining direct-port work is only an import over the
actual LML `measurableArgmax`/`IsAlgEnvSeq` symbols.

Seed-source audit of `IsAlgEnvSeq` records the exact feedback fields used by
this route: reward zero has `HasCondDistrib` given action zero with `env.ν0`,
and reward `n+1` has `HasCondDistrib` given `(history A R n, A (n+1))` with
`env.feedback n`. For `stationaryEnv nu`, the feedback kernel is action-
dependent; `ETC.arm_of_lt` makes the exploration action a.e. constant. ABRL's
compiled native Real source adapter now matches these conditioning variables.
It reduces the action-dependent kernel to the scheduled-arm constant kernel via
`RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected` and the action-
dependent full-history ETC endpoints for both max-gap and per-arm RHSs. A
direct LML wrapper remains optional
because the seed uses a newer toolchain and `HasCondDistrib`. Canonical
common-sub-Gaussian concentration, exact per-arm counts, cast-pushforward Real
kernel gaps, native Real stationary-kernel regret, conditional-law source
transport, least-encoded tie semantics, three-piece action assembly,
source-shaped history-score mapping, local faithful field bundling, and finite-
sum regret now compile. The remaining mismatch to `Bandits.ETC.regret_le` is
strictly symbol/toolchain-level: the actual upstream declarations are not
imported. ABRL uses Lean/mathlib `v4.29.1`; the pinned LML checkout uses Lean
`v4.32.0-rc1` and mathlib commit
`9ca31d8b72cf8c317e49c301bfdbfbe91fc49136`.

## Migration Notes

- LML currently uses a newer Lean toolchain than ABRL's dependency-light core.
- Do not add LML as a dependency without a task-level decision and build test.
- For small local ports, copy the theorem statement manually, attribute LML,
  and reprove or adapt the proof under ABRL's gate.
- For direct import, update `lakefile`, `lean-toolchain`, `NOTICE.md`, and the
  conversion window in the same change.

## Local Per-Arm RHS Progress

The generic per-arm Bochner assembly now compiles as
`ETC.integral_real_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_sum_gap_mul_commit_prob`.
This matches the structural gap-weighted armwise shape of the upstream ETC
conclusion without claiming source equivalence. The local ABRL route now also
has a canonical bounded-Rat armwise commit-probability bound, its finite Real
conversion, a canonical per-arm Bochner endpoint, and transport of that
integral to any external law with the same exploration-prefix pushforward.
The local ABRL route now also derives that prefix identity from a time-zero
marginal plus successor `condDistrib` laws and returns the per-arm conclusion
on the original sample space. Scheduled-arm and action-dependent full-history
conditional laws now compile for this RHS. The local
`RealMeanRegretPullCount` and `RealKernelRegretPullCount` modules now compile
the LML-aligned Real scalar and stationary-kernel gap/regret expected
pull-count decompositions. `ETCExpectedPullCount` now additionally compiles the
exact pathwise-count/indicator-integration endpoint and turns any Real
`P(commit=a)` bound into the LML-shaped `m + (n-K*m) * p` expected-count bound.
`ETCExactSubGaussianTail` now compiles the exact common-proxy exponent and its
canonical Rat-arm-law commit-fiber and per-arm expected-count endpoints. It
proves the proxy sum `2*m*sigma2`, rewrites the non-best threshold as `m*gap`,
and obtains `exp (-m*gap^2/(4*sigma2))`, including the zero-proxy boundary.
`ETCRatArmLawRealKernel` pushes those arm laws to a Markov Real kernel and
assembles the cast-model exact sum. The subsequent native Real modules compile
direct Real empirical means and argmax measurability, product-law
concentration, exact counts/regret, finite-prefix transport, and extraction of
the scheduled laws from upstream-shaped selected feedback kernels. The least-
encoded and history-score leaves prove the strict fold is the least-encode
Nat.find argmax, combine exploration/commit/persistence, and align the upstream
finite-history score. The newest compatibility leaf bundles the exact
`IsAlgEnvSeq` consequences and returns the exact sum. Only direct import and
symbol identity across the audited toolchain mismatch remain.

## LML-UCB-REGRET Exact Seed Contract

At pinned commit `19dc3ab132c2a7539f5944503d1114eac4c5bb74`, the upstream
theorem has the stationary Real-kernel form:

```lean
theorem Bandits.UCB.regret_le
    [Nonempty (Fin K)]
    (h : IsAlgEnvSeq A R
      (ucbAlgorithm hK (c * sigma2)) (stationaryEnv nu) P)
    (hnu : forall a, HasSubgaussianMGF
      (fun x => x - (nu a)[id]) sigma2 (nu a))
    (hsigma2 : Not (sigma2 = 0)) (hc : 0 < c) (n : Nat) :
    P[regret nu A n] <=
      Finset.univ.sum (fun a =>
        8 * c * sigma2 * log (n + 1) / gap nu a +
          gap nu a * (2 + 2 * (constSum c n).toReal))
```

The source defines `ucbWidth'` on inclusive finite histories with denominator
`pullCount'` and logarithm `n+2`, and `ucbWidth` on traces with denominator
`pullCount` and logarithm `n+1`. The action is a round-robin initializer followed
by `measurableArgmax (empMean' + ucbWidth')`.

ABRL's `UCB-NATIVE-REAL-HISTORY-INDEX` leaf now ports these score definitions,
the inclusive-history/trace offset, least-encoded maximization, and
measurability. LML remains theorem-card evidence, not an imported dependency.

The upstream one-sided tail proof does not assign a deterministic variance
proxy to the random empirical mean. It invokes
`prob_pullCount_prod_sumRewards_mem_le` to partition the adaptive
`(pullCount,sumRewards)` event by fixed sample count and transport each fiber
to a fixed arm-reward sum under `streamMeasure`; only then does it apply the
sub-Gaussian sum tail.

ABRL's `UCB-FIXED-COUNT-PEELING-LAW` leaf now ports that generic event and law
transport under an explicit `FixedArmPrefixSource`: selected rewards must be
the prefix of a measurable latent arm stream at the realized pull count, and
one complete-stream `IdentDistrib` law supplies all fixed-count laws. This is a
local theorem, not an imported LML declaration. The remaining source-specific
blocker is constructing that prefix source and canonical stationary/product
stream law for the actual generated UCB process (or proving an equivalent
conditional-MGF route), then specializing the fixed-sum tails. The older ABRL
deterministic `proxy : Nat -> Arm -> NNReal` surface is useful abstract
confidence algebra but is not definitionally the source UCB width.
