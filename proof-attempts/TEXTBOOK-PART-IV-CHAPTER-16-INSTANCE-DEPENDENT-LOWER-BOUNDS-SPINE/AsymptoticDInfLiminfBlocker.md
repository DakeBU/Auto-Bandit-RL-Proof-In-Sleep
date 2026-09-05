# Chapter 16 asymptotic d_inf-to-liminf blocker

Resolution on 2026-09-05: the exact per-arm
`consistentPolicy_liminf_expectedPull_div_log_ge_inv_dInf` and regret
`consistentPolicy_liminf_expectedRegret_div_log_ge` terminals now pass the
3584-job focused build. The source class is an arbitrary unstructured
finite-mean probability-law product class; consistency uses exact `n`-pull
regret. `ENNReal.inv_sInf` retains all information branches, and finite-count
Fatou proves the final sum direction. Historical blocker notes below record
the development route. Final canary, source audit, full gates, and artifact
synchronization remain required before completion.

Task: `TEXTBOOK-PART-IV-CHAPTER-16-INSTANCE-DEPENDENT-LOWER-BOUNDS-SPINE`

## Compiled frontier

The finite-mean environment producer, exact Lemma 16.3, and exact Gaussian
Theorem 16.4 compile. The remaining source terminal is Theorem 16.2.

## Exact unresolved seam

Environment producer route (2026-09-05): use
`Kernel.ofFunOfCountable` on a single-arm conditional law, with the original
probability and integrability certificates on unchanged arms and explicit
probability/integrability certificates for the alternative. Set its mean to
the actual integral and its best arm to the changed arm. Strict improvement
over the original optimum proves optimality. Componentwise class membership
then proves closure in the source unstructured product class. This is a
project-local source wrapper, with no new Mathlib dependency.

This route now compiles: `withImprovedArm`, `withImprovedArm_mem`,
`withImprovedArm_unique`, and `exists_confusingEnvironment_lt` on
`FiniteMeanBanditEnvironment` passed the 3584-job target build. The last
theorem supplies a class member, unchanged other arms, a unique best changed
arm, and directed KL below the chosen strict upper bound. The remaining seam
starts at consistency-to-per-arm asymptotics, not at alternative construction.

Progress on 2026-09-05: `divergenceInfimum_exists_alternative_lt` now
constructs a confusing alternative below every strict extended-real upper
bound on `d_inf`. `divergenceInfimum_eq_top_iff` characterizes the infinite
branch, including emptiness and nonempty all-infinite classes. Both passed
direct Lean source checking. The proof uses `le_sInf`,
`divergenceInfimum_le`, and order contradiction; it assumes neither an
attained infimum nor finite positive information cost.

For each suboptimal arm, the compiled producer now constructs alternatives in
the unstructured component class with mean strictly above the original optimum
and KL below each strict upper bound on `d_inf`. The proof must combine Lemma 16.3 with
consistency of both environments, divide by `log n`, and take a `liminf`.

The formal statement must keep `d_inf : ENNReal` throughout. Four cases stay
explicit:

- an empty confusing-alternative set, hence `d_inf = infinity`;
- zero information cost;
- finite positive information cost;
- infinite information cost not arising solely from emptiness.

After the per-arm result, the proof must pass from the finite sum of
gap-times-pull-count ratios to the regret `liminf` without assuming convergence
or exchanging `liminf` and a sum in the wrong direction.

## Pivot rule

Finite-sum route: `lintegral_liminf_le` on `Measure.count` over `Fin K`,
rewritten with `lintegral_count` and `tsum_fintype`, gives the required sum
inequality. `ENNReal.le_liminf_mul` handles each constant nonnegative gap.
The exact horizon regret decomposition and `ofReal_sum_of_nonneg` identify
the resulting sum with normalized regret for all `n > 1`.

Information aggregation API found: `ENNReal.inv_sInf` expresses the inverse
infimum as the supremum of inverses of all alternative costs. Apply each
per-alternative bound via `iSup_le`. Infinite costs contribute zero; zero
individual KL is excluded by different finite means, while a zero infimum
still yields an infinite supremum. The empty-class supremum is zero. This
is an exact complete-lattice route retaining every source branch.

Horizon route (2026-09-05): define expected regret and pull count after exactly
`n` pulls by zero at `n = 0` and the existing inclusive history at `n = m+1`.
Instantiate consistency directly on these source sequences. For positive
finite arm KL, obtain positive total regret from the compiled majority-event
producer and use Lemma 16.3 at `m`; the analytic liminf leaf then applies
without shifting its consistency hypothesis or dropping the zero horizon.

Consistency extraction route (2026-09-05): reuse
`IsConsistentRegret.eventually_log_add_div_log_le`. For each real
`r < 1 / d`, choose `p = (1 - r*d)/2 > 0`; the source logarithmic lower
bound divided by `log n` eventually dominates `r`, since the constant term
divided by `log n` tends to zero. APIs: `Real.tendsto_log_atTop`,
`tendsto_natCast_atTop_atTop`, `Tendsto.div_atTop`, eventual strict bounds,
and positive-denominator division. Keep this as a source-specific analytic
leaf, then lift its eventual bounds to the extended-real liminf.

Both analytic leaves now pass the focused build:
`IsConsistentRegret.eventually_pull_div_log_ge` and
`IsConsistentRegret.liminf_pull_div_log_ge`. The latter uses `ENNReal.ofReal`
and permits infinite liminf. They consume the eventual source logarithmic
inequality, rather than assuming a per-arm liminf conclusion. Remaining:
instantiate with the actual environment regret and horizon convention;
derive every information branch from the near-infimum producer; aggregate
the finite sum.

Do not replace the source theorem with a theorem that assumes its per-arm
`liminf` conclusion, coerce `infinity` through `ENNReal.toReal`, assume a
minimizing alternative exists, or drop the zero-information branch. The next
valid progress is to connect the compiled extended-real near-`sInf`
alternative lemma to a finite-positive per-arm `liminf` theorem and explicit
zero/infinite cases, then prove the finite-sum terminal.
