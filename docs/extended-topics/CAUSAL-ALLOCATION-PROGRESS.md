# Causal allocation geometry

`CausalAllocation.lean` defines the actual source design objective as the
maximum action importance second moment under the PMF sampling mixture.

- Under support coverage each action second moment is at least one. The proof
  expands the nonnegative mixture expectation of (P_a/Q-1)^2 and uses the
  previously proved change-of-measure identity and PMF normalization.
- The library's uniform finite PMF covers all action supports. Each likelihood
  ratio is at most the action count, so each action moment and the maximum
  design cost are at most that count. This realizes the frozen uniform design
  result rather than assuming a feasible bound.
- A Bernoulli selection constructs convex mixtures of actual allocations.
  Mixing two covered designs preserves coverage, including endpoint weights.
  The reciprocal inequality proves convexity of each moment and hence the
  maximum objective on this covered domain.
- On a covered cost sublevel m(eta)<=K with K>0, every action and state satisfy
  Q_eta(z)>=P_a(z)^2/K. Thus each state in the union support stays uniformly
  away from zero on that sublevel. This is the denominator control needed by
  the compactness/continuity proof of an attained optimum.

The canary uses two distinct point-mass action laws and proves that their
uniform design attains second moment two for either action. This checks the
sharp uniform bound but does not replace the frozen noisy performance canary.

Still open: realize the simplex/sublevel as a compact space and prove a covered
optimizer exists; the source parallel allocation bridge; actual repeated
sampling, Bernstein and full simple regret; noisy full-chain canary; independent
semantic review, topic mapping and all-topic ICLR evidence. Convexity alone
does not justify assuming an optimizer or claiming topic acceptance.
