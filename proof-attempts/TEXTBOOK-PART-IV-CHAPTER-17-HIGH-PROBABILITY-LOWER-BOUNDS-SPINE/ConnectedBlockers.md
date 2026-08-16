# Chapter 17 connected blockers

## Stochastic branch

Theorem 17.1 reaches the same missing interface as Chapters 15--16: one common
possibly randomized nonanticipating policy must induce two history laws whose
relative entropy decomposes into original-law expected pull counts times
original-to-alternative arm KL. Installed Mathlib's composition-product chain
rule stops before the required conditional integral of pointwise kernel KL.

The threshold, event direction, Gaussian arm KL, Bretagnolle--Huber, and
least-arm averaging are available. Replacing the policy by a deterministic
action map would change the source theorem and is rejected.

## Adversarial branch

The textbook intentionally gives only a high-level proof of Theorem 17.4. The
missing formal technology is the bounded reward-matrix law obtained by
clipping a shared Gaussian noise variable, the same-policy interaction law,
Claim 17.6's information calculation, Eq. (17.8)'s construction-level pathwise
comparison, and Claim 17.7's clipping concentration.

Claim 17.5's first-moment witness, the event subtraction, and the final
quarter-horizon algebra now compile. They do not discharge the construction
or concentration blockers.

## Evidence classification

- compiled: threshold definitions, Claim 17.5, event subtraction, conditional
  Eq. (17.8) algebra;
- blocked: Theorem 17.1, Corollaries 17.2--17.3, Theorem 17.4, Claims
  17.6--17.7, and construction-level Eq. (17.8);
- route evidence only: Gerchinovitz--Lattimore (2016) and
  `WEAPON-KL-CHANGE-OF-MEASURE`.
