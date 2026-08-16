# Open problem: Chapter 17 adversarial clipped-normal lower bound

Problem id: `CH17-ADVERSARIAL-CLIPPED-NORMAL`

Source theorem: Lattimore--Szepesvari (2020), Theorem 17.4, Claims 17.5--17.7,
and Eq. (17.8). Detailed route evidence is Gerchinovitz--Lattimore,
*Refined Lower Bounds for Adversarial Bandits*, NeurIPS 2016.

Formal target: construct the source clipped-normal reward-matrix law and its
interaction with one possibly randomized nonanticipating policy; prove Claim
17.6's pull-count event, Eq. (17.8)'s pathwise regret inequality, Claim 17.7's
clipping-count tail, and the exact deterministic-witness conclusion of
Theorem 17.4.

Current Lean status: partial/blocked. Claim 17.5's first-moment content, the
`2delta-delta` event subtraction, and the deterministic quarter-horizon
algebra compile. The hard law and source terminals do not.

Theorem cards: `TXT-LS-2020-THM-17-4-ADVERSARIAL-TAIL`,
`TXT-LS-2020-CLAIMS-17-5-17-7`, and
`PPR-GERCHINOVITZ-LATTIMORE-2016-REFINED-LOWER-BOUNDS`.

Acceptance gate: a Borel reward-matrix law with source clipping, within-round
arm dependence and across-time IID preserved; same-policy history law; exact
Claims 17.6--17.7 and Eq. (17.8); Theorem 17.4 with its universal constants,
horizon condition, CDF direction, typed canary, Tests, and placeholder scan.

Next smallest leaf: define the scalar `clip_[0,1]` map, prove its Borel
measurability and range, and lift one Gaussian noise variable to the source
correlated `Fin k -> [0,1]` reward row.

Nonweakening fence: do not replace the correlated reward row by independent
arms, replace random regret by pseudo-regret, drop clipping, or treat the
external paper as a compiled theorem.
