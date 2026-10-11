# Proposed correction to one proof display, separate from the pinned source

Orabona arXiv:1912.13213v10, printed14/PDF26: the second equality in the proof of Theorem2.13 displays the interior coefficient `(1/η_(t+1) - 1/η_t)` multiplying the next squared distance. The preceding expression divides each squared distance by `2η_t`; the interior coefficient must therefore be `(1/(2η_(t+1)) - 1/(2η_t))`. The subsequent `D²/2` line and the stated theorem agree with the latter coefficient.

This proposes a correction to an intermediate algebraic equality only. The pinned PDF and frozen theorem terminal remain unchanged. Independent source review is required; no author endorsement is claimed.

For a direct scalar audit, use two rounds, squared distances `[0,1,1]` and steps `[1,1/2]`. The original sum of potential differences is `-1/2 + 0 = -1/2`. The displayed expansion without the half factor is `0 - 1 + (2-1) = 0`. The corrected expansion is `0 - 1 + (2-1)/2 = -1/2`. These distances can occur for linear losses on `[-1,1]`, comparator and initial point0, supports `[-1,0]`, and the stated steps; the second update leaves the point1 unchanged.

The current preparatory Lean target uses general weights directly, so the positive-step specialization is `w_t=1/(2η_t)`. Zero weights are a new algebraic extension required for the later adaptive zero-feedback trajectory. Neither this correction nor that extension proves the parent algorithm or changes any required Chapter2 obligation. Whole Chapters1–16 Goal remains ACTIVE.
