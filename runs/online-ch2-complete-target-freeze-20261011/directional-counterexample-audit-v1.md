# Directional constant audit: exact finite counterexample

Proposal and mathematical audit only. Actor `/root/adaptive_decoder`; requested GPT-6 Astra / medium; no runtime attestation. No Lean proof, compiler, canonical metadata, contract, or OSD RUN write. Proof denominator remains null; no chapter acceptance. Earlier source familiarity is disclosed; this is not blind decoding.

## Source and statement boundary

Frozen Orabona v10 PDF: `E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf`, raw SHA256 `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`, unchanged before/after extraction and computation.

Printed p.216 / PDF p.228, Section13.4 specifies Euclidean unit-ball OSD, initial point zero and eta_t = sqrt(2)/(2 L sqrt(t)) = 1/(L sqrt(2t)). The source page pixels were inspected at `../online-ch2-forward-source-repair-20261011/pdf-228-v2.png`. Eq13.2 is a bound for the **combined KT magnitude plus OSD direction learner**:

R_T(u) <= L ||u|| [sqrt(log(e ||u|| T/epsilon + 1)) + 1] sqrt(2T) + L epsilon.

Algorithm12.3 and Theorem12.16, printed203–204 / PDF215–216, give the exact linear-regret decomposition R_scalar(||u||) + ||u|| R_direction(u/||u||), for nonzero u; zero comparator separate. The implied directional estimate R_direction(v) <= L sqrt(2T) is a sufficient intermediate supporting the displayed +1 coefficient. It is **not a separately printed numbered theorem**. This audit refutes that intermediate for the prescribed OSD schedule. It does not establish that Eq13.2 itself is false: unused slack in the magnitude bound might compensate, and the combined learner was not simulated or bounded here.

## Exact causal counterexample

Dimension one; V=[-1,1], T=16, L=1, x_1=0. Choose predetermined linear losses ell_t(x)=g_t x, with g_1=g_2=1, g_3=...=g_8=0, and g_9=...=g_16=-1. Every loss is convex, differentiable everywhere, and 1-Lipschitz; every feedback is its actual unique gradient, with |g_t|<=1. Output x_t before observing g_t, then update

x_{t+1}=max(-1,min(1,x_t-g_t/sqrt(2t))).

Zero-gradient rounds count in t. This is the exact prescribed time schedule, with no restart or omitted rounds. Comparator u=1 is feasible and optimal because sum g_t=-6.

The first update gives x_2=-1/sqrt(2); the second gives x_3=-1, because 1/sqrt(2)+1/2>1 (equivalently sqrt(2)<2). Zero gradients keep x_3 through x_9 equal to -1. On rounds9–16 all updates increase the point by 1/sqrt(2t)<1/4. Their total is <2, so none reaches the upper endpoint and no upper clipping occurs. Consequently, for t=9,...,17,

x_t=-1+sum_{s=9}^{t-1}1/sqrt(2s).

Thus exactly

R_16(1)=14-1/sqrt(2)-sum_{s=9}^{15}(16-s)/sqrt(2s).

Since 1/sqrt(2)<1, each reciprocal square root in the sum is <1/4, and sum_{s=9}^{15}(16-s)=28,

R_16(1)>14-1-28/4=6>sqrt(32).

The last inequality follows from 36>32. These inequalities supply a short exact mathematical certificate independent of floating-point search. This is not a Lean-checked proof.

## Executed experiments and independent interval computation

`audit-direction-v1.py` executes the recurrence, preserves all tested trajectories in `executed-trials-v1.json`, and independently propagates exact Fraction intervals through the causal recurrence. Square-root brackets use integer `isqrt(n*10^24)` with denominator10^12; reciprocals reverse the interval endpoints. Clipping is monotone, and multiplication by a negative gradient swaps the interval endpoints. The final lower regret bound exceeds the upper bound for sqrt(32) by more than1.61309513308.

| Executed trial | Regret to best comparator | Claimed bound | Outcome |
|---|---:|---:|---|
| T16, twelve +1 then four -1 | 0.14400615455 | 5.65685424949 | No violation |
| T8, +1,+1,0,0 then four -1 | 3.49959840966 | 4 | No violation |
| T16 witness above | 7.26994938258 | 5.65685424949 | Certified violation |
| T10000, 9718 gradients1/sqrt(20000), then282 gradients -1 | 161.78212258862 | 141.42135623731 | Floating-point violation only |

Only the T16 witness receives the rigorous interval certificate. The T10000 parent-suggested heuristic is executed and retained but is unnecessary to the conclusion. No claim of exhaustive search or sharp worst-case constant is made.

## Conservative repair candidate and retained debt

For arbitrary dimension, L>0, T>=1, unit ball, ||g_t||<=L, and the same eta_t, Theorem2.13 (printed13–14 / PDF25–26), applied to the direction learner's linear losses with diameter D=2, gives

R_direction(v) <= 4/(2 eta_T) + (L^2/2) sum eta_t
 <= 2 L sqrt(2T) + (L/(2 sqrt(2))) 2 sqrt(T)
 = (5/2) L sqrt(2T).

The inverse-root sum bound follows, for example, from 1/sqrt(t)<=2(sqrt(t)-sqrt(t-1)), t>=1, which telescopes. This is a valid conservative mathematical bound, not a sharpness claim or accepted source replacement. It keeps the actual printed algorithm and its schedule. Conditional on independently validating the scalar KT bound used in the source, the reduction would support replacing the displayed directional +1 by +5/2. The scalar KT proof and a formal producer for this repaired composition remain explicit debt. Do not overwrite or mark the original Eq13.2 as discharged.

Required next review: retain original Eq13.2 and exact algorithm as source obligation; record the failed directional intermediate and this witness; independently investigate whether the combined source bound can hold through compensation, or propose and review an explicit corrected algorithm/bound. The same p=2 direction-intermediate issue also touches the later Lp specialization, without refuting its combined bound. No later target is removed, no source freeze or chapter completion is certified.
