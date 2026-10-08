# Upper no-regret and an ordinary-limit caveat

Source: Orabona v10, printed p.2 / PDF p.14. The paragraph says regret is at most sublinear and displays an ordinary limit of signed comparator regret divided by T as nonpositive. These formulations require care when the normalized sequence has no ordinary real limit. The pinned source is kept unchanged.

For the same fixed losses, predictions and feasible comparator set, the shared upper property is

\[
\forall u\in V\quad\forall\varepsilon>0\quad\exists N(u,\varepsilon)\quad
\forall T\ge N(u,\varepsilon):\quad R_T(u)/T\le\varepsilon.
\]

The literal-limit property additionally requires, separately for each comparator, an ordinary real limit a_u≤0. Limits and eventual thresholds may depend on u. No uniformity over the comparator set is claimed.

If a limit a exists and the upper property holds, taking limits in R_T(u)/T≤ε gives a≤ε for every positive ε. If a were positive, ε=a/2 would contradict this. Conversely, if a_u≤0 is an actual ordinary limit, the normalized regret eventually lies below any ε>0. Thus the two properties agree when every feasible comparator's ordinary limit exists. Neither property requires limit zero or nonnegative signed regret.

The distinction is strict in the general real-valued-loss model. Set V=[0,1], fix the constant causal learner x_t=0, and define the same infinite sequence of affine losses by

\[
F(T)=\begin{cases}T&T\text{ even},\\0&T\text{ odd},\end{cases}
\qquad \ell_t(x)=(F(t+1)-F(t))x.
\]

Actual finite prefix sums telescope to F(T)u, so R_T(u)=-F(T)u≤0 for every feasible u. The upper property follows at every horizon. At comparator1, positive even horizons have R_T(1)/T=-1 and odd horizons have0. Both subsequences tend to infinity, so uniqueness of ordinary real limits rules out any common limit. This construction uses signed losses unbounded over time; it is not a squared-loss or bounded-loss nonconvergence example and does not show that meanPredict itself fails to converge.

The source-to-Lean ledger explicitly records the upper-condition interpretation, the literal property and the convergence premise. This is a proposed source reconciliation/strict obstruction, pending source/body/reader acceptance. Existing meanPredict_noRegret is an actual upper no-regret producer from the same causal mean strategy and its regret bound; it is not an unconditional ordinary-limit producer. Full Chapter1 best-fixed/minimum and the other contributor gaps remain required, as do Chapter2 and Chapters3–16. No chapter, whole Goal, main or live completion follows from this package.
