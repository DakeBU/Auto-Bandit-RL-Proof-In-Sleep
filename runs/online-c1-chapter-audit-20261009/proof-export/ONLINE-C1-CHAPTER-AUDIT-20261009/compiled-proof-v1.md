# Initialized FTL: compiled Lean proof export

The four named public Lean proofs and actual27chaptercanaries passed the combined root, Tests and full harness gate. This export is a mathematical note, not a new Lean certificate or chapter acceptance. Source is Orabona v10 printed3-5/PDF15-17, SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Generic Chapter1 integration/FINAL/native/delivery remain candidate; whole16GoalACTIVE.

Model: squared loss, legal initial a and targets in[0,1]; source round t+1 is Lean t. Predictor is a at0 and the strict-past empirical mean later, with actual recursive count/mean state. G001 algebra permits arbitrary real data, T>0; G002 requires legal initial/scored prefix; G003/G004 require one all-time bounded stream. No supplied regret/stability or horizon-selected algorithm.

- `BanditRL.OnlineLearning.ftlPredict_bestRegret_initial_correction`

  $$R_T^{a}=R_T^{1/2}+(a-y_0)^2-(\tfrac12-y_0)^2\quad(T>0).$$

  Expand the actual two played-loss sums. Every positive-time prediction is the same strict-past empirical mean, so the tails cancel. The identical feasible comparator infimum cancels too; only the two first squared losses remain. No boundedness is needed for this real-valued algebra, but positive horizon is essential.

- `BanditRL.OnlineLearning.ftlPredict_bestRegret_refined`

  $$R_T^{a}\le1+4\sum_{s=2}^{T}\frac1s\quad(a\in[0,1],\ T>0).$$

  Reuse the actual half-initial quarter-plus-reciprocal bound and the exact first-loss correction. For legal initial and first observation, quarter plus that correction is at most1. Later updates and their denominators are unchanged. The terminal is1+4 times the reciprocal tail from source2 throughT, without replacing it by a loose logarithmic bound.

- `BanditRL.OnlineLearning.ftlPredict_upperNoRegret`

  $$\forall u\in[0,1],\ \forall\varepsilon>0,\ \exists N,\ \forall T\ge N:\ R_T^{a}(u)/T\le\varepsilon.$$

  Bound each feasible fixed-comparator regret by the actually produced TRUE-best regret. The same initial correction gives a derived logarithmic upper whose quotient tends0. The eventual positive-epsilon adapter then proves NoRegret for the same actual predictor and every feasible comparator. No ordinary comparator convergence is inferred.

- `BanditRL.OnlineLearning.ftlPredict_bestRegret_average_tendsto_zero`

  $$R_T^{a,\mathrm{best}}/T\longrightarrow0.$$

  Combine the actual half-initial TRUE-best average-zero theorem with the fixed first-loss correction divided byT, which tends0. The equality holds eventually at positive horizons. This ordinary zero limit concerns the realized best metric and needs no empirical-mean convergence assumption.

Dependencies: actual half-initial refined/log/best-average producers, comparator-to-produced-minimum transport and eventual upper adapter in the same shared Lean graph; all required compiler VALUE pairs recorded. T0 is empty regret0; its nonzero first-loss correction is inapplicable. Ordinary comparator limits are not inferred: the same bounded actual half-FTL dyadic obstruction is retained. Expected-FIXED and pathwise-best metrics stay distinct; IID information and measurability conditions are explicit in the current source contracts. No unproved probability assumption is hidden in these deterministic four proofs.
