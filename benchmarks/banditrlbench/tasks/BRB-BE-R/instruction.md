# Uniqueness without contraction

In the finite undiscounted model of BRB-BE-K (definitions repeated here),
 B_t f(s)=sum_a pi_t(a|s)[r(s,a)+sum_s' P(s'|s,a)f(s')].
 Fix H and the policy. Two sequences U_0,...,U_H and V_0,...,V_H have
 U_H=V_H=0 and satisfy U_t=B_t U_{t+1}, V_t=B_t V_{t+1} for all t<H.
 Prove U_t=V_t for all t<=H. Diagnose this proof: "B_t is a strict
 contraction because P is stochastic, so Banach's theorem gives uniqueness."
 Give an explicit one-state, one-action counterexample to uniqueness if the
 terminal condition is removed. Explain the relation to infinite horizon.
 Submit answer.txt with the proof and counterexample (at most 700 words).

This task is public dev. Time budget: 600 seconds; at most 100 tool calls and
20,000 tokens. Closed-book for natural-language tasks; Lean-assisted for Lean.
Factual statements and explanations receive separate rubric credit.
