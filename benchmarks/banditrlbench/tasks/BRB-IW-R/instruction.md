# Derive variance and diagnose a false bound

Use the same one-round finite probability model: p_i>0, sum_j p_j=1,
 losses l_j in [0,1] fixed before drawing I~p, and hat(l)_i=l_i 1{I=i}/p_i.
 Derive E[(hat(l)_i-l_i)^2] from finite sums, showing both moments.
 Diagnose: "Since l_i<=1, the estimator lies in [0,1], so its variance is
 at most 1/4 regardless of p_i." Give a numeric two-arm counterexample,
 calculate its variance, and explain why zero support cannot be repaired by
 declaring 0/0=0. Submit a derivation in answer.txt (at most 700 words).

This task is public dev. Time budget: 600 seconds; at most 100 tool calls and
20,000 tokens. Closed-book for natural-language tasks; Lean-assisted for Lean.
Factual statements and explanations receive separate rubric credit.
