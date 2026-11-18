# Support and predictability

Fix a history H, a finite nonempty arm set A, a probability vector p on A,
 and losses l_i in [0,1] fixed given H. Draw I with conditional law p and observe
 only l_I. For a named arm i with p_i>0, define hat(l)_i=l_i 1{I=i}/p_i.
 (1) State E[hat(l)_i | H] and E[hat(l)_i^2 | H].
 (2) Explain the distinct roles of positive support, the actual sampling law,
 and fixing losses before the action. Explain what can break without each.
 Do not merely list assumptions. State whether independence between rounds is
 needed and whether these one-round identities alone imply a regret rate.
 Submit an English explanation in answer.txt (at most 600 words).

This task is public dev. Time budget: 600 seconds; at most 100 tool calls and
20,000 tokens. Closed-book for natural-language tasks; Lean-assisted for Lean.
Factual statements and explanations receive separate rubric credit.
