# What finite-horizon Bellman evaluation means

Consider a finite-state, finite-action MDP with horizon H, deterministic
 reward r(s,a), transition probabilities P(s'|s,a), and a fixed stage-dependent
 Markov policy pi_t(a|s). Rewards are undiscounted and terminal payoff is zero.
 (1) State the terminal condition and the chronological Bellman expectation
 recursion for V_t^pi, specifying valid stages.
 (2) Explain why the terminal condition matters and what changes if it is g(s).
 (3) Explain why the policy expectation cannot be replaced by max_a when
 evaluating a fixed policy. Give a one-step example where this changes value.
 State whether a discount factor below one is needed for this finite recursion.
 Submit answer.txt in English (at most 600 words).

This task is public dev. Time budget: 600 seconds; at most 100 tool calls and
20,000 tokens. Closed-book for natural-language tasks; Lean-assisted for Lean.
Factual statements and explanations receive separate rubric credit.
