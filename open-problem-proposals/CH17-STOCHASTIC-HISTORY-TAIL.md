# Open problem: Chapter 17 stochastic history tail bridge

Problem id: `CH17-STOCHASTIC-HISTORY-TAIL`

Source theorem: Lattimore--Szepesvari (2020), Theorem 17.1 and Corollaries
17.2--17.3; dependent on Lemma 15.1.

Formal target: construct the history law for one possibly randomized
nonanticipating policy and prove the original-to-alternative one-arm KL
identity needed to show the exact random-pseudo-regret tail in Theorem 17.1.
Then retain the exact side condition and tail integration needed by the two
corollaries.

Current Lean status: blocked. Chapter 14 Bretagnolle--Huber and Chapter 15
unit-Gaussian arm KL compile. The conditional integral of pointwise kernel KL
and the canonical stochastic-policy history law do not.

Theorem cards: `TXT-LS-2020-LEMMA-15-1-DIVERGENCE-DECOMPOSITION`,
`TXT-LS-2020-THM-17-1-STOCHASTIC-TAIL`,
`TXT-LS-2020-COR-17-2-STOCHASTIC-MINIMAX-TAIL`, and
`TXT-LS-2020-COR-17-3-UNIFORM-TAIL-IMPOSSIBILITY`.

Acceptance gate: a source-faithful Lean theorem for the same randomized
policy, original-law pulls, original-to-alternative KL, exact event direction,
and exact constants; typed canary plus full Tests and placeholder scan.

Next smallest leaf: a finite-horizon stochastic policy-kernel history law with
one-step composition and an explicit same-policy kernel cancellation lemma.

Nonweakening fence: do not use a deterministic policy surrogate, reverse KL,
change random pseudo-regret into expected regret, or restrict the theorem's
uniform environment/confidence quantifiers.
