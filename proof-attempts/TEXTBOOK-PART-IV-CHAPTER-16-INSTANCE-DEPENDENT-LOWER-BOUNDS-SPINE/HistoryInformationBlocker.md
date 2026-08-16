# Chapter 16 history-information blocker

Task: `TEXTBOOK-PART-IV-CHAPTER-16-INSTANCE-DEPENDENT-LOWER-BOUNDS-SPINE`

## Attempted route

The source proof of Theorem 16.2 and Lemma 16.3 changes one suboptimal arm,
then invokes Lemma 15.1 to replace the KL divergence of the two complete
history laws by the original-law expected pull count times the changed arm KL.
Chapter 14 supplies the event-level Bretagnolle--Huber inequality, and Chapter
15 supplies the exact unit-Gaussian arm KL.

## Blocker

The installed Mathlib theorem `InformationTheory.klDiv_compProd_eq_add`
leaves its conditional term as the divergence between two composition-product
measures; it does not identify that term with the base-law integral of
pointwise kernel KL. The repository also lacks a canonical finite-history law
for a possibly randomized nonanticipating policy kernel shared by both
environments. Its existing policy surfaces do not have the source semantics.

Therefore the one-arm history identity and expected-pull information
constraint are not available. Theorem 16.2, Lemma 16.3, and Theorem 16.4 remain
blocked. The compiled Chapter 16 consistency, `d_inf`, Gaussian candidate, and
log-growth leaves do not discharge this semantic obligation.

## Pivot rule

Continue only by proving the conditional kernel-KL integral and stochastic
history interface, or by adding transparent general analytic leaves that do
not assume the blocked bandit conclusion. Do not restrict the source terminal
to deterministic policies, reverse the KL direction, or pass the history
information inequality as a premise while labelling the terminal compiled.
