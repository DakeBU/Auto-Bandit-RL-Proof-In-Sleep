# Chapter 16 history-information blocker (resolved)

Task: `TEXTBOOK-PART-IV-CHAPTER-16-INSTANCE-DEPENDENT-LOWER-BOUNDS-SPINE`

## Attempted route

The source proof of Theorem 16.2 and Lemma 16.3 changes one suboptimal arm,
then invokes Lemma 15.1 to replace the KL divergence of the two complete
history laws by the original-law expected pull count times the changed arm KL.
Chapter 14 supplies the event-level Bretagnolle--Huber inequality, and Chapter
15 supplies the exact unit-Gaussian arm KL.

## Historical blocker

The installed Mathlib theorem `InformationTheory.klDiv_compProd_eq_add`
leaves its conditional term as the divergence between two composition-product
measures; it does not identify that term with the base-law integral of
pointwise kernel KL. The repository also lacks a canonical finite-history law
for a possibly randomized nonanticipating policy kernel shared by both
environments. Its existing policy surfaces do not have the source semantics.

This blocker was resolved by the compiled canonical history-law and
conditional kernel-KL layers. The one-arm history identity, majority event,
Bretagnolle--Huber inequality, and gap-event regret charges now compile.

The subsequent finite-mean environment producer now identifies unchanged laws
with unchanged integral means and supplies the exact gaps needed by Lemma
16.3. Lemma 16.3 and Theorem 16.4 compile; only Theorem 16.2's asymptotic
`d_inf`/`liminf` bridge remains blocked.

## Pivot rule

Retained as historical evidence. Future work should use the compiled history
and finite-mean interfaces and must not reopen this resolved blocker.
