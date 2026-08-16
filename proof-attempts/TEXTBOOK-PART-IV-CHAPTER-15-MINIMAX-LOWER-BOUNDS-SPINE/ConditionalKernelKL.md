# Conditional composition-product KL audit

Date: 2026-08-16

Status: blocked (`local Lean lemma gap` plus `semantic interface gap`)

## Target

The Chapter 15 history induction needs a regularity-explicit specialization of

```text
klDiv (mu tensor kappa) (mu tensor eta)
  = integral (fun x => klDiv (kappa x) (eta x)) dmu(x).
```

For the bandit consumer, `kappa` and `eta` must be one-round action/reward
kernels built from the same stochastic policy kernel and two arm-law families.

## Installed Mathlib evidence

`Mathlib.InformationTheory.KullbackLeibler.ChainRule` compiles
`InformationTheory.klDiv_compProd_eq_add` and
`InformationTheory.klDiv_compProd_left`. The former leaves conditional KL as
`klDiv (mu tensor kappa) (mu tensor eta)`. The file's own TODO asks for the
integral form and notes that measurability of
`x |-> klDiv (kappa x) (eta x)` is not automatic.

No installed declaration was found that converts this conditional term into
the integral needed for expected pull-count weighting.

## Repository semantic evidence

`BanditRLProof.Policy.MeasurablePolicy` is a deterministic measurable action
map. It cannot represent the source quantifier over possibly randomized
nonanticipating policies. The existing action/reward `partialTraj` machinery
therefore cannot serve as the exact Lemma 15.1 terminal without adding a
distinct policy-kernel history interface.

## Safe next leaf

Prove the conditional-KL integral under a deliberately sufficient measurable
setting (for example, finite actions and standard-Borel rewards), then build a
recursive stochastic-policy history law and prove same-policy cancellation.
Until both compile, keep Lemma 15.1 and Theorem 15.2 blocked. Do not replace
the source terminal by a deterministic-policy theorem or by an equality
assumed as a premise.
