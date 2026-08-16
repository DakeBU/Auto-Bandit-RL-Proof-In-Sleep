# Proof Export: Chapter 14 Information-Theory Spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-14-INFORMATION-THEORY-SPINE`

Status: the scoped §14.2 declaration surface is compiled at Lean source commit
`10dfd88`. The repository, website, review, and remote gates are recorded in
the task packet rather than inferred from this mathematical export.

This export covers Eqs. (14.4)--(14.6), Theorem 14.1, the event specialization
of Exercise 14.10, and Theorem 14.2 in Lattimore--Szepesvári, *Bandit
Algorithms*, Part IV, Chapter 14. It does not claim the entropy/coding results
of §14.1, full arbitrary-sub-sigma-algebra data processing, or an adaptive
bandit-history chain rule.

## Lean Declarations

- `LowerBounds.relativeEntropy`
- `LowerBounds.relativeEntropy_of_absolutelyContinuous_of_integrable`
- `LowerBounds.relativeEntropy_of_probability_absolutelyContinuous_of_integrable`
- `LowerBounds.relativeEntropy_eq_top_of_not_absolutelyContinuous`
- `LowerBounds.relativeEntropy_ne_top_iff`
- `LowerBounds.bernoulliRelativeEntropy`
- `LowerBounds.rnDeriv_restrict_restrict`
- `LowerBounds.relativeEntropy_restrict_add_compl`
- `LowerBounds.bernoulliKLCore_event_le`
- `LowerBounds.exp_neg_half_bernoulliKLCore_le_affinity`
- `LowerBounds.half_binaryAffinity_sq_le_eventError`
- `LowerBounds.binaryBretagnolleHuberCore`
- `LowerBounds.bretagnolleHuberScale`
- `LowerBounds.bretagnolleHuberScale_nonneg`
- `LowerBounds.binaryBretagnolleHuber`
- `LowerBounds.bernoulliRelativeEntropy_event_le`
- `LowerBounds.bretagnolleHuberScale_antitone`
- `LowerBounds.bretagnolleHuber`

## Natural-Language Proof

Define `relativeEntropy P Q` to be Mathlib's extended-real `klDiv P Q`.
Mathlib's representation yields two exact branches. When `P` is absolutely
continuous with respect to `Q` and the log likelihood ratio is integrable
under `P`, KL is the nonnegative extended-real embedding of its integral,
with a finite-measure mass correction that vanishes for probability laws.
When absolute continuity fails, KL is infinity. Conversely, KL is not infinity
exactly when absolute continuity and log-likelihood integrability both hold.

For a measurable event `A`, assume first that the full KL is finite. Restrict
both laws to `A` and to `Aᶜ`. The Radon--Nikodym derivative of the restricted
pair agrees almost everywhere, on the restricted law, with the original
derivative. Splitting the KL integral over the two cells therefore gives

```text
D(P || Q) = D(P|A || Q|A) + D(P|Aᶜ || Q|Aᶜ).
```

Mathlib's convex `klFun` lower bound applied to each restricted pair bounds the
two restricted divergences below by their mass-level contributions. Adding
them gives the interior Bernoulli inequality

```text
d(P(A), Q(A)) <= D(P || Q).
```

If `Q(A)` is zero or one, finite KL supplies the corresponding zero mass under
`P`; if the full KL is infinite, the desired extended-real inequality is
immediate. Thus event-level binary data processing is unconditional and keeps
the direction `P` to `Q`.

For the binary testing step, first take interior `q`. Concavity of the real
logarithm applied with weights `p` and `1-p` yields

```text
exp(-d(p,q)/2) <= sqrt(p*q) + sqrt((1-p)*(1-q)).
```

A two-term square-root inequality bounds half the square of the right-hand
affinity by `p + (1-q)`. Squaring the exponential inequality therefore gives

```text
exp(-d(p,q))/2 <= p + (1-q).
```

The cases `q=0` and `q=1` are proved separately using the exact Bernoulli-KL
support convention: matching point masses have zero KL, while support mismatch
has infinite KL. Define the source testing scale to be `exp(-d.toReal)/2` for
finite `d` and zero for `d=∞`. This scale is nonnegative and antitone.

Finally, apply event data processing, then antitonicity of the scale, then the
endpoint-complete binary theorem. Rewriting `1-Q(A)` as `Q(Aᶜ)` proves

```text
bretagnolleHuberScale (D(P || Q)) <= P(A) + Q(Aᶜ).
```

This is the unconditional Theorem 14.2 terminal. No finite-KL premise, mutual
absolute continuity, policy, horizon, filtration, kernel chain rule, or
stopping-time assumption is present.

## Verification boundary

- The typed canary applies the public terminal to finite and singular examples
  through the root `BanditRLProof` import.
- The canary's axiom print contains only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Imported Mathlib KL theorems and the existing project Bernoulli-KL surface
  are dependencies, not newly claimed proofs.
- The compiled data-processing theorem observes one event; it is not the full
  arbitrary-sub-sigma-algebra statement in Exercise 14.10.
- Chapter 15 must still construct the same-policy adaptive bandit-history laws,
  prove their KL decomposition, and consume this testing terminal.
