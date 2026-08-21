# Conversion window: NeurIPS 2025 succinct lower bounds

Task: `PAPER-AUDIT-NEURIPS-2025-SUCCINCT-LOWER-BOUNDS`

Status: `source-frozen; first geometric leaves compiled; paper lower-bound
endpoint blocked`

## Source notation

The paper works in a real inner-product space `V`.  Axiom 3.1 supplies a
nonempty atom set `U` of unit vectors closed under negation.  An indexed
positive-cardinality family `{E_i}` is a succinct support when

```text
sup_{E in U} sum_i |<E, E_i>| = 1.
```

It then defines

```text
Q(X) = sup_{E in U} <X,E>,
R(X) = sup_{Q(Y) <= 1} <X,Y>.
```

Printed pp. 4--5 contain Definitions 3.1--3.3 and Lemmas 3.1--3.6.  Appendix
A on printed pp. 11--12 gives the proof routes used by this port.

## Lean representation

- `SuccinctUnitSystem.atoms` is a `Set V`, not a finite surrogate.
- `sourceQ` and `sourceR` preserve the paper's real-valued `sSup` notation.
- `IsSuccinctSupport.correlation_bddAbove` makes the ordinary mathematical
  meaning of the displayed finite supremum explicit.  It is paired with the
  literal equality `correlation_sSup_eq_one` rather than replacing the source
  condition with orthogonality.
- The source's positive support size is represented by
  `[Nonempty (Fin s)]` only on the theorems that take a maximum or a sign
  witness.
- Coefficient sign uses `+1` at zero, matching the Appendix-A footnote.

## Intended proof routes

### Lemma 3.1

The support supremum gives a pointwise correlation-sum upper bound.  Evaluating
it at each support atom proves mutual orthogonality.  Triangle inequality and
the finite maximum give the upper `Q` bound; the signed maximizing support
atom reaches it.

### Lemma 3.2

Atom symmetry gives `|<Y,E_i>| <= Q(Y)`.  Therefore every `Q(Y) <= 1` witness
is bounded above by the coefficient `l1` sum when paired with a succinct
vector.  The signed sum of support atoms has `Q=1` by Lemma 3.1 and reaches the
same `l1` sum.

## Global `R` diagnostic

For a nonzero `X` orthogonal to all atoms, Lean proves `Q(r X)=0` for every
real `r`.  Hence the set defining `R(X)` contains values growing without
bound.  Real `sSup` is totalized on unbounded sets, so later proofs must never
use its value without a `BddAbove` proof.  This is the formal boundary behind
the paper's informal claim that `R` is a globally real-valued seminorm.

## Compiled local slice

The isolated full gate now compiles the source-shaped atom system, `sourceQ`,
`sourceR`, the literal succinct-support contract, support orthogonality,
Lemma 3.1, Lemma 3.2 for succinct combinations together with its local
boundedness witness, and the nonzero-orthogonal-vector unboundedness
diagnostic.  These declarations establish only the geometric window above;
they do not instantiate the paper's stochastic-bandit construction or its
lower-bound endpoint.

## Remaining source obligations

- choose and justify a global repair for `R` before Lemmas 3.5--3.6;
- formalize strict-support minimality in Lemmas 3.3--3.4;
- encode the grouped supports and `Phi_G` geometry of Assumption 3.7;
- construct the action set and parameter family of Theorem 3.8;
- instantiate the same-policy history-KL and testing lower-bound chain;
- recover the theorem's two-regime rate and constants.
