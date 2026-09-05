# Chapter 14 finite-discretisation supremum route

Source: `TXT-LATTIMORE-SZEPESVARI-2020`, Eq. (14.5) and Theorem 14.1.
The target remains equality of the supremum over finite measurable
discretisations and the existing RN-based `relativeEntropy`, for arbitrary
probability measures on an arbitrary measurable space.

Represent a finite measurable partition by a measurable function into `Fin n`.
Its cells are the singleton preimages, its masses are those of the mapped
measures, and Eq. (14.4) gives their exact finite-sum KL. Empty cells are allowed
and contribute zero. Taking the supremum over all `n` and all such maps avoids
a fixed alphabet-size restriction and does not assume a countably generated
source sigma-algebra.

Retrieval cards: `MLIB-MEASURE-INTEGRAL`, `MLIB-FINTYPE-FIN`, and
`MLIB-KL-TRIM-CONDITIONAL-JENSEN`. Local `finitePartition` memory/declaration
searches found no existing result. Direct Mathlib searches for KL map,
partition, and supremum identities found no direct theorem.

First dependency leaf: singular branch. If `P` is not absolutely continuous
with respect to `Q`, select a measurable Q-null set of positive P mass using
`Measure.AbsolutelyContinuous.mk` (or `exists_measurable_superset_of_null`).
Map its event/complement to `Fin 2` using `Measurable.ite`. `Measure.map_apply`
and `relativeEntropy_eq_top_of_atom_support_mismatch` show that this one
finite discretisation already has infinite KL; hence so does the supremum.
This branch needs no finite-measure hypothesis.

Subsequent dependencies: finite-map data processing, then approximation of the
RN convex integrand by finite measurable partitions, including the
absolutely-continuous but nonintegrable case. Full sub-sigma-algebra DPI alone
does not prove this approximation direction. No missing approximation lemma
will be inserted as a caller hypothesis in the final equality.

Classification: generic bridges are Mathlib-candidates; the named source
supremum definition and Chapter 14 adapters are project-local. No new package
or weakened theorem contract is required. This is a route record, not evidence
that Eq. (14.5) is complete.

Upper-bound bridge route: expose the finite-measure total-mass Jensen bound
in ENNReal via `mul_klFun_le_toReal_klDiv`, splitting infinite KL first.
For a finite measurable map, `rnDeriv_restrict_restrict` and
`lintegral_iUnion` split KL into its disjoint fiber restrictions. Sum the
total-mass bounds over fibers and use `relativeEntropy_finite_klFun` for the
mapped laws. Taking the supremum then gives the forward inequality. This
does not require countable generation or positive masses on every cell.

## Focused compiled progress

`FinitePartitionKL.lean` builds successfully (2,672 jobs), and
`Tests/TextbookPartIVChapter14PartitionCanary.lean` passes direct checking.
The eleven declarations cover the source supremum definition, the exact
finite-map cell formula, total-mass Jensen, fiber KL decomposition, finite-map
DPI, the supremum upper bound, the binary singular witness, singular-branch
equality, and equality on `Fin n` via the identity observation. The canary
includes three-symbol equal and singular Dirac cases. All printed dependencies
are only `propext`, `Classical.choice`, and `Quot.sound`.

One elaboration failure occurred: reverse rewriting by `tsum_fintype` left
the new summation-filter parameter unknown. Supplying
`(L := .unconditional _)` resolved it without changing the proof route.
There is one harmless style warning in the canary (`simpa using hp`).

This is focused evidence only: the new module is not yet root-imported, the
new canary is not yet included in the aggregate Tests target, and no full
harness/site/remote gate is claimed for Eq. (14.5). Whole-chapter coverage
remains partial.

## Reverse-direction retrieval

Installed Mathlib provides `SimpleFunc.eapprox`, `iSup_eapprox_apply`, and
`tendsto_eapprox`, as well as `Integrable.tendsto_ae_condExp` in
`Probability.Martingale.Convergence` and `lintegral_liminf_le` in
`Integral.Lebesgue.Add`. A promising implementation of the planned RN
approximation is to build increasing finite sigma-algebras from simple
approximants to the density, apply the upward conditional-expectation
convergence theorem, and use continuity of `klFun` plus Fatou. It must still
construct the finite observations and show the limiting sigma-algebra makes
the RN density measurable; these are obligations, not caller hypotheses.
The density is integrable even when its KL integrand is not, so this route
could cover the absolutely-continuous infinite-KL case without a finite-KL
assumption. No reverse-direction theorem is proved yet.
