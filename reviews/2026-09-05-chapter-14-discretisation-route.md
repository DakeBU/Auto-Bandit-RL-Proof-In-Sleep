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

## Filtration recovery leaf: route before tactics

Target a reusable intermediate theorem for finite `P,Q`, `P ≪ Q`, and a
filtration whose limiting sigma-algebra makes the real RN density strongly
measurable: original KL equals the supremum of the trimmed KL values.
The measurability premise is explicit in this intermediate leaf and must be
discharged by the future finite-partition construction, not assumed in the
final source theorem.

APIs: `Measure.integrable_toReal_rnDeriv`,
`Integrable.tendsto_ae_condExp` (requires only a finite reference measure),
`toReal_rnDeriv_trim`, `lintegral_trim`, continuous `klFun` and `ENNReal.ofReal`,
`lintegral_liminf_le`, and `Filter.liminf_le_of_frequently_le'`.
First expose trimmed KL as the lower integral of `klFun` of the conditional
density, with no KL-integrability assumption. Almost-everywhere convergence,
continuity, and Fatou then give the reverse bound. The already-compiled full
trim DPI gives the other bound. This includes infinite KL under absolute
continuity. Search-memory and declaration lookup for `klFiltration` found no
local result. Classification: Mathlib-candidate, same measure/conditional-Jensen
retrieval cards, plus the martingale-convergence API.

The filtration recovery and conditional-density lower-integral lemmas now
pass direct Lean checking. Next construct the natural filtration of
`SimpleFunc.eapprox` of the density. `Filtration.stronglyAdapted_natural`
makes each approximant measurable in its own layer; monotonicity into the
supremum and `SimpleFunc.iSup_eapprox_apply` make the density measurable in
the limiting sigma-algebra. This discharges the intermediate measurability
premise without assuming a countably generated ambient space. Finite encoding
of each layer remains a separate required bridge to Eq. (14.5).

The concrete density-approximation filtration and its limiting measurability
now also pass direct checking. To connect a finite observation to a trimmed
layer, use `toReal_rnDeriv_map` and `lintegral_map` to identify mapped KL with
the KL of the observation's comap sigma-algebra, under the existing AC branch.
This measure-transport identity is independent of finite-valued encoding;
the eventual observation construction must supply that finiteness separately.

All six declarations in `RelativeEntropyFiltration.lean` now pass direct
Lean checking and its focused Lake build succeeds (2,703 jobs). They prove
the conditional-integral identity, observation/comap KL equality, filtration
recovery by Fatou, construct the natural density-approximation filtration,
prove limiting density measurability, and recover KL along this concrete
filtration with no additional density-measurability premise. No finite-KL
assumption was introduced.

Initial errors were elaboration-only: implicit measurable-space selection
inside `rw`, lifting conditional-expectation measurability to the ambient
space, and a dependent `iSup` argument. Explicit integral expressions,
`stronglyMeasurable_condExp.mono (F.le n)`, and a fully typed `le_iSup`
resolved them. The source target and Fatou route are unchanged.

Next exact construction: the first `n+1` simple approximants have jointly
finite range, using `Set.Finite.pi` from `Data.Fintype.Pi`; encode that range
with `Fintype.equivFin`. Show each approximant factors through the encoded
observation, hence the natural filtration's nth layer is contained in its
comap sigma-algebra. `Measure.trim_trim`, trim DPI, and the new observation/
comap equality then bound that layer's KL by the finite-partition supremum.
Taking suprema should finish the AC branch; combine with the existing
singular branch. This finite encoding has not yet been implemented.

`Tests/TextbookPartIVChapter14FiltrationCanary.lean` subsequently passed
direct checking. All six printed declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The new filtration module and canary
remain focused-only, pending root/aggregate integration and the final full
gate together with the finite-observation encoding.
