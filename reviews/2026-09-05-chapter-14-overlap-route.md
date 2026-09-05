# Chapter 14 measure overlap route

Source: official author PDF, printed p. 191 / physical p. 200, Eqs. (14.8)
and (14.9), checked against `tmp/pdfs/chapter14-pages195-206.txt`.
For common densities p,q, the targets are integral(min(p,q)) at least
exp(-KL)/2 and at least half the square of integral(sqrt(p*q)).

First leaf route: define common-density overlap and the measurable likelihood
comparison event A={p<=q}. Prove integrability via `Integrable.inf`, split with
`integral_add_compl`, and use `Measure.setIntegral_toReal_rnDeriv` to show
overlap equals P(A)+Q(A complement). Applying the already compiled event BH
theorem gives exact Eq. (14.8), including infinite KL. This is not circular:
that event theorem was proved using binary affinity, independently of these
measure-overlap declarations. It is an alternative route to the source's
measure-level Jensen proof, not a claim to have reproduced that proof yet.

Next leaf: Eq. (14.9) by Cauchy--Schwarz on sqrt(min(p,q)) and sqrt(max(p,q)),
with the maximum-density integral bounded by 2. Candidate APIs are
`memLp_two_iff_integrable_sq`, `integral_mul_le_Lp_mul_Lq_of_nonneg`, and real
sqrt/rpow identities. The measure-level affinity/KL Jensen step in the body
still requires its own evidence; a compiled overlap terminal does not supply
that intermediate inequality.

Retrieval cards: measure/integral and real sqrt/log. Local `commonDensityOverlap`
searches found no match. Generic integral adapters are Mathlib-candidates;
source-named quantities are project-local. Common domination is sigma-finite,
P and Q are probability measures for the terminal, and no mutual AC, finite KL,
or positive-everywhere density assumptions are introduced.

Eq. (14.8), overlap nonnegativity/integrability, and the attaining-event
identity now pass direct Lean checking. For Eq. (14.9), first prove the
generic square-root Cauchy bound using L2 square integrability and Holder's
inequality with conjugate exponents 2,2. Apply it to the minimum and maximum
densities, use `min_mul_max`, and bound the maximum-density integral by 2.
The square-root product integrability is separately supplied by
`MemLp.integrable_mul`; it is not inferred from a totalized real integral.

## Focused result

`lake build BanditRLProof.LowerBounds.CommonDensityOverlap` passed (2,672 jobs).
`lake env lean Tests/TextbookPartIVChapter14OverlapCanary.lean` passed for
arbitrary sigma-finite domination and a non-finite Lebesgue dominating measure.
The six printed proof dependencies contain only `propext`, `Classical.choice`,
and `Quot.sound`. Both exact inequalities compile without positive-density,
mutual-absolute-continuity, or finite-KL assumptions. The module has no own
linter warnings. Initial API repairs used continuous composition for square-root
AEStronglyMeasurable and unfolded pointwise multiplication before rewriting;
no target assumptions were altered.

The full harness pass at `78846b8` covers CommonDensityKL, not this new module.
Overlap root/aggregate integration remains pending. In particular the source
measure-level Jensen assertion relating affinity to exp(-KL/2) is still open;
the alternate attaining-event proof of Eq. (14.8) is not evidence for it.

## Jensen continuation route

Use `ConvexOn.map_integral_le` from `Mathlib.Analysis.Convex.Integral`
with `Real.convexOn_exp` on the whole real line, under P and with
f=-LLR/2. First work relative to Q: the scalar identity
r*exp(-log(r)/2)=sqrt(r) for nonnegative r (including zero) transports both
integrability and the integral from Q to P via RN change of measure.
Finite KL supplies LLR integrability and P<<Q; infinity stays a separate
zero-scale branch. A common-dominator affinity identity is then needed to
transport the result to arbitrary sigma-finite mu. Cards:
MLIB-MEASURE-INTEGRAL, MLIB-EXP-LOG-INEQUALITIES, MLIB-REAL-LOG-SQRT,
TXT-LATTIMORE-SZEPESVARI-2020. Searches for affinity found only the binary
Jensen leaf and the new overlap module. The scalar adapter is a
Mathlib-candidate; the source-mapped measure wrappers remain project-local.

## Jensen focused proof result

`AffinityKL.lean` now focused-builds (2,673 jobs) without own warnings.
Its eight declarations supply the zero-safe scalar identity, square-root RN
integrability, exponential LLR integrability and change of measure, integral
Jensen under P, common-density affinity transport, and the unconditional
`bretagnolleHuberScale_le_half_commonDensityAffinity_sq`. The top-KL branch
has zero scale; the finite branch derives AC/integrability from finite KL.
The terminal does not assume positive densities, mutual AC, or finite KL.
Its Q-domination premise suffices: finite KL implies P<<Q<<mu, and at infinite
KL the conclusion is just nonnegativity. The common-density transport uses
`Measure.rnDeriv_mul_rnDeriv` and real square-root algebra.

This supplies the previously missing source Jensen intermediate, not merely
the alternative event proof. The canary composes this result with Eq. (14.9)
to recover Eq. (14.8) through the source route. Root/aggregate verification
for the overlap and affinity additions remains pending.

The focused affinity canary passed before switching it to a root import;
all eight printed axiom sets contain only `propext`, `Classical.choice`, and
`Quot.sound`. Both new modules and both canaries are now registered with the
root library and aggregate Tests, ready for the new full integration gate.

## Full integration result

At b8325c2, the full check in C:/a14 passed: root library, aggregate Tests
(8,907 jobs), proof-graph export, placeholder scan, and 400 Python tests
(7 skipped, 190.612s). Log: C:/a14/tmp/ch14-affinity-full-check.log.
This covers overlap and the source Jensen intermediate, not the subsequent
Gaussian and coding-bound additions. Whole Chapter 14 remains partial.
