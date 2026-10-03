# Conversion Window: Theorem2.26
Task id: `ONLINE-SUBGRADIENT-MAX`
Source card: docs/contracts/online-subgradient-max-v1/contract.md

## Natural-language statement
For a finite nonempty family of proper convex extended-real functions on finite-dimensional Euclidean space, at a point in every domain where every function is continuous, the maximum function has precisely the convex hull of the subgradients of functions attaining that maximum.

## Lean Mapping
| Source | Lean | Meaning |
| --- | --- | --- |
| finite I | Fintype ι, Nonempty ι | actual maximum defined |
| proper convex fi | SourceProper, IsConvexExtended | no bottom, finite witness, convex real epigraph |
| domain/continuity | effectiveDomain, ContinuousAt | every function finite and ambient continuous at x |
| F | SourceFiniteMax | actual Finset.univ.sup' |
| A(x) support union | SourceActiveSubgradientUnion | equality fi(x)=F(x) and full all-y support |
| conv union | convexHull ℝ | ordinary hull, no closure |

## Proof-DAG / allowed conversion
Native full equality frozen. Leaf active-support -> support convexity -> hull forward; actual continuity-to-interior -> supports compactness -> finite compact hull and actual reverse decomposition. No target weakening, extra source closedness or supplied decomposition. API failure changes implementation route only after typed repair; changed target requires new version/review. Scratch proof and run/contract/task scope first; public integration follows candidate/semantic gates. Root/Tests/harness/site remain pending; global frontier pointer unchanged.
