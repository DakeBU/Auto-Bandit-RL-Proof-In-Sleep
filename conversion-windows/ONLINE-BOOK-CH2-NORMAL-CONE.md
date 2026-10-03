# Conversion Window: Example2.25 v1

Source card: Orabona v10 Example2.25 printed18/PDF30, fixed PDF digest in contract.
Task id: ONLINE-BOOK-CH2-NORMAL-CONE

## Source and Lean mapping

| Source symbol | Meaning | Lean declaration | Status |
| --- | --- | --- | --- |
| ι_V | zero inV, positive infinity outside | extendedIndicator V | reused public |
| ∂ι_V(x) | every global support vector | SourceSubdifferential (extendedIndicator V) x | reused public |
| N_V(x) | x∈V and all feasible displacement inner products nonpositive | SourceNormalCone V x | new frozen definition |
| intV | ambient interior, not relative interior | interior V | pinned Mathlib |
| unit ball | closed Euclidean norm≤1 | {y:E | ‖y‖≤1} | exact source |
| nonnegative ray | actual α≥0 withg=α•x | existential ray set in frozen header | exact source |

## Assumptions and quantifiers

Finite-dimensional real inner-product space explicit source terminal binder. Arbitrary nonempty convexV in first two terminals, no closed/bounded/domaininterior premise added. Indicator equality everyx, including outsideV where both sides empty; interiorzero onlyx∈intV. Unitballboundary onlynormx=1, exact α≥0 including0. Global support∀y ambient; normalcone∀y∈V. EmptyV excluded by originalnonemptypremise, not claimed harmless for unguarded improper support. No stochastic/algorithm information structure.

## Initial DAG and bounded route

Actual proper-indicator/domain/EReal API → indicator-cone equality. Actual interior ball neighborhood/inner self norm → interiorzero. Actual norm normalization/Cauchy/norm-sub-square → full unitballray. Allthree source terminals are required independent dependency-ready leaves after distinct stabilization. First selected leaf is indicator characterization; subsequent leaf bodies cannot silently edit frozen source assumptions/conclusions. Parser-only by slots unproved, not compilable evidence. No public acceptance before source body, canary, root/Tests/fullharness/axiom/nativehash/actualgraph/site/reader/committed gates.
