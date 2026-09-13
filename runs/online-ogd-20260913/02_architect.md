# Architect output

Exact source and semantic review: docs/contracts/online-ogd-v1/contract.md.
The first-order leaf is derived by restricting the loss to x+t(u-x), applying
ConvexOn.le_slope_of_hasDerivAt at 0 and 1, and identifying its derivative with
inner (gradient f x) (u-x). Projection uses the mathlib variational inequality.
Freeze all public definitions and headers; only bodies/helpers may change afterward.
