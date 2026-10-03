# Extended-real singleton subdifferential and differentiability

Task id: `ONLINE-BOOK-CH2-SUBGRADIENT-DIFFERENTIABILITY`
Kind: `theorem`
Status: `stabilized-full-contract; proving-finite-prerequisites`
Harness: `hierarchical`

Source Orabona v10 printed17/PDF29 Theorem2.22, exact convex extended-real function finite atx, differentiable iff singleton global subdifferential with gradient identity. No extra proper/interior/closedness premise in full endpoint. SourceDifferentiableAt is a differentiable real neighborhood representative, preventing toReal from falsely treating infinite values as finite.

Version1 equivalence header was faithful but full-source coverage lacked a gradient identity declaration. Preserve initial rejection of full coverage; version2 adds explicit gradient identity for every local real representative and undergoes separate repair review. Actual native fences and assumptions/context fingerprints retained. No full theorem body exists yet.

Finite lower leaves: uniqueness at an actual differentiable interior point; singleton implies actual domain interior via supporting normal perturbation; singleton implies actual continuity via global support/convexity. Scratch-only compiler evidence, not public or source theorem acceptance. No public module has been created. Next missing boundary: support boundedness/closed-graph/compactness to derive Frechet differentiability from a singleton, and faithful forward neighborhood chain. Shared-root/public-canary/axiom/graph/harness/site/contribution gates required after actual public theorem closure. Global frontier unchanged. No chapter/book completion.

Version2 full contract accepted-with-explicit-delta by the distinct reviewer; both public source theorem bodies remain open. See draft-source-review-v2.md. Actual local representative -> neighborhood finite/interior/toReal differentiable scratch leaf also compiles.
