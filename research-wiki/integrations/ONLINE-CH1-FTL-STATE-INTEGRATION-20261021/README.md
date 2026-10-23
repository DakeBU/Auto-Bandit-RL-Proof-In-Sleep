# Recursive Follow-the-Leader state integration

This candidate adds three definitions and eight proofs from PR #189 to the shared library. For initialization c and observations y, the state starts at (0,c), then updates (n,m) to (n+1,m+(y(n)-m)/(n+1)). Its proved invariant is (t,ftlPredict(c,y,t)). The first observation cancels c, and later steps use the existing empirical-mean recurrence.

The source is Francesco Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*, arXiv:1912.13213v10, Chapter 1, printed pages 3-6 (PDF pages 15-18). Page 3 permits an arbitrary feasible first prediction. Theorem 1.3 uses one half. The running-summary paragraph motivates the operational representation but does not print this recurrence or prove a machine-cost bound.

`statement-map.json` preserves the exact new interfaces. `semantic-review.json` records the independent blind reconstruction and source comparison, including all assumptions and derived-result classifications. `source-inventory.json` and `source-topology.json` preserve the source-only extraction, with the later Stage A acceptance bound separately. These source edges must not be displayed as compiled proof dependencies.

The reader delta adds the state family, nine explanatory notes (including the already accepted empirical-mean recurrence), and a proof bridge to the existing half-initialized route. All six canaries and the source-range hook are retained. The recursive definition must display both its zero and successor equations; raw-file and block hashes fail closed if that disclosure becomes stale.

`retained-obligations.json` preserves the original scope and unresolved provenance. All 860 original changed paths remain recoverable, including historical failures and foreign records embedded in global snapshots. Eighteen artifact-hash use sites remain OPEN. The separate PR #203 and broader chapter obligations are not discharged.

Current state: focused and combined library/Tests Lean builds passed, together with six source-boundary regressions,24 imported named type/axiom checks,19 proposition identities and16 required proof-value pairs. `compiled-dependencies.json` records actual compiled dependencies. `historical-publication.json` maps all16 original publication objects, including four featured flags already accepted on main. Full harness, final public projection, rendered reader, CI, merge and deployment acceptance remain pending. This packet authorizes neither original PR closure nor branch retirement.
