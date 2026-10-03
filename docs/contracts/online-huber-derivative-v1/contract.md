# Huber scalar derivative v1

Source Example2.15, Orabona v10 printed15-16/PDF27-28, SHA256 cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17 rechecked2026-10-03. Exact source absolute-value loss is retained from scalar-v2; prior seam and scalar bodies are context dependencies, not new axioms. Expanded imports are recorded in the exact prefix.

Director/architect review: freeze a reusable global derivative join and the actual Huber derivative for every delta>=0 and every real residual, including both seams and delta0. The derivative uses three intervals matching the exact source loss; conversion to the source sign expression remains required. No differentiability assumption is accepted in lieu of deriving it. Same-model sequential roles, GPT-6 Astra/medium; no independent review claim.

DAG: existing seam lemma -> global join -> inner quadratic/right affine join -> outer left affine join -> source loss identity -> actual derivative. Future monotone derivative/convexity, sign expression, feature-linear gradient and bounded-feature estimate feed the full-space causal OGD distance endpoint. These source endpoints remain required; the current derivative is not the whole Example2.15.

Body-only scratch conversion window; both headers and complete prefix fixed before proof work. Compilation and canaries yield a candidate only. Public integration, root/Tests, full harness, graph and site gates are mandatory before accepted-local.
