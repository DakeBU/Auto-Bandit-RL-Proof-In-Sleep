# Huber scalar source representation v1

Source: Orabona v10 Example 2.15, printed pp.15-16/PDF pp.27-28, pinned PDF SHA-256 cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. This bounded prerequisite uses the exact scalar loss r^2/2 for |r|<=delta and delta*(|r|-delta/2) otherwise.

Director/architect review (same GPT-6 Astra/medium): freeze the definition prefix and two headers before bodies. The three-piece representation keeps both boundary equalities, assumes only delta>=0, and is designed to connect the existing seam candidate to the two Huber thresholds. The zero-threshold identity separately records the degenerate constant loss. No derivative, convexity or algorithm guarantee is assumed or claimed by these algebraic terminals. Delta<0 is outside the convex-loss interpretation; the definition itself is total.

DAG: source absolute-value definition -> three-piece identity and zero-threshold identity -> future scalar derivative joining -> convexity/vector gradient/feature bound -> actual unconstrained fixed-step OGD endpoint. The latter targets remain draft; these are reusable prerequisites, not Example2.15 completion. Conversion window is body-only in the scratch file with the exact prefix preserved. Native fences supplement actual compilation, and do not substitute for it. Public integration and complete project gates remain required.
