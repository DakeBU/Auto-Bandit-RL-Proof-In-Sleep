# Huber scalar convexity and source derivative v1

Source Example2.15, pinned Orabona v10, printed15-16/PDF27-28; same PDF hash as online-huber-derivative-v1. Four exact headers and full dependency prefix are frozen before proof work. Prerequisite huber_hasDerivAt is actually compiled in the prior run, not assumed. Import Real.Sign is an explicit context extension; old contracts stay unchanged.

Director/architect semantic review: identify the actual derivative with the clamp to [-delta,delta], deduce monotonicity and convexity of the exact source Huber function, prove its uniform absolute derivative bound, and identify the source sign expression. Quantify all real residuals and delta>=0, including delta0 and both seams. No bounded-input hypothesis or assumed convexity. Same-model GPT-6 Astra/medium sequential review.

DAG: actual derivative -> clamp identity -> monotone derivative -> convexity; clamp -> absolute bound and source sign identity. These directly feed the required vector feature pullback and unconstrained OGD endpoint. Body-only scratch window, context/header fingerprints fixed. Public integration and full acceptance gates remain mandatory; scalar closure alone is not Example2.15 completion.
