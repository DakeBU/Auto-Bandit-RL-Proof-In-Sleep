# Body-only repairs

full-leaf01: norm_smul_inv_norm inferred a scalar field with an explicit real coercion pattern that did not match the real scalar normalized vector. Original target/snapshot/error log retained; specialize actual pinned API to 𝕜=real. No source/header/context mathematical change. Failed recovery sorryAx rejected; compile02 separately required.

full-leaf02: explicitly real scalar field still retains RCLike real-coercion syntax in the normalized-vector lemma pattern, so direct rw cannot match syntactically. Actual source/API/type audit confirms identical scalar norm identity; no mathematical contract defect. Replace only rw with simpa on the specialized identity inequality to simplify real-coercion syntax. Same normalization/Cauchy route and frozen headers; failed02 recovery sorryAx rejected.

full-leaf03 simpa simplifies the real RCLike coercion and all three unchanged source endpoints compile with standardaxioms; full-canary01 four nondegenerate geometry/source tests compilefirsttry. Failed01/02 remain rejected evidence. Public integration changes comments/imports only; no terminal weakening.
