# Norm-bound attempt repair

norm-bound01 failed because the newly introduced NNReal notation needed its explicit scope and field_simp had already solved the scaling identity before an extra ring tactic. Error recovery sorryAx is rejected. Add only the notation scope to the leaf context and remove the redundant body tactic. Header and mathematical terminal unchanged; record the exact standalone context.

norm-bound02 exposed the actual LipschitzOnWith.dist_le_mul API: points are explicit arguments before their membership proofs. Correct the call to z,hz,x,hx; original error retained. No terminal changes.

norm-bound03 used the wrong multiplication-order API name. Actual pinned le_of_mul_le_mul_left accepts the multiplied inequality and positive factor. Replace that last body step; mathematical norm-bound statement unchanged.
