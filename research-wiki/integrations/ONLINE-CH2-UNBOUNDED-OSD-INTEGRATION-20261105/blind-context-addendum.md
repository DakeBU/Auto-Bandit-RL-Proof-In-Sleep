# Projection-context reconstruction addendum

**Finding:** the supplied signature resolves the missing existential witness contract for the projection definition. This updates that one context gap in the original review. It is not source-fidelity approval, proof verification, or an independently verified attribution to an upstream repository revision.

## Input and preserved context

The newly read file is `projection-supplement.json`, SHA-256 `6d5b372963e8ea44fc235e290ff6721ae39f6919835fb029f5194665785c199a`. It matches the supplied expected hash. The original packet was verified in the preceding review with SHA-256 `d2c9388d6e4248a2d76e3353d765c0eced4b454e368d111285744fae35ed7fe4`. The original packet and prior outputs were not reread in this follow-up. Their bindings below are the hashes recorded and verified during that review. No original source, target proof, or other maintenance input was inspected.

## Exact newly supplied signature

```lean
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
theorem exists_norm_eq_iInf_of_complete_convex {K : Set F} (ne : K.Nonempty) (h₁ : IsComplete K)
    (h₂ : Convex ℝ K) : ∀ u : F, ∃ v ∈ K, ‖u - v‖ = ⨅ w : K, ‖u - w‖
```

## Seven semantic slots

- **Objects and spaces:** F is a real inner-product space with NormedAddCommGroup F and InnerProductSpace R F. K is a subset of F. The theorem quantifies over u in F and produces v in F. The infimum is real-valued and indexed by the subtype K, whose elements are vectors together with membership in K.
- **Quantifiers:** for every K satisfying the three hypotheses, and for every u in F, there exists v in F such that both v belongs to K and the displayed norm equality holds.
- **Assumptions:** K is nonempty, complete as a subset, and convex over R. The theorem signature itself does not require CompleteSpace F or finite dimensionality. In the original project expression, the supplied ambient CompleteSpace instance and V.closed.isComplete provide the required completeness of V.carrier.
- **Conclusion:** there is v in K with norm(u-v) = inf_{w in K} norm(u-w). Thus the distance infimum is attained at a point belonging to K.
- **Constants and indexing:** there are no numerical approximation constants. The equality is exact. The index w : K ranges over every point of the carrier through subtype coercion, not over natural time, a finite sample, or a discretization.
- **Probability and feedback:** the existence and choice are deterministic mathematical specifications. No probability space, random sampling rule, feedback protocol, numerical algorithm, or efficiency guarantee is supplied.
- **Boundaries:** nonemptiness and completeness are substantive hypotheses. K need not be bounded or finite-dimensional. The statement supplies attainment, not an explicit uniqueness clause, error tolerance, computable construction, or a formula for the chosen point.

## What Classical.choose receives

Substituting K = V.carrier and u = z, the original expression supplies Classical.choose with a proof of the proposition

```lean
exists v : E, v in V.carrier /\
  norm (z - v) = infimum (fun w : V.carrier => norm (z - (w : E)))
```

This display is explanatory pseudocode. In the supplied Lean syntax, `exists v in K, P v` expands to an existential over the ambient type with membership conjoined to P v. Therefore Classical.choose returns a vector in E, not a subtype value and not a pair of proofs. Classical.choose_spec for this same existential supplies both carrier membership and the norm equality.

Consequently the original `project V z` has the nearest-point contract

1. `project V z` belongs to V.carrier.
2. Its distance from z equals the infimum of distances from z to all points of V.carrier.

Interpreting this as minimum distance uses the standard infimum property. The distance family is nonempty because K is nonempty and is bounded below by zero because norms are nonnegative. Its infimum is therefore no greater than the distance to any given w in K. The supplied equality yields norm(z-project(V,z)) <= norm(z-w) for every w in K. This is mathematical reconstruction, not a separately compiled lemma.

For the supplied fullSpace carrier, z itself is feasible. Its distance from itself is zero, so the infimum is zero by nonnegativity and the feasible zero-distance witness. The chosen point consequently satisfies norm(z-project(fullSpace,z))=0, hence project(fullSpace,z)=z. This identity follows from the supplied contract and elementary norm properties. No target theorem proof was inspected to obtain it.

## Resolution and remaining limits

The earlier statement that the projection witness's membership and minimization contract was unavailable is resolved by this supplement. The existing v1 files remain unchanged and should be read together with this addendum and the earlier count-correction addendum.

The supplement does not provide target proof terms, source identity or correspondence, elaborated signatures of every supporting declaration, general EReal arithmetic definitions, or probability and feedback assumptions. The prior limits concerning those items remain. The mathematical nearest-point statement is now readable, but no Lean compilation, theorem correctness certification, source-fidelity certification, independent upstream provenance check, or claim of numerical computability has been performed. Uniqueness is not expressly part of the new header and is not needed for the reconstructed choice contract.

## Prior-artifact bindings

- `reconstruction.md`: `59e97a09128f56b1915c003f8db5cabe03c71f04ee40ce9b3c6fe2a5013d6e2c`
- `semantic-slots.json`: `2f1326f8677d0f7aacd3890a94cbeebb8b52067332629a4d746bff98f778fe40`
- `receipt.json`: `3685b357d746b7918d8f4061e9edd2ee6a38efad5d7b9a6b93a29f54d9667414`
- `validation-addendum.json`: `c896c0a7f398308a3f7bd09c5bfa297b925af66a5a5a4eb2c0274d4f20dcf0a3`

Actor: `/root/batch41_blind_decoder`, continuing the same source-blind reconstruction role. Generic ABRL environment metadata previously disclosed remains the only extra project context. The only additional pre-existing file read in this follow-up was the authorized projection supplement.
