# Proof obligations: NeurIPS 2025 succinct lower bounds

| Leaf | Target | Dependencies searched | Route | Status |
| --- | --- | --- | --- | --- |
| `SUCCINCT-UNIT-SYSTEM-Q` | Axiom 3.1 and Definition 3.2's `Q` | `MLIB-CONVEX-LINALG`, real `sSup`, Cauchy--Schwarz | nonempty unit atom set closed under negation; bound the image by `norm X` | compiled |
| `SUCCINCT-SUPPORT-ORTHOGONALITY` | Definition 3.1 implies mutual orthogonality | `MLIB-FINSET-SUMS`, `le_csSup`, nonnegative finite sums | evaluate the correlation sum at a support atom and erase its unit diagonal term | compiled |
| `SUCCINCT-LEMMA-3-1-Q-LINF` | `Q(sum a_i E_i)=max |a_i|` | finite `sup'`, triangle inequality, signed atom witness | Appendix A.1 upper bound plus attained maximum | compiled |
| `SUCCINCT-LEMMA-3-2-R-L1` | `R(sum a_i E_i)=sum |a_i|` | Lemma 3.1, atom symmetry, finite sum algebra | prove the relevant `R` set bounded, then use the signed support sum as a witness | compiled |
| `SUCCINCT-R-CODOMAIN-DIAGNOSTIC` | expose when the global real-valued `R` set is unbounded | `BddAbove`, scalar multiples, positive real inner self-product | a nonzero vector orthogonal to all atoms gives feasible multiples with unbounded pairing | compiled |
| `SUCCINCT-DEFINITION-3-3-REPRESENTATION` | exact `s`-succinct and strict `s`-succinct representations | `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN` | package positive size, support, coefficients, exact combination equality, and coefficient nonvanishing | compiled |
| `SUCCINCT-LEMMA-3-3-UNIT-CORRELATIONS` | strict second representation forces unit correlations with the first support's sign sum | local Lemma 3.2 twice, strict coefficient positivity, finite nonnegative sum equality | follow Appendix A.3 without consuming global `R` | compiled |
| `SUCCINCT-LEMMA-3-3-BESSEL` | `s`-succinct plus strictly `z`-succinct implies `z <= s` | `MLIB-CONVEX-LINALG`, `Orthonormal.sum_inner_products_le`, sign-sum norm identity | finite Bessel inequality on the strict support | compiled |
| `SUCCINCT-LEMMA-3-4-UNIQUENESS` | two strict succinct representations have equal sizes | Lemma 3.3 in both directions | antisymmetry | compiled |
| `SUCCINCT-LEMMAS-3-5-3-6` | primal/dual inequalities and dual recovery | global `R` repair plus Lemmas 3.1--3.2 | require spanning, extended-real, or span/quotient decision first | blocked |
| `SUCCINCT-THEOREM-3-8` | general two-regime minimax lower bound | Assumption 3.7 groups, same-policy history KL, testing and regret assembly | exact source construction and constants | blocked |

## Active leaf contract

- Local APIs/imports: `Mathlib.Analysis.InnerProductSpace.Basic`,
  `Mathlib.Analysis.InnerProductSpace.Orthonormal`, real conditionally complete
  `sSup`, `Finset.sup'`, finite sums, absolute values.
- Intended route: preserve the possibly infinite atom set and the paper's exact
  support supremum; prove boundedness wherever `sSup` is consumed.
- Hidden regularity: the source's displayed real supremum presupposes
  boundedness.  Atom nonemptiness and negation closure alone do not imply it
  for global `R`.
- Failure policy: do not replace `U` by a finite standard basis, assume it
  spans `V`, or convert an unbounded real `sSup` into a valid dual norm without
  recording the additional contract.
- Mathlib candidacy: the resulting declarations are paper-specific wrappers;
  generic `sSup` and inner-product facts already belong to Mathlib.

### Active Lemma-3.3 leaf contract

- Representation leaf: exact equality to `supportCombination`, `0 < s`, and
  pointwise coefficient nonvanishing for the strict predicate.
- Equality leaf: use `sourceR_supportCombination_eq` for each local succinct
  combination; do not infer a global norm law for `sourceR`.
- Geometric leaf: derive `Orthonormal ℝ basis` from
  `inner_basis_basis`, prove the sign-sum squared norm is `s`, and apply
  `Orthonormal.sum_inner_products_le` to the second support.
- Terminal leaf: export source-shaped Lemmas 3.3 and 3.4 with distinct support
  families and explicit size positivity.

## Verification snapshot

- `lake env lean BanditRLProof/LowerBounds/SuccinctGeometryAudit.lean`: pass.
- `lake env lean Tests/SuccinctLowerBoundPaperAuditCanary.lean`: pass.
- `lake build BanditRLProof Tests`: pass, 8,846 jobs in the current extension
  worktree.
- Definition 3.3 and Lemmas 3.3--3.4 add 18 named declarations, taking this
  module from 36 to 54 declarations in the refreshed local index.
- Representative theorem axiom reports: `propext`, `Classical.choice`, and
  `Quot.sound` only.
- Overall paper-audit status: partial.  The nine compiled rows above do not
  promote Lemmas 3.5--3.6 or Theorem 3.8.
