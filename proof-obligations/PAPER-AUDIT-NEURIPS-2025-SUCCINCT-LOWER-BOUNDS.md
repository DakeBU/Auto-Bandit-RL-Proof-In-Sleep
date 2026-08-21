# Proof obligations: NeurIPS 2025 succinct lower bounds

| Leaf | Target | Dependencies searched | Route | Status |
| --- | --- | --- | --- | --- |
| `SUCCINCT-UNIT-SYSTEM-Q` | Axiom 3.1 and Definition 3.2's `Q` | `MLIB-CONVEX-LINALG`, real `sSup`, Cauchy--Schwarz | nonempty unit atom set closed under negation; bound the image by `norm X` | compiled |
| `SUCCINCT-SUPPORT-ORTHOGONALITY` | Definition 3.1 implies mutual orthogonality | `MLIB-FINSET-SUMS`, `le_csSup`, nonnegative finite sums | evaluate the correlation sum at a support atom and erase its unit diagonal term | compiled |
| `SUCCINCT-LEMMA-3-1-Q-LINF` | `Q(sum a_i E_i)=max |a_i|` | finite `sup'`, triangle inequality, signed atom witness | Appendix A.1 upper bound plus attained maximum | compiled |
| `SUCCINCT-LEMMA-3-2-R-L1` | `R(sum a_i E_i)=sum |a_i|` | Lemma 3.1, atom symmetry, finite sum algebra | prove the relevant `R` set bounded, then use the signed support sum as a witness | compiled |
| `SUCCINCT-R-CODOMAIN-DIAGNOSTIC` | expose when the global real-valued `R` set is unbounded | `BddAbove`, scalar multiples, positive real inner self-product | a nonzero vector orthogonal to all atoms gives feasible multiples with unbounded pairing | compiled |
| `SUCCINCT-LEMMAS-3-3-3-4` | strict-support minimality and uniqueness | orthogonal projection, Cauchy--Schwarz, Lemmas 3.1--3.2 | source Appendix A.3--A.4 after representation API stabilizes | planned |
| `SUCCINCT-LEMMAS-3-5-3-6` | primal/dual inequalities and dual recovery | global `R` repair plus Lemmas 3.1--3.2 | require spanning, extended-real, or span/quotient decision first | blocked |
| `SUCCINCT-THEOREM-3-8` | general two-regime minimax lower bound | Assumption 3.7 groups, same-policy history KL, testing and regret assembly | exact source construction and constants | blocked |

## Active leaf contract

- Local APIs/imports: `Mathlib.Analysis.InnerProductSpace.Basic`, real
  conditionally complete `sSup`, `Finset.sup'`, finite sums, absolute values.
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

## Verification snapshot

- `lake env lean BanditRLProof/LowerBounds/SuccinctGeometryAudit.lean`: pass.
- `lake env lean Tests/SuccinctLowerBoundPaperAuditCanary.lean`: pass.
- `lake build BanditRLProof Tests`: pass, 8,846 jobs.
- Representative theorem axiom reports: `propext`, `Classical.choice`, and
  `Quot.sound` only.
- Overall paper-audit status: partial.  The five compiled rows above do not
  promote Lemmas 3.3--3.6 or Theorem 3.8.
