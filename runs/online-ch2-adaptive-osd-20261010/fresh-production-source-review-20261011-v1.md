# Fresh production source/BODY review, 2026-10-11 v1

**Verdict: accepted-with-explicit-delta.** No blocking mathematical or source-body mismatch found in the complete three production modules. Scope is production semantic/BODY review and separately reviewed mathematical minimum/infimum repair only.

Actor `/root/adaptive_reviewer`, distinct from historical root formalizer, current canary formalizer `/root/adaptive_formalizer`, and staged decoder `/root/osd_blind`. Requested GPT-6 Astra / medium; no independent runtime model/effort attestation. Fresh anti-anchored internal automated review, not human/external review. Source cards refer to old outcomes, but no old verdict report was opened. Historical decoder reused-context and incidental source-named API exposure disclosures are retained; no absolute-blindness claim.

Workspace `E:/ABRL/worktrees/research-online-book`, branch `codex/research-online-ch2-adaptive-osd`, HEAD `0283616c8439b09fc49d5e35373ff74aa11371cc`; canonical source `E:/ABRL/research`, shared Git store `E:/ABRL/research/.git`. Target production modules and current packet are untracked at acquisition. No input mutation or commit; checkout retained. Parent handles fetch/integration.

Pinned Orabona arXiv1912.13213v10 PDF SHA256 `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` verified. Personally viewed complete existing images of printed13/PDF25, printed14/PDF26, printed39/PDF51, printed40/PDF52: Theorem2.13 proof, Eq4.3/4.4 and Theorem4.14. Existing PNGs inspected, not freshly rendered in this turn.

General terminal: `regret <= (1/(2alpha)+alpha) D sqrt(S_T) - norm(X_T-u)^2 sqrt(S_T)/(2alphaD)`. X_T is source x_(T+1); S_T is actual selected squared-norm sum from the same recursion.

## Seven semantic slots

1. **Objects and spaces: accepted-with-explicit-delta.** Potential is deterministic real-sequence algebra, not actual OSD. OSD uses finite-dimensional real inner-product E, the shared nonempty closed convex Domain and actual nearest projection; this realizes Euclidean source coordinates. EReal losses are proper with global source supports; finiteness at played and comparator points is produced before real-loss interpretation. Four benchmark leaves are scalar; the fifth is a same-run performance conjunction.

2. **Quantifiers and order: accepted.** Performance covers every T in Nat and every feasible fixed u with identical V/alpha/D/loss/x1/p throughout. Horizon and comparator are absent from recursion. Potential alone requires T>0; regret_bound splits T=0 before using it. No existential future schedule or exogenous trace is assumed.

3. **Assumptions and regularity: accepted-with-explicit-delta.** General regret_bound has sufficient proper/global-support assumptions without separate convexity. Four source wrappers and the final benchmark conjunction retain explicit IsConvexExtended, defined by the real epigraph. Geometry is in Domain; pairwise norm<=D does not assume a maximizing pair. alpha>0,D>=0; no positive energy, bounded gradient or Lipschitz assumption. LegalFeedback is actual selected global support membership, never the desired bound. oracle_feedback and canonical_feedback construct it from regularity, actual feasibility and shared canonicalPolicy_legal.

4. **Conclusion and metric: accepted-with-explicit-delta.** Cumulative fixed-comparator real loss difference; no expectation, averaging, absolute value or best-rerun objective. General endpoint retains -(norm(output T-u)^2 sqrt(energy T))/(2 alpha D). Potential retains signed -a T*w(T-1) with no terminal bound or positivity assumption. Source specializations legitimately drop a nonnegative subtrahend. Benchmark conjunction keeps performance alongside the repaired equality.

5. **Constants and normalization: accepted.** Source 1..T maps to Lean0..<T; terminal x_(T+1) is output T. energy T=sum selected squared norms of exactly those T updates; eta uses inclusive t+1 energy. Coefficient1/(2alpha)+alpha gives3/2 at alpha1 and sqrt2 at alpha=sqrt2/2. The weighted potential uses sqrt(inclusive energy)/(2alphaD). PDF26 already contains norm(x_(t+1)-u)^2/2 outside inverse-step parentheses; no missing-half erratum exists.

6. **Probability feedback and information: accepted-with-explicit-delta.** Deterministic pathwise full information. state_prefix proves strict-past state dependence for fixed p,V,alpha,D,x1 and equality of whole past functions. Current output exists before p sees current full loss; selected and eta may depend on that current loss. Parameters/policy closure are not certified exogenous if reselected with future information. No probabilistic law, measurability or executable oracle claim. Benchmark varies scalar eta holding actual realized energy fixed, not rerunning learners.

7. **Boundary and excluded regimes: accepted-with-explicit-delta.** T0, D0, leading/all-zero energy and zero support after positive energy remain covered. D0 forces singleton feasible outputs and regret/terminal norm zero, but not zero ambient supports. Zero actual support skips update and implies gap<=0, not equal losses or constant function. Total division at zero is an observer convention, not a positive step. Potential T0 excluded explicitly. Benchmark has unique positive minimizer iff D,S positive, every eta positive at both-zero, and no attained minimum at exactly one zero.

## Complete BODY review

- **OnlineAdaptivePotential.lean: accepted-with-explicit-delta.** Whole BODY uses Finset.sum_range_by_parts and telescoping with nonnegative increments, played upper bounds and initial nonpositive residual. Terminal sign is unchanged. It is an algebraic generalization of the source proof with zero weights, not all of Theorem2.13.

- **OnlineAdaptiveOSD.lean: accepted-with-explicit-delta.** Every definition and BODY read. Joint Nat.rec stores actual history and energy; prefix induction, energy identities, feasibility and finite-loss adapters derive from it. Zero support uses lawful global support; nonzero branch uses shared lemma_2_31 and divides only after positive eta/energy. regret_bound splits T0/D0, applies weighted potential to actual distances and monotone sqrt energy, applies prefix-norm bound to actual selected sequence, and preserves terminal subtraction. Source wrappers/canonical variants preserve the very same run. No desired-bound premise.

- **OnlineAdaptiveBenchmark.lean: accepted-with-explicit-delta.** Whole BODY read. IsGLB lower/greatestness proof treats all coefficient branches with concrete witnesses. source_benchmark_value supplies eta1 nonempty witness and csInf_eq rather than junk total infimum. Strict-decrease lemmas rule out mixed-zero attainment; positive minimum includes admissibility/value/lower-bound/unique equality. Last conjunction consumes same-run source performance plus actual energy nonnegativity.

## Separate mathematical repair

Separate repair accepted: for all D,S>=0 use inf_(eta>0)[D^2/(2eta)+eta*S/2]=D*sqrt(S), retain exact attainment classification. D>0,S0 gives positive D^2/(2eta), strictly reduced by doubling eta; D0,S>0 gives positive eta*S/2, reduced by halving eta. Both source-compatible: constant losses on nontrivial bounded domain; nonzero affine ambient support on singleton domain. Bothzero every positive eta attains0. Positive pair has unique eta=D/sqrt(S). Literal printed attained min over all regimes is rejected. Keep original source unchanged and repair separate; do not remove zero cases or add D/S positivity to full regret. No author endorsement/published erratum claimed.

The old missing-/2 allegation is independently rejected from original PDF26 pixels. Moving that factor into w=1/(2eta) is algebra, not correction. This is separate from the actual benchmark attainment issue.

## Evidence limits and actions

Compared the neutral potential, algorithm, prefix, bootstrap, actual-step, specialization-v2 and benchmark decoder reconstructions against current complete statements. They agree, but header-only reports are not proof evidence. All three complete target BODYs were inspected independently; shared API reads establish reused mechanisms, not a fresh transitive kernel/dependency audit. No canary, root proposal, public/axiom/VALUE evidence, native lifecycle, compiler, reader/site or old verdict review is claimed here.

- **P1 (integration-documentation)**: Add dated superseding frontier for stale historical draft no-production/BODY-not-yet prose, preserving frozen contracts. Parent has indicated additive update planned. No production math defect.

- **P2 (mandatory-disclosure)**: Keep min-versus-infimum repair and exact attainment classification explicit beside source/Lean statement. Never certify literal min in mixed-zero regimes.

- **P3 (remaining-validation)**: Fresh canary/public/axiom/VALUE/root/reader/site/native/package gates remain separate. This receipt does not accept chapter/book/merge/deployment.

## Raw byte binding

Production/PDF hashes were captured with first full acquisition and checked here. Auxiliary hashes bracket receipt finalization, not an asserted earlier snapshot. JSON lists before/after SHA256 over raw bytes, without normalization. All match.

- `BanditRLProof/OnlineAdaptivePotential.lean`: `7b8a515dbc2f681ff2c230faa81c132665dd89b2e78d6973c1e6821151f55709`

- `BanditRLProof/OnlineAdaptiveOSD.lean`: `197f1f6460168daafe23f4a8017f2c11b54566e0f7749da77bd031d4ab7babef`

- `BanditRLProof/OnlineAdaptiveBenchmark.lean`: `a734ad7f4d91291ad20b60266dcd5e311b22048a15063b0ea59a32f95f7f92eb`

- `../research-online-ogd/tmp/pdfs/orabona-v10.pdf`: `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`
