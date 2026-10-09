# Generic FTL exact CONTRACT review

Verdict: accepted-with-explicit-delta. All four definitions and nine exact headers are suitable for stabilization and bounded dependency-ready proving. Required repairs: none. No theorem BODY has been accepted or inferred from the successful type probes.

This is the reused distinct staged automated source reviewer /root/source_reviewer, separate from formalizer and neutral decoder. Requested Astra/medium is not runtime attestation. Prior source-model history is disclosed; no human/external or absolute-blind claim is made.

All 25 RAW rows, pinned PDF and nine normalized header hashes were independently checked before/after. The definition/context SHA is 112847a69636cd98ea1413861fa77dd5d315493f8c591893b4166080674c6db2. I personally viewed original PDF23 and PDF24 PNGs this turn and reread their text: strict-past argmin over V, followed by arbitrary feasible first-round action. The adjacent Example2.10 is not an arbitrary-loss attainment theorem. Both production and neutral probes have actual exit0 and authentic decoded stdout hashes; their #check propositions are types, not proofs. Unused binder warnings remain visible. Initial read commands guessed two filenames incorrectly; the actual manifest names were then read without file mutation.

The four definitions are faithful as an explicit conditional mathematical completion of the source display. Finite tuples model history, not finite V. minimizers includes membership separately from IsMinOn. select uses a classical choice of the minimizer SET if nonempty, otherwise none. predict time zero returns the supplied subtype initial; positive times select directly from the current strict prefix. No recursive failure state exists, so failure is not absorbing. The book does not prescribe Option, and this representation must remain an explicit source delta.

The strongest proposed equalities, select_congr and predict_prefix, are mathematically plausible for these exact definitions. EqOn of each loss on V yields equality of cumulative values at feasible points and equality of the complete minimizer sets: for points outside V both predicates are false. Rewrite that SET equality through the fixed set-based Classical.choose construction; proof irrelevance handles evidence of nonemptiness, not an unjustified equality between arbitrary minimizers. The actual chosen Option must be proved equal. Equality of only minimum values, or independent policy choices over the same set, would not suffice. No target weakening to set/value equality is approved.

At t=0, predict_none_iff is sound because the supplied feasible initial attains the zero objective, so both sides are false. select allows empty V and returns none even for empty history; predict cannot be instantiated for empty V. A full-space affine history can have no attained minimum although V is nonempty. Ties permit some arbitrary fixed selected point; identifying a supplied p requires the explicit uniqueness premise. The arbitrary X formulation generalizes Euclidean source geometry harmlessly for this relation. Real-valued source losses on V are represented by ambient extensions, and restricted-prefix equality is precisely the required invariance. No regret, gradient, convexity, compactness, existence, measurability, efficiency or executable selection claim is introduced.

## 1. BanditRL.OnlineFTLSelector.cumulative_prefix

Verdict: accepted-with-explicit-delta. Header SHA 71b72fc0bee0b002d718799e8c56c776b982aeb131a16c3c8f52617eeccc91b2.

Objects: Arbitrary X, real loss stream and point; Quantifiers: Universal loss,t,x; no premises; Assumptions: Only finite-sum algebra; Conclusion: Fin t sum equals range t sum; Constants/indexing: Exactly indices 0 through t-1; empty sum zero; Information: No current/future loss; Boundary: No minimization or regret assertion.

## 2. BanditRL.OnlineFTLSelector.select_some_spec

Verdict: accepted-with-explicit-delta. Header SHA bcd8b9078a46bd58cb2fa521adc00698bbe057fc7cb9844ff7d6b36a526dc67c.

Objects: Arbitrary X,V,finite tuple,p; Quantifiers: Success equality supplied, actual returned p; Assumptions: No attainment/uniqueness assumed separately; Conclusion: Membership AND IsMinOn produced; Constants/indexing: All n including zero; Information: Only finite history; Boundary: Empty V cannot succeed; not every tied minimizer selected.

## 3. BanditRL.OnlineFTLSelector.select_none_iff

Verdict: accepted-with-explicit-delta. Header SHA 0042ed37a64506bf69842957ed66b24b7a5089aeab135247f71d09f99e817bc4.

Objects: Same generic selector; Quantifiers: Universal V,past; negated feasible-minimum existential; Assumptions: No compactness/convexity/existence; Conclusion: none iff no feasible attained minimum; Constants/indexing: Empty prefix reduces to V nonempty; Information: No timeout or probability interpretation; Boundary: Finite history does not imply finite feasible domain; ties do not fail.

## 4. BanditRL.OnlineFTLSelector.select_congr

Verdict: accepted-with-explicit-delta. Header SHA 0b78e696ebe780a59061ab400724d81f82d8bb26c28c812a7524576e11bcc108.

Objects: Two equal-length histories, same V; Quantifiers: All per-index EqOn V, then actual Option equality; Assumptions: No uniqueness or global function equality; Conclusion: Exact chosen-point equality, not just value/set agreement; Constants/indexing: All n, empty-domain case included; Information: Off-domain observations irrelevant; Boundary: Actual set-based selector only; not arbitrary tie-breaking policies.

## 5. BanditRL.OnlineFTLSelector.select_eq_some_of_unique

Verdict: accepted-with-explicit-delta. Header SHA 5b832f27496c2167d36e070bf34e06fdf374e01758a18524e05df11015331e41.

Objects: Feasible p and arbitrary competing q in V; Quantifiers: Universal p with quantified uniqueness premise; Assumptions: Feasibility and IsMinOn and uniqueness separate; Conclusion: Actual select equals some p; Constants/indexing: Empty-history singleton case supported; Information: No future/gradient/desired regret; Boundary: Without uniqueness only success specification, not prescribed tie result.

## 6. BanditRL.OnlineFTLSelector.predict_zero

Verdict: accepted-with-explicit-delta. Header SHA 5ac4b6562e95b2da8fd0720304c347cae9f1c0af91d52871963db8f6d42c9b76.

Objects: V with supplied initial subtype; Quantifiers: Universal loss, shared feasible initial; Assumptions: Feasibility is carried by subtype; Conclusion: Exact initial value returned; Constants/indexing: t=0/source round1; Information: Ignores whole loss stream; Boundary: Empty V has no initial; not equal to independently chosen empty selector necessarily.

## 7. BanditRL.OnlineFTLSelector.predict_some_spec

Verdict: accepted-with-explicit-delta. Header SHA 0408a9a96a34adb67459e7d7be8402e0236dc89c4d6d71b1ce7550d952227562.

Objects: Actual predict and cumulative strict-prefix objective; Quantifiers: Universal t,p conditional on actual success; Assumptions: Subtype feasible initial; no desired optimality premise; Conclusion: Feasible and IsMinOn range t produced; Constants/indexing: t=0 also valid, constant-zero objective; Information: Current loss excluded; Boundary: No unconditional full successful run or performance guarantee.

## 8. BanditRL.OnlineFTLSelector.predict_none_iff

Verdict: accepted-with-explicit-delta. Header SHA 58a169edfa7bff27c956c4e028ee092ac19b0b58f822e8b32bc99cbfe2fff272.

Objects: Same actual per-prefix predictor; Quantifiers: Universal t, iff negated feasible-minimum existential; Assumptions: Only subtype feasibility; Conclusion: Exact failure/nonattainment equivalence; Constants/indexing: At t=0 both sides false; Information: Failure judged independently at each prefix; Boundary: Not absorbing Option recursion; future recovery possible.

## 9. BanditRL.OnlineFTLSelector.predict_prefix

Verdict: accepted-with-explicit-delta. Header SHA 8e78c64ecd26dadab9da1e26f0852726736b8fba18558ce0719b0681a87bb79c.

Objects: Same V,initial,t; two loss streams; Quantifiers: For every s<t, EqOn V; Assumptions: No current/future/off-domain equality or uniqueness; Conclusion: Exact Option chosen-result equality; Constants/indexing: Zero-time premise vacuous; Information: Strict-past causal functional dependence; Boundary: No different-initial or arbitrary-policy comparison.

## Allowed proof progression and remaining gates

After exact stabilization, permit only NEW BanditRLProof/OnlineFTLSelector.lean containing the frozen import/scoped context, four exact definitions and nine exact public headers with actual proofs, plus necessary explicitly identified private helpers and create-only OWN leaf evidence. First leaf select_some_spec is dependency-ready through choose_spec. select_none_iff, cumulative_prefix, select_congr and predict_zero are also ready from the definitions and retrieved finite-sum/set APIs. Prove uniqueness and prediction terminals only after their DAG parents. No public definition/type/import weakening is permitted; any semantic change requires a versioned contract review.

The planned nonconstant quadratic canary should actually prove the feasible trajectory 3/4 -> 1/4 -> 1/2 from losses centered at 1/4 then 3/4, and retain public selector/prediction values. Also require ties without an asserted specified choice, empty select domain, empty history versus supplied initialization, full-space affine nonattainment, strict current/future independence and off-domain invariance. A per-prefix recovery example may expose nonabsorbing semantics. These are requirements for a separately frozen and roundtripped NEW canary contract; no Test bodies or Test/root imports are authorized now.

This contract addresses source-model R1's generic interface gap at the specification stage only. R2/R3/R4 remain open. Complete production BODY, canary BODY, kernel/value/fence evidence, combined root/Tests/harness, reader/registry/site/pixels, FINAL/native/post-native/delivery are future gates. No shared root/reader/native acceptance/global metadata/Git changes, chapter completion, merge, deployment or main/live update is authorized. Chapter2 remains partial/null and the whole Goal ACTIVE.
