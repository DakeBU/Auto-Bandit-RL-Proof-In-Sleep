# Batch25 private reader-text review, stage 4

Reviewer: `/root/batch25_source_reviewer`. This stage follows the sealed source, semantic and implementation reviews. **Draft v1 requires correction; successor draft v2 is accepted for bounded reader text, formulas, source attribution and field-preserving projection.** This is not a rendered-page, publication, main-merge or live-site verdict.

Exact reviewed drafts:

- v1: `batch25-reader-draft-v1/draft.json`, SHA256 `2a30d40275a3793767336964a893aba757ab892259a519ff7ca4246b58cdf626`.
- v2: `batch25-reader-draft-v2/draft.json`, SHA256 `5208b7ce8df1295dbf05d23d2d4d7e627c7e0d60bf0ee0027dbe9710a10e01e8`.

Canonical comparison is clean `repository`, main `b4205fcf445d387f8226c0d763aac70afb189f98`. The review read the four new highlights, complete new source card, changed stochastic-notation paragraph, chapter updates, the current generator provenance-label branch, and the original/current publication field-disposition ledger. An independent script compared the proposed reader/chapter objects against current canonical JSON. All current objects outside the reported paths compare identically; their unchanged historical content was not treated as new claims requiring a fresh whole-page mathematical audit here.

## Findings in v1 and verified resolution in v2

**R1, required source-attribution correction.** The new card lacked `statement_provenance`. At `website/scripts/build_site.py:1831`, omission defaults to `source-restatement`, which renders the label “Source theorem · faithful restatement” and prose asserting an original statement at the source location. That would incorrectly present the composite derived stochastic result as printed source material, despite the accurate relationship paragraph. V2 adds `statement_provenance: derived-support`. The inspected renderer branch will therefore choose “Derived library result” and explicitly say this displayed statement is not printed there as-is. This is a static rendering-rule check, not an observed rendered-page check.

**R2, boundary scope clarification.** The preserved chapter gap said “no unconditional meanPredict limit producer,” which was too broad beside the newly established IID expected-excess zero limit. V2 specifies “no unconditional deterministic comparator-wise ordinary-limit producer for meanPredict.” This keeps the existing adversarial no-regret gap distinct from the new stochastic result.

V1 remained byte-unchanged after the findings. V2 changes only these two content locations relative to v1; the extra timestamp/supersedes/correction metadata preserve the review history. The four highlights and all old source cards remain identical between draft versions. No unresolved blocking text finding remains in v2.

## Mathematical text and formula review

The new source card visibly distinguishes the source context, derived statements and actual learner. Its formulas define A_T as expected cumulative squared loss, the fixed expected-loss minimum over deterministic u in [0,1], and excess A_T-Tv. The minimization is outside expectation. The mean, variance and positive-horizon conventions are explicit in the adjacent contract. Real sInf versus attained minimum is justified by the reviewed `expected_fixed_prefix_minimum` producer, rather than by the definition name alone.

The wording that the fixed comparator chooses a deterministic u before taking expectation is correct: u is constant across outcomes and times, and expected loss is then optimized over such u. It does not say to take a pathwise minimum before expectation. The explicit displayed inf/min formula and the separate hindsight regret formula remove that possible ambiguity.

All four new highlight statements match the sealed anchors:

1. **Centered total adapter:** arbitrary signed total and c; little-o iff centered average tends to zero. The text correctly excludes a hidden A0=0/c=0 condition and distinguishes eventual positive normalization from a zero-horizon identity.
2. **Randomized policy criterion:** all-horizon nonnegativity plus the two equivalences. The policy is jointly measurable in one whole-process-independent seed and the strict finite history; feasibility quantifies every seed on every legal history. The whole process and policy are fixed before horizons. Cesaro expected MSE is distinguished from per-time L2 convergence. A persistent bit can fail, so no all-policy success is asserted.
3. **Mean learner upper bound:** exact half initialization and strict-past averaging, positive T, measurable common-law a.s. support. Dependence is allowed; the result is only an upper bound. The correlated negative-excess diagnostic is consistent with the proof and prevents deriving a lower bound or zero limit from S003 alone.
4. **Actual IID success:** the concrete mean learner receives no population law, mean or horizon as input. IID supplies the separate causal lower bound; the pathwise source supplies the upper. The displayed inequality is qualified by T>0, and both ordinary zero normalized expected excess and signed little-o are asserted. The text does not confuse these expected quantities with realized pathwise limits or the adversarial one-sided NoRegret predicate.

The proof prose supplies a connected mathematical argument rather than only an inventory: finite risk sum-of-squares identity -> positive-horizon normalization -> policy iff; and pathwise comparator comparison -> integrability -> expected fixed benchmark -> IID lower bound -> logarithmic envelope -> squeeze -> little-o. It preserves source Eq. (1.1)/(1.2) and the complete Theorem 1.3 proof range through printed p6/PDF18. The displayed pathwise and expected regrets remain different objects.

The new card's attributed source is Orabona arXiv:1912.13213v10, printed pp1–2 and4–6/PDF13–14 and16–18. It explicitly calls the seed criterion/Cesaro characterization and stochastic upper/success applications derived results, not additional numbered source theorems. The generic algebraic adapter is separately described as an extension. The statement_provenance correction makes this distinction operative in the generator too.

Every listed dependency in the four highlights is an actual proof-value reference from the reviewed compiled graph. These lists select substantive mathematical parents; they do not claim to enumerate every type constant or bookkeeping reference. The reader does not misidentify the separately available sharp-initial/refined lemmas as direct dependencies of S003. Exact folded signatures/proofs and current graph expansion still need inspection after actual production integration and rendering.

## Current-data preservation and original history

The independent comparison outputs are `stage4-v1-preservation-check.json` and `stage4-v2-preservation-check.json`, produced by `check_reader_draft.py`.

- The current reader has 15 source cards. All 15 are an exactly equal prefix of both draft source-card arrays, followed by one new card. No stale ancestor reader replaces the accepted current object.
- The five current `teaching_route` declaration references are unchanged: `lemma_1_2`, `theorem_1_3`, `meanPredict_noRegret`, `iid_meanPredict_excess`, and `ftlState_eq_predict`, all in `BanditRL.OnlineLearning`. This certifies the five source references, not five actually rendered previews.
- Current highlights contain 383 occurrences. The four proposed names are disjoint from all current names. The draft provides an append fragment, not an assembled highlights file, so final preservation of all 383 occurrences and the resulting total 387 must be checked after the root applies it.
- Relative to current main, v2 reader changes only `notation[2].meaning` and the appended source card. V2 chapter changes only the new production module glob, stochastic gap `open_gaps[4]`, and the clarified deterministic gap `open_gaps[1]`.
- The existing worked example, algorithm, proof bridge, primary source metadata, teaching route and old source cards are unchanged.
- The publication field ledger retains original values and historical owner statuses. Its source_theorems field has 14 original-head cards and 15 current-main cards. The “sixteen original card leaves” scope is not a claim of sixteen old cards. Historical main6847/PR195-unmerged prose remains in the history ledger and is absent from the proposed current reader content.

## Status boundary

V2 is still a private reviewed projection. Its prospective compiled local-status label is supported at this review stage by the root-run exact-original private probe inspected in stage 3; it is not evidence that the page or declarations were already installed on canonical main. Full integration, imported-module/project gates, exact production JSON comparison, renderer math/Lean adjacency, visual layout, generated graph links, final publication and live checks belong to later evidence.

No user-facing sourcecard, highlight, chapter, generated output or Git state was modified by this reviewer. This review accepts the bounded revised text and preserves the stage-2 explicit mathematical deltas. It gives no entire-PR closure, chapter completion, merge or ref-retirement authorization.


---
Public location projection of private evidence batch25-source-review-v1/stage4-reader-text-review.md. Original SHA256: `c98fd5c264a9edb7229384e0ea224f7d160bbb2964c24b59b6b2b81403fe8b50`. Physical paths alone are logicalized; original stage wording and limits remain unchanged. Later bounded status is recorded in review-binding.json.
