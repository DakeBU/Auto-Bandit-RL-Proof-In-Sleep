# Independent source review: closed and proper functions

Verdict: **accepted-with-explicit-delta**.

Actor: `/root/source_reviewer`, distinct from the formalizer and `/root/closed_blind`. Requested review configuration: GPT-6 Astra, medium reasoning. Date: 2026-10-03. I independently searched for mismatches in the actual definitions and three public targets before reading the new blind reconstruction. No previous closed/proper candidate review or acceptance verdict was read as evidence. This is a semantic review; no compilation, integration, publication, or Chapter 2 completion is certified here.

## Read inventory and frozen bytes

Repository: `E:/ABRL/worktrees/research-online-book`; inspected branch `codex/research-online-closed-proper`; HEAD `0b049d54d2f734809813a62b2690c3a137bd3f5d`. The working tree was dirty, including website and registry-test changes. Hashes below identify the reviewed bytes, rather than assuming all files are represented by HEAD.

- `.agents/skills/bandit-semantic-roundtrip/SKILL.md`: role and seven-slot requirements, read earlier in this actor's current session.
- `README.md`: repository orientation, read earlier in this actor's current session.
- `BanditRLProof/OnlineClosedProper.lean`: complete file, two definitions, three statements and proof bodies. SHA256 `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6`.
- `BanditRLProof/OnlineConvexExtended.lean`: opening scoped context and actual `extendedIndicator` definition, lines 1–28. Containing-file SHA256 `fec3efd071a069050593babb9eafee7262684b477b58ce8f045fe18c1add5d0f`.
- `.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean`: header/scoped context and the open strict-superlevel / closed sublevel characterizations, especially lines 175–203. Containing-file SHA256 `b9f72ca970c076ce6d466a3f0efd05306c4f9dc0df6e7eb52329e66414410065`.
- `runs/online-closed-proper-20261003/blind-reconstruction.md`: entire newly written reconstruction by `/root/closed_blind`. SHA256 `bfea5838ff89e35d7f806f188ebac62df2f0488d6a2a361d53399435cc77ad51`.
- `website/content/readings.json`: current `online-closed-proper` entry. Containing-file SHA256 `880c3b049b2c95cc8e2d56764fd774de50f01c318c18a921c9a507184c56f02d`.
- Source PDF: `E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf`, Orabona arXiv:1912.13213v10. SHA256 freshly recomputed as `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`, matching the pinned source.
- Physical PDF page 28 was freshly extracted directly from that PDF with `pdftotext`. Reviewed Definition 2.16, its following lower-semicontinuity note, Example 2.17, Definition 2.18, and Example 2.19, all printed page 16. No secondary description substituted for the source page.

## Direct source-to-target checks

Definition 2.16 defines closedness using all real sublevel thresholds for an extended-real function on Euclidean space. `SourceClosed` preserves exactly those threshold quantifiers and both infinite function values. It does not silently define closedness as lower semicontinuity and then prove a tautological equivalence: the source-style sublevel predicate is separately defined and bridged to Mathlib's topological predicate.

The following source note states the equivalence in Euclidean spaces and more generally Hausdorff spaces. `sourceClosed_iff_lowerSemicontinuous` extends it to arbitrary topological domains. This removes a source scope condition, rather than adding a restriction. The proof genuinely needs no Hausdorff premise: complements of closed real cuts give open strict real superlevels; the strict superlevel above negative infinity is the union of all those real superlevels; the strict superlevel above positive infinity is empty. Conversely, the library characterization directly gives every real closed cut. The inspected Mathlib characterization uses precisely this strict-superlevel meaning of lower semicontinuity.

Example 2.17 is `sourceClosed_indicator_iff`. The reused indicator is exactly zero on V and positive infinity outside; it is not the ordinary zero-outside or 0/1 indicator. For real r<0 its sublevel is empty, and for r>=0 its sublevel is V. The cut at zero recovers V. No convexity, nonemptiness, or properness is required.

Definition 2.18 is `SourceProper`: a conjunction of nowhere negative infinity and a finite-value witness `exists x, exists r : real, f x = r`. The second conjunct excludes the everywhere-positive-infinity case. It does not replace finite somewhere by merely not being everywhere positive infinity while permitting negative infinity.

Example 2.19 is `sourceProper_indicator_iff`. The indicator never equals negative infinity, and finite values occur exactly on V, at value zero. Consequently properness is equivalent to nonemptiness of V, independently of closedness or convexity.

## Seven semantic slots

| Slot | Finding |
| --- | --- |
| 1. Objects and spaces | Source functions use Euclidean domains; the semicontinuity note mentions Hausdorff spaces. Lean permits arbitrary topological domains, including empty and non-Hausdorff spaces. This mathematically valid generalization must remain explicit. Properness and its indicator equivalence are actually set-theoretic; no metric or vector-space operation enters their content. |
| 2. Quantifiers/order | `SourceClosed` quantifies over every finite real r, not just nonnegative r or finite values of f. `SourceProper` separately quantifies universally over all x to exclude bottom, then existentially over x and real r for finiteness. The three equivalences apply to every f or set V. No implicit nonempty domain or feasible-set premise appears. |
| 3. Assumptions/regularity | No convexity, properness, continuity, separation, boundedness, or finiteness assumption is introduced into the closedness theorem. Closedness of V is the exact equivalent condition in Example 2.17; nonemptiness is the exact equivalent condition in Example 2.19. The source's later interest in convex proper functions is motivation, not a hidden hypothesis for these claims. |
| 4. Conclusion/metric | Each target is a bidirectional logical equivalence, not just a sufficient condition. Lower semicontinuity has the standard open strict-superlevel interpretation verified against the imported API. No algorithm, regret, minimizer, subgradient existence, or optimization convergence is claimed. |
| 5. Constants/normalization | The indicator uses 0 and positive infinity with no finite penalty surrogate. The threshold at 0 is included and recovers V. Real coercion into EReal is explicit. There are no rate constants or asymptotic quantifiers. |
| 6. Probability/feedback | Entirely deterministic topological/set-theoretic statements; no probability, expectation, information-access, filtration, or stopping semantics are present or needed. |
| 7. Boundaries/exclusions | Both infinite function values are retained by closedness. Constant positive- and negative-infinity functions are closed. Both fail properness; on empty domains the finite-witness condition fails. The empty set indicator is closed but not proper. A nonempty nonclosed set may have a proper indicator without a closed indicator. No implication from closed to proper or proper to closed is introduced. |

## All five targets and their status

| Target | Status |
| --- | --- |
| Definition `SourceClosed` | Literal source real-cut condition, with explicit arbitrary-topology extension of the domain. |
| Definition `SourceProper` | Literal nowhere-bottom / finite-somewhere conjunction; preserves both required conditions. |
| `sourceClosed_iff_lowerSemicontinuous` | Accepted with the explicit extension beyond the source Euclidean/Hausdorff scope. Infinite thresholds are derived correctly from real cuts. |
| `sourceClosed_indicator_iff` | Accepted with the same domain generalization. Both implications hold for all sets, including empty. |
| `sourceProper_indicator_iff` | Accepted with the same generalized ambient scope; mathematical content needs no topology. Empty-set and empty-domain behavior is correct. |

The new blind reconstruction accurately identifies these quantifiers and boundary cases. Its stated caveat that the imported lower-semicontinuity predicate had not been inspected is resolved here by inspecting the actual Mathlib equivalence. Its negative-infinity sublevel intersection explanation and the Lean proof's complementary strict-superlevel union explanation are mathematically equivalent.

## Reader assessment, repairs, and verdict boundary

The inspected reader explicitly says that the arbitrary topological domain is a generalization of the source Euclidean domain and that no Hausdorff premise is needed. Its real-cut explanation, derived infinite threshold, zero/top indicator, and separate properness conditions are accurate. The reader does not claim that these definitions prove a subgradient theorem or complete Chapter 2. Its compiled-status label is outside this semantic review's validation scope.

Minor exposition caveat, not a theorem defect: the worked example says the constant-negative-infinity function fails the nowhere-bottom condition. That reason assumes an inhabited domain, as in the source Euclidean setting and the neighboring real-interval example. On an empty generalized domain, properness still fails, but due to the absent finite witness. Specifying that this worked example is on the real line would remove the implicit contextual assumption; the mathematical conclusion is unchanged.

Required Lean repairs: **none**. No blocking reader repair is required for the source Euclidean interpretation; the worked-example clarification above is recommended for the generalized-domain presentation. The acceptance record must preserve the explicit domain generalization and must not attribute the full arbitrary-topology scope as a literal printed source claim. No historical review, compiler result, or later changed file is certified by this receipt.

## Subsequent reader-only receipt, 2026-10-03

The same independent actor reread the complete current `online-closed-proper` entry after the reader clarification and proof-flow addition. New containing-file SHA256 for `website/content/readings.json`: `069bc12fac88b44ef938c574552e694d87b8522c858ab8c86dbfd5d6558271fe`. The earlier snapshot and its hash `880c3b049b2c95cc8e2d56764fd774de50f01c318c18a921c9a507184c56f02d` remain preserved above; this receipt extends the reader review to the new bytes rather than retroactively replacing that earlier binding.

The worked-example introduction now explicitly places the examples on the real line. This resolves the inhabited-domain exposition caveat: a constant-negative-infinity function there does fail the nowhere-bottom condition. The newly added `algorithm` object is labelled "Definitions and proof flow" / "foundational equivalences" and accurately summarizes the existing bridge: complement real sublevels and recover the infinite strict threshold by a union; compute indicator sublevels; separate finite witnesses from closedness. It introduces no algorithmic or regret guarantee and changes no mathematical target.

Fresh hashes of `OnlineClosedProper.lean` and `OnlineConvexExtended.lean` equal the previously bound values, respectively `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` and `fec3efd071a069050593babb9eafee7262684b477b58ce8f045fe18c1add5d0f`. No new Lean review was necessary for these unchanged bytes. The semantic verdict remains **accepted-with-explicit-delta**, specifically the openly stated arbitrary-topology generalization. Required remaining reader or Lean repairs: **none**. Compiler and test results reported by other actors are not independently certified by this semantic receipt.
