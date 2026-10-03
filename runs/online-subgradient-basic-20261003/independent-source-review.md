# Independent source review: basic subgradients

Verdict: **accepted-with-explicit-delta** for the reviewed mathematical packet. Reader/publication mapping is **pending and unreviewed**.

Actor: `/root/source_reviewer`, distinct from the formalizer and `/root/closed_blind`. Requested review configuration: GPT-6 Astra, medium reasoning. Date: 2026-10-03. I compared the actual source and actual Lean statements before reading the new blind reconstruction. No old packet verdict was used as evidence. This receipt does not certify compilation, integration, publication, interior subgradient existence, Theorem 2.22, or Chapter 2 completion.

## Read inventory and hashes

Repository `E:/ABRL/worktrees/research-online-book`; inspected branch `codex/research-online-subgradient-basic`; HEAD `a22aed64b4cfbe79654dedd944e5af4a00b8aeb2`. The target file was untracked, and the working tree contained public-root/test changes and new packet files. The following raw-file hashes bind the inspected content independently of HEAD.

- `BanditRLProof/OnlineSubgradientBasic.lean`: complete file, including definition and both theorem statements/proofs. SHA256 `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962`.
- `BanditRLProof/OnlineClosedProper.lean`: opening scoped context and actual reused `SourceProper` definition. Containing-file SHA256 `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6`.
- `BanditRLProof/OnlineConvexExtended.lean`: opening scoped context and actual reused `effectiveDomain` definition. Containing-file SHA256 `fec3efd071a069050593babb9eafee7262684b477b58ce8f045fe18c1add5d0f`.
- `runs/online-subgradient-basic-20261003/blind-reconstruction.md`: entire new source-blind reconstruction. SHA256 `501af105d7ccee56cb60c17d0d6a5925acab31dfad670ebfa0f41a38a2cac726`.
- Source `E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf`: SHA256 freshly computed as `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`, matching the pinned Orabona arXiv:1912.13213v10 file. Physical pages 28–29 were freshly extracted directly from that PDF with `pdftotext`, covering printed pages 16–17.
- Reviewed source anchors: Definition 2.20; its following description of the subdifferential and finite-domain inclusion; Theorem 2.21 and proof. Adjacent interior-existence prose and Theorem 2.22 were read to identify scope boundaries, not treated as proved by this packet.
- `.agents/skills/bandit-semantic-roundtrip/SKILL.md` and repository `README.md` were read earlier in this actor's current session and supply review procedure/orientation, not mathematical evidence for this new packet.

No website mapping was supplied for review in this assignment; its absence is a publication gap, not evidence against the inspected mathematical statements.

## Direct target comparison

**Definition 2.20 / `SourceSubdifferential`.** The source defines supporting vectors for a proper function using `f(y) >= f(x) + <g,y-x>` for every ambient y. The Lean definition preserves that global quantifier and direction. It is defined for every EReal-valued f without an embedded properness premise. This is a totalized definitional extension: on proper functions it agrees with the source; outside that class it must not be marketed as an unchanged source convention. At an f(x) of negative infinity every vector satisfies the inequality; the everywhere-positive-infinity function also admits every vector. These behaviors do not contaminate either theorem because the first assumes properness and the second uses globally real-valued f. The inner product is always finite, so no sum of opposite infinities occurs in the support expression.

**Finite-domain inclusion / `subgradient_point_finite`.** The source discusses emptiness of the subdifferential outside the effective domain for proper convex functions. Lean proves the implication from an individual supporting vector to effective-domain membership assuming properness alone. Convexity is unnecessary: evaluate support at the finite-value witness supplied by properness; positive infinity at x would contradict that finite value. The conclusion `f x < top` together with nowhere-bottom means genuinely finite f(x). Without properness, effectiveDomain by itself includes negative infinity; the receipt therefore does not equate effective-domain membership with finiteness for arbitrary f. The pointwise theorem implies the source's domain inclusion by unpacking existence of a supporting vector, though no separate `dom subdifferential` object is introduced.

**Theorem 2.21 / `theorem_2_21`.** The source f is globally real-valued, and so is the actual Lean f. The pointwise EReal coercion is only the adapter to the shared definition. Globally real-valued functions on E are proper automatically: no value is bottom and f(0) is a finite witness, since E has a zero vector. Thus no source properness condition is lost by the absence of an explicit `SourceProper` argument. For every x in convex V there exists a supporting vector working for every y in E. The output is only convexity of f restricted to V, not convexity outside V. The proof chooses support at the convex combination and evaluates it at the two endpoints, exactly the source proof strategy. It preserves both endpoints of the mixing interval by using nonnegative weights with sum one.

## Seven semantic slots

| Slot | Adversarial check and outcome |
| --- | --- |
| 1. Objects and spaces | Source uses finite-dimensional Euclidean vectors; Lean uses a real inner-product space with its normed additive group structure, without completeness or finite dimension. This valid generalization is explicit here and requires explicit reader attribution. EReal is appropriate for Definition 2.20; globally real f is retained in Theorem 2.21. |
| 2. Quantifiers/order | Support is `for all y in E`, not merely for y in V or in the effective domain. The theorem assumes `for all x in V, exists g, for all y in E`; a single chosen g must work for all y at each x. It is not `for all x,y, exists g` and does not require one common g for all x. No support is assumed outside V. |
| 3. Assumptions/regularity | The finite-point theorem assumes properness, not convexity; this strengthens the surrounding source observation and should be labelled as such. The convexity theorem assumes convex V and global supporting vectors at points in V, with no differentiability, closedness, interior, or smoothness premise. Those omitted assumptions are not source requirements for Theorem 2.21. |
| 4. Conclusion | First theorem gives effective-domain membership and hence finiteness under its properness premise. Second gives `ConvexOn` on V. Neither supplies supporting-vector existence from convexity, singleton subdifferentials, or equivalence with differentiability. |
| 5. Constants/normalization | Support inequality has coefficient one and displacement y-x with the correct sign. Weights a,b are nonnegative and sum to one, equivalent to source lambda and 1-lambda. No constants, error terms, or asymptotic weakening are inserted. |
| 6. Probability/feedback | Purely deterministic convex-analysis statements. No stochastic, causal-update, regret, feedback, or stopping guarantee is present. |
| 7. Boundary/exclusions | Positive infinity outside the domain is correctly ruled out at supporting points of proper functions. Negative infinity is excluded by properness. V may be empty or a singleton; global support remains potentially stronger than support restricted to a singleton. No domain-relative support convention is silently substituted. Interior existence and Theorem 2.22 remain outside the packet. |

## Blind reconstruction comparison

The new reconstruction correctly exposes the global support quantifier, extended-real definition outside proper functions, role of the finite witness, difference between effective-domain membership and unconditional finiteness, global real-valuedness in Theorem 2.21, and inner-product-space scope without completeness. It matches the actual declarations. Its uncertainty about repeated contextual `SourceProper` text in the packet is resolved by the actual files: the production file imports the existing definition; it does not redeclare it. The blind packet is contextual source material rather than an asserted independently compilable module.

## Required deltas, repairs, and publication boundary

Required Lean repairs: **none** for these targets. The acceptance record and future reader must disclose:

1. The extension from Euclidean spaces to arbitrary real inner-product spaces; this is not a general Banach-space/dual-functional theorem and does not require completeness.
2. The definition's availability for arbitrary EReal functions beyond the source proper-function convention, with properness or real-valuedness restoring the source regime in consumers.
3. The strengthened finite-point/domain-inclusion consequence, whose proof does not need convexity.
4. Global support for every ambient y despite the convexity conclusion being restricted to V.
5. Interior subgradient existence, the differentiability/singleton equivalence in Theorem 2.22, subsequent source results, and full Chapter 2 completion remain unproved by this packet.

The mathematical verdict is **accepted-with-explicit-delta**. Reader mapping is pending: this report cannot approve wording or provenance that has not yet been written and inspected. Compilation and broader acceptance evidence must be separately verified.

## Subsequent reader-only receipt, 2026-10-03

The same independent source-review actor has now read the complete `online-subgradient-basic` entry in `website/content/readings.json`. Containing-file SHA256: `32c3093c5ea85473718f3c5cb1793a27e1285090bc33fd3c52579cb6ccd5bc15`. This receipt resolves the original pending-reader status for precisely these bytes and preserves the earlier source/Lean review above. Freshly computed SHA256 of `OnlineSubgradientBasic.lean` remains `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962`, so its inspected mathematical target is unchanged.

The reader correctly states the total support predicate's extension beyond proper functions, the Euclidean-to-normed-real-inner-product-space extension, and the fact that domain inclusion needs no convexity hypothesis. Its contract keeps support global in y, while Theorem 2.21 retains globally real-valued f and concludes only convexity on V. It distinguishes properness from effective-domain membership and says why their combination yields a finite value. It does not claim completeness, a general Banach-space dual result, interior existence, or a converse to Theorem 2.21. Its generic later-results boundary does not discharge Theorem 2.22; that theorem remains outside this receipt.

The three-step proof flow and proof bridge match the actual arguments: contradict the finite witness if a supporting point has positive-infinite value; choose support at a convex combination in V; cancel the weighted linear terms. The displayed support-domain implication is read under the adjacent explicit properness contract, and the displayed convexity implication is read under the adjacent convex-V/global-real-f contract. No extra hypothesis is hidden by those display abbreviations.

The real-line examples are mathematically correct. The identity `y^2-x^2-2x(y-x)=(y-x)^2` supplies global quadratic support and hence Theorem 2.21 gives convexity. At 2, the indicator of [0,1] has positive-infinite value while being proper, so all supporting vectors are excluded. To check the reader's claim that these examples call the public producers/consumers, I also inspected the complete `Tests/OnlineSubgradientBasicCanary.lean`, SHA256 `f031106fc8f3fdec2bc1118fba66494a6782e1d2d2764937ea9bffc676d20c4c`. Its `square_support`, `square_convex`, and `interval_outside_no_support` declarations follow exactly those routes. This was source inspection, not a new compilation run. The worked-example title "Nonzero supporting slope" is illustrative: the actual formula also correctly gives slope zero at x=0; no nonzero-slope hypothesis is encoded or needed.

Reader semantic verdict: **accepted-with-explicit-delta**, with the same deltas as the mathematical review. Required reader or Lean repairs: **none**. The original pending status is superseded only for the reviewed mapping at the hash above; generated-site rendering, compilation, full acceptance, and publication remain separate evidence obligations.
