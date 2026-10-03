# Full Theorem 2.23 scratch source review

Verdict: **accepted-with-explicit-delta for both complete scratch endpoints, inclusion and exact mixed-qualified equality, and the inspected scratch canaries**. No mathematical repair required. This is source-faithfulness acceptance of the inspected implementation with observed focused compilation evidence, not public integration or combined root/Tests/harness/site acceptance, main/merge/live status, or book/Goal completion.

Actor: `/root/source_reviewer`, same separate automated anti-anchored source-review actor, requested GPT-6 Astra / medium, 2026-10-03. Not external-human review. Prior leaf verdicts do not substitute for this audit of the actual complete body.

## Exact read scope and source

I read the complete current equality scratch file and complete equality-canary file (including its copied theorem bodies), frozen inclusion/equality headers, source contract and both native endpoint JSONs, full unchanged blind-reconstruction-v2, equality-leaf03 and equality-canary02 logs, equality-frozen01 and finite-frozen01 JSONs. For rejected recovery logs equality-leaf01/02 and equality-canary01, I inspected error and axiom-result lines, not every diagnostic context. I freshly extracted Theorem 2.23 from physical29–30/printed17–18 of the pinned original PDF and independently hashed that PDF. Its raw hash matches cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17.

The reused definition/support interfaces were inspected earlier in this same sequential review: SourceProper, SourceClosed, SourceSubdifferential, effectiveDomain, realEpigraph, IsConvexExtended, subgradient_point_finite and supporting_functional_at_closure (including its body). For this full-body pass I additionally inspected the actual upperAdd/convex_upperAdd interface and convexity proof, and finitePart_eventually statement/body. The hash table binds their containing files, not a claim of reviewing all unrelated declarations or every transitive dependency. No compilation was rerun by this reviewer.

## Seven semantic slots

| Slot | Audit result |
| --- | --- |
| 1. Objects/spaces | EReal-valued functions on a finite-dimensional real inner-product space, representing source Euclidean space. Witness-defined Minkowski sum consists of actual component supports and an exact vector sum. No closure, convex hull, approximate support or presumed decomposition replaces it. |
| 2. Quantifiers/order | Inclusion allows every finite index type and every x. Equality has positive Fin(n+1) indexing, one z in the last domain and every OTHER ambient domain interior, then every query x. No x=z condition, qualification at x, last-interior condition or relative-interior substitution. |
| 3. Assumptions | Inclusion keeps only component properness. Equality preserves component properness, convexity and closedness and the exact mixed qualification. No query-finiteness, aggregate-properness, boundedness, differentiability, dual attainment or support-decomposition assumption is added. Needed finite facts are produced internally. |
| 4. Conclusions | Both required endpoints now have actual bodies: inclusion and exact equality for all x. Reverse inclusion constructs a full indexed family, not merely a binary split or finite-domain-only result. |
| 5. Constants/normalization | Unweighted sums, coefficient one; the ordinary EReal sum appears in the source terminal. upperAdd is used only inside a convexity proof after proving it equals ordinary addition when both arguments are not bottom. No mixed-infinity arithmetic substitution is hidden. |
| 6. Probability/information | Deterministic convex analysis; no algorithm, probability, filtration, causal access or measurable-selection premise. |
| 7. Boundaries | Inclusion explicitly extends to empty finite index types. Equality is positive-family only, includes singleton with vacuous other-interiors, retains arbitrary x including top-valued aggregate queries, and admits the last qualifying point on its domain boundary. |

## Complete construction audit

The inclusion body consumes an actual vector-family witness, sums the global inequalities at arbitrary y, and uses additive coercion and sum_inner. Properness remains an explicit terminal parameter although unused in this algebraic proof; it is not removed or replaced by convexity.

All six finite helpers have genuine bodies. upperAdd_eq_add_of_ne_bot handles extended-real constructors with the no-bottom hypotheses. ereal_finset_sum_ne_bot is an insertion induction. convex_finset_sum uses that fact to identify convex_upperAdd with ordinary addition at each insertion. finite_sum_point constructs the sum of actual real representatives through the additive coercion homomorphism. sum_finite_implies_components_finite isolates one summand with erase; a top component would force the sum to top because the remainder is not bottom. interior_domain_sum intersects the finitely many eventual finite neighborhoods and sums their real representatives. It neither assumes an aggregate interior nor interchanges an infinite intersection with interior.

The embedded binary producer constructs the projected product epigraph C={(u-v,a+b-inner(g,v))}. The actual aggregate support bounds the height of every point with displacement zero below by q=f(x)+h(x)-inner(g,x). The contact point belongs to C and cannot be interior. The supporting-functional theorem produces nonzero L; its vertical coefficient c is nonpositive by increasing epigraph height. If c=0, the mixed qualifier makes the horizontal linear functional attain a local maximum at the first domain's interior point while fixing a finite point of the second domain, forcing the horizontal part to vanish too. Thus c<0. Riesz representation of -A/c constructs p; actual epigraph points with one component fixed at x give full global supports p and g-p, explicitly handling top-valued test points. No dual-attainment or decomposition premise is consumed.

The singleton induction base simplifies the aggregate to its only function and chooses the constant one-element support family. It does not ask for an interior point of that function. This covers n=0 even when the effective domain has empty ambient interior.

In the successor case, the prefix fp contains exactly the castSucc indices, excluding the original last component h. The same source witness z is in every prefix interior. The proof derives finite values there, properness and convexity of the prefix sum F, and z in interior(dom F). The last component retains only domain membership at z. It independently proves the whole aggregate proper: no bottom follows componentwise, and z gives an actual finite sum witness.

Given an arbitrary aggregate support g at x, subgradient_point_finite produces aggregate finiteness at x from this derived properness. The sum-finiteness helper then produces finiteness of every component; these supply the binary helper's finite-at-query inputs. Hence the full terminal has no such extra assumption. The binary producer splits g into p supporting F and g-p supporting the original last component. The prefix induction hypothesis is applied with the same z: its own last member is already an interior member of the original prefix, so only domain membership is passed for that member; the other prefix interiors remain valid. Original component closedness hypotheses are forwarded to this induction call, not replaced by an assumed closedness of F. The resulting actual prefix family G is extended by Fin.snoc with g-p, and the exact vector sum is proved by p+(g-p)=g.

This construction works under the exact source mixed condition. The stronger binary helper does not need closedness, but the source endpoint still retains it. The proof does not accidentally demand closedness of a partial sum, an all-interiors qualifier, or a new qualifier at each query.

## Outside-domain and convention audit

No finite-domain restriction has been introduced through the proof's assumption hg: reverse set inclusion universally quantifies any candidate member. If the aggregate is top at x, derived properness makes such an hg impossible. Similarly a top-valued proper component has no support, so the Minkowski set is empty. Thus both sides are empty outside the common domain; this logical branch is covered even though the main proof need not spell out a separate by_cases.

For inclusion alone, individually proper components can have disjoint domains, making the aggregate identically top. The existing unguarded global-inequality subdifferential then contains every vector, unlike a domain-guarded convention, but its Minkowski input side is empty everywhere. This remains a disclosed vacuous convention boundary, not a support-existence result for an improper aggregate. Equality's common witness excludes this improper case. Other explicit deltas are coordinate-free Euclidean presentation and generic finite/empty-family inclusion. The source does not provide this detailed equality proof; it refers to Bauschke–Combettes Corollary 16.50. This review verifies the source statement and the actual construction, not an independent audit of that external reference.

## Canaries, blindness, and compilation

The three-component canary is two squares plus the [0,2] indicator. It proves aggregate support -1 at x=0 directly, then invokes the complete equality to obtain an actual Fin3 family of supports summing to -1. The last_domain_boundary theorem proves the qualifying point is not interior to the last domain. outside_domain_both_empty uses the same equality at x=3, proves the Minkowski set empty through the last component's domain contradiction, and transfers emptiness to the aggregate support set. The singleton canary uses the indicator of {0}, proves its domain interior empty, constructs the vacuous mixed qualifier, and invokes equality to obtain support 7 in the one-component sum. These exercise the finite-family induction, nonzero vector sum, mixed boundary, arbitrary query and singleton semantics. They establish existential decompositions, not separately enumerated unique component values.

The blind reconstruction correctly recovers both endpoints, all-x scope, mixed qualification, positive equality indexing and the improper-sum convention. The actual current bodies implement that reconstructed contract. The decoder's own disclosed provenance is preserved; it is a separate automated actor, not a human reviewer.

Observed equality-leaf03.log reports theorem_2_23_equality with only propext, Classical.choice and Quot.sound. equality-canary02.log reports the same standard three axioms for equality and all five printed canary endpoints. Remaining messages are unused-variable/section-variable/tactic-style/simp warnings. equality-leaf01 and leaf02 contain errors and sorryAx; equality-canary01 has a singleton typeclass error and sorryAx for that canary. Those failed runs are rejected as acceptance evidence and remain historical. Focused logs are not a fresh reviewer-run build or an immutable execution-to-source manifest; current source and log bytes are separately bound below.

The full terminal header matches the frozen equality header and native JSON; equality-frozen01 reports identical expected/actual statement hash f8f55e9cb1443f1d86097737e3b76aa2e729ae897e601e207f6f78e5c8b9a1c3. finite-frozen01 reports success for all six helper statements. These are observed fence results, not a substitute for the body audit. Native JSON empty source_assumptions arrays do not erase explicit theorem assumptions.

## Limits and required next stage

No semantic proof repair is requested for these bytes. Both source obligations have progressed beyond the earlier contract-only and binary-only receipts; those historical reports are preserved. Public module integration, public canaries/import roots, combined root/Tests/harness gates, website readers and their binding reviews remain outside this receipt and are not approved here. Frozen draft prose saying no theorem body existed remains historical contract-time metadata, not the current scratch status.

## Independently measured raw receipts

Hashes are computed from actual raw bytes, without line-ending normalization or reserialization. Paths are relative to E:/ABRL/worktrees/research-online-book. Backtick-delimited entries bind the inspected files and the explicitly scoped containing modules.

| File | Raw SHA256 |
| --- | --- |
| `tmp/online-subgradient-sum-equality.lean` | `86c134f3c75ca7aa28f1705632c9c87b365fb0fbb438a264ce9bb302131247b6` |
| `tmp/online-subgradient-sum-equality-canary.lean` | `d64b6e60f426eca7cd81b8e0d96aafaac1845685eabb630c288a2edc0c4f7dc2` |
| `docs/contracts/online-subgradient-sum-v1/inclusion-header.txt` | `9cd548022c463e6be3631685a7c687116b176f005341eecbb7f324f26273124b` |
| `docs/contracts/online-subgradient-sum-v1/equality-header.txt` | `04daea804ef2da692817458481240e079892c03383e83acd3b9f20f1f2ea32da` |
| `docs/contracts/online-subgradient-sum-v1/contract.md` | `5b09efee5962772ecadb5afc63a85d560c2c2483c4003b6ff61520c0bd7095ac` |
| `docs/contracts/online-subgradient-sum-v1/theorem_2_23_inclusion.json` | `e09198bb68b61320952decb46f359ef0633e49518b5ecf79dc12358052a16471` |
| `docs/contracts/online-subgradient-sum-v1/theorem_2_23_equality.json` | `a6b11235782600cdef78d90c4ebbe2fa7ca274bec7654530a510afa6a50f06ca` |
| `runs/online-subgradient-sum-20261003/blind-reconstruction-v2.md` | `80a186970ec70e5f6ffed7496b716d763eb9e1030e47682bf5472ceb8892e953` |
| `runs/online-subgradient-sum-20261003/equality-leaf01.log` | `a05cda948c78eb31a980f877d1dbe341ffa53a77efa53ff303f2f8e5168cb07c` |
| `runs/online-subgradient-sum-20261003/equality-leaf02.log` | `1b409ed0bfe8bbb0cb059ebb1d275492350dce978bdc6ec400de80a80089cf75` |
| `runs/online-subgradient-sum-20261003/equality-leaf03.log` | `a5e96f82494fc81491d2ef7803d883d47f5b903e5506f8a41e9b7eeb6c8d151d` |
| `runs/online-subgradient-sum-20261003/equality-canary01.log` | `76392c355efe9d4d71423a77b2f61ab95a7dd04856da7968a6b2ded03af9fd7a` |
| `runs/online-subgradient-sum-20261003/equality-canary02.log` | `4a68edcbde8e2bcf871f58e5d791041c4ba4ac80a10d4979a2c0b6ea39522620` |
| `runs/online-subgradient-sum-20261003/equality-frozen01.json` | `5cda3c0621bcd533e470642ce6cf4e721e0a8c518208e5e836f3b3892bf30c32` |
| `runs/online-subgradient-sum-20261003/finite-frozen01.json` | `48277114708f8c58db45dd360a7d691f8a9c1f988bd04f6468b62b21237a7967` |
| `BanditRLProof/OnlineConvexSums.lean` | `3087d7f69c36c7a02e4b28a17576629c57c851e38630352a2b66c5934116c758` |
| `BanditRLProof/OnlineConvexFirstOrder.lean` | `9921bf1ed9391ddf01221be77f0321cc72a3caa4c1c97b058da3e145d8b2c60e` |
| `BanditRLProof/OnlineConvexBarycenter.lean` | `b994e697375c2f52e3e5ec4249239c54d625a84d97f500e122fb78d164ffeb40` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `BanditRLProof/OnlineConvexExtended.lean` | `fec3efd071a069050593babb9eafee7262684b477b58ce8f045fe18c1add5d0f` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
