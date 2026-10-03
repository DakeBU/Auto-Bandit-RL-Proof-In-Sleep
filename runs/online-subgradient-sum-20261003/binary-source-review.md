# Binary decomposition source review

Verdict: **accepted-with-explicit-delta for this binary scratch dependency leaf and its inspected boundary canary only**. No mathematical repair is required for the current body. This is not acceptance of positive-finite-family Theorem 2.23 equality, full Theorem 2.23, public/root/Tests/harness/site integration, main, deployment or the book Goal. All earlier receipts remain unchanged.

Actor: `/root/source_reviewer`, distinct automated reviewer; requested GPT-6 Astra / medium; 2026-10-03. Not external-human review. I inspected the actual proof rather than treating the prior contract decision or compiler output as semantic authority.

## Source and read scope

I freshly extracted Theorem 2.23 from the pinned original Orabona v10 PDF, physical29–30/printed17–18, and independently measured its raw hash below. The source requires inclusion for proper components and equality for proper convex closed components under one mixed common point in the last domain and all other ambient interiors. The present artifact is a binary decomposition dependency for that equality, not the source terminal itself.

I read both complete scratch files, the binary header and native JSON fence, binary leaf contract, frozen check, both leaf compilation logs and the canary log, original inclusion/equality headers and source contract. I also inspected supporting_functional_at_closure with its surrounding finite-dimensional context and body, and the actual SourceProper, SourceSubdifferential, effectiveDomain, realEpigraph and IsConvexExtended interfaces. Hashes bind full containing files; review scope for existing modules is limited to these interfaces and supporting-functional body, not all unrelated declarations. No compiler was rerun by this reviewer.

## Seven semantic slots

| Slot | Finding |
| --- | --- |
| 1. Objects/spaces | Two EReal functions on a finite-dimensional real inner-product space; convexity is real-height epigraph convexity. The helper constructs a vector p, not an assumed decomposition or closure approximation. Coordinate-free finite-dimensional presentation covers source Euclidean space. |
| 2. Quantifiers/order | Query x and sum support g are arbitrary, subject here to explicit component finiteness at x. Qualification has one independent z in interior(dom f) and dom h. No requirement x=z or z in interior(dom h) appears. Both output supports quantify globally over all y. |
| 3. Assumptions | Properness and convexity of both functions, actual aggregate support, query finiteness, and exact mixed binary qualification. No closedness, boundedness, local differentiability, decomposition or dual-attainment premise. Absence of closedness strengthens this helper; query finiteness is an extra helper restriction and must be derived at the source terminal. |
| 4. Conclusion | Exists p supporting f globally at x, with g-p supporting h globally at x. Thus p+(g-p)=g. This is a genuine reverse-direction producer for two functions, not yet finite-family equality. |
| 5. Constants/normalization | Unweighted sum; projected height subtracts inner(g,v); supporting functional has coefficient c<0. The Riesz vector represents -A/c, producing p and g-p with the correct signs. |
| 6. Probability/information | Deterministic convex geometry. No stochastic, causal, measurable-selection or future-information condition. Standard classical choice is not an assumed support-decomposition theorem. |
| 7. Boundaries | Infinite test-point values are handled explicitly by le_top. Properness excludes bottom for all finite conversions. The second qualifying point may be a genuine domain boundary, as tested. Empty-family, singleton-family and all-x top branches of the final source equality remain separate obligations. |

## Producer and sign audit

The proof constructs the linear image C of the product of the two real epigraphs through P((u,a),(v,b))=(u-v,a+b-inner(g,v)). Convexity follows from actual component epigraph convexity and a linear image. With f(x)=r and h(x)=s, q=r+s-inner(g,x), the proof constructs (0,q) in C. For any (0,t) in C the displacement equality forces u=v, and the actual global sum-support inequality at v gives q<=t. This is the needed lower bound on the zero-displacement vertical slice; no global minimization or dual attainment is assumed.

The proof excludes (0,q) from interior C by showing that otherwise the identity real function would have a local minimum, contradicting derivative 1. The reused supporting_functional_at_closure consumes convexity, closure membership and failure of interior membership, returning a nonzero continuous linear functional L bounded above at (0,q). Its inspected body handles both nonempty interior by geometric Hahn–Banach and empty interior through a proper affine span. It requires no closedness of C and assumes no component decomposition.

Writing L(v,t)=A(v)+t*c, raising one epigraph height by 1 gives c<=0. If c=0, the points (u-z,f(u)+h(z)-inner(g,z)) in C for every u in dom f imply A(u)<=A(z). Since z is in ambient interior(dom f), this is a local maximum of the linear functional, so its derivative forces A=0. Together with c=0 this would force L=0, contradicting its nonzero property. This is precisely where the first interior and second finite-domain membership are used; the proof never needs the second interior. Consequently c<0.

Riesz representation of (-c inverse)*A constructs p with inner(p,v)=-A(v)/c. The epigraph point with the second component fixed at x yields f(y)>=r+inner(p,y-x). The point with the first component fixed at x yields h(y)>=s+inner(g-p,y-x). Division uses c<0 with the reversed inequality; inspection of the two displayed numerators confirms the signs. Each proof splits top-valued y, then uses properness to justify toReal in the remaining case. These are full global supports, not just supports on a neighborhood or the common domain.

## Canary and compiler evidence

The canary establishes actual aggregate support g=-1 for y^2 plus the indicator of [0,2] at x=0 directly: inside the interval, -y<=y^2; outside it the aggregate is top. It proves properness, convexity, query finiteness and the mixed qualification, then calls binary_subgradient_decomposition to obtain the two supports. The companion last_qualifier_is_not_interior explicitly proves 0 is not interior to the indicator domain. Thus this is an actual nonzero aggregate-support boundary consumer, not an all-interiors test disguised as the mixed condition. It proves existential decomposition, not a separate explicit identity p=0.

binary-leaf01.log contains four real proof errors and sorryAx; that run is rejected as validation and preserved as history. binary-leaf02.log reports the binary declaration with only propext, Classical.choice and Quot.sound and no error. binary-canary01.log reports the same standard three axioms for the copied binary declaration and both canaries. Only a harmless tactic-style warning remains. This is observed focused compilation evidence, not an independently rerun or combined public gate. Current body bytes and log bytes are bound separately; the logs are not themselves immutable execution-to-source manifests.

The current body header matches binary-header.txt and its native JSON statement. binary-frozen01.json reports equal expected and actual statement hash 9e5236d9c6a2c7cf1943a87aa6a43e2e3d5e95ccf3e98dacbc5bf8b8a28c33e2, no findings. The empty source_assumptions metadata array does not erase the explicit helper premises.

## Required completion boundary

Retain the original source equality header exactly, including proper/convex/closed components, positive Fin(n+1) indexing, one mixed qualifier and every query x. Closedness is unnecessary for this stronger binary helper but remains in the source-facing endpoint. The helper's finite-at-query assumptions cannot be copied into that endpoint: later work must obtain a common finite point from qualification, establish properness of the aggregate, derive component finiteness from an actual aggregate support, and handle the empty-support/outside-domain branch. It must also construct the full indexed decomposition through a correct finite-family reduction and cover the singleton case without adding a last-interior condition. None of those remaining obligations is certified here.

## Raw SHA256 receipts

Computed independently from current raw filesystem bytes during this review, with no normalization or JSON reserialization. Paths are relative to E:/ABRL/worktrees/research-online-book.

| File | Raw SHA256 |
| --- | --- |
| tmp/online-subgradient-sum-binary.lean | 708f845200ff493edc0fe978f16181532fb4485217f3bb26e0ee25f86ef5fcd2 |
| tmp/online-subgradient-sum-binary-canary.lean | 1fee3b473918060e4435b92186072c1616c5e3bcafb1d95ea7dc3409c8cfe2ea |
| docs/contracts/online-subgradient-sum-v1/binary-header.txt | e55042ed6e6f5675bd820475633e30f466e23426e6698c47f92ea61f215fe45a |
| docs/contracts/online-subgradient-sum-v1/binary_subgradient_decomposition.json | f640f1ac8a4307d6244a0a27a9e5d3bf2247b8acf531f3e34bb49885dc8037f1 |
| runs/online-subgradient-sum-20261003/binary-leaf-contract.md | 8d46b9b57778e5097202ae6f8c3fd667355f42e3131916d8f8e19c74d9145d6c |
| runs/online-subgradient-sum-20261003/binary-frozen01.json | a0c5fd1ef0f4e326bd89a6babeed436ee314fb8ac5d3e229086352f00a93b993 |
| runs/online-subgradient-sum-20261003/binary-leaf01.log | ea6cef3147bf1ff41dde3ba628db8f453e79d40f98b2bbaa51c52f8fc82bfdba |
| runs/online-subgradient-sum-20261003/binary-leaf02.log | 17092cce80621f9f2112351eb265bddf022beb2b7dfde8a8412f3a82dcc6fc8e |
| runs/online-subgradient-sum-20261003/binary-canary01.log | 430352b3ff9849d64058c707943be40d1877f54c39c3e8b4dd4187228331bddc |
| docs/contracts/online-subgradient-sum-v1/inclusion-header.txt | 9cd548022c463e6be3631685a7c687116b176f005341eecbb7f324f26273124b |
| docs/contracts/online-subgradient-sum-v1/equality-header.txt | 04daea804ef2da692817458481240e079892c03383e83acd3b9f20f1f2ea32da |
| docs/contracts/online-subgradient-sum-v1/contract.md | 5b09efee5962772ecadb5afc63a85d560c2c2483c4003b6ff61520c0bd7095ac |
| BanditRLProof/OnlineConvexBarycenter.lean | b994e697375c2f52e3e5ec4249239c54d625a84d97f500e122fb78d164ffeb40 |
| BanditRLProof/OnlineClosedProper.lean | 9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6 |
| BanditRLProof/OnlineSubgradientBasic.lean | 4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962 |
| BanditRLProof/OnlineConvexExtended.lean | fec3efd071a069050593babb9eafee7262684b477b58ce8f045fe18c1add5d0f |
| ../research-online-ogd/tmp/pdfs/orabona-v10.pdf | cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17 |
