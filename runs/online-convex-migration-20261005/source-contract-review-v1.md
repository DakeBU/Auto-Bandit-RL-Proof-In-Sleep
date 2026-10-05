# Convex foundation migration: source-contract review v1

Verdict: **accepted-with-explicit-delta**, for stabilization of 22 retained headers and five definitions across the four named modules. No mathematical target repair is required. Three future reader corrections are required below; current reader content is not accepted by this contract verdict. Existing bodies were read to seek contradictions, not independently accepted as freshly compiled proofs.

Actor `/root/source_reviewer`, distinct automated anti-anchored source reviewer, requested GPT-6 Astra / medium; no independent runtime-model attestation, human or external-model review claim. Historical same-model acceptance is not authority.

## Raw/source/header checks

All 228 fixed inputs independently raw-read and hashed with zero drift. The receipt additionally binds the inventory and two actual mathlib files inspected for imported arithmetic. Ancillary historical artifacts are bound for integrity, not recertified semantically. Close reading covers all four actual modules (including existing bodies), all scoped contexts and22 headers, source intent/card, fresh restricted packet/decoder/receipt, selected current reader entries, and imported EReal arithmetic. All22 normalized actual public headers equal the frozen statement strings and hashes; every declared source-premise fragment occurs in the actual header. Native capture is not a fresh safe-verify or compile gate.

Original Orabona v10 raw SHA256 `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`; directly re-extracted/read physical21–22, printed9–10. Original Rockafellar Conjugate Duality and Optimization raw SHA256 `29d57ab07857b8270c175343746c77b4138f2db6161ae20174a0bba076991b0e`; directly re-extracted/read physical17, printed6. The latter explicitly prescribes positive infinity for mixed-infinity addition when adding convex functions and warns that the opposite convention belongs to concave functions. Orabona's closure bullet does not specify this arithmetic convention. The two sources must not be conflated.

Fresh decoder reconstructs Q0–Q4 and M01–M22 with seven slots, including noBottom/domain guards and real-valued composition. It expressly did not inspect imported arithmetic implementations. This review independently checked actual mathlib Basic zero_mul and toReal definitions, and Operations add_bot/bot_add: zero multiplication returns zero even at both infinities; toReal maps both infinities to zero; ordinary addition is bottom-dominant. Hence the supplied upperAdd definition yields the claimed top-dominant convention. This supplemental reviewer verification does not falsely enlarge the decoder's permitted inputs.

## Five-definition context audit

- `effectiveDomain`: f<top, not the finite-real-value locus; bottom is included. Empty domain is permitted.
- `realEpigraph`: subset E×real; top has empty fiber, bottom has all real heights. Replacing real heights by EReal would change the contract.
- `IsConvexExtended`: convexity of that epigraph, with neither properness nor noBottom silently embedded. Constant top and bottom remain convex.
- `extendedIndicator`:0 inside/top outside, arbitrary set, including empty set; distinct from a zero-outside indicator.
- `upperAdd`:−(−a+−b), explicit top-dominant mixed-infinity operation. Real arithmetic agrees with ordinary addition; ordinary EReal addition is not interchangeable in the general closure theorem.

`convex_effectiveDomain` may choose toReal(bottom)=0 as a real upper height because bottom≤0; it does NOT conclude bottom is finite or use a false coe_toReal identity there. In the toReal equalities and Theorem2.4, domain membership excludes top and noBottom excludes bottom. Thus there is no infinity-to-zero shortcut masquerading as equality.

## Per-target seven slots

All names below carry the full namespace. Slots are objects, quantifiers, assumptions, conclusion, constants, information/probability and boundary. Every result is deterministic static convex analysis: the information slot for EVERY row is **no probability, filtration, algorithm or regret statement**. Every row is accepted at contract level with the ambient/convention/refinement deltas stated here.

| Actual target | Objects | Quantifiers | Assumptions | Conclusion | Constants/index | Boundary |
|---|---|---|---|---|---|---|
| `BanditRL.OnlineConvex.definition_2_2` | Real module/set V | Every V,x,y in V,θ | 0<θ<1 on RHS only | Convex iff strict segment closure | θ and1−θ | Empty/singleton allowed; structural definition equivalence |
| `BanditRL.OnlineConvex.convex_effectiveDomain` | Extended f/domain | Every convex f | Epigraph convexity | Convex domain | f<top includes bottom | Empty domain allowed; does not imply finite values |
| `BanditRL.OnlineConvex.effectiveDomain_indicator` | Set V/0-top indicator | Every V | None | Domain=V | Zero inside/top outside | Empty/nonconvex V allowed |
| `BanditRL.OnlineConvex.convex_indicator_iff` | Set V/real epigraph | Every V | None | Indicator convex iff V convex | 0/top | No closedness/nonemptiness |
| `BanditRL.OnlineConvex.realEpigraph_toReal` | Extended f/E×real | Every f and pair | Everywhere noBottom | Epigraph equals domain-and-toReal set | Finite real heights | Domain guard essential; top outside allowed |
| `BanditRL.OnlineConvex.convexExtended_iff_toReal` | Extended f/real restriction | Every f | Everywhere noBottom | Convex iff ConvexOn domain toReal | Exact iff | ConvexOn includes convex domain; empty allowed |
| `BanditRL.OnlineConvex.theorem_2_4` | Extended f/domain points | Every f,x,y in domain,θ | noBottom AND convex domain;0<θ<1 | Epigraph convex iff weighted inequality | θ,1−θ sum1 | No finite-cardinality premise; no tests outside domain |
| `BanditRL.OnlineConvex.convex_add_indicator` | Extended f and set V | Every f,V | noBottom;convex f,V | Convex ordinary sum with indicator | Ordinary EReal + | Empty/disjoint domains allowed; not general upperAdd |
| `BanditRL.OnlineConvex.convexExtended_coe_iff` | Real f embedded in EReal | Every real-valued f | None | Extended convex iff ConvexOn univ | Finite embedding | No infinity input; whole-space bridge |
| `BanditRL.OnlineConvex.example_2_5` | Real inner-product space,z,b | Every z,b | Ambient structure only | Convex inner(z,x)+b | Arbitrary offset | No completeness/finite dimension; zero slope allowed |
| `BanditRL.OnlineConvex.example_2_6` | Real normed space | Every such space | Normed real structure | Convex norm | Norm, not squared norm | No inner product/completeness; mandatory example despite exercise proof |
| `BanditRL.OnlineConvex.convex_comp_affine` | Real modules,EReal f,affine A | Every f,A | Convex f | Convex f∘A | Translation allowed | No rank/continuity/properness; constant A allowed |
| `BanditRL.OnlineConvex.convex_iSup` | Arbitrary index family,EReal | Every index type and family | Each f_i convex | Convex pointwise supremum | Complete-lattice supremum | Empty family=bottom; unbounded/top allowed |
| `BanditRL.OnlineConvex.convex_comp_monotone` | Real f:E→real,g:real→real | Every f,g | Both convex, global Monotone g | Convex g∘f | Finite embedding | Real-valued types essential; no EReal composition assertion |
| `BanditRL.OnlineConvex.upperAdd_coe` | Two embedded real values | Every real a,b | None | upperAdd equals embedded real sum | Unit coefficients | Finite arithmetic helper, not arbitrary ordinary-add identity |
| `BanditRL.OnlineConvex.upperAdd_top` | EReal a and top | Every a | None | upperAdd a top=top | Top dominates | Includes a=bottom |
| `BanditRL.OnlineConvex.top_upperAdd` | Top and EReal a | Every a | None | upperAdd top a=top | Top dominates | Includes a=bottom |
| `BanditRL.OnlineConvex.upperAdd_le_coe_iff` | EReal a,b; real h,r,s | Every a,b,h; existential r,s | h finite by type | Sum≤h iff real upper witnesses with r+s≤h | Exact bound | Top input impossible; bottom allowed; no infinite height claim |
| `BanditRL.OnlineConvex.convex_upperAdd` | Two extended functions | Every f,g | Both epigraph-convex | Convex pointwise upperAdd | Top-dominant operation | No proper/common finite-point premise |
| `BanditRL.OnlineConvex.positive_mul_le_coe_iff` | Real a,h; EReal z | Every a,z,h | a>0 | a*z≤h iff z≤h/a | Positive division | z infinities allowed; a=0 excluded |
| `BanditRL.OnlineConvex.convex_nonneg_mul` | Extended f,real a | Every f,a | Convex f;a≥0 | Convex value scaling | 0 times infinity=0 | Includes a=0 and improper f; no negative scale |
| `BanditRL.OnlineConvex.convex_nonneg_linear_combination` | Extended f,g,real a,b | Every f,g,a,b | Convex f,g;a,b≥0 | Convex upperAdd(a*f,b*g) | Weights need not sum1 | Both zero allowed; explicit convention, not ordinary EReal sum |

## Anti-anchored source comparison and explicit deltas

**Source theorem hypotheses are retained.** Definition2.2 uses strictly interior weights; endpoints are automatic and do not require a nonempty set. Definition2.3 permits both infinities. Theorem2.4 specifically excludes bottom, assumes convex domain, and tests only domain points with strict weights. No properness/nonempty-domain condition was added. The indicator-addition consequence uses ordinary addition safely because f has no bottom value. Its assumption is source-stated, not an arbitrary restriction of the general weighted-sum theorem.

**Scope generalization is mathematical, not attribution drift.** Source Euclidean spaces embed in the real-module interfaces. Affine examples generalize to real inner-product spaces and norms to real normed spaces; finite dimensionality/completeness are not needed for these statements. Arbitrary affine maps include constants and noninjective maps. Arbitrary supremum indices include the empty type, giving constant bottom, and unbounded families, giving top. These are explicit included boundary interpretations rather than hidden nonempty/boundedness premises.

**Monotone composition is exactly real-valued.** Source printed10 explicitly has f:real^d→real and g:real→real. Both Lean input types reflect this, with global nondecreasing g. This is not an extended-real composition theorem and does not assert extension of g to infinities. A statement that no finite-value hypothesis is present is misleading unless it explicitly explains that finiteness is already enforced by these types.

**General sums require the convention delta.** Under ordinary bottom-dominant addition the unrestricted closure is not generally valid. Concretely, let f be bottom at0 and top elsewhere, and g bottom at2 and top elsewhere. Each real-height epigraph is a singleton times the whole real line, hence convex. Ordinary bottom-dominant addition is bottom at0 and2 but top at their midpoint1; its epigraph is not convex. The retained spike canary encodes precisely this counterexample (fresh canary compilation is not certified here). The actual generic upperAdd target avoids this by top dominance and its finite-height existential characterization. A bottom argument still allows real upper witnesses when neither input is top. Zero weights are intentionally included via0·±infinity=0; this is a separately explicit formal arithmetic convention, not a zero-scalar assertion quoted from the displayed Rockafellar passage (which states positive scaling). Positive scaling and zero scaling must remain distinguished. No claim that Orabona literally prints upperAdd or the zero convention is accepted.

**Helpers versus source obligations.** The22 declarations comprise bridges and operation laws as well as numbered examples and unnumbered consequences. They are not22 printed theorems or new proofs. The norm example remains mandatory source mathematics despite its proof being left as an exercise. All four printed closure bullets are addressed by these contracts, with weighted combinations subject to the explicit interpretation; whole-chapter coverage does not follow.

## Required future reader corrections

1. Replace Theorem2.4's ambiguous “finite-domain conditions” (including corresponding bridge wording) with explicit “no negative-infinity values and a convex effective domain; values at domain points are finite.” No finite-cardinality assumption is intended.
2. Replace monotone-composition note “no ... finite-value ... hypotheses” with an accurate statement that f and g are globally real-valued by type and g globally nondecreasing; no additional domain/image condition is needed. Do not imply general EReal composition.
3. Update the foundation indicator card's statement that weighted combinations/affine composition/supremum remain separate required obligations: distinguish existing retained closure bodies and this migration's pending independent body/package acceptance from genuinely missing mathematical implementation. Keep all four closure rules visible, with separately attributed upperAdd convention.

These are reader integration requirements, not reasons to weaken or version the frozen mathematical targets. Mathematical required repairs: none. Current reader acceptance is expressly deferred.

## Remaining gates and limits

Fresh actual-body/canary audit, focused and combined root/Tests/full harness, actual axiom/safe-guard evidence, appropriate reused-versus-new graph attribution, shared Book/registry/site and contributor checks, final immutable bindings and separate package/PR decision remain required. Existing graph readiness is not a new export or canary graph gate. No compilation or old-body acceptance is granted here. No other historical mathematical path, Chapter2 enumeration, chapter/book/Goal completion, main merge or live deployment is accepted. The accepted FTL/OGD receipts and originals remain immutable; future shared reader changes require explicit preserved raw snapshots.

## Exact raw bindings

All hashes are actual raw SHA256, no normalization.

| Path | Raw SHA256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `BanditRLProof.lean` | `d16d741b3bca1b4f7c30fbad7a2b5b3e8283d079cf49695720f4b256fb3b5bfb` |
| `BanditRLProof/OnlineConvexClosures.lean` | `401d747a63de2205701e1defb25bde9341a60e1365b529fb78866555e54c2133` |
| `BanditRLProof/OnlineConvexExamples.lean` | `371918f1252c57e01ee71afb1bdbfd1d7715a3bb8e421308b8cb77a019ea94d6` |
| `BanditRLProof/OnlineConvexExtended.lean` | `fec3efd071a069050593babb9eafee7262684b477b58ce8f045fe18c1add5d0f` |
| `BanditRLProof/OnlineConvexSums.lean` | `3087d7f69c36c7a02e4b28a17576629c57c851e38630352a2b66c5934116c758` |
| `Tests.lean` | `693654a3126313f0e7db548ff08f6ee961e8b7656602fb56dc590a1cdbe0a825` |
| `Tests/OnlineConvexClosuresCanary.lean` | `422d6bf8a8d64260839e8929e2c11213ab07e1c02a92d1834675886defa9729b` |
| `Tests/OnlineConvexExamplesCanary.lean` | `398f09f34957b5ad89cbf9b2d35a472db45b0fb15066b454fb684c3b2e50f112` |
| `Tests/OnlineConvexExtendedCanary.lean` | `d49bee7eae40c76579c9c0f56dc4d92012bf6e977ce8e4fe43e8be865f1ac8c7` |
| `Tests/OnlineConvexSumsCanary.lean` | `e1a0de929b121e83ad4fecbe0d9b2b31f1a1d5ff669fff8a1912d4df46e6140f` |
| `conversion-windows/ONLINE-CONVEX-MIGRATION-20261005.md` | `e594699d4141a81300a83d166c6c68d6dde5375633154d0fb63e75c03752f991` |
| `docs/contracts/online-book-v1/coverage.json` | `fd7580c2d0ec040352317d3c53dc583a6b9b75a68b4026ebf3b38f7010a98f1e` |
| `docs/contracts/online-book-v1/source-inventory.json` | `a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7` |
| `docs/contracts/online-convex-closures-v1/context.json` | `1b430f4b39521027514f9b7c171e359e27eef57031375e1718727cdeacffa239` |
| `docs/contracts/online-convex-closures-v1/contract.md` | `330e783a01aeaafcefd883cd8c2df4ede15de720d82f2b2d6e9cc31da0665dc7` |
| `docs/contracts/online-convex-closures-v1/convex_comp_affine.json` | `3abd2a9ab7cf8e6671a65c8a7030a76fd3f9d3c58faae814f397d104cd14ebb4` |
| `docs/contracts/online-convex-closures-v1/convex_comp_monotone.json` | `7e1ca4cd08a808f832476d99dd7af0a5f8ec67f8077ada120459332092285774` |
| `docs/contracts/online-convex-closures-v1/convex_iSup.json` | `d2c3d456df2c50bbfa7e38eae287f13f8e5d30537799a8c922c1bc0c74cc807d` |
| `docs/contracts/online-convex-closures-v1/headers.json` | `ad130fc730d2be2de8883873600a1557fc4da3f36a6951a4c336cdc2514e6550` |
| `docs/contracts/online-convex-examples-v1/context.json` | `1ddd716db004af54cba7a3effdbb38e41fe4b09d05d05198f3188039585c99c0` |
| `docs/contracts/online-convex-examples-v1/contract.md` | `83bac9a912963a835b25333fb495af058b80e3ebc4fd73c62057533aa6e4c861` |
| `docs/contracts/online-convex-examples-v1/convexExtended_coe_iff.json` | `fc22bb56ab3df8482fd1141c27077d73937a90eb46aceca2eea812ba84b034d3` |
| `docs/contracts/online-convex-examples-v1/example_2_5.json` | `c21135032c8dc22c2f79807479093fed3b82b500b6348e9b743b7ec00665127c` |
| `docs/contracts/online-convex-examples-v1/example_2_6.json` | `b3f3b9b3858f2295e2eed7517d90e3204455bec1442f9fb962e40bca0c8fc248` |
| `docs/contracts/online-convex-examples-v1/headers.json` | `47fa8fb087732c8affa19432461421887c8387b253fb4560585781afca33ad8a` |
| `docs/contracts/online-convex-extended-v2/context.json` | `67f368cf60e0ab720de4f8ec9a7b46f4a030f4c060c4fc27b785759cb77c5639` |
| `docs/contracts/online-convex-extended-v2/contract.md` | `c94b7b59bc5f80c0967eab1c47b29389ef09f6bf6cef75b2e7250504506a3534` |
| `docs/contracts/online-convex-extended-v2/convexExtended_iff_toReal.json` | `cfc1945a8a217fa254cec009e9801126dc55213013c80b395a2169a473d9c56a` |
| `docs/contracts/online-convex-extended-v2/convex_add_indicator.json` | `591565b17da4f4bee43e136e569c4be2749a20944a7e3ea1bf3a06901f0c7c9a` |
| `docs/contracts/online-convex-extended-v2/convex_effectiveDomain.json` | `8ec3a39bc835b294fa97e9d72dc2dcfd488866a93ac1d538de2ad4e0ab9fd630` |
| `docs/contracts/online-convex-extended-v2/convex_indicator_iff.json` | `cc0cddb9d6a68ac9ffd09bc0e7574c60feb7a13cd8bab877af4e242b7f873ae6` |
| `docs/contracts/online-convex-extended-v2/definition_2_2.json` | `d22050585877d6fe8ebd5aa4d61f046a204760f49c8c44d073b9f77791948ecd` |
| `docs/contracts/online-convex-extended-v2/effectiveDomain_indicator.json` | `94bd1850e9f03d11393a6859862c427e9277cadedb5f8ec45ca67e5ebc5dba1d` |
| `docs/contracts/online-convex-extended-v2/headers.json` | `9c5872561284ff40021a24be19384b251d1f364e60ec6b2c12dabf9a084ed2f1` |
| `docs/contracts/online-convex-extended-v2/realEpigraph_toReal.json` | `caeb0cd3500d975a0cbd4fce78ae2276d0adb06b52cf0a3ca69d05b25a0ff47f` |
| `docs/contracts/online-convex-extended-v2/theorem_2_4.json` | `239f7f650b1ebf4c5c1ca2f882ef89f55ddd32f10478fc25be79daefe13b8c19` |
| `docs/contracts/online-convex-migration-v1/OnlineConvexClosures-context.lean.txt` | `da59c98c6e7f8d1effbb299bf0d9361e8e001b70bd025040885e4ac202549092` |
| `docs/contracts/online-convex-migration-v1/OnlineConvexExamples-context.lean.txt` | `a47f2bc37d9b7e0dc6ae71245d2e761d311b759c8d752628e9695eaa4a472741` |
| `docs/contracts/online-convex-migration-v1/OnlineConvexExtended-context.lean.txt` | `1968de772d0052d60bd7442b872fe11c56296cdc7166c9928c7add64713c8190` |
| `docs/contracts/online-convex-migration-v1/OnlineConvexSums-context.lean.txt` | `af803a05f24c3e52f485b39fd8b274ef884be20e499b05e68a355e949f011b9e` |
| `docs/contracts/online-convex-migration-v1/convexExtended_coe_iff-header.txt` | `2a85c26889a7a35ed9d95803e8c35bb8686347b0ebfc6b3cd53e3b8e01c714bb` |
| `docs/contracts/online-convex-migration-v1/convexExtended_coe_iff.json` | `ed09aea8feefea7eb0699dcf24ecebc5df4a6339f183ba44f8f8cb1c117f6f55` |
| `docs/contracts/online-convex-migration-v1/convexExtended_iff_toReal-header.txt` | `63961e172321d79f823cec356142599fe858bd31b138ea83a4cb349385333439` |
| `docs/contracts/online-convex-migration-v1/convexExtended_iff_toReal.json` | `8fe97753432baf5d9973d87f84b1b3cfa234411f96455ba1d307406719a26493` |
| `docs/contracts/online-convex-migration-v1/convex_add_indicator-header.txt` | `cec960a0c71ce9c16d4676b65763d440fa9a545cbbf8626df735265e351a5900` |
| `docs/contracts/online-convex-migration-v1/convex_add_indicator.json` | `28e3eed9c7a2d62d49c847c36f3754003ef3b54d72e2e6a45c8108aa05f4555d` |
| `docs/contracts/online-convex-migration-v1/convex_comp_affine-header.txt` | `09435e56d8f24cbad9987b036f5e7cf66cddcb3e0bac61ed1727697d6c2dfd12` |
| `docs/contracts/online-convex-migration-v1/convex_comp_affine.json` | `ab34adecb18cf8d907f24168bbb378e78f1d2814e715de1db4b421db762711ba` |
| `docs/contracts/online-convex-migration-v1/convex_comp_monotone-header.txt` | `e0a77815e8ff49091c6496439d1c284c7d6399dc88f2c40bedae5de7a039aebf` |
| `docs/contracts/online-convex-migration-v1/convex_comp_monotone.json` | `88a15fa11a097cf1f6c92b9c0daa2b1b5889bc753a2cfa60afcfe8de46732c8a` |
| `docs/contracts/online-convex-migration-v1/convex_effectiveDomain-header.txt` | `be3300cef5e6795c0ddb274d707f4e5a78da70f13d1c012c9d3b72a41cf2120b` |
| `docs/contracts/online-convex-migration-v1/convex_effectiveDomain.json` | `ed1a10e777f1efff264504dbc9fbe8c728d096c107e0a61d9c94c5195340edf4` |
| `docs/contracts/online-convex-migration-v1/convex_iSup-header.txt` | `7b1f0c79243e0a84a8b2b150db9f7a06d057887ea58c191f756c4d323449b281` |
| `docs/contracts/online-convex-migration-v1/convex_iSup.json` | `f2353ae6685c05fa57af757111aa1a2a4e7d3207e3c322c809ba7c54e9a333f8` |
| `docs/contracts/online-convex-migration-v1/convex_indicator_iff-header.txt` | `872a3f81cfe93bc866821d1af21611aa65921b3506aa0fff77f778f43e57e424` |
| `docs/contracts/online-convex-migration-v1/convex_indicator_iff.json` | `fced3826c33d1d809ec23cacefeef612f6852c34016bc1846a96dd61a743ae4a` |
| `docs/contracts/online-convex-migration-v1/convex_nonneg_linear_combination-header.txt` | `3c20a51b8136613ba776a9d989ef5312dc72f1031246081e8fc191c01b990f84` |
| `docs/contracts/online-convex-migration-v1/convex_nonneg_linear_combination.json` | `d3e65b271938dd2265f5a19c4e601a7a18179abb9fd215a6647e33d331107cb3` |
| `docs/contracts/online-convex-migration-v1/convex_nonneg_mul-header.txt` | `3b2dbba9e7aac7475f23d7b2e2ba2bdba51ff4245b578d723851f7fc6254a0e0` |
| `docs/contracts/online-convex-migration-v1/convex_nonneg_mul.json` | `580e37f59a9e60ebeede2d2b82d69e9542089b6c3c8902a18b9c4a3b0f417325` |
| `docs/contracts/online-convex-migration-v1/convex_upperAdd-header.txt` | `3d944935684d4630087604b1f4cb1464d916eab52c1a4f5f94f00bfe15a74a9a` |
| `docs/contracts/online-convex-migration-v1/convex_upperAdd.json` | `43147074c991207557f03cfb1905a7dc5fc4f34accf009774afe2ca03dfbe2d5` |
| `docs/contracts/online-convex-migration-v1/definition_2_2-header.txt` | `7937ce30172f9ebd064afb9182288d20fe6861de9e388e27e9174e2085bcaa3c` |
| `docs/contracts/online-convex-migration-v1/definition_2_2.json` | `f22f146750c5abe78a75c771fe5b05125ae4b983741bec002bc12706d74fbfcf` |
| `docs/contracts/online-convex-migration-v1/effectiveDomain_indicator-header.txt` | `dbf43bbe228fffd1b38f2922e87fe1b3f70ef8fa404079f49980d22bedc9a32a` |
| `docs/contracts/online-convex-migration-v1/effectiveDomain_indicator.json` | `cd830783c5a5af6b11006f06acafc456c40386397bcbe9fc9453350f6c74b434` |
| `docs/contracts/online-convex-migration-v1/example_2_5-header.txt` | `51fafd82a3065f52285e73045029ea0d31a678a472ab04c6813af8127522cdda` |
| `docs/contracts/online-convex-migration-v1/example_2_5.json` | `b8e1d66345fd7dbeb268d9cac5856f42f8373654b906d53ac31dc3fe18ff72c2` |
| `docs/contracts/online-convex-migration-v1/example_2_6-header.txt` | `18a6caeeeb5434303e281a20a805642dfbde8576e3da3c13578face86827533c` |
| `docs/contracts/online-convex-migration-v1/example_2_6.json` | `3903c19a9aa5ae4dec9293a5b8ff0738017da088d36a1b807f9f2a5f2c4cf835` |
| `docs/contracts/online-convex-migration-v1/neutral-name-map.json` | `77806214949e37c1c3c374d66e519fd2aa0718d00abcc06b648e1d0891f550d5` |
| `docs/contracts/online-convex-migration-v1/positive_mul_le_coe_iff-header.txt` | `3ed97b185434eaee24809fa53137a36074cc52e108989b4d73e265f79c4335d4` |
| `docs/contracts/online-convex-migration-v1/positive_mul_le_coe_iff.json` | `90872738c49799b307b1f1a73af3aac0dc6815b51c196ae064c2469405f40e86` |
| `docs/contracts/online-convex-migration-v1/realEpigraph_toReal-header.txt` | `fab1cc91d0f692e590c4d13569b811e2e65544af804c288b2c61a33f8cba956e` |
| `docs/contracts/online-convex-migration-v1/realEpigraph_toReal.json` | `96e5cc087b50607177713f7c7f2e73b5b759d700d3f7ecea0aaa57bdadb3b833` |
| `docs/contracts/online-convex-migration-v1/source-card.json` | `fe4758e6c0896710d57736eedfb0f1ab8e63ebe4e0106187f7cbeb49122ff0bc` |
| `docs/contracts/online-convex-migration-v1/source-intent.md` | `b0533f9d8da1abe9a3416bda5c3fd614da11ac5a6b2c38ee0cce8729d15faca9` |
| `docs/contracts/online-convex-migration-v1/theorem_2_4-header.txt` | `ac429eab93117d14fb707961c8240bab20b21bb1782f11749a419c8e765f9b97` |
| `docs/contracts/online-convex-migration-v1/theorem_2_4.json` | `bc230447c286875213a0b812bb0186f9dbee7d77d9c86b05d0a64c36dcf217e3` |
| `docs/contracts/online-convex-migration-v1/top_upperAdd-header.txt` | `f114c2f20a1e985f7251e0831a7ace240ee54346078a98a41274ef7e6357cff4` |
| `docs/contracts/online-convex-migration-v1/top_upperAdd.json` | `1175afc79b4993b2609164c7c4a1250701ef3ca3d28792ff5f8bf32daebcb339` |
| `docs/contracts/online-convex-migration-v1/upperAdd_coe-header.txt` | `34bf757e67ed47245fbad8bcbf6057a0a31ff739ca7a39336dbc36ff51a30b33` |
| `docs/contracts/online-convex-migration-v1/upperAdd_coe.json` | `3216a04d6dedcddaa0f07df0d5a0df67b03eba57c87332d17d7705441635ff30` |
| `docs/contracts/online-convex-migration-v1/upperAdd_le_coe_iff-header.txt` | `f4d5b65724af4bf1fd69f7abfa817b4c4d2240e0d2fe9dcc9a190279ffd8e5b0` |
| `docs/contracts/online-convex-migration-v1/upperAdd_le_coe_iff.json` | `25b45caa6bba8ed1fc74ad71ac80ce0720a7602a0affb0dacbe44bc8fca7e811` |
| `docs/contracts/online-convex-migration-v1/upperAdd_top-header.txt` | `9ceecdd8cef602c789be41671919bc79c21dea9a2a350c3b6f292e7690af2aff` |
| `docs/contracts/online-convex-migration-v1/upperAdd_top.json` | `f89eef185e1ea1505e8289fda5323d822aba25f8e60c67674398f208b3598638` |
| `docs/contracts/online-convex-sums-v1/context.json` | `63cf0ea664a4be1ad65b543c4f015cbe1a9021b81effd143382390e445af4243` |
| `docs/contracts/online-convex-sums-v1/contract.md` | `809cbd2f812471e208d787f3853ab3edbaae9147c6a42af77959702f01c8c430` |
| `docs/contracts/online-convex-sums-v1/convex_nonneg_linear_combination.json` | `70299a1152ab14adfd824cebd9fa2e6da0c4e17511563f309f5d7e4b9d8aa79f` |
| `docs/contracts/online-convex-sums-v1/convex_nonneg_mul.json` | `dc725156739226df9d7ef2a9e17f79aabda50b979d33c6b467fe70199566f2a7` |
| `docs/contracts/online-convex-sums-v1/convex_upperAdd.json` | `2bb6aebc4dc26e970c00738e8b3dd228dd3fb3212df2f2f751b7bcad680f7378` |
| `docs/contracts/online-convex-sums-v1/headers.json` | `d49fc9d132fa045ce358df6687869ce5853990b99fc58ab54e446c4ff1f5fe8e` |
| `docs/contracts/online-convex-sums-v1/positive_mul_le_coe_iff.json` | `de3f07f77bba7ac3e24dbc39a1bc1095f2b45bd3cc619a92d71cb0f87c9a9409` |
| `docs/contracts/online-convex-sums-v1/top_upperAdd.json` | `25c314e291ee92a411b1b03199a4cda2733438208234bc29ee298e5f88f9d33e` |
| `docs/contracts/online-convex-sums-v1/upperAdd_coe.json` | `9a0cead85dc8457a362dcb589a43e704d66c8f600346dfc6226795b20301c21c` |
| `docs/contracts/online-convex-sums-v1/upperAdd_le_coe_iff.json` | `dfe07cc2ffc8f929df0b62f696c0605e387c3540f8b479ff96a898fde90278fd` |
| `docs/contracts/online-convex-sums-v1/upperAdd_top.json` | `1fe57d522e1aa2276149822e36ccaea71d8ef103c16a67f56f26def9f66a346f` |
| `docs/hierarchical_harness.md` | `6027004b33e316f5d47794ddbda01414ce6c811ba164163c7b2ece671b9468b7` |
| `docs/lifecycle_and_proof_frontier_hardening.md` | `335a861e00d13d59f88080ec54e6174722afc7534ad9e74f4261b4247f50165a` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `proof-obligations/ONLINE-CONVEX-MIGRATION-20261005.md` | `5084cb10a4d443706302ceb5c040d36cad644eda003cb0f230924ee51098bc69` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `runs/online-ch2-enumeration-20261005/source-navigation-draft-v1.json` | `d048e0adc6aec11efc83b4aa50c870c57b72008371960f00f487e57e236f3fd0` |
| `runs/online-ch2-enumeration-20261005/unnumbered-source-audit-draft-v2.json` | `2c882b170fd701871efe511d610b2aebce3a28396240262b49d1d5bca32ee77f` |
| `runs/online-convex-20260914/00_context.md` | `c01420b004173da8d0da75811c49bbada41c27c46db7d7acb8e55bf92c9bd968` |
| `runs/online-convex-20260914/04_reviewer.md` | `77abe8e190cebe003fbf27e2d280f8c06ea95402cb4da1b3ea6f6540d86111b6` |
| `runs/online-convex-20260914/acceptance-decision.md` | `331b764bf3fa7ee1f8991c4467dd68331d888ce77781f910938ed50dd92e177d` |
| `runs/online-convex-closures-20260914/00_context.md` | `0f2621bc12e3824cbd1b92d18226129aea99e701e2eaba6a6cac9747fef48a59` |
| `runs/online-convex-closures-20260914/04_reviewer.md` | `392a4c00da0835a908d3498754f8f584d3ba8a9a0c2fe200f0d874ff8c0b9c84` |
| `runs/online-convex-closures-20260914/acceptance-decision.md` | `796899a95f6bc2911cdbab1c800b187c76390268d03fc6a984ba7a0bdaf6780a` |
| `runs/online-convex-examples-20260914/00_context.md` | `015513d82edeb1a900f867a80ca6c2eddd49d7a3e46203d7b7a15e866d285333` |
| `runs/online-convex-examples-20260914/04_reviewer.md` | `fec31109288a7b64ac64989b38f321001cfcbe8221a97e939d27103b5867fd83` |
| `runs/online-convex-examples-20260914/acceptance-decision.md` | `212bda3ea960232c1c34177087d81fbd6b8164f5fb0f25475f0086b41f8cc505` |
| `runs/online-convex-migration-20261005/00_context.md` | `36f6c30a5961a60dab61df34a2ee48d3e835cb7783d58feca0de2870efedd1da` |
| `runs/online-convex-migration-20261005/10_upper_director-v1.md` | `4e59081bcd9cd926bc11c2e6d71f8a45e02f06c8771324a4db2110b15f18db70` |
| `runs/online-convex-migration-20261005/20_architect-v1.md` | `69cf307b513b005570a33053014b0aba63dace9a4449116188ca3b50198a34fc` |
| `runs/online-convex-migration-20261005/actual-declaration-retrieval-exit.json` | `ad31027618825589f930023117916d8676f5d317981f4e7a00a2950a98be53b5` |
| `runs/online-convex-migration-20261005/actual-declaration-retrieval.log` | `067b3494fd104d98ac756bf3550be1281dbf4979c65c43a068039af87f34f02f` |
| `runs/online-convex-migration-20261005/blind-packet-v1.md` | `fdb3770cbfb89203ed06c0f4de8cb0d112d733c4963da141ef55f5c2fef210c1` |
| `runs/online-convex-migration-20261005/blind-receipt-v1.json` | `d6fa0f3a6cd42f11cb09b921a9a806a0edd89b23f1a679053fdb99767296e133` |
| `runs/online-convex-migration-20261005/blind-reconstruction-v1.md` | `1beb18cf09e389309bc01083a307a535078b0e8b0440814100a013e0d94b2b1c` |
| `runs/online-convex-migration-20261005/convention-printed6-pdf17.txt` | `ab2c340c2a104b080c9b33c207aed87f7c029834699497d4fa802641409f78c9` |
| `runs/online-convex-migration-20261005/draft-freeze-v1.json` | `c5c4898b49dd4b3bb26d01f5c6d733d3a95f2d2cafe2de4f33d8fbe41385ce59` |
| `runs/online-convex-migration-20261005/draft-lifecycle-exit.json` | `f111776d7a9ffec198dc7e0d3a881bede7cfffe4cc195f45c5f9516b04dafc7d` |
| `runs/online-convex-migration-20261005/draft-lifecycle.log` | `5da8ad7784c525037cf94bdd9cc658cce6f0b931623e7cf0c19889407c3cd2d0` |
| `runs/online-convex-migration-20261005/fence-convexExtended_coe_iff-exit.json` | `24e2ed47cf92f856defeb3f307746ab679f3a7d7e2d014b4f232f0abb7ecfda1` |
| `runs/online-convex-migration-20261005/fence-convexExtended_coe_iff.log` | `205509be84315678ee423775555cfab386f6f2d9f2be00b7799519639ad44add` |
| `runs/online-convex-migration-20261005/fence-convexExtended_iff_toReal-exit.json` | `ffd336ace0bb1854b315c2b0029b780e55a9455a85e89e0c22be52fec9ab2262` |
| `runs/online-convex-migration-20261005/fence-convexExtended_iff_toReal.log` | `8edabb76e191a5112ad4259420310ece3e7b8d0e01845249c4bdaeef96f3d8f7` |
| `runs/online-convex-migration-20261005/fence-convex_add_indicator-exit.json` | `5dd31f01e4aa237c608b1fa123fc47087b1ae24e31713bbbc7f96e5dfc0b5010` |
| `runs/online-convex-migration-20261005/fence-convex_add_indicator.log` | `34d26c7c7f326acb3d21ef562e262a99f0cecdcd2e41cb3bc4b9161c38bb6996` |
| `runs/online-convex-migration-20261005/fence-convex_comp_affine-exit.json` | `d0804268237af237defe16d9738e7e384803a5fb74a78c53ef99b4c421fce443` |
| `runs/online-convex-migration-20261005/fence-convex_comp_affine.log` | `141fb849036174761ae81eb161e2bac8ef5d2feb726a1cb0c002b6c837b20cd9` |
| `runs/online-convex-migration-20261005/fence-convex_comp_monotone-exit.json` | `8f84ad6c8322e4e350887814d2fb2ca568842c74c85eb2d9831d06247f461167` |
| `runs/online-convex-migration-20261005/fence-convex_comp_monotone.log` | `b59cce18bfbc3d90181e6f2cf656acc36f9f74b55a4537ab8adb73f041e1cc20` |
| `runs/online-convex-migration-20261005/fence-convex_effectiveDomain-exit.json` | `976dac533a2e312f3e903aa1267ab2daf88e0912c6dc8f345b97af692c763c7b` |
| `runs/online-convex-migration-20261005/fence-convex_effectiveDomain.log` | `e744731d621aa63fb3f4ef37754aac45770144a2ec81b0981e8e8258193c44b8` |
| `runs/online-convex-migration-20261005/fence-convex_iSup-exit.json` | `76bd5b70b2788f1da66c811f5394712576f3bf54e8de2d21ff9b17408c296b01` |
| `runs/online-convex-migration-20261005/fence-convex_iSup.log` | `ac33c4f22ee2d304bb631c983e6aa4258d02453fc4b4af5e2f06f3277e585434` |
| `runs/online-convex-migration-20261005/fence-convex_indicator_iff-exit.json` | `b3cd591df4e244a51b75f83c824035c54564748ef84d60ac4b8229a61bd2a03e` |
| `runs/online-convex-migration-20261005/fence-convex_indicator_iff.log` | `83daf2b9d8192c2febd434a58a2d2396af7a93d662a4833736877cde9efe4eea` |
| `runs/online-convex-migration-20261005/fence-convex_nonneg_linear_combination-exit.json` | `54684c7263e5b4fd9acd50733d17f404af9505cd7a831e20b58f6bbad09d8f96` |
| `runs/online-convex-migration-20261005/fence-convex_nonneg_linear_combination.log` | `35aad511eafd813ae333990549d5402b1eeb8095170462b874f2811e560260a0` |
| `runs/online-convex-migration-20261005/fence-convex_nonneg_mul-exit.json` | `b583e9ac68c8bc7773b96e04736ebf822f6f41591127ddfb4604b9d41980d77f` |
| `runs/online-convex-migration-20261005/fence-convex_nonneg_mul.log` | `4ac46a0d5a7e509e524a25c2d996ffc5bcd4ac204fb33e9b7bdf30269c970aae` |
| `runs/online-convex-migration-20261005/fence-convex_upperAdd-exit.json` | `39a60456fb45acf5fc94c92f100f863a46297d666ca607b6bc8df92884a5fe03` |
| `runs/online-convex-migration-20261005/fence-convex_upperAdd.log` | `f8360f896fc90b379b97813a15bd77eb7d6941b17129a31a02018592b3227dab` |
| `runs/online-convex-migration-20261005/fence-definition_2_2-exit.json` | `1c1afb63f5a80d47b716e63aaa96c08fac24b99c920ab96b9bf2940eac2567f4` |
| `runs/online-convex-migration-20261005/fence-definition_2_2.log` | `48a82a1595b69afa2aa4fbdbdc97c4263a089ba0a15d42a29847dcff176e8022` |
| `runs/online-convex-migration-20261005/fence-effectiveDomain_indicator-exit.json` | `821ad60ae3bdef6d4f0e20190a938a09815e5aa09af3ea6a176cf3b46050cece` |
| `runs/online-convex-migration-20261005/fence-effectiveDomain_indicator.log` | `9ee1ea5557bb36e04d701bb139634dc0016c4e70e41b85fedc54933169f29873` |
| `runs/online-convex-migration-20261005/fence-example_2_5-exit.json` | `9a0890a49e8df60051c9a933427ecc3ff4972eedab80e07425d967ce5a0a58b6` |
| `runs/online-convex-migration-20261005/fence-example_2_5.log` | `bb26a7d723502e82b9a6f2eacf0ae499dd253b5105484bd0e00479bf23da03fb` |
| `runs/online-convex-migration-20261005/fence-example_2_6-exit.json` | `08ce3b307cb1eee43201ac4e268fedb54cd50ee1dc279170e3d828f49e14f794` |
| `runs/online-convex-migration-20261005/fence-example_2_6.log` | `b3aa21cfe65a8f245345990aa01af386125eff95b3d0a89ddc9d85dde23be292` |
| `runs/online-convex-migration-20261005/fence-positive_mul_le_coe_iff-exit.json` | `deee8f744081737ff4e72ea0f38ec03cc716f75e19e563e39f37cc3c9a040af0` |
| `runs/online-convex-migration-20261005/fence-positive_mul_le_coe_iff.log` | `0521a3e5195cf83876d16c6180b8dfbf80962e7e18e734f752d149e1024bd7b0` |
| `runs/online-convex-migration-20261005/fence-realEpigraph_toReal-exit.json` | `4c1ec3a788b073165a9a15faf9abab728dc03fc7e7d0ee0f68c6180b8fde0b77` |
| `runs/online-convex-migration-20261005/fence-realEpigraph_toReal.log` | `87b900ff50e9b923b652175dd29efaabb2fea3dc7ca086166f7392a41cbe5fb1` |
| `runs/online-convex-migration-20261005/fence-theorem_2_4-exit.json` | `13864b8f3c377b25b5c7f41b6ec1a6cbe700d10340858c4f969b98d0a9fd5e0e` |
| `runs/online-convex-migration-20261005/fence-theorem_2_4.log` | `3915b622419d1b9639527784f3ad7fedb74fe41b7038b5f87b4e05e62b74488e` |
| `runs/online-convex-migration-20261005/fence-top_upperAdd-exit.json` | `3c67d1321715a090d698824bbd2f3288dd55d4946bc12238c232d9ce3d17e45f` |
| `runs/online-convex-migration-20261005/fence-top_upperAdd.log` | `d69e563dfb3ac13953a1a70acc772eb040cf6303ef6d2912c91ba30683a80c2d` |
| `runs/online-convex-migration-20261005/fence-upperAdd_coe-exit.json` | `29f02cf792ff7068f561ab1e48eb2144f45df8b2b06ca7eb65cf193b90df636c` |
| `runs/online-convex-migration-20261005/fence-upperAdd_coe.log` | `569999e674ea06fe7b74370551c335576fe23ce50e7cca62c6f565c5b0f96abe` |
| `runs/online-convex-migration-20261005/fence-upperAdd_le_coe_iff-exit.json` | `61bcd10d11b4e3ac1108393e15297223057dc48b17e226c0bf26fda2b5811df1` |
| `runs/online-convex-migration-20261005/fence-upperAdd_le_coe_iff.log` | `7ef93e34cce459889c3179ed668fabcc8629c8486f943638c82c4be7aeba1b5c` |
| `runs/online-convex-migration-20261005/fence-upperAdd_top-exit.json` | `fc19aa716350c76f8a5ebcfc92af3832c6e43ca28b84188a3c02c42c7258afce` |
| `runs/online-convex-migration-20261005/fence-upperAdd_top.log` | `ded784b0b9a6372fe46870e6bbf54fe2ead8c46c8192516d671aa16d21118bc0` |
| `runs/online-convex-migration-20261005/native-fences/convexExtended_coe_iff.json` | `205509be84315678ee423775555cfab386f6f2d9f2be00b7799519639ad44add` |
| `runs/online-convex-migration-20261005/native-fences/convexExtended_iff_toReal.json` | `8edabb76e191a5112ad4259420310ece3e7b8d0e01845249c4bdaeef96f3d8f7` |
| `runs/online-convex-migration-20261005/native-fences/convex_add_indicator.json` | `34d26c7c7f326acb3d21ef562e262a99f0cecdcd2e41cb3bc4b9161c38bb6996` |
| `runs/online-convex-migration-20261005/native-fences/convex_comp_affine.json` | `141fb849036174761ae81eb161e2bac8ef5d2feb726a1cb0c002b6c837b20cd9` |
| `runs/online-convex-migration-20261005/native-fences/convex_comp_monotone.json` | `b59cce18bfbc3d90181e6f2cf656acc36f9f74b55a4537ab8adb73f041e1cc20` |
| `runs/online-convex-migration-20261005/native-fences/convex_effectiveDomain.json` | `e744731d621aa63fb3f4ef37754aac45770144a2ec81b0981e8e8258193c44b8` |
| `runs/online-convex-migration-20261005/native-fences/convex_iSup.json` | `ac33c4f22ee2d304bb631c983e6aa4258d02453fc4b4af5e2f06f3277e585434` |
| `runs/online-convex-migration-20261005/native-fences/convex_indicator_iff.json` | `83daf2b9d8192c2febd434a58a2d2396af7a93d662a4833736877cde9efe4eea` |
| `runs/online-convex-migration-20261005/native-fences/convex_nonneg_linear_combination.json` | `35aad511eafd813ae333990549d5402b1eeb8095170462b874f2811e560260a0` |
| `runs/online-convex-migration-20261005/native-fences/convex_nonneg_mul.json` | `4ac46a0d5a7e509e524a25c2d996ffc5bcd4ac204fb33e9b7bdf30269c970aae` |
| `runs/online-convex-migration-20261005/native-fences/convex_upperAdd.json` | `f8360f896fc90b379b97813a15bd77eb7d6941b17129a31a02018592b3227dab` |
| `runs/online-convex-migration-20261005/native-fences/definition_2_2.json` | `48a82a1595b69afa2aa4fbdbdc97c4263a089ba0a15d42a29847dcff176e8022` |
| `runs/online-convex-migration-20261005/native-fences/effectiveDomain_indicator.json` | `9ee1ea5557bb36e04d701bb139634dc0016c4e70e41b85fedc54933169f29873` |
| `runs/online-convex-migration-20261005/native-fences/example_2_5.json` | `bb26a7d723502e82b9a6f2eacf0ae499dd253b5105484bd0e00479bf23da03fb` |
| `runs/online-convex-migration-20261005/native-fences/example_2_6.json` | `b3aa21cfe65a8f245345990aa01af386125eff95b3d0a89ddc9d85dde23be292` |
| `runs/online-convex-migration-20261005/native-fences/positive_mul_le_coe_iff.json` | `0521a3e5195cf83876d16c6180b8dfbf80962e7e18e734f752d149e1024bd7b0` |
| `runs/online-convex-migration-20261005/native-fences/realEpigraph_toReal.json` | `87b900ff50e9b923b652175dd29efaabb2fea3dc7ca086166f7392a41cbe5fb1` |
| `runs/online-convex-migration-20261005/native-fences/theorem_2_4.json` | `3915b622419d1b9639527784f3ad7fedb74fe41b7038b5f87b4e05e62b74488e` |
| `runs/online-convex-migration-20261005/native-fences/top_upperAdd.json` | `d69e563dfb3ac13953a1a70acc772eb040cf6303ef6d2912c91ba30683a80c2d` |
| `runs/online-convex-migration-20261005/native-fences/upperAdd_coe.json` | `569999e674ea06fe7b74370551c335576fe23ce50e7cca62c6f565c5b0f96abe` |
| `runs/online-convex-migration-20261005/native-fences/upperAdd_le_coe_iff.json` | `7ef93e34cce459889c3179ed668fabcc8629c8486f943638c82c4be7aeba1b5c` |
| `runs/online-convex-migration-20261005/native-fences/upperAdd_top.json` | `ded784b0b9a6372fe46870e6bbf54fe2ead8c46c8192516d671aa16d21118bc0` |
| `runs/online-convex-migration-20261005/new-task-v1-01-exit.json` | `57d4d6ab355e0e76f72e8f4729ca22b1de6ad76eeddd5c13ab9e67eca21d1e73` |
| `runs/online-convex-migration-20261005/new-task-v1-01.log` | `ff750e0a23fe02031481de4e96e347d6775ac6bc12ee16425b1c701904e5571a` |
| `runs/online-convex-migration-20261005/original-OnlineConvexClosures.lean.txt` | `401d747a63de2205701e1defb25bde9341a60e1365b529fb78866555e54c2133` |
| `runs/online-convex-migration-20261005/original-OnlineConvexClosuresCanary.lean.txt` | `422d6bf8a8d64260839e8929e2c11213ab07e1c02a92d1834675886defa9729b` |
| `runs/online-convex-migration-20261005/original-OnlineConvexExamples.lean.txt` | `371918f1252c57e01ee71afb1bdbfd1d7715a3bb8e421308b8cb77a019ea94d6` |
| `runs/online-convex-migration-20261005/original-OnlineConvexExamplesCanary.lean.txt` | `398f09f34957b5ad89cbf9b2d35a472db45b0fb15066b454fb684c3b2e50f112` |
| `runs/online-convex-migration-20261005/original-OnlineConvexExtended.lean.txt` | `fec3efd071a069050593babb9eafee7262684b477b58ce8f045fe18c1add5d0f` |
| `runs/online-convex-migration-20261005/original-OnlineConvexExtendedCanary.lean.txt` | `d49bee7eae40c76579c9c0f56dc4d92012bf6e977ce8e4fe43e8be865f1ac8c7` |
| `runs/online-convex-migration-20261005/original-OnlineConvexSums.lean.txt` | `3087d7f69c36c7a02e4b28a17576629c57c851e38630352a2b66c5934116c758` |
| `runs/online-convex-migration-20261005/original-OnlineConvexSumsCanary.lean.txt` | `e1a0de929b121e83ad4fecbe0d9b2b31f1a1d5ff669fff8a1912d4df46e6140f` |
| `runs/online-convex-migration-20261005/pinned-api-retrieval-v1-01-exit.json` | `e8113bc0d3c54080f6f4a42934cd4b83dfcc595b09dd9a68d9c9d41de6df609c` |
| `runs/online-convex-migration-20261005/pinned-api-retrieval-v1-01.log` | `a2aa99c51f9dab8248169aa7cb7486700e2030f2b0e259df205a5d860d1493f6` |
| `runs/online-convex-migration-20261005/prepare-draft-v1-01-exit.json` | `01185d9b3a7992caf7d7883c3e7af10348a1b512273e384705d4e6d676e21873` |
| `runs/online-convex-migration-20261005/prepare-draft-v1-01.log` | `1769a557be42ec0aca42d5bdf9cf75d39e46cb9b765495455dc567da52decff8` |
| `runs/online-convex-migration-20261005/prepare-draft-v1.py` | `5e5e157ae74722903a9e54008973244a1c12139b59742e6ca01bbf5a56e18f1e` |
| `runs/online-convex-migration-20261005/prepare-source-review-v1.py` | `0f43862af0642eea5dbc1ef498f0c2711e565f2602c824975e191631d505193b` |
| `runs/online-convex-migration-20261005/proof-obligations-v1.json` | `f764ac916ab9d689986047b7c0ebd72fce9212da4de9971234aec80268b593b2` |
| `runs/online-convex-migration-20261005/ready-dependencies-v1.json` | `946d77391fa814330d259bc0193e343eb4b9abe54465308fa3a9f933365ba85e` |
| `runs/online-convex-migration-20261005/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `runs/online-convex-migration-20261005/source-printed9-10-pdf21-22.txt` | `33e607bfb535f9855173eb71d744ca5d6ff74f5f2cc4146d582b0535ac367ac3` |
| `runs/online-convex-migration-20261005/source-review-packet-v1.md` | `55d9cf390c27cbec1b835e49040260efc4fc0c9a985b4e455a81cd74fd504732` |
| `runs/online-convex-migration-20261005/workspace-workflow-audit-v1.json` | `358af463f1ffdec821e3a2bacce653108a5fdac9c0af1ec5788511e9756586fa` |
| `runs/online-convex-sums-20260914/00_context.md` | `4130d230ec81b616a5ae626f939578e4eac3055f9045baa2b04aa78af0bf5edd` |
| `runs/online-convex-sums-20260914/04_reviewer.md` | `278d6ce53da53bec1e79368db2d4755a4f657468dadafb42e7139542797245a3` |
| `runs/online-convex-sums-20260914/acceptance-decision.md` | `38fcbd6e943981307577b067ed831cbd98d10dd3845b67799d352fab46c6d571` |
| `runs/online-ftl-migration-20261005/accepted-decision-v1.json` | `fcf1f0de33811b6c9eecb8aa6b0af05ad51899660a8bd073853ff7c712398b08` |
| `tasks/ONLINE-CONVEX-MIGRATION-20261005.md` | `dc34c32fb3ec99d7cf41a53aa93967324c415e5e9ace11e0655f558f8b48866f` |
| `tmp/online-ogd-migration-full-graph.json` | `035630137ecb541e2680c1db4f0ce03b2380f46f322efc157227c6fc73bd9613` |
| `tmp/rockafellar-conjugate-duality.pdf` | `29d57ab07857b8270c175343746c77b4138f2db6161ae20174a0bba076991b0e` |
| `website/content/chapters.json` | `02657d915f7ef37567b798d37c3790049876120c1e40e4ee73ffc63fb2048cd4` |
| `website/content/highlights.json` | `ab9d73d726173b9be1d2986c769e6e8c2cd1a14240f0ae1228772e3d828d4ea8` |
| `website/content/readings.json` | `d9cab8bde84e6210253d52bc116f896156935cf57d64c63e1f8bdfa993823f7c` |
| `runs/online-convex-migration-20261005/contract-source-inputs-v1.json` | `0dd174117a08998ec7845c8e35179d35cf884927b1d044e5b88e67012d703d9d` |
| `.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean` | `bf69a9ed4bc39134bbefac1a43b187e2f1e66fd43f352d0810ab89474f054922` |
| `.lake/packages/mathlib/Mathlib/Data/EReal/Operations.lean` | `50717cddbcd70f8650cf25c4bd37f07e07de14ee8117099a4d9f7aee6d36a791` |
