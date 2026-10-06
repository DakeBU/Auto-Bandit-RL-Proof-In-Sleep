# Distinct BODY review — Theorem 2.23

Verdict: **accepted-with-explicit-delta**, for the actual nine production proofs, complete witness definition and twenty old canary proofs/three canary definitions. No mathematical repair is required. This is not final package or reader acceptance.

Actor `/root/source_reviewer`, requested GPT-6 Astra / medium, distinct automated reviewer with disclosed prior project/contract history. No human, external-model or runtime model attestation is asserted. The source-blind actor's current restricted packet and prior actor history are preserved honestly.

All **379** fixed raw hashes and **291** prior contract raw bindings independently match. The production module and whole old canary match original raw bytes exactly; all nine normalized public headers reproduce frozen hashes. The inventory is separately bound. Actual semantic review uses source/complete declarations and producer bodies, full old canary, relevant shared interfaces and current logs/graph; administrative/history inputs are integrity checks, not blanket mathematical acceptance.

## Source, full definition and explicit deltas

Orabona v10 printed17–18/PDF29–30, PDF digest `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`: one printed Theorem2.23 has both inclusion and equality branches. Source pages and the actual current bytes remain those independently read in the immediately preceding contract pass; their equality was rechecked here. Neither prior acceptance nor compilation substitutes for this body judgment.

`SourceSubgradientSum` is the complete set of g admitting an ACTUAL simultaneous G, each G(i) a global support of f(i) at the SAME x, with vector sum g. It has no functional premises or finite-dimensional binder; it is not an aggregate-support alias. Empty family gives {0}, singleton its component set, empty component set empties the witness set. All individual supports quantify over every ambient y. Six vector proof interfaces retain finite-dimensional real inner-product classes; three scalar interfaces have no E. Completeness is derived and dimension zero permitted.

The source Def2.20 proper-function restriction and generic all-EReal support convention remain a necessary explicit delta. Proper component indicators of disjoint real singletons give an identically-top, improper aggregate: its generic S is ALL vectors, while the component Minkowski set is empty. Inclusion remains true and vacuous; this is not an improper outside-domain emptiness theorem or a support-existence guarantee. No aggregate properness or common point is added to inclusion. Ordinary EReal addition differs from upperAdd on mixed infinities; proper component nowhere-bottomness avoids that conflict.

Equality retains every proper/convex/CLOSED input, and exactly one z in LAST domain and all OTHER AMBIENT interiors, independent of arbitrary query x. This qualification produces a common finite point and proper aggregate. Given a real support, query/component finiteness is genuinely derived. The stronger binary helper lacks closedness but has explicit query-finite hypotheses, which must not be silently promoted to source-terminal assumptions. Singleton nonlast-interior clauses are vacuous while its proper/convex/closed binders remain.

## Nine targets: seven slots and actual producers

### `BanditRL.OnlineConvex.upperAdd_eq_add_of_ne_bot`

BODY verdict: **accepted-with-explicit-delta**.

- **objects spaces**: Scalar a,b:EReal; no E or space classes.
- **quantifiers**: Every pair excluding bottom.
- **assumptions**: a != bottom and b != bottom.
- **conclusion**: upperAdd a b = ordinary a+b.
- **constants**: Exact identity.
- **information probability**: Deterministic assertion; no algorithm, measurable selection, probability, regret, uniqueness or executable oracle.
- **boundaries**: Top permitted; mixed top/bottom excluded, where the operations differ.

Actual proof: Cases on both EReal arguments and exclusion of bottom establish agreement with upperAdd; no unconditional mixed-infinity identity is used.

### `BanditRL.OnlineConvex.ereal_finset_sum_ne_bot`

BODY verdict: **accepted-with-explicit-delta**.

- **objects spaces**: Arbitrary index type, finite set s, scalar EReal values; no E.
- **quantifiers**: Every member of s has no bottom value.
- **assumptions**: Pointwise noBottom on s only.
- **conclusion**: The finite scalar sum is not bottom.
- **constants**: Empty sum zero.
- **information probability**: Deterministic assertion; no algorithm, measurable selection, probability, regret, uniqueness or executable oracle.
- **boundaries**: Top allowed; does not establish finite sum or a common finite point.

Actual proof: Finite-set induction uses add_ne_bot_iff on the inserted value and actual inductive sum; empty sum is zero. Top is permitted.

### `BanditRL.OnlineConvex.convex_finset_sum`

BODY verdict: **accepted-with-explicit-delta**.

- **objects spaces**: Finite-dimensional real inner-product E; finite set of EReal functions.
- **quantifiers**: Every indexed component on s and every ambient y.
- **assumptions**: Each component convex and nowhere bottom; no common finite point.
- **conclusion**: Ordinary pointwise finite sum has convex real-height epigraph.
- **constants**: Empty set yields constant zero.
- **information probability**: Deterministic assertion; no algorithm, measurable selection, probability, regret, uniqueness or executable oracle.
- **boundaries**: Aggregate may be identically top and improper; convexity is not properness.

Actual proof: Finite-set induction first produces nowhere-bottom for the partial sum. Existing convex_upperAdd produces convexity; the noBottom identity rewrites it to ordinary addition. No common finite point is inferred.

### `BanditRL.OnlineConvex.finite_sum_point`

BODY verdict: **accepted-with-explicit-delta**.

- **objects spaces**: Finite-dimensional real inner-product E and arbitrary Fintype family.
- **quantifiers**: At the same x each component has an actual real witness.
- **assumptions**: All component values at x are finite; no global properness or convexity.
- **conclusion**: There exists a real witness for the aggregate at x.
- **constants**: Finite sum of witnesses, empty case zero.
- **information probability**: Deterministic assertion; no algorithm, measurable selection, probability, regret, uniqueness or executable oracle.
- **boundaries**: Pointwise finiteness, not a neighborhood or derivative assertion.

Actual proof: Chooses actual real witnesses at the same x and uses a real-to-EReal additive homomorphism and map_sum to exhibit their real sum.

### `BanditRL.OnlineConvex.sum_finite_implies_components_finite`

BODY verdict: **accepted-with-explicit-delta**.

- **objects spaces**: Fintype scalar EReal family, no E classes.
- **quantifiers**: Every component i.
- **assumptions**: All a(i) != bottom and total sum != top.
- **conclusion**: Every component equals an actual real number.
- **constants**: Exact finiteness.
- **information probability**: Deterministic assertion; no algorithm, measurable selection, probability, regret, uniqueness or executable oracle.
- **boundaries**: The noBottom hypothesis is essential to rule out mixed-infinity masking; empty family conclusion vacuous.

Actual proof: If one component were top, add_sum_erase and nowhere-bottom of the remainder would make the total top, contradiction. Both infinity exclusions then justify each toReal witness.

### `BanditRL.OnlineConvex.interior_domain_sum`

BODY verdict: **accepted-with-explicit-delta**.

- **objects spaces**: Finite-dimensional real inner-product E; Fintype family and z.
- **quantifiers**: One z lies in every component AMBIENT domain interior.
- **assumptions**: All components nowhere bottom; no convexity assumption.
- **conclusion**: z belongs to ambient interior of the sum domain.
- **constants**: Finite intersection of neighborhoods; no supplied radius.
- **information probability**: Deterministic assertion; no algorithm, measurable selection, probability, regret, uniqueness or executable oracle.
- **boundaries**: Only prefix helper uses all interiors; not the mixed source terminal. Empty family gives whole-space domain.

Actual proof: Finite eventual_all intersects actual finite-part neighborhoods at z; pointwise real sum witness proves a neighborhood belongs to aggregate domain. This is the prefix helper, not a replacement of the source mixed condition.

### `BanditRL.OnlineConvex.binary_subgradient_decomposition`

BODY verdict: **accepted-with-explicit-delta**.

- **objects spaces**: Finite-dimensional real inner-product E; proper convex f,h.
- **quantifiers**: Every finite queried x, every aggregate support g; separate exists z in int dom f intersect dom h.
- **assumptions**: Component properness/convexity, both actual finite values at x, aggregate global support, mixed qualification. No closedness.
- **conclusion**: There exists actual p supporting f at x and g-p supporting h at x.
- **constants**: Exact complementary sum g.
- **information probability**: Deterministic assertion; no algorithm, measurable selection, probability, regret, uniqueness or executable oracle.
- **boundaries**: Stronger helper lacks closedness but requires query finiteness. Last h may be boundary at z. Not a global set equality or universal support existence.

Actual proof: Actual convex epigraph-product image gives contact at (0,q). Aggregate support bounds that slice; a local minimum of identity excludes interior. Nonzero supporting L splits as A+ct. Upward height implies c<=0; c=0 gives a local maximum of A at the qualifying interior point and forces A=0, contradicting L nonzero. Hence c<0 allows legal division and Riesz to construct p. Two epigraph substitutions yield global p and g-p inequalities; top branches are handled before finite-part conversion.

### `BanditRL.OnlineConvex.theorem_2_23_inclusion`

BODY verdict: **accepted-with-explicit-delta**.

- **objects spaces**: Finite-dimensional real inner-product E; arbitrary Fintype family.
- **quantifiers**: Every x and every actual simultaneous component-support witness G.
- **assumptions**: Only component properness; no convexity, common point, query finiteness or closedness.
- **conclusion**: Witness-defined Minkowski sum is contained in global support set of the ordinary sum.
- **constants**: Any finite size, including empty indexing as explicit library extension.
- **information probability**: Deterministic assertion; no algorithm, measurable selection, probability, regret, uniqueness or executable oracle.
- **boundaries**: Proper components do not imply proper aggregate. If identically top, generic support set is E and Minkowski side is empty; not an improper outside-domain emptiness claim.

Actual proof: Unpacks the actual simultaneous G witness and sums all individual global inequalities. Finset.sum_add_distrib, sum_inner and additive map_sum yield the aggregate inequality for every ambient y. Properness is retained in the source header despite unused warning; it is not replaced by convexity or finite-point assumptions.

### `BanditRL.OnlineConvex.theorem_2_23_equality`

BODY verdict: **accepted-with-explicit-delta**.

- **objects spaces**: Finite-dimensional real inner-product E; positive family Fin(n+1).
- **quantifiers**: Every n,f and queried x; one independent z in last domain and ALL OTHER ambient interiors.
- **assumptions**: Every component proper, convex and SourceClosed; exact mixed qualification. No query-finiteness or aggregate-proper premise.
- **conclusion**: Global support set of sum equals actual simultaneous component Minkowski sum for every x.
- **constants**: n=0 singleton; no empty-family equality endpoint.
- **information probability**: Deterministic assertion; no algorithm, measurable selection, probability, regret, uniqueness or executable oracle.
- **boundaries**: Closedness retained for all, including last. Singleton nonlast-interior conditions vacuous, but P/C/closed binders remain. Qualification derives proper aggregate; outside-domain both sides empty legitimately.

Actual proof: Induction on n: singleton directly reuses its actual support without an interior requirement. Successor uses the common z to produce prefix properness/convexity/interior and aggregate properness. Actual aggregate support then forces query finiteness and every component finite. Binary splitting yields p and g-p; recursive equality yields a prefix witness, and Fin.snoc gives all component memberships and exact total g. Closedness is retained and passed recursively, although the stronger binary producer does not consume it.

## Canary nonvacuity

The entire old module contains twenty proofs and three fixture definitions, not merely the final examples. It actually establishes square/interval/family properness, convexity, closedness and mixed qualification before invoking the source equality. Its aggregate -1 support for two squares plus the [0,2] indicator at 0 is proved directly; the equality then supplies an actual three-component witness. The last component domain boundary at 0 is proved, so an all-interiors substitution would fail this example. At 3 component support impossibility and source equality prove both sides empty under a genuinely proper qualified aggregate.

The one-component REAL singleton example supplies its own proper/convex/closed premises, proves empty ambient interior and produces support7 through the singleton equality. It makes no zero-dimensional empty-interior claim. Quadratic-plus-constraint support2 uses an explicit actual component witness and public inclusion. The empty-index example also invokes inclusion. The concave quadratic fixture proves no support at0 using y=1 and y=-1; its companion proves empty Minkowski membership. It does not directly invoke inclusion or separately prove a named nonconvexity statement. No improper-disjoint-domain example is claimed as a new compiled canary; that convention remains an explicit semantic audit, not invented test coverage.

No decomposition, desired bound or dual-attainment oracle is assumed. The local extrema in separation apply to auxiliary identity/linear functionals, not differentiability of the losses. Proof choices have no algorithm, probability or computability interpretation.

## Actual evidence and limits

Public body re-elaboration exited0 in20.094s; focused module build reports3319jobs and whole-canary build9091jobs. These include cached/replayed jobs, not clean recompilation of every item. The actual full named kernel log independently parses to29 UNIQUE names and only propext/Classical.choice/Quot.sound, no sorryAx. Nine native guards are separately passed statement/scan checks, not compilation. Unsuppressed unused-premise/section and tactic linters are nonblocking; preserving source premises is intentional.

Actual compiled selected graph has33nodes: nine production proofs, one full M definition, twenty canary proofs and three canary definitions, with2844directreferences. Independently checked22required value calls in node dependencies and exact equality of every original10node/1146reference readiness node. This is not the full declaration registry. A module import does not manufacture a direct T2.22 production value edge. Preparation/count/path/CLI mistakes remain historical diagnostics, not concealed theorem repairs.

## Reader obligations still separate

1. Explicitly label ONE printed Theorem 2.23 with TWO branches; nine proofs and one definition are library refinements, not nine printed results or new mathematics.

2. Publish the precise improper-aggregate convention next to inclusion: Definition 2.20 restricts proper functions, but generic S extends to all EReal; disjoint proper domains give identically top sum with S=E and empty Minkowski side. Do not say the improper aggregate support is empty or silently assume aggregate proper.

3. Describe ordinary EReal addition versus upperAdd: mixed infinities differ; component properness excludes bottom and legitimizes their agreement here. Proper components alone do not provide a common finite point.

4. Keep exact all-x positive-family equality with independent qualifying z, last-domain membership only and all other AMBIENT interiors. Singleton qualification reduces to nonempty last domain but actual proper/convex/closed premises remain; this is not a theorem with only nonempty-domain assumptions.

5. Explain complete simultaneous witness definition and the empty-Fintype inclusion extension. Real singleton empty-interior example must remain explicitly on the real line; zero-dimensional E is allowed by general targets.

6. Distinguish stronger binary helper without closedness and with query-finite inputs from the source equality, which retains ALL closedness inputs and derives aggregate properness and query finiteness.

7. Explain actual epigraph image/separation, strict negative height coefficient and normalization/Riesz, then prefix interior/properness and Fin.snoc induction; no decomposition/dual-attainment oracle or algorithm is assumed.

8. Publish exact class scope: six vector theorems finite-dimensional real inner-product, three scalar theorems without E, full definition without finite-dimensional binder; completeness derived. Closed means real sublevels, not necessarily closed effective domain.

9. Replace stale historical gate wording with current evidence: 29 unique named standard-axiom checks, nine separate guards, selected33nodes2844refs/22actualvaluepairs including whole20canaryproofs3defs. The original10node1146ref graph is exact. Combined gates/site/FINAL still remain separate.

10. Preserve original four curated route links and all ten canonical module links. Twenty unchanged canary proofs/three definitions now have fresh focused/kernel evidence; the concave fixture proves support absence but does not itself invoke inclusion or prove a named nonconvexity proposition.

11. Keep adjacent Example2.24/later Chapter1/2/appendix and whole-book obligations mandatory, Chapter2 null/incomplete and Goal active; local contract acceptance is not package, main or live acceptance.

## Disposition

Mathematical repairs: none. No production source, old report or fixed input was changed. Combined root/Tests/full harness, contributor/history gates, reader/site/registry/browser/FINAL review, immutable acceptance and actual PR delivery remain required. This accepts actual bodies only for one T2.23 source result with two mandatory branches; zero new production or Test mathematics was introduced. Adjacent Example2.24 and later Chapter1/2/appendix/book obligations remain mandatory. Chapter2 totalnull/incomplete and the whole Goal remain active; no main/merge/deployment/live/retirement acceptance.

## Exact raw reviewed files

| Path | SHA-256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean` | `4130e166fde65ec3815b73c94021a2a30aa99374de6ddbf5aa97f0e192d492ea` |
| `.lake/packages/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean` | `ec09dfe037c654dc65051e22fd9e1d76055ef340089a631c304b700d0406109e` |
| `.lake/packages/mathlib/Mathlib/Analysis/Convex/Basic.lean` | `7518823b27d039545d9aaecc7fada405751d0ccb9d83dbb2adeb9a15148d3359` |
| `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean` | `e80bb3d346ad6dcaceab9c99dd57025809e3beffded7f92b71104df5fc72d698` |
| `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean` | `6e25613a0a200590fe3510cb618efd1addac49928d5b6361c2be2cf3951908c3` |
| `.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean` | `bf69a9ed4bc39134bbefac1a43b187e2f1e66fd43f352d0810ab89474f054922` |
| `.lake/packages/mathlib/Mathlib/Data/EReal/Operations.lean` | `50717cddbcd70f8650cf25c4bd37f07e07de14ee8117099a4d9f7aee6d36a791` |
| `BanditRLProof.lean` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `BanditRLProof/OnlineClosedProper.lean` | `c66f00c33b45fb8a0e11583eeadf506e176c16166ce2af02f41f0674507cebe7` |
| `BanditRLProof/OnlineConvexBarycenter.lean` | `beb198b8be313c36a73eb1e20acdc8b8845d40d18d70f169c129a35c338f36c0` |
| `BanditRLProof/OnlineConvexExtended.lean` | `bd30bb95a46ccdc3f6d25f808c175af5fee71d075c2b46ffcf6508f15f1ed66a` |
| `BanditRLProof/OnlineConvexSums.lean` | `0abd620cb419fec2899146a3f201401aaa410d01409a33c81836b54dcfd932ca` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `BanditRLProof/OnlineSubgradientDifferentiability.lean` | `4f21c5d7fd0ef27a860390b698072d65527610d55e60c16568e82fa99215c1d3` |
| `BanditRLProof/OnlineSubgradientSum.lean` | `8fbeaa5f8d46df667db31373d712d9a7ca494c8ff8948f2cb45a2299b35440da` |
| `MANIFEST.md` | `ee59861c268dab0971eb9b96444169df6a21297c582e7becdca3740ae98a0e9d` |
| `Tests.lean` | `cd21ef4e7cea89c7d245eaf4dff14be8baa34f2d336e40d6f6bbb16011678340` |
| `Tests/OnlineSubgradientSumCanary.lean` | `a0c773f08fd5c597bb12a92f71e33f0438e8211bf998c8cd5d370ce263c2d234` |
| `conversion-windows/ONLINE-SUBGRADIENT-SUM-MIGRATION-20261007.md` | `dfe9f138591f3f231bdb64185f9b909f092595ef6c0cd447fc0fab7b2cfb7b9e` |
| `docs/contracts/online-barycenter-migration-v1/integral_mem_convex_finiteDimensional-header.txt` | `41b6ac00a399c7563f8649aff881d221bf00368a95d564c645da5345601d1f24` |
| `docs/contracts/online-barycenter-migration-v1/integral_mem_convex_finiteDimensional.json` | `4b794c9bbd3e79c648f94315c9f0bcb154df988ecd3cbea80d99007f94e6d923` |
| `docs/contracts/online-barycenter-migration-v1/scoped-contexts.json` | `b28181ee60e5a9d4bd636f71fac87826897f9822e58b60d674f3fe2132f84634` |
| `docs/contracts/online-barycenter-migration-v1/source-card.json` | `7c219502f544c670ab1b7f5e81628bb7b1506cd068797aa6e8e147e5d16c24d7` |
| `docs/contracts/online-barycenter-migration-v1/source-intent.md` | `a448cb43a6ef2631f179e28eb26174f2644dbbbca50add65b3c07f831e7871ec` |
| `docs/contracts/online-barycenter-migration-v1/supporting_functional_ae_eq_mean-header.txt` | `f2c7ff1bb073e956a2f840829843f3e62002f255f2c88df8f15bbddcc90022ca` |
| `docs/contracts/online-barycenter-migration-v1/supporting_functional_ae_eq_mean.json` | `a0757c9f4feed80e519618d6aaacb2830f8714c25cc2e9c9b00b018e8e823ad0` |
| `docs/contracts/online-barycenter-migration-v1/supporting_functional_at_closure-header.txt` | `04203cec9cdcdd7717909c970a5f8bad28e068ec722322ff237a0c69f76d1811` |
| `docs/contracts/online-barycenter-migration-v1/supporting_functional_at_closure.json` | `d4fa06954fbe16bc5ae924a222e9c284205fc591f6242ce68e43be6c6354ef79` |
| `docs/contracts/online-closed-proper-migration-v1/dependency-DAG-v1.json` | `3659660c05afa78390cd8ea3fc7e8158e5f52d2471980a1d976bba15a5f136dd` |
| `docs/contracts/online-closed-proper-migration-v1/headers.json` | `ecc8b8932b44fca5a1ba8864823b3efa92987ba9e5d716b0e94d1d3d28839fc2` |
| `docs/contracts/online-closed-proper-migration-v1/scoped-contexts.json` | `79fab5a659166c38133c8c3c9dd818af16a14995199df8f241f3131b145dbf7b` |
| `docs/contracts/online-closed-proper-migration-v1/source-card.json` | `d34ab01cb96ead6bcef78188908af12bd27ace1c825b6ba8e1fa918adf1b4db4` |
| `docs/contracts/online-closed-proper-migration-v1/source-intent.md` | `3da680aaec30807ecabfdfa2ac6e23d16ded2d8f230d75fd70777790b37c89aa` |
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
| `docs/contracts/online-subgradient-basic-migration-v1/dependency-DAG-v1.json` | `bd14bcd04f062212ea2ee12502e6778b99a1b348fe4ebf29986703e138f82259` |
| `docs/contracts/online-subgradient-basic-migration-v1/headers.json` | `c7b60223ad97ffd4ea481e6b320252b31fbd3f373aa85413be671bbf2b09b83d` |
| `docs/contracts/online-subgradient-basic-migration-v1/scoped-contexts.json` | `8f9505e35d08a2a20a5896dc765157d19c6e8edfc0641271121cd1b9fddbd86f` |
| `docs/contracts/online-subgradient-basic-migration-v1/source-card.json` | `e7870fade027b927a69475c040536c95a1ffb64041d2538165f74872603e80bc` |
| `docs/contracts/online-subgradient-basic-migration-v1/source-intent.md` | `d49174fb1d280462c0d22ab43c7cb2d8f5f834ea62929274063960a0bcb359aa` |
| `docs/contracts/online-subgradient-differentiability-migration-v1/dependency-DAG-v1.json` | `9d9c6af7e1b7a3d036b6c73c9314fa03fcb80ffbc2ae377cd917d5103ed6a70e` |
| `docs/contracts/online-subgradient-differentiability-migration-v1/headers.json` | `6be24efdabc55ce4a25d4afed47df44f446bd160a9d8a9cac3ee766ba64adea6` |
| `docs/contracts/online-subgradient-differentiability-migration-v1/new-canary-terminals-v1.json` | `16d6fff3a655810b9901714deef09cabdae3ca5e96dcc03d4005a32690ecf96e` |
| `docs/contracts/online-subgradient-differentiability-migration-v1/scoped-contexts.json` | `22415309433d0e8465553ab3b05d0f893726022fde0b9d7fdcdcd8ef72410c77` |
| `docs/contracts/online-subgradient-differentiability-migration-v1/source-card.json` | `370156fa9c3b224fa93ebbe74b05fa8c6471e8b1a191871b90754e2a180ad836` |
| `docs/contracts/online-subgradient-differentiability-migration-v1/source-intent.md` | `1a730fc9eae224025dfc48b2ff603bd858aa9111ba6630b7ec5b295e14d4addf` |
| `docs/contracts/online-subgradient-sum-migration-v1/dependency-DAG-v1.json` | `7b11546c0e5a145d23936336d8ed08b76bb573598ff830327ffb316796339394` |
| `docs/contracts/online-subgradient-sum-migration-v1/headers.json` | `f0a3d44453462a19e4f2881da5995aeade6327fa7984518fee57140963f09a42` |
| `docs/contracts/online-subgradient-sum-migration-v1/scoped-contexts.json` | `bdca3e33be8de7d8d38d9436803c07f296649dfe38b44ea03b47ac85cba38389` |
| `docs/contracts/online-subgradient-sum-migration-v1/source-card.json` | `151f4e89fa6548c60e348a8b3f51298f9ef0ff687efb502261dc3bde57b49f68` |
| `docs/contracts/online-subgradient-sum-migration-v1/source-intent.md` | `1b44021de5273fd724cd58e6d824e7b6b9c9c1c402d0c30b6a8a81d4316fcde3` |
| `docs/contracts/online-subgradient-sum-public-v1/binary_subgradient_decomposition.json` | `c305f9a0b51cbeb9f47fcd72673bc1cab268b0d72f26947d8ebd1ff44f57211c` |
| `docs/contracts/online-subgradient-sum-public-v1/convex_finset_sum.json` | `2dcdfc3fbd7177daef8893336f014acf9e8053c84b0ae2b167726919973de6bc` |
| `docs/contracts/online-subgradient-sum-public-v1/ereal_finset_sum_ne_bot.json` | `68dffd2d785635381c916df88bea04b5d9a8e41793314bacdd83e3f4f9345559` |
| `docs/contracts/online-subgradient-sum-public-v1/finite_sum_point.json` | `314ef3e05c41abc0817ac6b49ba5cbc9f9df86d268d35a6b378883af5d370c6e` |
| `docs/contracts/online-subgradient-sum-public-v1/integration.json` | `8b72354a62baf9ae7260dc5e0a0ba1349dd27f589fc6d518dafa69ac9a663f3d` |
| `docs/contracts/online-subgradient-sum-public-v1/interior_domain_sum.json` | `6c3b5099b9c09e873ae796f84aa8cb69b494c31f3ae3d41dff79fd948f84d134` |
| `docs/contracts/online-subgradient-sum-public-v1/sum_finite_implies_components_finite.json` | `5ba7803ca88e4f405ff63dc111533f6491fbd9a348e5a9643d2a326be3d71bb2` |
| `docs/contracts/online-subgradient-sum-public-v1/theorem_2_23_equality.json` | `5f1cbca43e829198332f18614f3bb3bdef02e4abc55f9f90dc17faa9138f02a6` |
| `docs/contracts/online-subgradient-sum-public-v1/theorem_2_23_inclusion.json` | `29936a877003eab81a664a35ed706a8126255e21b9e80fd28399a866d14ed88c` |
| `docs/contracts/online-subgradient-sum-public-v1/upperAdd_eq_add_of_ne_bot.json` | `23c30cd536c3a962ed128c3abc6b55d929b22b9b22a5bc692be61e12a9c9d8ef` |
| `docs/contracts/online-subgradient-sum-v1/binary-header.txt` | `e55042ed6e6f5675bd820475633e30f466e23426e6698c47f92ea61f215fe45a` |
| `docs/contracts/online-subgradient-sum-v1/binary_subgradient_decomposition.json` | `f640f1ac8a4307d6244a0a27a9e5d3bf2247b8acf531f3e34bb49885dc8037f1` |
| `docs/contracts/online-subgradient-sum-v1/context.txt` | `7c49b10c1e933dac2f41ebfb195151224156c14f6ef81fed82a5c4269d5ee1d8` |
| `docs/contracts/online-subgradient-sum-v1/contract-manifest.json` | `1992bd69dba31dfca18b50640e7fb9f7708731658fc70d3bba86fd2be7578d8b` |
| `docs/contracts/online-subgradient-sum-v1/contract.md` | `5b09efee5962772ecadb5afc63a85d560c2c2483c4003b6ff61520c0bd7095ac` |
| `docs/contracts/online-subgradient-sum-v1/convex_finset_sum.json` | `5bb829df97ab29fd98fe68589b1e98d9aab62ba350faac675aa0a9999e7e8af2` |
| `docs/contracts/online-subgradient-sum-v1/equality-header.txt` | `04daea804ef2da692817458481240e079892c03383e83acd3b9f20f1f2ea32da` |
| `docs/contracts/online-subgradient-sum-v1/ereal_finset_sum_ne_bot.json` | `5480fa8069ded8f42664ea0b90a2c4fd478a347472467744a0e27d15ba0363d4` |
| `docs/contracts/online-subgradient-sum-v1/finite-helper-context.txt` | `fd76eb63a9e585973636264be788c592ea9f2bafd8e6886dea91d17edaaab96a` |
| `docs/contracts/online-subgradient-sum-v1/finite-helper-headers.txt` | `e299273be2118dfa7da9fb41d9b05cb61080769aa788f84508517c402a7957a9` |
| `docs/contracts/online-subgradient-sum-v1/finite_sum_point.json` | `9339484e04e3dae3ef99ca4a0da939f4d73bc4cb8d6aaba7e1b9e8c4c439d6e8` |
| `docs/contracts/online-subgradient-sum-v1/inclusion-header.txt` | `9cd548022c463e6be3631685a7c687116b176f005341eecbb7f324f26273124b` |
| `docs/contracts/online-subgradient-sum-v1/interior_domain_sum.json` | `690a50f77f54ed9d0298598c57a6b3579f39fa29032ceef53526e0d741114700` |
| `docs/contracts/online-subgradient-sum-v1/sum_finite_implies_components_finite.json` | `fcab66c63ef7b6a8708966d8f9bef1b357bbbae5573605c52f5456d9bcb80497` |
| `docs/contracts/online-subgradient-sum-v1/theorem_2_23_equality.json` | `a6b11235782600cdef78d90c4ebbe2fa7ca274bec7654530a510afa6a50f06ca` |
| `docs/contracts/online-subgradient-sum-v1/theorem_2_23_inclusion.json` | `e09198bb68b61320952decb46f359ef0633e49518b5ecf79dc12358052a16471` |
| `docs/contracts/online-subgradient-sum-v1/upperAdd_eq_add_of_ne_bot.json` | `8a1b8d4c0aaf6db44d512ed426dc0c861068a803a65c5718eb337bf762d5d366` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `proof-obligations/ONLINE-SUBGRADIENT-SUM-MIGRATION-20261007.md` | `dfe9f138591f3f231bdb64185f9b909f092595ef6c0cd447fc0fab7b2cfb7b9e` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `runs/online-barycenter-migration-20261005/accepted-decision-v1.json` | `5f23be0e6b4dc407d991084751dacadd21379b2755d84118e5150dd5c28388b9` |
| `runs/online-barycenter-migration-20261005/final-reader-receipt-v1.json` | `b467d48bb60fc1a0347139266d04303e63e4bf835baea7a03818e67e198d8544` |
| `runs/online-barycenter-migration-20261005/final-reader-review-v1.md` | `16ec495943d9a42aa8dd4e5d3d2a43a6cf5d7544fac4021872e2609ff23d40a8` |
| `runs/online-barycenter-migration-20261005/pr-delivery-v1.json` | `a2cbf7ccb2f87d1ddd164f033f307959023b417e0dbc473ca94a40155a696a97` |
| `runs/online-closed-proper-migration-20261006/accepted-decision-v1.json` | `638d4873b46f2189adc1a5145a9cf6efd5a47ce7ddf164e10c69b42cf1b3c41f` |
| `runs/online-closed-proper-migration-20261006/delivery-v1.md` | `3f38739febc454354d2cb044526d6f545d92ba5e480659b42fbb37d9def663e2` |
| `runs/online-closed-proper-migration-20261006/final-reader-receipt-v1.json` | `29fff14670caff6ebaef064e86daf228dee7c3747d5f9bcae57c63244d472751` |
| `runs/online-closed-proper-migration-20261006/final-reader-review-v1.md` | `e379ec039e1ffe9bf5389c05200461429c3b256a5e25344250ca14d65d8a7355` |
| `runs/online-convex-migration-20261005/accepted-decision-v1.json` | `f51a42a62f280cee72b6747415ab55762f313797d1c748ac332a9d7b3262123b` |
| `runs/online-convex-migration-20261005/final-reader-receipt-v1.json` | `78d303a13f5b87cc71046f06f1c8da4708522d98a311fffec9c8159599320235` |
| `runs/online-convex-migration-20261005/final-reader-review-v1.md` | `680ca9dcdb4e535f0eca1e04a5b13785a179726bf23131866fd97efacbb71e59` |
| `runs/online-convex-migration-20261005/pr-delivery-v1.json` | `0eff5f5da15b89269df2c8c41f9d6159289a9c76f6f582634394ca95d873986e` |
| `runs/online-subgradient-basic-migration-20261006/accepted-decision-v1.json` | `5647a4b1f5fab20af3a7d95e5fe3f3a7d84f38224f54563315ee3099dd1eede0` |
| `runs/online-subgradient-basic-migration-20261006/delivery-v1.md` | `ac0de1b57abcb42eb56219967f8c7aa721f934722e05ada4650130933dbb4252` |
| `runs/online-subgradient-basic-migration-20261006/final-reader-receipt-v1.json` | `2d4a76d9bf32820f5c6ed42d32b6f73de08010ca7d1094ed43f3bf95591046f0` |
| `runs/online-subgradient-basic-migration-20261006/final-reader-review-v1.md` | `85b1836b6d480ba247ca2763d12d00ca8bb100ae35297c787b9fa52fbd1d42be` |
| `runs/online-subgradient-differentiability-migration-20261007/accepted-decision-v1.json` | `7aa4147564d0c2b2b63060662c9c921c72b834ad4278e4f27cb5ef736ac78896` |
| `runs/online-subgradient-differentiability-migration-20261007/delivery-v1.md` | `8684427346fbfb6b59d00f80198e3306679672ae60d78f3d310b7eec9f41e11a` |
| `runs/online-subgradient-differentiability-migration-20261007/final-reader-receipt-v1.json` | `53914c8afc9ff0fbba82875296fde4cb1a53212fbc3c907263048dcb0f7ce068` |
| `runs/online-subgradient-differentiability-migration-20261007/final-reader-review-v1.md` | `723930613284f83759ba0fb00f6341f6787719bc356854e25cedb21f5a7f7a65` |
| `runs/online-subgradient-sum-migration-20261007/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `runs/online-subgradient-sum-migration-20261007/00_context.md` | `4da1f81118eaf12dd95666accef2bf6bccbc085d11f1c313c3164d1e80246c89` |
| `runs/online-subgradient-sum-migration-20261007/10_upper_director-v1.md` | `79140a6102ef028273b4f170b3e248eadc32f139718f764d4814cc7c49ae7653` |
| `runs/online-subgradient-sum-migration-20261007/20_architect-v1.md` | `abe092e217a10531e62a684c9205f0cefd097e147166b6c21bf2b3095f651fcf` |
| `runs/online-subgradient-sum-migration-20261007/30_lower_worker-public-evidence-v1.md` | `b9e744fd2ada4f7896a2dc789d9073f03464c696f89bc0ad27247abd639e16df` |
| `runs/online-subgradient-sum-migration-20261007/30_lower_worker-v1.md` | `2bfc2f4140e42f554b3d679079b02a0e80ce8b8adbe270360bc95d2fa4149202` |
| `runs/online-subgradient-sum-migration-20261007/actual-types-v1-01-exit.json` | `e39bd4c14bf03f17c715d3be964ba5d09433bb1c59d7bba13076de0f1d522105` |
| `runs/online-subgradient-sum-migration-20261007/actual-types-v1-01.log` | `2f8f83414acd02ca01d12a0234d49f0284851d447081ed8f2188933df266fd5e` |
| `runs/online-subgradient-sum-migration-20261007/authoritative-private-workflow-binding-v1.json` | `e15a1e7890dfc844960403df526b5814b605704c21b0c28c72be114547b5f2be` |
| `runs/online-subgradient-sum-migration-20261007/blind-packet-v1.md` | `0075ceb0894954d0cec202ce325059b91dc195fccc2c47e44590c82c46848e29` |
| `runs/online-subgradient-sum-migration-20261007/blind-receipt-v1.json` | `b385f81b637446a7697d4ca04822f28e599dbb9402df3c1338e35b2fd84a30f3` |
| `runs/online-subgradient-sum-migration-20261007/blind-reconstruction-v1.md` | `71dbdccfd715601ca84a2818817bc0d8d89c6e597d8eda6038acd1bf9df61200` |
| `runs/online-subgradient-sum-migration-20261007/body-helper-before-use-v1.json` | `15ac393f0a0ea5a5ef7257d036b19fd7762c410d5791bf0f14478b32f756eab8` |
| `runs/online-subgradient-sum-migration-20261007/bootstrap-count-preparation-repair-v2.md` | `3f12fb0704a0ed4173da3aa94506568bfa0538ad99b31a0762fc76bc9e3f490b` |
| `runs/online-subgradient-sum-migration-20261007/bootstrap-generated-before-use-v1.json` | `f0f8de8ce42d2b29f520f79762f5de93fabf9b5c8a609acc28bd0ce3639ed82f` |
| `runs/online-subgradient-sum-migration-20261007/bootstrap-helper-before-use-v1.json` | `580711dfa07de5678f27a5e97f3551d44c2b9053b411bb38dd5ad99bde121564` |
| `runs/online-subgradient-sum-migration-20261007/bootstrap-helper-before-use-v2.json` | `ce5bab165eebd55af7cc38f2f0a9e566848ea3e1548aa95751e0ea34047d47c4` |
| `runs/online-subgradient-sum-migration-20261007/bootstrap-v1.py` | `6698e9d579644dab65f7754809b34964c372032f87ac7716d72b56204370671b` |
| `runs/online-subgradient-sum-migration-20261007/bootstrap-v2-01-exit.json` | `bf52f9da3f1925ede512ccf0f9cc70e2280c2f5fe3ea5d27be75626aad6cd4fd` |
| `runs/online-subgradient-sum-migration-20261007/bootstrap-v2-01.log` | `e90602762e0a9aac5fa67bb247fca4faa90c551e72736844e6e4cffa5f6556a0` |
| `runs/online-subgradient-sum-migration-20261007/bootstrap-v2.py` | `c7cfd5bf0923ee376a38e4282c74fbfd841af12f9a32ceeeee118c588bae536d` |
| `runs/online-subgradient-sum-migration-20261007/compiled-dependencies-v1.json` | `cc7d76c6c44473f7e0386bae20a567fa8bb38012cf4e23ab2f142692ad80439d` |
| `runs/online-subgradient-sum-migration-20261007/compiled-public-graph-v1-01-exit.json` | `7d39a52317c35f1e679b35c3f9cf99ee6880c4f8c2f958b1728f5474aad3d1a3` |
| `runs/online-subgradient-sum-migration-20261007/compiled-public-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-subgradient-sum-migration-20261007/compiled-public-graph-v1.json` | `bccd23b3f1d0018846bafb5d657e238a03042ef00da9617512164a96f5864960` |
| `runs/online-subgradient-sum-migration-20261007/compiled-ready-graph-v1-01-exit.json` | `69a8c16fbaf043dcea08a99b2ea748cb1ff81577b52d3403b09f3c8c6f82109b` |
| `runs/online-subgradient-sum-migration-20261007/compiled-ready-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-subgradient-sum-migration-20261007/compiled-ready-graph-v1.json` | `2810f2a507e1ab87fe759612ecdf5a8cda2d0aa0d9f5063e7bcc2d002dd03ea3` |
| `runs/online-subgradient-sum-migration-20261007/contract-binding-audit-v1.json` | `22f99937b33cfbbfb36a2fd2ba529858d74ed6059037137070274ef8c75eed8e` |
| `runs/online-subgradient-sum-migration-20261007/contract-source-inputs-v2.json` | `d7fa765d51ea83b6c4ee01d5d40500a7a759c7d44d6df4e776ab15154cffb86c` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-binary_subgradient_decomposition-v1-exit.json` | `d98148a95f02a2d578549a3b220d83bbffa6d630d6642ba1ca62d0b876653e5b` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-binary_subgradient_decomposition-v1.log` | `005cd1d06307ed3a6369cf32298be77fadad3df1b95e102187499ea3b5c9d79f` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-convex_finset_sum-v1-exit.json` | `e759b04a5090739c744dae8b6330c1cf2a0f2adbb867b23d334cf1ee4438cd33` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-convex_finset_sum-v1.log` | `3c3eb92944030ef5dafd173a80efbcb04305abe139a9f95d57fd8a5cb51c0abc` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-ereal_finset_sum_ne_bot-v1-exit.json` | `e54c17b3264519534ce99ed3b0f99a4a0156f8c0d10f570c66e3f936b95e2f50` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-ereal_finset_sum_ne_bot-v1.log` | `ceb730e72796d3a18b46826a7ca5a678590f59960ebebf97b700748438c665e9` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-finite_sum_point-v1-exit.json` | `25dd0430e81230dcc4841d70ddb3a33318ffec30a1a8d80071f8ac5299ce06a9` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-finite_sum_point-v1.log` | `3d22e9439232eb9df14f1cfb207df03e687f2391e5f12142024de56bcfa26a64` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-interior_domain_sum-v1-exit.json` | `5d37d86d7da4b84001cbab0417c06c5884795cb7411713a425c9897aef7e4bd5` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-interior_domain_sum-v1.log` | `f0cd670e5116e4837ca7f7bf266374db850e4fc4442567c4aeed73e3d172fddf` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-sum_finite_implies_components_finite-v1-exit.json` | `b58445ef07a5db66a1a7ced9e1a90076a03c2102fc7343e6915dcac0c345b276` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-sum_finite_implies_components_finite-v1.log` | `48e0b8b6a465512d51892f17704ae4048045aa7c1a31eb817e801f72b5554e8e` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-theorem_2_23_equality-v1-exit.json` | `cb9a8b18977693b106c613a21e7d07e1f1a7c921cbc331b175677263c540f346` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-theorem_2_23_equality-v1.log` | `39f0388ec0a6f3611765bfa37b35ad1187ab1ec58af0bf1b7fb43e0975c5783a` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-theorem_2_23_inclusion-v1-exit.json` | `a01f03aafaafce1140df5085012e27b2138d1ceb6e15ba2639f59991ef2422ca` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-theorem_2_23_inclusion-v1.log` | `4400a713ff38d97025f7cbee52ca6a008719cabb7798e7a86f1543a8d2c46738` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-upperAdd_eq_add_of_ne_bot-v1-exit.json` | `19b703e1b0fa7aeae316c409242a007d22a14165510f859c187738770a942679` |
| `runs/online-subgradient-sum-migration-20261007/draft-fence-upperAdd_eq_add_of_ne_bot-v1.log` | `0c1c67c173cdae8f59a77c8a049aecca67c608c1698d488aa3294d9aed31d954` |
| `runs/online-subgradient-sum-migration-20261007/draft-freeze-v1.json` | `634a78a0363f1ea45b2d2fd4d2b65f846399bda25fbfba32a089848ad0aee653` |
| `runs/online-subgradient-sum-migration-20261007/draft-generated-before-use-v1.json` | `9e589495ebc002e3bc2ffa0f221bedfcc0a0be8c25545b18368516951abd9d51` |
| `runs/online-subgradient-sum-migration-20261007/draft-helper-before-use-v1.json` | `7f815ba723d7dd36b667329b90454df03846f45403b9012561dba75b3bbefdd5` |
| `runs/online-subgradient-sum-migration-20261007/draft-lifecycle-v1-exit.json` | `f15b52ed90e46cabe10f7809deb5450ad3a0041bcc59497a9606ce232145a089` |
| `runs/online-subgradient-sum-migration-20261007/draft-lifecycle-v1.log` | `d52039b47eee36c5da8dd7356f46b87be454fabc34454121ef72e1e451e92d9f` |
| `runs/online-subgradient-sum-migration-20261007/guard-helper-before-use-v1.json` | `3fabecb85cf05607475117d85ca9001ed2a7587e450838e4f22cd42626258018` |
| `runs/online-subgradient-sum-migration-20261007/historical-raw-supersession-v1.json` | `269968cd6e2d195a7cf69e159b0cdc647eaf0d4c24f7278a7e7f84d00975aa00` |
| `runs/online-subgradient-sum-migration-20261007/historical-raw-supersession-v2.json` | `1d89fd3d923963b6b642102571f7a5f7faa31219e574f669ecdb49ac126522a5` |
| `runs/online-subgradient-sum-migration-20261007/leaves/actual-types-v1.lean` | `3703c5845565c64d053eb5794dc2412913b5159cdcd80869a7e1fb3216104a78` |
| `runs/online-subgradient-sum-migration-20261007/leaves/export-public-dependencies-v1.lean` | `f71a5e9b9f1c705a391bd44ca48fda73a8e1e77a49d5c5ae2786b2c059bc2950` |
| `runs/online-subgradient-sum-migration-20261007/leaves/export-scoped-dependencies-v1.lean` | `9fa3b1407a3c912945cabb799c5a36790fc3eef18e8e01d717d2af5249d7dc02` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pinned-required-APIs-v1.lean` | `d4a60f3f6e0adbec3ee5f187b7e5a8120499071d548892bc42c63d8b08ebad1d` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-BanditRLProof--OnlineClosedProper.lean.txt` | `c66f00c33b45fb8a0e11583eeadf506e176c16166ce2af02f41f0674507cebe7` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-BanditRLProof--OnlineConvexBarycenter.lean.txt` | `beb198b8be313c36a73eb1e20acdc8b8845d40d18d70f169c129a35c338f36c0` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-BanditRLProof--OnlineConvexExtended.lean.txt` | `bd30bb95a46ccdc3f6d25f808c175af5fee71d075c2b46ffcf6508f15f1ed66a` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-BanditRLProof--OnlineConvexSums.lean.txt` | `0abd620cb419fec2899146a3f201401aaa410d01409a33c81836b54dcfd932ca` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-BanditRLProof--OnlineSubgradientBasic.lean.txt` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-BanditRLProof--OnlineSubgradientDifferentiability.lean.txt` | `4f21c5d7fd0ef27a860390b698072d65527610d55e60c16568e82fa99215c1d3` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-BanditRLProof--OnlineSubgradientSum.lean.txt` | `8fbeaa5f8d46df667db31373d712d9a7ca494c8ff8948f2cb45a2299b35440da` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-MANIFEST.md.txt` | `ee59861c268dab0971eb9b96444169df6a21297c582e7becdca3740ae98a0e9d` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-Tests--OnlineSubgradientSumCanary.lean.txt` | `a0c773f08fd5c597bb12a92f71e33f0438e8211bf998c8cd5d370ce263c2d234` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-Tests.lean.txt` | `cd21ef4e7cea89c7d245eaf4dff14be8baa34f2d336e40d6f6bbb16011678340` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-runs--lifecycle_sessions.jsonl.txt` | `e03e3b9adcffe439872dbfd67b1fed02f83790a94c2c8c482ef44abde029d5f7` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-runs--trials.jsonl.txt` | `08ce8ad334ed6652452482ba52c92b58d0b67357e4d488b296758aaf3fbb2255` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-v2-BanditRLProof--OnlineClosedProper.lean.txt` | `c66f00c33b45fb8a0e11583eeadf506e176c16166ce2af02f41f0674507cebe7` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-v2-BanditRLProof--OnlineConvexBarycenter.lean.txt` | `beb198b8be313c36a73eb1e20acdc8b8845d40d18d70f169c129a35c338f36c0` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-v2-BanditRLProof--OnlineConvexExtended.lean.txt` | `bd30bb95a46ccdc3f6d25f808c175af5fee71d075c2b46ffcf6508f15f1ed66a` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-v2-BanditRLProof--OnlineConvexSums.lean.txt` | `0abd620cb419fec2899146a3f201401aaa410d01409a33c81836b54dcfd932ca` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-v2-BanditRLProof--OnlineSubgradientBasic.lean.txt` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-v2-BanditRLProof--OnlineSubgradientDifferentiability.lean.txt` | `4f21c5d7fd0ef27a860390b698072d65527610d55e60c16568e82fa99215c1d3` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-v2-BanditRLProof--OnlineSubgradientSum.lean.txt` | `8fbeaa5f8d46df667db31373d712d9a7ca494c8ff8948f2cb45a2299b35440da` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-v2-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-v2-MANIFEST.md.txt` | `ee59861c268dab0971eb9b96444169df6a21297c582e7becdca3740ae98a0e9d` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-v2-Tests--OnlineSubgradientSumCanary.lean.txt` | `a0c773f08fd5c597bb12a92f71e33f0438e8211bf998c8cd5d370ce263c2d234` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-v2-Tests.lean.txt` | `cd21ef4e7cea89c7d245eaf4dff14be8baa34f2d336e40d6f6bbb16011678340` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-v2-runs--lifecycle_sessions.jsonl.txt` | `e03e3b9adcffe439872dbfd67b1fed02f83790a94c2c8c482ef44abde029d5f7` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-v2-runs--trials.jsonl.txt` | `08ce8ad334ed6652452482ba52c92b58d0b67357e4d488b296758aaf3fbb2255` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-v2-website--content--chapters.json.txt` | `ae9fe7cbf1aac546df9aff911df08d29a824cbd2d810cc3a81a0206ff1e42fc0` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-v2-website--content--highlights.json.txt` | `87741e432a78161a42719fee6732298eb2cb45ee8da943909419fc640e1bfd1e` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-v2-website--content--readings.json.txt` | `3cb544fab868c3328b1fb1bd28235bd83e0da8ca79d4ec6e7b7e064bae86be0a` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-website--content--chapters.json.txt` | `ae9fe7cbf1aac546df9aff911df08d29a824cbd2d810cc3a81a0206ff1e42fc0` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-website--content--highlights.json.txt` | `87741e432a78161a42719fee6732298eb2cb45ee8da943909419fc640e1bfd1e` |
| `runs/online-subgradient-sum-migration-20261007/leaves/pre-integration-website--content--readings.json.txt` | `3cb544fab868c3328b1fb1bd28235bd83e0da8ca79d4ec6e7b7e064bae86be0a` |
| `runs/online-subgradient-sum-migration-20261007/leaves/public-all-axioms-v1.lean` | `3fdb8c088a23fdfccf83f8e67a5e0d67fb88bc558ba600338bd9ce3372478167` |
| `runs/online-subgradient-sum-migration-20261007/local-declaration-search-v1-01-exit.json` | `c39dd2c28a037211c4c372b09dbecb621dab0234c8128876b5100b386536f726` |
| `runs/online-subgradient-sum-migration-20261007/local-declaration-search-v1-01.log` | `988983811a3665924cf51ec4f18f091bdb50ca9ca52a767dacc0f0044bc00a5d` |
| `runs/online-subgradient-sum-migration-20261007/local-memory-search-v1-01-exit.json` | `50f88d27f4cb2324645d75e7feed75c292cab44bf5db79e202d891c037a7da6e` |
| `runs/online-subgradient-sum-migration-20261007/local-memory-search-v1-01.log` | `e54574da7331161efdc1f375d2c6fe554b7e57b23fb17251f5d23b15aadc3397` |
| `runs/online-subgradient-sum-migration-20261007/native-draft-fences/binary_subgradient_decomposition.json` | `005cd1d06307ed3a6369cf32298be77fadad3df1b95e102187499ea3b5c9d79f` |
| `runs/online-subgradient-sum-migration-20261007/native-draft-fences/convex_finset_sum.json` | `3c3eb92944030ef5dafd173a80efbcb04305abe139a9f95d57fd8a5cb51c0abc` |
| `runs/online-subgradient-sum-migration-20261007/native-draft-fences/ereal_finset_sum_ne_bot.json` | `ceb730e72796d3a18b46826a7ca5a678590f59960ebebf97b700748438c665e9` |
| `runs/online-subgradient-sum-migration-20261007/native-draft-fences/finite_sum_point.json` | `3d22e9439232eb9df14f1cfb207df03e687f2391e5f12142024de56bcfa26a64` |
| `runs/online-subgradient-sum-migration-20261007/native-draft-fences/interior_domain_sum.json` | `f0cd670e5116e4837ca7f7bf266374db850e4fc4442567c4aeed73e3d172fddf` |
| `runs/online-subgradient-sum-migration-20261007/native-draft-fences/sum_finite_implies_components_finite.json` | `48e0b8b6a465512d51892f17704ae4048045aa7c1a31eb817e801f72b5554e8e` |
| `runs/online-subgradient-sum-migration-20261007/native-draft-fences/theorem_2_23_equality.json` | `39f0388ec0a6f3611765bfa37b35ad1187ab1ec58af0bf1b7fb43e0975c5783a` |
| `runs/online-subgradient-sum-migration-20261007/native-draft-fences/theorem_2_23_inclusion.json` | `4400a713ff38d97025f7cbee52ca6a008719cabb7798e7a86f1543a8d2c46738` |
| `runs/online-subgradient-sum-migration-20261007/native-draft-fences/upperAdd_eq_add_of_ne_bot.json` | `0c1c67c173cdae8f59a77c8a049aecca67c608c1698d488aa3294d9aed31d954` |
| `runs/online-subgradient-sum-migration-20261007/native-public-fences/binary_subgradient_decomposition.json` | `2cf18b0149f67b763e98c6940c22e04c485f077761cae092cb6abd48b5dc9cc9` |
| `runs/online-subgradient-sum-migration-20261007/native-public-fences/convex_finset_sum.json` | `526e7abc0e0be8590b28b31165008729957acbfaed78a4246f2ac04edcd9aa08` |
| `runs/online-subgradient-sum-migration-20261007/native-public-fences/ereal_finset_sum_ne_bot.json` | `16b3ba2eb68212002fbb2dd42154226ac7eeb82f8eefbe3b0dcd1bad2d456470` |
| `runs/online-subgradient-sum-migration-20261007/native-public-fences/finite_sum_point.json` | `8e0ea5a77a86205099b4c9bf9a79a0211ed48ca27d782e27f42c22f81b5a80b2` |
| `runs/online-subgradient-sum-migration-20261007/native-public-fences/interior_domain_sum.json` | `11c1cad770995b3d1ec234cd6a64494ee0c798c1236d282476cbc676e8d65836` |
| `runs/online-subgradient-sum-migration-20261007/native-public-fences/sum_finite_implies_components_finite.json` | `6c454476c429c1a3d44c68416be102be50db8912aeee8966f231b9f620c5c3bc` |
| `runs/online-subgradient-sum-migration-20261007/native-public-fences/theorem_2_23_equality.json` | `28e16c9ff2dd6805ecff8a3dfa6df1f33dfccca136a93625e849f2fd1bccbcc9` |
| `runs/online-subgradient-sum-migration-20261007/native-public-fences/theorem_2_23_inclusion.json` | `9188e225eedbfe9da758c45f0af01fcb4f40eee93534036528cf321faad807fa` |
| `runs/online-subgradient-sum-migration-20261007/native-public-fences/upperAdd_eq_add_of_ne_bot.json` | `b3b5b81053c0ad25727eae35599bd30f4da410984197be628d85856a3a243e30` |
| `runs/online-subgradient-sum-migration-20261007/original-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-subgradient-sum-migration-20261007/original-OnlineConvexBarycenter.lean.txt` | `beb198b8be313c36a73eb1e20acdc8b8845d40d18d70f169c129a35c338f36c0` |
| `runs/online-subgradient-sum-migration-20261007/original-OnlineConvexSums.lean.txt` | `0abd620cb419fec2899146a3f201401aaa410d01409a33c81836b54dcfd932ca` |
| `runs/online-subgradient-sum-migration-20261007/original-OnlineSubgradientBasic.lean.txt` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `runs/online-subgradient-sum-migration-20261007/original-OnlineSubgradientDifferentiability.lean.txt` | `4f21c5d7fd0ef27a860390b698072d65527610d55e60c16568e82fa99215c1d3` |
| `runs/online-subgradient-sum-migration-20261007/original-OnlineSubgradientSum.lean.txt` | `8fbeaa5f8d46df667db31373d712d9a7ca494c8ff8948f2cb45a2299b35440da` |
| `runs/online-subgradient-sum-migration-20261007/original-OnlineSubgradientSumCanary.lean.txt` | `a0c773f08fd5c597bb12a92f71e33f0438e8211bf998c8cd5d370ce263c2d234` |
| `runs/online-subgradient-sum-migration-20261007/original-Tests.lean.txt` | `cd21ef4e7cea89c7d245eaf4dff14be8baa34f2d336e40d6f6bbb16011678340` |
| `runs/online-subgradient-sum-migration-20261007/pinned-required-APIs-v1-01-exit.json` | `bc8d325102e0e8fc3fea544d3362825be82c9e4d97c2d7bbb9572fa86a4b3765` |
| `runs/online-subgradient-sum-migration-20261007/pinned-required-APIs-v1-01.log` | `0b970d367c0fcdee9143b8d05c9d273a1f5afe8cd875b6e6ff776053996a6c71` |
| `runs/online-subgradient-sum-migration-20261007/preparation-read-diagnostics-v1.md` | `7bf58de9100ac9fc499c55853cbfe63c7b40e2b37a7f037f6d876c23b1a947dd` |
| `runs/online-subgradient-sum-migration-20261007/prepare-body-review-v1.py` | `7e9145a9eecd6244185773f680b627169213f0d354e97635ad5b28b3fe0bf8a3` |
| `runs/online-subgradient-sum-migration-20261007/prepare-draft-v1-01-exit.json` | `ce8090352705a45ea68df242a965408ba6290c9931df3538b8f59ec80f04730e` |
| `runs/online-subgradient-sum-migration-20261007/prepare-draft-v1-01.log` | `72a08031b074200712e0be690b6d02f333d35faa08785f919ef1eed58b5fa0d3` |
| `runs/online-subgradient-sum-migration-20261007/prepare-draft-v1.py` | `41cbed0520a494ed3baa17cc481c5801fa39af0205acc924080dc087bff5e3c9` |
| `runs/online-subgradient-sum-migration-20261007/prepare-proving-v1.py` | `6bfa48a1e6ffdac20217b5c48ed09960f0ce691ca8cc09243856f2105d7cf1ea` |
| `runs/online-subgradient-sum-migration-20261007/prepare-proving-v2-01-exit.json` | `c65cbd3ab6c29281458537a11ea97d88aff77851bf4aa33eeeb26c27903b1cf5` |
| `runs/online-subgradient-sum-migration-20261007/prepare-proving-v2-01.log` | `a8d4ec9722586f9e60c621bbc8a29b5bbe207c8381e6a29c640e491c4bcc14ce` |
| `runs/online-subgradient-sum-migration-20261007/prepare-proving-v2.py` | `2d23ce4e2e52690ef034fd7a31287d987076ed3b5c32412990251aad7f504f28` |
| `runs/online-subgradient-sum-migration-20261007/prepare-source-review-v1-01-exit.json` | `2c5fac9703ac4a15052ca48f2b70cbf152e2183ae9ff24b2c9b204a1e9e98051` |
| `runs/online-subgradient-sum-migration-20261007/prepare-source-review-v1-01.log` | `44a9db8780665f26568881b99ed11fa92de93d859b0b1ec9adffdda897402ded` |
| `runs/online-subgradient-sum-migration-20261007/prepare-source-review-v1.py` | `ea32ddeda64c63b90d97b5036ad547b55d5961049221de6c7737df4655467ac0` |
| `runs/online-subgradient-sum-migration-20261007/prepare-source-review-v2-01-exit.json` | `419baa094bc540541df218f2ec8ffe6e4c3a59f12d6b0ad8cca72739b3b22742` |
| `runs/online-subgradient-sum-migration-20261007/prepare-source-review-v2-01.log` | `3217077483a980b2b1699f6874fd21e700c7ac2d6663304d751ef982b096baa4` |
| `runs/online-subgradient-sum-migration-20261007/prepare-source-review-v2.py` | `bf16d061b3c8d12ea9950d0099a0a2010953898eb199a7031b3e9f1aa23b2ac9` |
| `runs/online-subgradient-sum-migration-20261007/prior-contract-binding-v1.json` | `aecd6feceab6ec0fa278ea0459c32010129b1d67bf77baa2042ff5578c5c54b3` |
| `runs/online-subgradient-sum-migration-20261007/proof-obligations-proving-v1.json` | `a1b0ba7b949a9dafbd6efd30f20d00ece7c5971ae41d8305d6e585afd26b0d5f` |
| `runs/online-subgradient-sum-migration-20261007/proof-obligations-v1.json` | `0f0635a0960d5d8d3feb2ececbd83a331f57f96f0a76dd90e1d1e0c5c1080924` |
| `runs/online-subgradient-sum-migration-20261007/proving-generated-before-use-v1.json` | `403887afa2c1b6c8c71211a6eaa13ecfe38c5c80d94369bd75bfae9d232ee75e` |
| `runs/online-subgradient-sum-migration-20261007/proving-helper-before-use-v1.json` | `616e08128c84adf6d46c7bd90280ee69e025bb739ef78082396c2b15a1e34e59` |
| `runs/online-subgradient-sum-migration-20261007/proving-helper-before-use-v2.json` | `fa0c19e8d963396146448aa480f24b03848fadf618f34fe6fabc133758c5af98` |
| `runs/online-subgradient-sum-migration-20261007/proving-lifecycle-v1-exit.json` | `41dfce756799c1388e5095a3e95efd372bafab705a4c6e9c58f7b29ee610085b` |
| `runs/online-subgradient-sum-migration-20261007/proving-lifecycle-v1.log` | `cd57c782d0a97db41fce5a3253d0f0e49b1bbeb7ba076a0eb16519ec24ff2e82` |
| `runs/online-subgradient-sum-migration-20261007/public-actual-bindings-v1.json` | `30bb1ed6618b8aa861c33c26d51257c476f121528089b98917e1e0b689893d7d` |
| `runs/online-subgradient-sum-migration-20261007/public-all-axioms-v1-01-exit.json` | `273b71e6857330351646a58adfc81655e835164bf7e9af06c7938c340387d8c7` |
| `runs/online-subgradient-sum-migration-20261007/public-all-axioms-v1-01.log` | `4e7fcbfa5c76587bde2e8fc3a683be3dd4578cb94877c253c2993afe12b335c5` |
| `runs/online-subgradient-sum-migration-20261007/public-body-inputs-v1.json` | `9da3676dd8a236a3e66136297af6e0b5aee43ab95659a3c73a81e815d576cbab` |
| `runs/online-subgradient-sum-migration-20261007/public-body-review-packet-v1.md` | `c75a7834ffd5c60e1d69bda7284a05a3375df97964924b054ce844f665ca1a20` |
| `runs/online-subgradient-sum-migration-20261007/public-body-v1-01-exit.json` | `9ea8c484a30672228cf05c1e64e6c952b508e7197ce3a6b67a16ee6d3b3ade98` |
| `runs/online-subgradient-sum-migration-20261007/public-body-v1-01.log` | `26e10bf3c7216400d7531589b7495796de1f9ba865dd19f87aefcd5244ce4b35` |
| `runs/online-subgradient-sum-migration-20261007/public-canary-focused-v1-01-exit.json` | `3bf4a56a316a721b7c0c71a660ad38426a7bd98dcd0fb559beeca0b3a7848f39` |
| `runs/online-subgradient-sum-migration-20261007/public-canary-focused-v1-01.log` | `059762c5295814a0854ed76687cfa4e179428187643d392fd809410128967675` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-binary_subgradient_decomposition-exit.json` | `f78a387f33b7535fd6a521067530ab2f9dee206087de2e39277f4f96523cbfed` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-binary_subgradient_decomposition.log` | `2cf18b0149f67b763e98c6940c22e04c485f077761cae092cb6abd48b5dc9cc9` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-convex_finset_sum-exit.json` | `a89f9d7c43898b8113a86e8498af4145b012b0c33fffd694f4123b85300b8a00` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-convex_finset_sum.log` | `526e7abc0e0be8590b28b31165008729957acbfaed78a4246f2ac04edcd9aa08` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-ereal_finset_sum_ne_bot-exit.json` | `5266696bbffbe92dc3c137c2bfabe8bd9bc5fc5574c8d538c7153a58c108abaa` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-ereal_finset_sum_ne_bot.log` | `16b3ba2eb68212002fbb2dd42154226ac7eeb82f8eefbe3b0dcd1bad2d456470` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-finite_sum_point-exit.json` | `4f97ae6d81c54fe0394c96fc883e6fcee26e4c985bac6d8b076be9e21d105678` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-finite_sum_point.log` | `8e0ea5a77a86205099b4c9bf9a79a0211ed48ca27d782e27f42c22f81b5a80b2` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-interior_domain_sum-exit.json` | `d3bd9835511c84fe549b91941542eb78b3d1bd854519dcf3914060c9162dda16` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-interior_domain_sum.log` | `11c1cad770995b3d1ec234cd6a64494ee0c798c1236d282476cbc676e8d65836` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-sum_finite_implies_components_finite-exit.json` | `4883aa301117f548d4eff73426debb2983601d7ae11eb0d017f7fc5ddc56aa0a` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-sum_finite_implies_components_finite.log` | `6c454476c429c1a3d44c68416be102be50db8912aeee8966f231b9f620c5c3bc` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-theorem_2_23_equality-exit.json` | `115ec30d63e935c04c401aa14f5f6b6753073d68da4e5dd9d617b9f0d9c5e7eb` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-theorem_2_23_equality.log` | `28e16c9ff2dd6805ecff8a3dfa6df1f33dfccca136a93625e849f2fd1bccbcc9` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-theorem_2_23_inclusion-exit.json` | `b84d9311617b665ffca88595e09f03bdb59b8afec13776fd83f55b5496565209` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-theorem_2_23_inclusion.log` | `9188e225eedbfe9da758c45f0af01fcb4f40eee93534036528cf321faad807fa` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-upperAdd_eq_add_of_ne_bot-exit.json` | `d1c009e035c94a9d52538ffc5fb720997a2f14be6b162e091bd6bc6e203019d8` |
| `runs/online-subgradient-sum-migration-20261007/public-fence-v1-upperAdd_eq_add_of_ne_bot.log` | `b3b5b81053c0ad25727eae35599bd30f4da410984197be628d85856a3a243e30` |
| `runs/online-subgradient-sum-migration-20261007/public-named-declarations-v1.json` | `df1bb95d22445348fe8c27c67383402e34816ee13cad22dfa1171c3642b1ed75` |
| `runs/online-subgradient-sum-migration-20261007/public-safe-guard-audit-v1.json` | `1ec54c8c0090527651421d5654f75658d45383a275778493213b8065c50b8bbf` |
| `runs/online-subgradient-sum-migration-20261007/ready-dependencies-v1.json` | `783bc6e91635017499728008aa281f910e1944abd6a791d750eabb4acc492c90` |
| `runs/online-subgradient-sum-migration-20261007/ready-dependencies-v2.json` | `783bc6e91635017499728008aa281f910e1944abd6a791d750eabb4acc492c90` |
| `runs/online-subgradient-sum-migration-20261007/ready-generated-before-use-v1.json` | `1a78e01a759b882c0c813cd2d285c7ff8b146e45c4362b6bca0ccae0ea8216ae` |
| `runs/online-subgradient-sum-migration-20261007/retained-body-trial-v1-exit.json` | `6b8823b2f59a9990d18e4de0061719faf461bab6cc8d795d3e3ac1584af3edcd` |
| `runs/online-subgradient-sum-migration-20261007/retained-body-trial-v1.log` | `accef0ee914a25b80e4868dc8175b59a3c15794d8dc0516b416d36da8408a4a3` |
| `runs/online-subgradient-sum-migration-20261007/retained-focused-v1-01-exit.json` | `9fc615c6ba353dd9086d16fcd9bc92d803db7713808c722ea0987168a87b2d2e` |
| `runs/online-subgradient-sum-migration-20261007/retained-focused-v1-01.log` | `6dd213ad36596431eef05d933887da36509df9ce262b5db77e64215da5c9437e` |
| `runs/online-subgradient-sum-migration-20261007/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-binary_subgradient_decomposition-exit.json` | `b65bc02988a2aae186d3af34088b7354776b82ceab5139738a949cbee1ef6243` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-binary_subgradient_decomposition.log` | `a0c5fd1ef0f4e326bd89a6babeed436ee314fb8ac5d3e229086352f00a93b993` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-convex_finset_sum-exit.json` | `ef7d9af11cf5661d823a5c8ffcca38090877cfbb82d1b94d0fc6e5dc4e7d2eec` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-convex_finset_sum.log` | `6dff348d5194a4d5c4b26da766d1dedd451fc3f408d79d2c8da3eeb235582676` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-ereal_finset_sum_ne_bot-exit.json` | `01203a15a79eba42b6be58a1f1b00dd47ddf3c7bb21ec6b32b1086daedd9edfe` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-ereal_finset_sum_ne_bot.log` | `1be891be8edf2b87ee7a541be39536ed95b397c3c706933d4c96a7ed787a1d82` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-finite_sum_point-exit.json` | `1f8bda2e7c7e66eccadeb9981ed3fbd31a8cbdf929040ad9637028872c5e565e` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-finite_sum_point.log` | `b40e23ecfc119ebbd9f97540dae931e39ced11090e91e2928e21260837670bc3` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-interior_domain_sum-exit.json` | `2ca09bbcf5aa037a71b5d2ce3e0267ad1f927962902ef9346b9ebb2aa2dd293a` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-interior_domain_sum.log` | `9fd5cc8609a84e383d76c96c7587f16b9f133c60f7980e5e3d6f8f2a25c57044` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-sum_finite_implies_components_finite-exit.json` | `91768cb8dc55f3256ef5aad3e15e7b05506610338ce4e0a67cd0b5f1fe559648` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-sum_finite_implies_components_finite.log` | `6cf00d81898c3654e4bcc0cbd57a6a6a25f15f4df438959c19eca06354b475dc` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-theorem_2_23_equality-exit.json` | `981d32ad45a55447e2148a2f0e18e4fc5b8a4a629c30b80c0ab232516113db41` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-theorem_2_23_equality.log` | `5cda3c0621bcd533e470642ce6cf4e721e0a8c518208e5e836f3b3892bf30c32` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-theorem_2_23_inclusion-exit.json` | `01d57cd8911e5d285d66b09505f3653e6e59df75a7f19fa39cfc296b17ac31ae` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-theorem_2_23_inclusion.log` | `7258638f4007d584ea266cf7d2442310dcf38bf9e3286f47f0ebc9d3a56f6b2c` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-upperAdd_eq_add_of_ne_bot-exit.json` | `3ca9d02cd716dbe582caf2df13ce04f0af9e87daeef64b2bb2f50c03fc7cf598` |
| `runs/online-subgradient-sum-migration-20261007/safe-public-v1-upperAdd_eq_add_of_ne_bot.log` | `ba86ce6ab14a41009e3ff0cf6f3c2adbd5714bd3bc49ca38b0b41e3ed875403d` |
| `runs/online-subgradient-sum-migration-20261007/source-contract-receipt-v1.json` | `fb9881f2c058684c1c42267b6eb66ac8dcb9587a33c41321902cd9c8c182e6c3` |
| `runs/online-subgradient-sum-migration-20261007/source-contract-review-v1.md` | `93856c9408091f33a322e27ab16a65879304410e80a458271a5431cb665fa334` |
| `runs/online-subgradient-sum-migration-20261007/source-helper-before-use-v1.json` | `da14984b27cc9e3cff85395959790da6fdcea965b1a9b3ddc22683ceffa222b6` |
| `runs/online-subgradient-sum-migration-20261007/source-helper-before-use-v2.json` | `31c3ceb29caeac53865532e9368b736f60f1041097254e86ca4733763be40524` |
| `runs/online-subgradient-sum-migration-20261007/source-printed17-pdf29.txt` | `38f58d214ab8616aef7b7147338f7fd91ecdcf159b5286ea47092cf4ece81c46` |
| `runs/online-subgradient-sum-migration-20261007/source-printed18-pdf30.txt` | `669b3f91ea4bda1846f3fb238276bc15d1f337a66b0aef3b1a51a747b6a2317d` |
| `runs/online-subgradient-sum-migration-20261007/source-render-binding-v1.json` | `55dd24fb3dcf7fcfc41c052bb20477baf80d9f3bfd2cfbed9e284dd64268cb67` |
| `runs/online-subgradient-sum-migration-20261007/source-render-pdf30-v1-01-exit.json` | `9366c4c8510b71600394e5740fcafe78a3963d488213cda5e7deae76c31528c9` |
| `runs/online-subgradient-sum-migration-20261007/source-render-pdf30-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-subgradient-sum-migration-20261007/source-review-packet-v1.md` | `0ca0c71c3067e5c892f7f6c707a6f910d56d240578ec8713b1eea2712d502d19` |
| `runs/online-subgradient-sum-migration-20261007/source-review-packet-v2.md` | `c7308fb143b3cc18fcdcc70e3c59a66e4163ea2c1e68b27884da87090f3fdcb3` |
| `runs/online-subgradient-sum-migration-20261007/stabilized-lifecycle-v1-exit.json` | `80bf7e2e0b0df793961bcf014aede134d5e3c53eacd60fa1f29ef1ec7874482c` |
| `runs/online-subgradient-sum-migration-20261007/stabilized-lifecycle-v1.log` | `534639cf8d5e8816ff829e518478691d29a4e43ec35a1e4ff1c2a1bbacceced1` |
| `runs/online-subgradient-sum-migration-20261007/verify-public-fences-v1-01-exit.json` | `444e42e0ef57f05f4402fcd9099fd3ce544cf7cb9de927af9b20fb0e7d132a92` |
| `runs/online-subgradient-sum-migration-20261007/verify-public-fences-v1-01.log` | `398f888ec279b86167da557ff67ab8433f76036ffd2e5741fbcd3dc5222ca541` |
| `runs/online-subgradient-sum-migration-20261007/verify-public-fences-v1.py` | `f5f487d886cbea80d3a1a9e4d01f6b36249f93bfa5e4aff7f1d09f6eecddf784` |
| `runs/online-subgradient-sum-migration-20261007/workspace-audit-v1.json` | `40694142f131f6506ae2e430e886f117668912e3c0c422b3762093dde10ce160` |
| `tasks/ONLINE-SUBGRADIENT-SUM-MIGRATION-20261007.md` | `dfe9f138591f3f231bdb64185f9b909f092595ef6c0cd447fc0fab7b2cfb7b9e` |
| `tmp/online-subgradient-differentiability-source-pdf29-v2.png` | `7bc9bb6f72b9a03ee6d6c203fbe5db1c1f177a242f8375d0e0d1b60c2575c146` |
| `tmp/online-subgradient-sum-source-pdf30-v1.png` | `c4354de7297923fd82f74645ddd50fdb582f90b6eeb9a7536fd9f33ec5489ebd` |
| `website/content/chapters.json` | `ae9fe7cbf1aac546df9aff911df08d29a824cbd2d810cc3a81a0206ff1e42fc0` |
| `website/content/highlights.json` | `87741e432a78161a42719fee6732298eb2cb45ee8da943909419fc640e1bfd1e` |
| `website/content/readings.json` | `3cb544fab868c3328b1fb1bd28235bd83e0da8ca79d4ec6e7b7e064bae86be0a` |
