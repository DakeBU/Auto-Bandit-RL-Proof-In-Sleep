# Example2.24 distinct BODY source review

**Verdict: accepted-with-explicit-delta, BODY only.** No mathematical repair. Actor `/root/source_reviewer`; requested GPT-6 Astra / medium, runtime model unattested. Reused actor history acknowledged; no human/external review or new-history blindness claim. This is a separate actual-body decision, not automatic inheritance of CONTRACT acceptance.

## Source and full shared definition

Original PDF rehashed to `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`; physical30/printed18 freshly extracted again. ONE Example2.24 gives the positive singleton, full CLOSED zero interval, and negative singleton. Four retained proof declarations are refinements, not four printed source results. No new mathematics or tests are produced here.

Full borrowed S is `{g | forall y, f x + coe(inner real g (y-x)) <= f y}`. The generic definition has normed real inner-product context, permits arbitrary EReal functions and imposes no properness. Printed Definition2.20 restricts to proper functions. The fixed real absolute function is finite everywhere and has a finite witness at zero, so this specialization is faithful; no improper arithmetic/toReal fallback is used. All four actual targets are scalar real, without free E/finite-dimensional/completeness/convexity/differentiability premises. S is shared, not a locally owned definition.

I reread the complete actual module and whole canary. All necessities and sufficiencies are genuine producers; assuming membership hg during the forward inclusion is legitimate set-equality elimination, not assuming the terminal. EReal conversion is only between actual finite real coercions via coe_add and order equivalence. No desired bound is supplied from outside.

## Four targets, seven slots and actual proof routes

### `BanditRL.OnlineConvex.abs_subgradient_zero`

Verdict: accepted-with-explicit-delta (BODY only). Header SHA `e878c47ef95faa47b1418c365baea538ad208382d41cb020cb1d4724132ada34`.

- **objects_spaces**: Scalar real x,g,y; fixed f(y)=coe(|y|):EReal. No free E/finite-dimensional/completeness parameter.
- **quantifiers**: Fixed query x=0; every real slope g, each tested against every real y.
- **assumptions**: No premises.
- **conclusion**: S(abs,0)=Icc(-1,1), both inclusion directions.
- **constants**: Exact inclusive endpoints -1,1; every intermediate real slope.
- **information_probability**: Deterministic global set characterization; no probability, causal learner, measurable/computable choice or regret guarantee.
- **boundaries**: Both endpoints, fractional slopes, and exclusion of all slopes outside interval; not selected zero/singleton/existence-only.

Actual proof: Set extensionality proves both directions. From hg 1 and hg (-1), coe_add and coe_le_coe_iff give g<=1 and -1<=g. Conversely every interval member works for arbitrary y: y>=0 multiplies g<=1 by nonnegative y; y<0 multiplies -1<=g by nonpositive y, reversing order to yg<=-y. The y=0 case is included.

### `BanditRL.OnlineConvex.abs_subgradient_positive`

Verdict: accepted-with-explicit-delta (BODY only). Header SHA `7c28bc210670ae091789b68390cafca47f511cd3884a86e142611be79a001620`.

- **objects_spaces**: Scalar real x,g,y; fixed f(y)=coe(|y|):EReal. No free E/finite-dimensional/completeness parameter.
- **quantifiers**: Every real x with 0<x; every slope g and ALL ambient real test y.
- **assumptions**: Only strict positivity 0<x.
- **conclusion**: S(abs,x)={1}; both existence and uniqueness.
- **constants**: Exact +1.
- **information_probability**: Deterministic global set characterization; no probability, causal learner, measurable/computable choice or regret guarantee.
- **boundaries**: The sign restricts x, not y; zero excluded only in this leaf, covered by terminal.

Actual proof: Global support at0 and2*x, with |x|=x and |2*x|=2*x, forces x*(g-1)=0. Strict hx excludes x=0 and yields g=1. Conversely the proposed slope simplifies the real left side to y, bounded by |y| for EVERY y; no positivity restriction on y.

### `BanditRL.OnlineConvex.abs_subgradient_negative`

Verdict: accepted-with-explicit-delta (BODY only). Header SHA `72cc1d3ac4754af80a367ad2bec624bbdf45eca740ab79a29cc03f7ca3547a6e`.

- **objects_spaces**: Scalar real x,g,y; fixed f(y)=coe(|y|):EReal. No free E/finite-dimensional/completeness parameter.
- **quantifiers**: Every real x with x<0; every slope g and ALL ambient real test y.
- **assumptions**: Only strict negativity x<0.
- **conclusion**: S(abs,x)={-1}; both existence and uniqueness.
- **constants**: Exact -1, not +1.
- **information_probability**: Deterministic global set characterization; no probability, causal learner, measurable/computable choice or regret guarantee.
- **boundaries**: Positive and zero test points remain included; zero query is handled separately.

Actual proof: The same actual tests0 and2*x use |x|=-x and |2*x|=-2*x, forcing x*(g+1)=0. Strict negative x is nonzero, so g=-1. Converse simplifies to -y<=|y| globally; the minus sign is not lost.

### `BanditRL.OnlineConvex.example_2_24`

Verdict: accepted-with-explicit-delta (BODY only). Header SHA `4b044c75e8628878dea1648d15454734fb5eed6107330fca567ada3502f2cf1b`.

- **objects_spaces**: Scalar real x,g,y; fixed f(y)=coe(|y|):EReal. No free E/finite-dimensional/completeness parameter.
- **quantifiers**: Every real x, every candidate g; membership quantifies every ambient real y.
- **assumptions**: No sign, convexity, differentiability, finite-domain or support premise.
- **conclusion**: Full nested-conditional set equality: {1} if 0<x, Icc(-1,1) if x=0, {-1} otherwise.
- **constants**: Exact constants +/-1 and zero; no approximation.
- **information_probability**: Deterministic global set characterization; no probability, causal learner, measurable/computable choice or regret guarantee.
- **boundaries**: Final else implies x<0 from not(0<x) and x!=0. Exhaustive all-real query coverage retains the entire zero interval.

Actual proof: Actual split_ifs invokes positive, zero, negative producers. In the final branch le_of_not_gt hp and hz imply x<0. Thus no external support inequality, nonzero premise, selected slope or omitted query is introduced.

## Whole canary, actual gates and historical bytes

The zero-boundary canary rewrites the actual interval theorem and proves both endpoints and1/2 present and2absent. The non-singleton canary takes any hypothetical singleton, transports both distinct endpoints into it and contradicts their equality. The all-points canary really invokes the complete source terminal at2,-2,0. These three unchanged proofs contain no assumed oracle or manufactured regularity premise. Finite instances test meaningful boundaries; they do not replace the universal source proof.

All190fixed current raw rows rehashed successfully. All123prior CONTRACT raw rows resolve and match the unchanged original receipt. The two changed native logs have separately preserved exact reviewed prefixes; I additionally checked current bytes start with those exact snapshots. This is append-only history resolution, not replacing old receipt hashes with refreshed values.

Actual body re-elaboration exit0 took10.25s. Focused build3288jobs and whole-canary focused3289jobs exited0; cached jobs are not claimed as all clean rebuilds. Seven uniquely named #print outputs independently parsed as exactly propext/Classical.choice/Quot.sound, no sorryAx. Four separate native guards passed and actual frozen declaration hashes match. Guards do not themselves establish compilation or literature fidelity.

Actual selected graph has7proof nodes,0definition nodes,1024direct type/value occurrences. All nine required pairs are present in actual value_dependencies. The old four graph nodes match exactly, retaining the4node666reference readiness scope; this is neither a full registry nor unrelated canary export. Prepared v1 helper issues were corrected in versioned v2 before execution; no unexecuted helper error is relabeled as a failed Lean gate. Original diagnostics are retained.

## Reader obligations and remaining gates

No mathematical repair; the seven existing reader obligations remain separately required before FINAL:

1. Explicitly attribute ONE printed Example2.24 with THREE cases and FOUR retained proof refinements; zero new production definitions/proofs/TESTs/canonical nodes.

2. Publish the properness convention beside the source correspondence: generic shared S permits all EReal functions, unlike printed proper-function Definition2.20; absolute value is globally finite/proper so this specialization has no improper-function gap. The complete S is borrowed, not locally owned.

3. Keep all four actual types scalar real without extra E/FiniteDimensional/CompleteSpace/convexity/differentiability binders; no multidimensional norm generalization.

4. Retain both necessity and sufficiency, every real candidate g and ALL ambient real y, inclusive zero endpoints/full interval; explain the final else is genuinely negative, not an added x!=0 restriction.

5. Distinguish the actual zero/nonzero producer arguments, whole three retained canaries and current fresh gate records from old20261003 evidence; graph4nodes666direct occurrences/readiness is not full/canary/package acceptance.

6. Preserve four curated links, four canonical declarations, exactly three notation entries and other Book subtrees; curated teaching links are not exhaustive dependency graphs.

7. Keep adjacent Example2.25 and all remaining Chapter1/2/appendix work required, Chapter2 null/incomplete and whole Goal active; future body/combined/site/final/PR gates remain separate.

This BODY review does not accept the combined root/Tests/full harness, final reader/site/registry/immutable binding/PR stages. Chapter2 remains null/incomplete and whole Goal ACTIVE; adjacent Example2.25 and remaining source obligations remain mandatory. No main/live/merge/deploy/retirement or whole-package acceptance.

## Exact raw inventory

Fixed inputs and resolved contract snapshots were actually read as bytes and independently hashed. Administrative helper/history rows are provenance, not claims that planned future gates ran.

| Path | Raw SHA256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `BanditRLProof.lean` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `BanditRLProof/OnlineSubgradientAbsolute.lean` | `17157c976889f078d02f183b55edf2821e29efa5aa32d4bfff309c2b3713db0c` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `BanditRLProof/OnlineSubgradientSum.lean` | `580655a26e335d9db13c6ebb8f3c0d9ecf36ee07edc9d4c33c7d98194eae2b3c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/00_context.md` | `8db9f850f878d6d19a358a50c3c16be834b41e2cb7939ebb1a38788ac7114497` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/10_upper_director-v1.md` | `15c44191f3fb3f81ac7b1cb533bec5a2198418e58a886e1926e7373d0607311d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/20_architect-v1.md` | `fd1ef1292fb7999baadb8365f88ceeec6cf7f2185c60055fb85ad67d8acb5ae2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/30_lower_worker-v1.md` | `b6cfa16c53e82398378a0db466c7816a07e9aef538492ac23122f211dabf5aa5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/acceptance-helpers-before-use-v1.json` | `4665c9995a27f13c4665fbba8cc7e360de06f5cf9795a34116710116a71a8fec` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/actual-types-v1-01-exit.json` | `cce0c738315d41c2114d77094ae5eeb58804f96c3acc5757b9c5aee7ce21facb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/actual-types-v1-01.log` | `e077573262223580c7cadfd1ca6648354f9bd4514e10b0718deb5bd86f036ada` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/adapter-helpers-before-use-v2.json` | `14dcaf68a913abc9b20928aa5ddebdfc5959192481edfcc9cf0dfa9cda5d6fc2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/adapter-preparer-before-use-v2.json` | `784ef60835fcb2b29ba833f974f35a83bbcec79061da86e888c7dfc1d04d083b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/authoritative-private-workflow-binding-v1.json` | `e15a1e7890dfc844960403df526b5814b605704c21b0c28c72be114547b5f2be` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/bind-integrated-gates-v1.py` | `90642b5068990c758d62d1a726f6ec4685d50e07aa9d09f61497dc8630171b1e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/blind-generated-before-use-v1.json` | `ed6b6d1bfd0c203e514f755f80733806f4f61d52f557b1d21ecbdc55b7cab662` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/blind-packet-v1.md` | `c653be6cc0a60640a87c8da2323eb99e4be93a7038c3f9d52a616a5930a15fae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/blind-receipt-v1.json` | `39e2f5d6645c9bb090b9f2ed615fe923c8ea5f2f4fe14d690122d97326d9e011` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/blind-reconstruction-v1.md` | `a4812535cf42121998863869b3d7b19d18ae93f1062aac4b4407bc79ff20a3d1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/bootstrap-generated-before-use-v1.json` | `9a772eb86a70188f212edc57eeba4ceb634ce86bd6462f36903be197ff855720` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/bootstrap-helper-before-use-v1.json` | `ac53a48470e565d5ea92a22a52a0c4ba457145873961ab5863ea00d53a375c4b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/bootstrap-v1.py` | `4fd7da776cfe68f75970f3204f7989adfc9ea36effd7292981d0235eefcc174c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/browser-v1.py` | `3f2277a7974dc857c635020c993fbd62057ef5f3dc4a2cce7e959a7b29df8576` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/check-scoped-diff-v1.py` | `2c2d13c1de3c554ec3d9a7f1c1d08712b8a279fcbffaa0893099d60afa8568ed` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/commit-owned-v1.py` | `e61aac065d297a5bc2213b6633aa70f6eca48a0b3e87a0157ca815ba3cbb0be0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/common.py` | `84ee34ccd9f2f2e9775bf01337e42ba58c2de2f67068b38dff5328201361375d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/compiled-dependencies-v1.json` | `181d7e0112da3058f575da03e51593d2f4ed3ffd7aae56157f9bea545317a1fe` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/compiled-public-graph-v1-01-exit.json` | `64e0915979f8d8170f7d86cc150100301bf549b24f25d55e8feed0595e2adc59` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/compiled-public-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/compiled-public-graph-v1.json` | `885f9d4054de288ba19ac0106b490c192ceb6cddc55d2119a2f813520bfd7470` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/compiled-ready-graph-v1-01-exit.json` | `c5288b5f967d05c882beabe9bafd01119fa4624eafce60992527013c5bdd316f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/compiled-ready-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/compiled-ready-graph-v1.json` | `56a3d13e2a209aa290b3f44259c7ff3d0062d73425a3a6764e90f8bf2b12f3d7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/contract-binding-audit-v1.json` | `dde0c9aa18dd90b2b855faaeed21580324abb5edcd40ff624b2720e38d060c7c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/contract-fingerprint-overlay-v1.json` | `3eb2a03152e39bfaae9ae8b53e79746069bd0e90cd71cdd0b9558ee1161faaea` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/contract-helpers-before-use-v1.json` | `81c97907c16198eb19b36a7316095e78c2cde34bb1b13722ef6c12c93126a826` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/draft-fence-abs_subgradient_negative-v1-exit.json` | `3de9e3256112a3cb44f82fe9b450475ae98628964d2fa446489a67f34cfc7833` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/draft-fence-abs_subgradient_negative-v1.log` | `e03e583340994c9cff5ec16e3fbda25b24391e4b72361976bd41641a1b1080e8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/draft-fence-abs_subgradient_positive-v1-exit.json` | `ba7943ad11a85a5004cd7534b4fe38c9fa3d8b5e93cf3596f4d933bc2f19b6f9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/draft-fence-abs_subgradient_positive-v1.log` | `f916a234059585150277f941f1ef05ec4343c7512281eac5c10b780f931d004f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/draft-fence-abs_subgradient_zero-v1-exit.json` | `5b61bde70fdc5d85d933f6e0d7e530ed8176c3760cc0a3f3320d40f91adc72fc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/draft-fence-abs_subgradient_zero-v1.log` | `a64a9014570b067ce61dd3a38cd32c512b422001fa51a79e588490b3c0e542ca` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/draft-fence-example_2_24-v1-exit.json` | `f495a736083725e72a535d674f59879948f55d14c66672eaab4abfa5e3fdd70f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/draft-fence-example_2_24-v1.log` | `ad8428826296d0fe8d92a6830abde454205752db3901646a89cce4182e2d730f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/draft-freeze-v1.json` | `1b15d675a8c46c07a796c58572662cb9df8e06fb5916c0bd000fcbc0e9c18d5d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/draft-lifecycle-v1-exit.json` | `9deb026b813e56c88e659c704636dbc769c416011e9c7abad8d7578335e64270` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/draft-lifecycle-v1.log` | `0f96234035d928fc6cbdec9143c4a3b5fb982f0c8505136b1dc423972036e9fc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/gate-helpers-before-use-v1.json` | `6dd279144ff8d90fe9d5b57ac6156ce25e7456e1346494a6a5e610289b386809` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/historical-raw-supersession-contract-v1.json` | `4cf412352bf8887a33fc181e3ae38b5f1e9a7c039eb7d6bf4642fc053dd2410a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/historical-raw-supersession-v1.json` | `f53385b91f1dcddc6db0d62b128af723f56d30e2c94749d4e62a2a45c784fe31` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/integrate-reader-v1.py` | `6e554c453b09db45eecf9b2689c018383a0545a686867ad24cdc4886f1b8d28d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/leaves/actual-types-v1.lean` | `f7080a25092367854f5697e7f0dc350cfa2820337172db8c177d156fb2593454` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/leaves/export-public-dependencies-v1.lean` | `b07ae48bc3a5a1f7f19e7f5392d7bd2c1c8fc9b8539c12d8f682c7417a1fc9c2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/leaves/export-ready-dependencies-v1.lean` | `f17d5acf5143f79189db9f80cc9bb142a6d760c2bb26d6f56ffa14f2d955b3bc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/leaves/pinned-APIs-v1.lean` | `eda9950632425e0a098504419f7c49094657caca07248c9686b42514906689b6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/leaves/public-all-axioms-v1.lean` | `091ccc4435b25add7c285725253a34b57ed5ad09c11bca77b01a16f15ab2fa1d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/local-declaration-search-v1-exit.json` | `62261389e92c70b309b5f316b50c170e645cb5814fd18aa643fb2c79889d4ddd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/local-declaration-search-v1.log` | `ec8d0091756e40bf8c3ff739c4376b1791e9206ee6e51760238cdd26151d8b14` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/local-memory-search-v1-exit.json` | `36b70ee01a69f9b7e583e61b4cb5fe3b0ddbe43760ee0ab89d345beefaf965c9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/local-memory-search-v1.log` | `68e411a340587e2fc2480986a7c9093aa4cf4bfbac8f0cb53196f4f40cc7e060` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/native-draft-fences/abs_subgradient_negative.json` | `e03e583340994c9cff5ec16e3fbda25b24391e4b72361976bd41641a1b1080e8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/native-draft-fences/abs_subgradient_positive.json` | `f916a234059585150277f941f1ef05ec4343c7512281eac5c10b780f931d004f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/native-draft-fences/abs_subgradient_zero.json` | `a64a9014570b067ce61dd3a38cd32c512b422001fa51a79e588490b3c0e542ca` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/native-draft-fences/example_2_24.json` | `ad8428826296d0fe8d92a6830abde454205752db3901646a89cce4182e2d730f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/native-public-fences/abs_subgradient_negative.json` | `1bda0dcef5fd46e47d593142e0702d6ff44a09436c4f16000556c497a656a1a6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/native-public-fences/abs_subgradient_positive.json` | `2f465586fe384b9959bec8e258ef90f0f732a3a06f292d97cc84e9e192172f16` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/native-public-fences/abs_subgradient_zero.json` | `2011044f7b7338c70cf2048fb578a94220bf15c3924afd85e33c0bfa0e9d9b65` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/native-public-fences/example_2_24.json` | `d9e14466a6e3affca1f0f36810594eb7ffcb0c2c8796ae1a617a1833f776abe0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/phase-helpers-before-use-v1.json` | `58ed7e8e5815ee5d865cc849ebf03066c292496e414f6ad94ce685a24b4577ec` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/pinned-APIs-v1-01-exit.json` | `b1890bab5c10096334cabbd85e99568de3f7230dbabe7d633958a1baf8c6c257` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/pinned-APIs-v1-01.log` | `ddcf71fc9987d257745a88e690ceae0907ef2e0b853fb3d15328da32688ac29e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/preparation-diagnostics-v1.md` | `d4b7f1ca42edb3695c06a8d88a04a4d8f86dac37e7234570002553bc1c4d5981` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-contract-review-v1-01-exit.json` | `4c843e5f9900147315892cf1dc7c901bb8b34dbe4319f38122ef642864256e92` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-contract-review-v1-01.log` | `a4137471e6affcc568f94a051175a02bbaedf81a3e87c6995fa6ad2298099485` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-contract-v1-01-exit.json` | `d45214624d7117614f312f4b826806baa9a53f8b6504f102f46c387b83465851` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-contract-v1-01.log` | `28cc3430f768e594e0e18e41ca3d8b91dc6eaab1de35bfe2822893e36136de38` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-contract-v1.py` | `a2d8dd5cbaf076053db06fa9dfdbfb99c1a5827eed1d331e689cc5e4897ad708` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-gate-helpers-v1-01-exit.json` | `a70e370034064e26b4bc6ce343a29badbd4236c5c69f56c9f091e2ecd0f2247b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-gate-helpers-v1-01.log` | `6f75b43643173beecc3bee426c6771150c9d68850b637bac7fa33de218fd2439` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-gate-helpers-v1.py` | `907a3d835929e09d9d74ca0399f5be677be49e7a16c3ee9c3313923f843b277d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-helper-adapters-v2-01-exit.json` | `6defc7ec9d1f88612922d9b9caac2543b701cf82244a7ac76f8f38dd25f79692` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-helper-adapters-v2-01.log` | `44c8d1db609d66d6d203177caa62beb755c5a451cc64c2fee83eef75c07ef903` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-helper-adapters-v2.py` | `e6653377c4a95c5691d39bdffc0f8a051b28eba349f7c5c072fc9767d35bfa09` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/preserve-contract-native-v1-01-exit.json` | `29e3a1d931d612051841b510c940a30f995dba2df08f64925c0a2ce9ff6fc053` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/preserve-contract-native-v1-01.log` | `2593ab45223abe18c8e98ebd794ca1be801a29e92159a78231439872a5100491` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/preserve-native-prefix-v1.py` | `a9d04580fc1e9aa5bc23a4ac9491952ec497f834b02d5262aae029173d34dddc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prior-contract-binding-v1.json` | `91922b387b46120efdff9a83f2451ddb3835d1b7c01180d961dda63aa03718fe` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prior-delivery-raw-binding-v1.json` | `9a4683cba238e8263074d30a6e14208649c44950ae92383936a3824dceba864e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/project-gates-v1.py` | `e29f123be94f9b07b310b59381fef222cb2a43b9aa5ec2fae0daa75cd6413547` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/project-helper-before-use-v1.json` | `6f3f9e80862c8c1ae30c3d35c95c472c16b25735011a72a54679f29bbe1ca4dd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/proof-obligations-draft-v1.json` | `74e658d664fb2bd036ad99f94e5dda48d74e3190bfd2a2aa1b7472e42bff5bf7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/proof-obligations-proving-v1.json` | `f97e4f3bff8861947d0108466321c000656438fd82992d14036eff659b181d2d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/proving-lifecycle-v1-exit.json` | `3a705f9cda47c68881be959ec672ef6c229a1e92905aa302be310003a6f7abc5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/proving-lifecycle-v1.log` | `2749fcbff0f6e3ba9baf81f8944853662bd2395e436ed7352d3b1f9b2af5de7b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-actual-bindings-v1.json` | `8d774729434741cfc9c9dc617d861bb8e63c886fd0118cbca31231828540f67f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-all-axioms-v1-01-exit.json` | `c7d2c109592a4d230449c58fa1e644a856f6f5ded2191cb8df7fc5760db85674` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-all-axioms-v1-01.log` | `7870459307b4dc95ff5502c28329ad88d2d0d6453acce157566753a31126bb29` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-body-packet-v1.md` | `c46d42408345f19ec7b081efbd364bab054d8f58abf2f6704dc42e745141b44a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-body-v1-01-exit.json` | `26e4548fbf8d845f9f4880329d3cceaae57ed80977109471ba0b892e9706297c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-body-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-canary-focused-v1-01-exit.json` | `d2dfd1ede03961f88ee6bb7866c99e8e4ecbc626b7f6962c96784f509369bc59` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-canary-focused-v1-01.log` | `a6902d96c3b4cf6a13e5c0bfead2c1346ad8689799bd74d878e99bf50500c8be` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-fence-abs_subgradient_negative-v1-exit.json` | `68e0fdf5115d00aef953056050733f8340cd8d4ad9e039caf23557798f1fe358` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-fence-abs_subgradient_negative-v1.log` | `1bda0dcef5fd46e47d593142e0702d6ff44a09436c4f16000556c497a656a1a6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-fence-abs_subgradient_positive-v1-exit.json` | `1769dec8154b76913c37a9de0e56a2a3b4ab1783e5e34f08b0f0688fb112a093` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-fence-abs_subgradient_positive-v1.log` | `2f465586fe384b9959bec8e258ef90f0f732a3a06f292d97cc84e9e192172f16` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-fence-abs_subgradient_zero-v1-exit.json` | `6a5536cb30710dd9195703f1ee59a6c91c6b4b5fe46ab83cb18ac90f752fae84` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-fence-abs_subgradient_zero-v1.log` | `2011044f7b7338c70cf2048fb578a94220bf15c3924afd85e33c0bfa0e9d9b65` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-fence-example_2_24-v1-exit.json` | `8b12f47100242b22ca00012bd4786a7994f08ce9c90dee454f04cebabc6f8247` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-fence-example_2_24-v1.log` | `d9e14466a6e3affca1f0f36810594eb7ffcb0c2c8796ae1a617a1833f776abe0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-named-declarations-v1.json` | `4ecad6c29c3d4e8230ab3bae7bd95bbcb8466636004735d66ea6606159f9c363` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-safe-abs_subgradient_negative-v1-exit.json` | `3e5c09a5a94d5b82ac91d86b5d76f572008fc4caa17f7b11893db66777640366` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-safe-abs_subgradient_negative-v1.log` | `33d4ad414f54d0c5b50671adacf663c4b25135e53bb3486c12b0ba217ed6ec52` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-safe-abs_subgradient_positive-v1-exit.json` | `dd06dbd440834bccd96870cebb684ed9a6cd7c65d465663a82c88b2c2333cce5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-safe-abs_subgradient_positive-v1.log` | `3aca3ed48887f633435e10f2f1b066cb6e93cc4adad11da7ba7ff090beb0fa1b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-safe-abs_subgradient_zero-v1-exit.json` | `13b6ea3a56474983969a0ff1973b98ebc437ef723a6530b94e46a250c308e71b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-safe-abs_subgradient_zero-v1.log` | `5957806918e412ec0ed67f16395b82cba3b937cd0cf7f2ce21cd93ea20f0694d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-safe-example_2_24-v1-exit.json` | `9504c9d6346b75309e70847323145f57a26ed8bb6e9461a888efa94b8efcc2bf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-safe-example_2_24-v1.log` | `6fe646b606ce653832c785f688646c9637e16a692bde2a46aaca7fb5f8897968` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/ready-dependencies-v1.json` | `604d9f63831b80a62e767870f666d73350fb7e02cd47c8ec4bd3222c6b3b86f5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/record-acceptance-v1.py` | `530e9a5f443efb23973fe6ab032959699d2117aaacf81f0705237fa2aa863f57` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/record-acceptance-v2.py` | `3c6a67d521bbb56f85b994cc47f9f0518ca203216f82e55e35dbef0a03a8e4eb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/retained-body-trial-v1-exit.json` | `fa472b469c52fa0ea766a5f480bff0b9cb662e6b2d5447225ca45bbf29cc31a2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/retained-body-trial-v1.log` | `7519e9e3c3dd270e4b18618f4530049fea3fc104b363478016d4a9c924889196` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/retained-focused-v1-01-exit.json` | `a584711b8256e282cb4cfc2196a3454087ebd9b2b95937ba52808b22726e2a89` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/retained-focused-v1-01.log` | `4a280e2aee77bf32f4df8f77e13b1de3ef1ac8abd3b8f17e1562a49ea07a83df` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/retrieval-record-v1-exit.json` | `aa468f114d93ceb0fc21f60f3dc66dd6a528e1ca7f5b6b88868de3c55f3e0713` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/retrieval-record-v1.json` | `b4f474c50d8845393617154e29183c19aa7f4f43168b0ed1d7b841434a46a075` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/retrieval-record-v1.log` | `67c289eec37924024a63c5c528ded5f2f27b06909c5fca6fc4b315f7c938fcea` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/revalidate-bodies-v1-01-exit.json` | `13677f5f8cc7a518a800eba149d04b7732a5a12902f8605ce144b0a6cb32e4cb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/revalidate-bodies-v1-01.log` | `495cff6eb07adbeaf2380b835994b117762f6b98b1e91bbdf3f67ab34c320674` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/revalidate-bodies-v1.py` | `3927eea9305e97447dc512a8abd0a23da2e4145331971fbd27381bccbc72c6b0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/review-packets-v1.py` | `9c641c4d9e5e89b518167f26a82b00e0f952f3b4195876bf576a7c4e13ac65b6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/review-packets-v2.py` | `45cc83623dfc40f23e2644124e7aaaaa9e405e083ac2fa9288a904483771fdfe` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/BanditRLProof--OnlineSubgradientAbsolute.lean.txt` | `17157c976889f078d02f183b55edf2821e29efa5aa32d4bfff309c2b3713db0c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/BanditRLProof--OnlineSubgradientBasic.lean.txt` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/BanditRLProof--OnlineSubgradientSum.lean.txt` | `580655a26e335d9db13c6ebb8f3c0d9ecf36ee07edc9d4c33c7d98194eae2b3c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/MANIFEST.md.txt` | `bcc85d267f45cb7d5bf550528a927e20afae1b167aac2be8f2fafaf0efe3c158` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/Tests--OnlineSubgradientAbsoluteCanary.lean.txt` | `5234ba8106382687d2b56396f205c257648d89daa8177a696c91ff404bea3b46` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/Tests.lean.txt` | `cd21ef4e7cea89c7d245eaf4dff14be8baa34f2d336e40d6f6bbb16011678340` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/contract-reviewed-runs--lifecycle_sessions.jsonl.txt` | `063f5aec29b931cff6432f1f3b5e338192deb4dd21fa2efbe671076c4d4e7ae7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/contract-reviewed-runs--trials.jsonl.txt` | `d8e4cd2aebc9aaff68c9d90fc4bf79ca9238a6e534d7211a438b54d1aba3a87b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/lake-manifest.json.txt` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/lakefile.lean.txt` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/lean-toolchain.txt` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/runs--active_frontier.json.txt` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/runs--lifecycle_sessions.jsonl.txt` | `e8b706f13bfb868f6631ef77dae409b04299dc497e55b010210fdb4b0ede515e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/runs--trials.jsonl.txt` | `d8e4cd2aebc9aaff68c9d90fc4bf79ca9238a6e534d7211a438b54d1aba3a87b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/website--content--chapters.json.txt` | `3a8b9105ef1787d523f44fee562a36f3969adc4575674c4f60f22bdb75250978` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/website--content--highlights.json.txt` | `4d788ed4c49db41e30a9575c6beec5f89f37906ce6b431c3e3d22943f2dfc0f9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/website--content--readings.json.txt` | `deb116698be6d3c1fc433e39b52c7228acb7c07723f9bbd0a79bc837c6259847` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/source-contract-inputs-v1.json` | `3603203fc93017fb47c31853f2946c24a8d246d075a72ba4727b795be02c8be5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/source-contract-packet-v1.md` | `1b367c784c90cf9169e9442e51c533a2869ae1f0d822c57fef20988e169b41ae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/source-contract-receipt-v1.json` | `775f9baae4f8387a2ce84bc842e962ff4951d30a3b18c84e7c39eaeba95fe07f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/source-contract-review-v1.md` | `4f918e35f4af54965f235ab49ce0af346fbab01b0bb5c7c75970cb3e5d3b9156` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/source-printed18-pdf30.txt` | `79a3aacef74fc16fd80b21ef87043e0ff5999ff6cf540e4741f09ca6c6447edc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/source-render-binding-v1.json` | `2e08b294e632aef29a61697916322820bf491f2dacfe855df0b2ba0fe30934a7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/stabilized-lifecycle-v1-exit.json` | `79b010653a374f4a9d61ad1e28123c6e9e59e09b73ea373ce614a0908cae8942` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/stabilized-lifecycle-v1.log` | `c9df11e8d88d7b7ba8643371c1081fd2d66714c0dde77cc0ad4750a3838d7292` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/unused-helper-adapters-v2.md` | `2c819a4afadfbedf1b3c2dfe3e012d69ce1b6119137b82a726be9f11270194a4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/verify-history-bindings-v1.py` | `96793e903bed8e6b465bb496ae5f9a406b7de4dc8cbfe3a7345b78e096e89d7a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/verify-history-bindings-v2.py` | `029c5160c5f0946e3771256301d8dff03d9730db054e5a691db93e88405f1bc8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/verify-registry-v1.py` | `27122242b600c97d746637cf90e9dfc644dc462407a0e18de39a74577f4ee584` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/workspace-audit-v1.json` | `51856b6a0f0590744147ead9d41a9de25089f29ce9c291adadf6c2a63fc72d5d` |
| `MANIFEST.md` | `bcc85d267f45cb7d5bf550528a927e20afae1b167aac2be8f2fafaf0efe3c158` |
| `Tests.lean` | `cd21ef4e7cea89c7d245eaf4dff14be8baa34f2d336e40d6f6bbb16011678340` |
| `Tests/OnlineSubgradientAbsoluteCanary.lean` | `5234ba8106382687d2b56396f205c257648d89daa8177a696c91ff404bea3b46` |
| `docs/contracts/online-book-v1/source-inventory.json` | `a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7` |
| `docs/contracts/online-subgradient-absolute-migration-v1/borrowed-definition.txt` | `2c1c4b506ec806f256fad8c2f91633bf0948e326fab3f091f14a319f6b57dba4` |
| `docs/contracts/online-subgradient-absolute-migration-v1/dependency-DAG-v1.json` | `65b4a2ccc7c96c61d26ad018d04de6e511d3e5e3ed4c224f7eb0ff8a97426162` |
| `docs/contracts/online-subgradient-absolute-migration-v1/headers.json` | `929a29d936d37031544863d10fff4bfa10419112100344f9515da6aeb6e55ceb` |
| `docs/contracts/online-subgradient-absolute-migration-v1/scoped-contexts.json` | `31978bb157e60dfe2a4591d24509246b364040d44ddb7f1aeec3de7bf4273533` |
| `docs/contracts/online-subgradient-absolute-migration-v1/source-card.json` | `6c0faa8bf3c77451a162124de8bf9ae47720c1ebfa3da1a5366d0910e2e43d36` |
| `docs/contracts/online-subgradient-absolute-migration-v1/source-intent.md` | `8db9f850f878d6d19a358a50c3c16be834b41e2cb7939ebb1a38788ac7114497` |
| `docs/contributor-codex-contract.md` | `d7dfa3406def35de292b202f45ff8303b9a550310bd00979be838e5a2348a498` |
| `docs/theorem-publication-protocol.md` | `b1e5ac73cfe0a90742567736b422787c90a51e6b6ff007cc1dc8d598948f687e` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `research-wiki/mathlib/theorem-cards.md` | `4656c1a8ccd4b2d8523cf5cf48bd1f966e7ba2c2237e2e578d6b8c2ecc6fbd97` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `runs/lifecycle_sessions.jsonl` | `2ca4b24a8951fc8540a9da07808b3a103a37285c22674db81547337c54ea41e8` |
| `runs/online-subgradient-absolute-migration-20261007/public-body-inputs-v1.json` | `1c4fb16bf848871c4e71a9ab57c90808377011a3e6a074a8504988b852fee06d` |
| `runs/online-subgradient-absolute-migration-20261007/source-contract-inputs-v1.json` | `3603203fc93017fb47c31853f2946c24a8d246d075a72ba4727b795be02c8be5` |
| `runs/online-subgradient-absolute-migration-20261007/source-contract-receipt-v1.json` | `775f9baae4f8387a2ce84bc842e962ff4951d30a3b18c84e7c39eaeba95fe07f` |
| `runs/trials.jsonl` | `79dfde6b62fafc628283dfdc12182b12a276e07ee0618c9f9177a9d047e97426` |
| `tmp/online-subgradient-sum-source-pdf30-v1.png` | `c4354de7297923fd82f74645ddd50fdb582f90b6eeb9a7536fd9f33ec5489ebd` |
| `website/content/chapters.json` | `3a8b9105ef1787d523f44fee562a36f3969adc4575674c4f60f22bdb75250978` |
| `website/content/highlights.json` | `4d788ed4c49db41e30a9575c6beec5f89f37906ce6b431c3e3d22943f2dfc0f9` |
| `website/content/readings.json` | `deb116698be6d3c1fc433e39b52c7228acb7c07723f9bbd0a79bc837c6259847` |
