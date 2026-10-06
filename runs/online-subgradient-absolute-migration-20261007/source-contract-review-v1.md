# Example2.24 contract source review

**Verdict: accepted-with-explicit-delta — CONTRACT stabilization only.** No mathematical repair required. Actor `/root/source_reviewer`, requested GPT-6 Astra / medium; runtime provenance not independently attested. Prior source-review history is acknowledged; no new-history blindness or human/external-review claim.

## Source verification and attempted mismatch checks

All120fixed input hashes independently match. The original PDF was additionally hashed (`cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`), page30 freshly extracted, and the bound page image actually viewed. Printed18 Example2.24 is one example with exactly three branches, not four source results. Its zero branch visibly has the CLOSED interval [-1,1]. Adjacent normal-cone/max/hinge/affine results are separate mandatory work.

Four actual native declaration headers independently match their frozen hashes. Actual @types confirm scalar real specialization: no hidden ambient E, finite-dimensionality, completeness, convexity, properness or differentiability parameter. Properness is legitimate without a supplied premise because the fixed absolute function is real finite everywhere and real space has a finite witness at zero. The EReal embedding preserves real addition/order; no mixed-infinity arithmetic occurs in this instance.

The complete borrowed S is `{g | forall y, f x + coe(inner real g (y-x)) <= f y}` with generic normed real inner-product context, no finite-dimensional/proper binder. That generic scope is wider than printed Definition2.20; it must not be advertised as a new owned definition or as proof that arbitrary improper-function behavior is source-sanctioned. Here inner reduces to scalar multiplication and every value is finite, so the specialization faithfully represents the ordinary scalar support set.

Anti-anchoring checks found no selected-subgradient substitute, lost interval endpoints, sign error, local-only support, or added nonzero restriction on the full terminal. Each set equality quantifies all candidate slopes and both directions; the sign hypotheses constrain x only, never y. The residual else is negative by real order. Existing proof bodies were read solely for contradiction checks: zero necessity uses tests +/-1; nonzero necessity uses0 and2x and nonzero cancellation; sufficiency treats every y. The terminal calls allthree leaves. This is not a fresh BODY acceptance.

## Four target comparisons

### `BanditRL.OnlineConvex.abs_subgradient_zero`

Verdict: accepted-with-explicit-delta (contract only). Header SHA `e878c47ef95faa47b1418c365baea538ad208382d41cb020cb1d4724132ada34`.

- **objects_spaces**: Scalar real x,g,y; fixed f(y)=coe(|y|):EReal. No free E/finite-dimensional/completeness parameter.
- **quantifiers**: Fixed query x=0; every real slope g, each tested against every real y.
- **assumptions**: No premises.
- **conclusion**: S(abs,0)=Icc(-1,1), both inclusion directions.
- **constants**: Exact inclusive endpoints -1,1; every intermediate real slope.
- **information_probability**: Deterministic global set characterization; no probability, causal learner, measurable/computable choice or regret guarantee.
- **boundaries**: Both endpoints, fractional slopes, and exclusion of all slopes outside interval; not selected zero/singleton/existence-only.

### `BanditRL.OnlineConvex.abs_subgradient_positive`

Verdict: accepted-with-explicit-delta (contract only). Header SHA `7c28bc210670ae091789b68390cafca47f511cd3884a86e142611be79a001620`.

- **objects_spaces**: Scalar real x,g,y; fixed f(y)=coe(|y|):EReal. No free E/finite-dimensional/completeness parameter.
- **quantifiers**: Every real x with 0<x; every slope g and ALL ambient real test y.
- **assumptions**: Only strict positivity 0<x.
- **conclusion**: S(abs,x)={1}; both existence and uniqueness.
- **constants**: Exact +1.
- **information_probability**: Deterministic global set characterization; no probability, causal learner, measurable/computable choice or regret guarantee.
- **boundaries**: The sign restricts x, not y; zero excluded only in this leaf, covered by terminal.

### `BanditRL.OnlineConvex.abs_subgradient_negative`

Verdict: accepted-with-explicit-delta (contract only). Header SHA `72cc1d3ac4754af80a367ad2bec624bbdf45eca740ab79a29cc03f7ca3547a6e`.

- **objects_spaces**: Scalar real x,g,y; fixed f(y)=coe(|y|):EReal. No free E/finite-dimensional/completeness parameter.
- **quantifiers**: Every real x with x<0; every slope g and ALL ambient real test y.
- **assumptions**: Only strict negativity x<0.
- **conclusion**: S(abs,x)={-1}; both existence and uniqueness.
- **constants**: Exact -1, not +1.
- **information_probability**: Deterministic global set characterization; no probability, causal learner, measurable/computable choice or regret guarantee.
- **boundaries**: Positive and zero test points remain included; zero query is handled separately.

### `BanditRL.OnlineConvex.example_2_24`

Verdict: accepted-with-explicit-delta (contract only). Header SHA `4b044c75e8628878dea1648d15454734fb5eed6107330fca567ada3502f2cf1b`.

- **objects_spaces**: Scalar real x,g,y; fixed f(y)=coe(|y|):EReal. No free E/finite-dimensional/completeness parameter.
- **quantifiers**: Every real x, every candidate g; membership quantifies every ambient real y.
- **assumptions**: No sign, convexity, differentiability, finite-domain or support premise.
- **conclusion**: Full nested-conditional set equality: {1} if 0<x, Icc(-1,1) if x=0, {-1} otherwise.
- **constants**: Exact constants +/-1 and zero; no approximation.
- **information_probability**: Deterministic global set characterization; no probability, causal learner, measurable/computable choice or regret guarantee.
- **boundaries**: Final else implies x<0 from not(0<x) and x!=0. Exhaustive all-real query coverage retains the entire zero interval.

## Reconstruction, readiness and canary limits

The current restricted blind reconstruction agrees on all four contracts and complete global S. Its author explicitly retains prior actor history; this reviewer has source/body access and makes no blind-access claim. Compilation/API evidence is readiness only: the actual scoped graph has4proof nodes/666direct type/value references and all six required support/terminal value pairs are present. It is not a full graph or a current fresh whole-canary/package audit.

The whole existing canary was read: endpoints -1 and1 plus1/2 included,2excluded; a separate theorem rules out ANY singleton; terminal instantiated at2,-2,0. These are meaningful existing tests, not new tests or an independent proof of universal statements from samples. Fresh BODY/kernel/canary/integrated/reader/site/PR gates remain required. Read-only guessed-path diagnostics are retained and do not establish mathematical failure or repair. Administrative prepared helper files and snapshots are bound as raw provenance, not evidence that future commands ran.

## Required reader corrections and retained obligations

Current selected readers already state the global three-case formula accurately. The following are publication qualifications and preservation obligations, not required theorem weakenings:

1. Explicitly attribute ONE printed Example2.24 with THREE cases and FOUR retained proof refinements; zero new production definitions/proofs/TESTs/canonical nodes.

2. Publish the properness convention beside the source correspondence: generic shared S permits all EReal functions, unlike printed proper-function Definition2.20; absolute value is globally finite/proper so this specialization has no improper-function gap. The complete S is borrowed, not locally owned.

3. Keep all four actual types scalar real without extra E/FiniteDimensional/CompleteSpace/convexity/differentiability binders; no multidimensional norm generalization.

4. Retain both necessity and sufficiency, every real candidate g and ALL ambient real y, inclusive zero endpoints/full interval; explain the final else is genuinely negative, not an added x!=0 restriction.

5. Distinguish the actual zero/nonzero producer arguments, whole three retained canaries and current fresh gate records from old20261003 evidence; graph4nodes666direct occurrences/readiness is not full/canary/package acceptance.

6. Preserve four curated links, four canonical declarations, exactly three notation entries and other Book subtrees; curated teaching links are not exhaustive dependency graphs.

7. Keep adjacent Example2.25 and all remaining Chapter1/2/appendix work required, Chapter2 null/incomplete and whole Goal active; future body/combined/site/final/PR gates remain separate.

Mathematical repairs: none. Source package accepted: false at this contract stage. No root/Tests/full harness/final reader/immutable/PR result is inferred from retained readiness. Chapter2/book/Goal/main/live/merge/deploy/retirement are not accepted. Old reviews are historical evidence only.

## Exact raw reviewed inventory

All fixed paths were read as raw bytes and rehashed; source, declarations, imported definition, neutral reconstruction, selected readers, actual types/APIs and scoped graph received the semantic examination above. Administrative histories/snapshots are provenance reads, not blanket revalidation of unrelated mathematics.

| Path | Raw SHA256 |
|---|---|
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `BanditRLProof.lean` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `BanditRLProof/OnlineSubgradientAbsolute.lean` | `17157c976889f078d02f183b55edf2821e29efa5aa32d4bfff309c2b3713db0c` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `BanditRLProof/OnlineSubgradientSum.lean` | `580655a26e335d9db13c6ebb8f3c0d9ecf36ee07edc9d4c33c7d98194eae2b3c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/00_context.md` | `8db9f850f878d6d19a358a50c3c16be834b41e2cb7939ebb1a38788ac7114497` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/10_upper_director-v1.md` | `15c44191f3fb3f81ac7b1cb533bec5a2198418e58a886e1926e7373d0607311d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/20_architect-v1.md` | `fd1ef1292fb7999baadb8365f88ceeec6cf7f2185c60055fb85ad67d8acb5ae2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/actual-types-v1-01-exit.json` | `cce0c738315d41c2114d77094ae5eeb58804f96c3acc5757b9c5aee7ce21facb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/actual-types-v1-01.log` | `e077573262223580c7cadfd1ca6648354f9bd4514e10b0718deb5bd86f036ada` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/authoritative-private-workflow-binding-v1.json` | `e15a1e7890dfc844960403df526b5814b605704c21b0c28c72be114547b5f2be` |
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
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/compiled-ready-graph-v1-01-exit.json` | `c5288b5f967d05c882beabe9bafd01119fa4624eafce60992527013c5bdd316f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/compiled-ready-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/compiled-ready-graph-v1.json` | `56a3d13e2a209aa290b3f44259c7ff3d0062d73425a3a6764e90f8bf2b12f3d7` |
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
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/phase-helpers-before-use-v1.json` | `58ed7e8e5815ee5d865cc849ebf03066c292496e414f6ad94ce685a24b4577ec` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/pinned-APIs-v1-01-exit.json` | `b1890bab5c10096334cabbd85e99568de3f7230dbabe7d633958a1baf8c6c257` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/pinned-APIs-v1-01.log` | `ddcf71fc9987d257745a88e690ceae0907ef2e0b853fb3d15328da32688ac29e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/preparation-diagnostics-v1.md` | `d4b7f1ca42edb3695c06a8d88a04a4d8f86dac37e7234570002553bc1c4d5981` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-contract-v1-01-exit.json` | `d45214624d7117614f312f4b826806baa9a53f8b6504f102f46c387b83465851` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-contract-v1-01.log` | `28cc3430f768e594e0e18e41ca3d8b91dc6eaab1de35bfe2822893e36136de38` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-contract-v1.py` | `a2d8dd5cbaf076053db06fa9dfdbfb99c1a5827eed1d331e689cc5e4897ad708` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-gate-helpers-v1-01-exit.json` | `a70e370034064e26b4bc6ce343a29badbd4236c5c69f56c9f091e2ecd0f2247b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-gate-helpers-v1-01.log` | `6f75b43643173beecc3bee426c6771150c9d68850b637bac7fa33de218fd2439` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prepare-gate-helpers-v1.py` | `907a3d835929e09d9d74ca0399f5be677be49e7a16c3ee9c3313923f843b277d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/prior-delivery-raw-binding-v1.json` | `9a4683cba238e8263074d30a6e14208649c44950ae92383936a3824dceba864e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/proof-obligations-draft-v1.json` | `74e658d664fb2bd036ad99f94e5dda48d74e3190bfd2a2aa1b7472e42bff5bf7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/public-named-declarations-v1.json` | `4ecad6c29c3d4e8230ab3bae7bd95bbcb8466636004735d66ea6606159f9c363` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/ready-dependencies-v1.json` | `604d9f63831b80a62e767870f666d73350fb7e02cd47c8ec4bd3222c6b3b86f5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/retained-focused-v1-01-exit.json` | `a584711b8256e282cb4cfc2196a3454087ebd9b2b95937ba52808b22726e2a89` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/retained-focused-v1-01.log` | `4a280e2aee77bf32f4df8f77e13b1de3ef1ac8abd3b8f17e1562a49ea07a83df` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/retrieval-record-v1-exit.json` | `aa468f114d93ceb0fc21f60f3dc66dd6a528e1ca7f5b6b88868de3c55f3e0713` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/retrieval-record-v1.json` | `b4f474c50d8845393617154e29183c19aa7f4f43168b0ed1d7b841434a46a075` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/retrieval-record-v1.log` | `67c289eec37924024a63c5c528ded5f2f27b06909c5fca6fc4b315f7c938fcea` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/revalidate-bodies-v1.py` | `3927eea9305e97447dc512a8abd0a23da2e4145331971fbd27381bccbc72c6b0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/review-packets-v1.py` | `9c641c4d9e5e89b518167f26a82b00e0f952f3b4195876bf576a7c4e13ac65b6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/BanditRLProof--OnlineSubgradientAbsolute.lean.txt` | `17157c976889f078d02f183b55edf2821e29efa5aa32d4bfff309c2b3713db0c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/BanditRLProof--OnlineSubgradientBasic.lean.txt` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/BanditRLProof--OnlineSubgradientSum.lean.txt` | `580655a26e335d9db13c6ebb8f3c0d9ecf36ee07edc9d4c33c7d98194eae2b3c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/MANIFEST.md.txt` | `bcc85d267f45cb7d5bf550528a927e20afae1b167aac2be8f2fafaf0efe3c158` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/Tests--OnlineSubgradientAbsoluteCanary.lean.txt` | `5234ba8106382687d2b56396f205c257648d89daa8177a696c91ff404bea3b46` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/Tests.lean.txt` | `cd21ef4e7cea89c7d245eaf4dff14be8baa34f2d336e40d6f6bbb16011678340` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/lake-manifest.json.txt` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/lakefile.lean.txt` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/lean-toolchain.txt` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/runs--active_frontier.json.txt` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/runs--lifecycle_sessions.jsonl.txt` | `e8b706f13bfb868f6631ef77dae409b04299dc497e55b010210fdb4b0ede515e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/runs--trials.jsonl.txt` | `d8e4cd2aebc9aaff68c9d90fc4bf79ca9238a6e534d7211a438b54d1aba3a87b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/website--content--chapters.json.txt` | `3a8b9105ef1787d523f44fee562a36f3969adc4575674c4f60f22bdb75250978` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/website--content--highlights.json.txt` | `4d788ed4c49db41e30a9575c6beec5f89f37906ce6b431c3e3d22943f2dfc0f9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/snapshots/website--content--readings.json.txt` | `deb116698be6d3c1fc433e39b52c7228acb7c07723f9bbd0a79bc837c6259847` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/source-contract-packet-v1.md` | `1b367c784c90cf9169e9442e51c533a2869ae1f0d822c57fef20988e169b41ae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/source-printed18-pdf30.txt` | `79a3aacef74fc16fd80b21ef87043e0ff5999ff6cf540e4741f09ca6c6447edc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/source-render-binding-v1.json` | `2e08b294e632aef29a61697916322820bf491f2dacfe855df0b2ba0fe30934a7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/verify-history-bindings-v1.py` | `96793e903bed8e6b465bb496ae5f9a406b7de4dc8cbfe3a7345b78e096e89d7a` |
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
| `runs/lifecycle_sessions.jsonl` | `063f5aec29b931cff6432f1f3b5e338192deb4dd21fa2efbe671076c4d4e7ae7` |
| `runs/trials.jsonl` | `d8e4cd2aebc9aaff68c9d90fc4bf79ca9238a6e534d7211a438b54d1aba3a87b` |
| `website/content/chapters.json` | `3a8b9105ef1787d523f44fee562a36f3969adc4575674c4f60f22bdb75250978` |
| `website/content/highlights.json` | `4d788ed4c49db41e30a9575c6beec5f89f37906ce6b431c3e3d22943f2dfc0f9` |
| `website/content/readings.json` | `deb116698be6d3c1fc433e39b52c7228acb7c07723f9bbd0a79bc837c6259847` |
| `runs/online-subgradient-absolute-migration-20261007/source-contract-inputs-v1.json` | `3603203fc93017fb47c31853f2946c24a8d246d075a72ba4727b795be02c8be5` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `tmp/online-subgradient-sum-source-pdf30-v1.png` | `c4354de7297923fd82f74645ddd50fdb582f90b6eeb9a7536fd9f33ec5489ebd` |
