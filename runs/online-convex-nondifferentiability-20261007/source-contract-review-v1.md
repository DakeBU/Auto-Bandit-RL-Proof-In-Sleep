# Unnumbered two-dimensional nondifferentiability contract review

Overall verdict: **rejected**, narrowly for source-locator metadata M1. Mathematical contract comparison is accepted for the definition/global-convexity/source-segment targets and accepted-with-explicit-delta for the stronger entire-axis leaf. No mathematical target repair is required. Stabilization waits for a separately versioned locator correction; frozen v1 must remain unchanged.

Actor `/root/source_reviewer`, distinct automated source reviewer; requested GPT-6 Astra / medium. Prior staged source-review history acknowledged. Not blind/human/external review or runtime model attestation. Current restricted neutral decoder reconstructs the four items faithfully, but neither it nor type elaboration proves the targets.

## Actual source mismatch M1

Pinned PDF freshly rehashed `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`; printed19/PDF31 extracted and original PNG actually viewed. The paragraph follows Theorem2.30 and immediately precedes **2.2.2 Analysis with Subgradients**. Both frozen contract.md and source-card.json instead anchor it before section2.3. Page and mathematical example are correct; section attribution is not. Create a new versioned authoritative correction and review, preserving all v1 raw inputs/this rejection. Do not change mathematics to repair metadata.

## Four items, seven slots each

### BanditRL.OnlineConvex.coordinateAbsolute

Mathematical contract verdict: accepted. Raw statement `c8802ccddf8610159a438293c9689649ba96a0b7e7c2fea4b61a3dcf1aff6a04`; normalized native `c8802ccddf8610159a438293c9689649ba96a0b7e7c2fea4b61a3dcf1aff6a04`.

- **objects_spaces**: Actual EuclideanSpace real(Fin2) with L2 topology, real-valued coordinateAbsolute; Lean index0 is printed first coordinate and index1 second. No EReal conversion.

- **constants_normalization**: Exact dimension2, coordinate indices0/1, unit second-coordinate endpoint (0,1); real convex weights when applicable, no rate or approximation constants.

- **information_probability**: Deterministic convex analysis; no probability, feedback, oracle, online algorithm or regret claim.

- **quantifiers**: Every x in real Euclidean plane; complete body |x 0|, independent of x1.

- **assumptions**: No pointwise or regularity premise; everywhere real-valued.

- **conclusion**: Actual total function x->abs(first coordinate), not itself a convexity/differentiability theorem.

- **boundaries**: All real coordinates including zero/negative; no domain/segment restriction. Exact source function with indexing translation.

### BanditRL.OnlineConvex.coordinate_absolute_convex

Mathematical contract verdict: accepted. Raw statement `a277f9804e4c716f020a182d8f7c237030313c630cb257f11f1d66c710e5849f`; normalized native `5ceb15fd5d45f9016aa2f5fe987b5e71b74f5179b96ab3cbe7d3229203e914a8`.

- **objects_spaces**: Actual EuclideanSpace real(Fin2) with L2 topology, real-valued coordinateAbsolute; Lean index0 is printed first coordinate and index1 second. No EReal conversion.

- **constants_normalization**: Exact dimension2, coordinate indices0/1, unit second-coordinate endpoint (0,1); real convex weights when applicable, no rate or approximation constants.

- **information_probability**: Deterministic convex analysis; no probability, feedback, oracle, online algorithm or regret claim.

- **quantifiers**: All ambient pairs and all real nonnegative weights summing1, including endpoints0/1 through ConvexOn.

- **assumptions**: No supplied convexity premise; domain Set.univ.

- **conclusion**: Global ConvexOn real univ coordinateAbsolute, not merely convexity of a restriction.

- **boundaries**: All plane, not only vertical axis/segment; no derivative conclusion. Prospective proof still absent.

### BanditRL.OnlineConvex.coordinate_absolute_not_differentiable

Mathematical contract verdict: accepted-with-explicit-delta. Raw statement `53d604ff05aac824084dd5944b8f6675d8ef233ce9980abbf55c98ec8b023f40`; normalized native `5a4da6ffc5081b1db4f791d2d872ac6c37fe1fd60d55ec147e257e6758c8bc4b`.

- **objects_spaces**: Actual EuclideanSpace real(Fin2) with L2 topology, real-valued coordinateAbsolute; Lean index0 is printed first coordinate and index1 second. No EReal conversion.

- **constants_normalization**: Exact dimension2, coordinate indices0/1, unit second-coordinate endpoint (0,1); real convex weights when applicable, no rate or approximation constants.

- **information_probability**: Deterministic convex analysis; no probability, feedback, oracle, online algorithm or regret claim.

- **quantifiers**: For every x in real2, x0=0 implies ambient failure; second coordinate arbitrary real.

- **assumptions**: Only x0=0; no interval premise or supplied nondifferentiability.

- **conclusion**: Not DifferentiableAt real coordinateAbsolute x: no ambient Frechet derivative.

- **boundaries**: Entire vertical axis including outside[0,1] is a disclosed stronger library leaf; no iff off-axis characterization. Constant vertical restriction remains differentiable, which is a different predicate.

### BanditRL.OnlineConvex.convex_nondifferentiable_segment

Mathematical contract verdict: accepted. Raw statement `30f03b667f47303d7fe3168b5b19994f3b2c73d2ce7496396693c62f0c497221`; normalized native `4e034a3e6385b3ecc4cafa3dcf72f2ee850203d7a3921ec879b5d0c50c7c2deb`.

- **objects_spaces**: Actual EuclideanSpace real(Fin2) with L2 topology, real-valued coordinateAbsolute; Lean index0 is printed first coordinate and index1 second. No EReal conversion.

- **constants_normalization**: Exact dimension2, coordinate indices0/1, unit second-coordinate endpoint (0,1); real convex weights when applicable, no rate or approximation constants.

- **information_probability**: Deterministic convex analysis; no probability, feedback, oracle, online algorithm or regret claim.

- **quantifiers**: Conjunction global convexity and forall x in genuine closed segment from zero to PiLp.single2 1 1.

- **assumptions**: Only segment membership for nondifferentiability; no conclusion supplied as assumption.

- **conclusion**: Global convexity AND ambient Frechet failure at EVERY point of source segment, not a chosen point or scalar-only result.

- **boundaries**: Closed segment includes both endpoints; second coordinate in[0,1], first0. Does not encode Countable/uncountable nondifferentiability locus or complete the preceding misconception argument.

## Source consequences and evidence boundaries

The source function is genuinely real2->real, not a one-dimensional stand-in. Source segment has a nonzero endpoint and includes endpoints. The whole-axis target strengthens only the locus, not the assumptions; restricting a hypothetical ambient derivative along a smooth horizontal curve is an appropriate proposed contradiction route, while the function restricted vertically is constant. No theorem body is supplied or accepted here.

The preceding sentence's countability misconception is not encoded by these headers. source-context-obligations-v1.json correctly preserves a separately required planned cardinality terminal; an uncountability proof cannot be inferred from contract stabilization or passed Prop elaboration. Neither full paragraph nor chapter closes here.

The actual target log elaborates three propositions as Prop and prints the actual definition. Fifteen pinned APIs include real norm convexity/linear-map composition, abs nondifferentiability at0, ambient derivative composition, coordinate projection/single values and global closed-segment endpoints. Namespace failures and nonexistent lifecycle-start CLI are discovery/preparation failures preserved in v1/v2 records; corrected readiness is not three theorem proofs. Exact raw header fingerprints and normalize_statement fingerprints independently recomputed and distinguished; no target silently normalized into a different proposition.

All150fixed raw inputs matched independently; manifest additionally bound for151reviewed rows. Raw-read preservation of retrieval indices/snapshots is not broad semantic certification of all indexed results. Current scrutiny is the frozen definition/targets/source/neutral/API/context and intended route. No new body/native package/chapter/Goal acceptance, no edits to inputs or native logs.

Required mathematical repairs: none. Required metadata repair: M1 above. Future reader requirements follow; they are not already discharged.

- R1: Cite the unnumbered paragraph after Theorem2.30 at end of Section2.2.1, immediately before2.2.2, printed19/PDF31; do not call it a numbered theorem or three printed results.

- R2: Show actual real EuclideanFin2 function |x0| with printed x1=Lean index0, endpoint PiLp.single2 index1 value1=(0,1); no EReal/toReal or scalar-only substitute.

- R3: State global convexity and ambient Frechet failure at EVERY point of the CLOSED source segment, both endpoints included. Do not replace by within/relative/vertical-restriction differentiability; that restriction is constant zero.

- R4: Attribute ALL vertical-axis failure as stronger reusable library leaf; no interval premise there, and no off-axis iff claimed by its header.

- R5: Keep formal uncountability/cardinality consequence separately REQUIRED and planned until an exact target and actual proof exist. Current three headers do not encode Countable and do not close the entire paragraph or general almost-everywhere theorem.

- R6: Explain actual future producer (convex norm through coordinate linear map, horizontal composition contradiction with scalar abs at0, then closed-segment coordinates); proof/type probes are not theorem compilation and dependency readiness is not actual new proof export.

- R7: After actual proofs, show genuine2D endpoint/interior/nonsegment-axis/off-axis and constant-restriction canaries with truthful counts; no planned test promoted to passed.

- R8: Preserve failures and raw-vs-native fingerprint distinction, old math/shared pins/registry IDs/otherBooks; only actual later combined/site/FINAL/native/PR may establish bounded package acceptance. Chapter2null/incomplete/GoalACTIVE and nine otherChapter1 gaps remain.

## Raw reviewed inventory

| Path | Raw SHA-256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `BanditRLProof.lean` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `BanditRLProof/OnlineAffineSubgradient.lean` | `fb45e9a58a84770594d4e88a5df04f18a73203406e82f4a48edffd6d4419ff80` |
| `BanditRLProof/OnlineLipschitzSubgradient.lean` | `c6891c7b868208d707f05652c17ea5948e1bea272f69a7c1da9303c48769e085` |
| `BanditRLProof/OnlineSubgradientAbsolute.lean` | `bf3e8d97f67b78e7ad230b8efd321948f4d7ba1a0e9cde31e8d85c1e9019442b` |
| `BanditRLProof/OnlineSubgradientDifferentiability.lean` | `4f21c5d7fd0ef27a860390b698072d65527610d55e60c16568e82fa99215c1d3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/00_context.md` | `fac5b669860f7da50cacba194a4a850c7b69c0f003bd76e66d7fb32fb31f574d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/10_upper_director-v1.md` | `b3b60715e0200949d86662d75a475739fd92819fd8d68d4736d7af654bdd25c4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/20_architect-v1.md` | `d9c3a967ec6103c2b96417dea686f9184b789b02053c138f1455b006ed8f1221` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/base-PR176-fresh-v1.json` | `ed7e965b52baf37c8585a991dd1eb70874a0a1073901a4af67f028f9cb5c6a1f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/blind-packet-v1.md` | `50ee1b569b31296ab7a5cc681b64e05d350cf08c65abcfa29e0bc599795d3e9a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/blind-receipt-v1.json` | `298b085a211c0406ce77e58564ffd81363f571488c643b37dd9b858c3ad7ebc0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/blind-reconstruction-v1.md` | `7277c48f29c33d9a9a31b8099a7f04d742e3b575d6ba66b909807a46f6be53ac` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/canonical-worktree-audit-v1.json` | `32e4fca9bb6e508b67471342e90630256649f6b8bfaa15c501c313d28a426f69` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/common_v2.py` | `37b8558707c2d6ad1f648c83561b248b258c8c6dccb163b08c3061252e995f8b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/common_v3.py` | `34d2c54738d32b71391b322aa069deaf3714802435c6157a935f7d0fa0c7cacb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/draft-freeze-v1.json` | `cfba4f417953951635a2e3ca62bc5b65a5baf2da766f1e5b69ff9ef7e02296a4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/draft-lifecycle-v1-exit.json` | `d6ade669f2f8436aa18f2b4130fcde630d956cf1794d6be35af915de547262c4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/draft-lifecycle-v1.log` | `6631fb8c9f423cdd0a5afc7c132d18da59c73f4eebaee4c1a6f0ca0428df0b2e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-frontier-refresh-v2-exit.json` | `a71c25c6fdd718bf17635d213e5bc8342a37fdcf81ea5c7118200ba18c88710a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-frontier-refresh-v2.log` | `bff73ff554907d7c5dd50b99f2491f5675e93afb29829e402ec383fb52fe3cdc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-frontier-shadow-v2-exit.json` | `28b2e0609d3aaae09c2b139a4099fccc1b7fc546caf6f35532afbd117d0dbb64` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-frontier-shadow-v2.log` | `ad548f6e24b3214fbf5796c632caa24debbaa21c6622f7dab8abe268f521de7d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-lifecycle-event-v2-exit.json` | `ebf8f27362aba7312f1a6027671528003e2026e4136410d586178c9bd6e6e1bf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-lifecycle-event-v2.log` | `b1e8b438a9b725793b9888d206e98a971ace3df200ec90ed9cb63eab26b28507` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-lifecycle-start-v1-exit.json` | `9f7d744d7eae95ca4ed42c024fb620cc4b6ce4cdedc4e0ec5f4e4430c778c162` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-lifecycle-start-v1.log` | `a9ade7d1a4fc2b2402eb3fd72acafe7dcfc35d578500fea5344139d93f4c118a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-list-lean-decls-v1-exit.json` | `fc147e548d481e8e1437834bb6e1c5a8cf577f2ba84bbba94ebb914a7786a079` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-list-lean-decls-v1.log` | `258218f16a12b1a530d85ae83e6c2449237af8a0a1153bb35de40245d665b131` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-list-mathlib-v1-exit.json` | `d19402a179b96f9fdb3cd0d4832b5600679360936d37cb1689f3254438634916` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-list-mathlib-v1.log` | `eedc3e9609fdc7a3bcf76443a33933477de80dcc4ec9906b64a691e29b207e9d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-list-papers-v1-exit.json` | `4f6a7af9f6a074501d48723792a2f4a29ea1eaa584c692e65f22eb3800f4c407` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-list-papers-v1.log` | `57fdd9fadca031cddeec9da9c4ba947cccb3b1b155129de3a81b72b0c811a696` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-list-weapons-v1-exit.json` | `188d563fdf5643a44ea650f9f2d27c5c8dfa91307ed04493b407e733d5614f32` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-list-weapons-v1.log` | `529fdc45da8d53249b6cea7712803e68cc0251026c7a66d1a067ac6413c9617d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-reference-index-v1-exit.json` | `b701d9d6d9464533fe33e03808a30b46a891219f8ed29cd92949b4eec2578b52` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-reference-index-v1.log` | `6943acba1d20272cfd239404bfaaa8457d0205a56876004e7c3fed2df97fc3d8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-safe-verify-v1-exit.json` | `297bcc51e3a32d14ffd211d52fb5496017b0c6f91a533456ceb79abf05f0f264` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-safe-verify-v1.log` | `1773541c625f225e5a9abc61985c3ad19e871cf31aa0cf89cc440b3d8398862c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-search-memory-v1-exit.json` | `2066c18582a0abda12dcf7195adc533f8244d2a0d8565e4cd26b40861f3d7cdd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-search-memory-v1.log` | `b2f23faf2d0ee17c305335680ebdb2b83ca61999d18021e355d22587d712b79c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-statement-fence-v1-exit.json` | `71e5d3fdf1f363de6bd5c061cb73baa3d6c72042355f9e609769870b4d119d9a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-statement-fence-v1.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-trial-log-v2-exit.json` | `d60f5cd72a78dfe9e8cbd418f941de4f2225f40570ac9de47e8cb20861936634` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/help-trial-log-v2.log` | `ea7bd7e4d64216b46f554a90e02a3d58b4fcbe72766c2f7b316b656b94d19b32` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/initialize-v1.py` | `a767c2f140f08a247648b800ffbfba3ca8c2a87345684e6478250ebf5da66253` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/initialized-before-first-use-v1.json` | `c13e7dfcd34cca86d9176952cda1801ec70da90f175554c26f53424963b8294e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/leaves/pinned-APIs-v1.lean` | `73b0767b9548c192dd0db6bed8c9fc8d3a3e3fdb7b854d0cfd10359c78fab487` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/leaves/pinned-APIs-v2.lean` | `6ac4d725644439b51828ce7fa09e36c2be876d00340ac1901d1ce0ab56714b3b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/leaves/target-types-v1.lean` | `73af18825dabffacfe217a56e6cf6fc9e10de71de653fe4305f31f09141298c3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/list-mathlib-v1-exit.json` | `707bc21d7adbc90882874a62bb00897abb566bc709b23aba4d572f73111a8aba` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/list-mathlib-v1.log` | `884fab88619a3d1adcafe89eecddd2d98f4be5c6fa61262862134dde9e51d225` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/list-papers-v1-exit.json` | `6ad663b9abad7b39afee005f7047f7c1f07f542f7d2de3d9df640ca54f71972f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/list-papers-v1.log` | `9acd333996a893a7b5ccad3e674ece26ef05c8b737e7816b33043b121583a619` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/list-weapons-v1-exit.json` | `25a1510fa0fb0e25858d4d722e3d9c5920d36c6b525ef34e228e0c7342733d5d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/list-weapons-v1.log` | `a6e4b78de1a30fcf5a0ee66b868eb3ac1bfa68d2250c713f61e690ae064f7ef6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/memory-search-1-v1-exit.json` | `70fe05e095a2e8cc1509d3288fdbadfd2c7f2ec12b56afb27ff830e9adef799b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/memory-search-1-v1.log` | `11999fd2b01349cb48f47e2291dcbda3daeae233e4d63611c1bad6c59a86faae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/memory-search-2-v1-exit.json` | `911394b43bd0608ed4e680afface119ecbc6e8d7fda5a7728af2f30338e0a1e8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/memory-search-2-v1.log` | `11999fd2b01349cb48f47e2291dcbda3daeae233e4d63611c1bad6c59a86faae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/memory-search-3-v1-exit.json` | `43444f8d60ed0795b010b6c37e3cc6ff2e6fe530bb3897bfab253ccd95fc94a0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/memory-search-3-v1.log` | `fb8049b248b7439f94305264143646bc9d3304fbf0d68f2d2154740464a7331b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/memory_digest.md` | `330e1c64a3df2fc3a03e23a3eb84539dc2f51936d299df1873222a87383774c7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/pinned-APIs-v1-01-exit.json` | `79b18797d7310d28b7af566e275a0c146cd2e4eee60ac742dbdc068042a33d8d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/pinned-APIs-v1-01.log` | `09794503c1d17904b7d7d1591079ce5314766e2987b55b003b9e6a0d0c4321eb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/pinned-APIs-v2-01-exit.json` | `d27b9a2f976ab0338a4b8b21068be1f6927850d4e3e42996d17988476bd99b43` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/pinned-APIs-v2-01.log` | `a85726308a10854d6bd134bf1a083eafeeaf26f1c15a2db562e721038f2d5856` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/pre-use-fingerprint-distinction-v1.json` | `9ff7268bc91f62cfcc167838fbc962d4697f351e7c3f1625f631bdf77d4449b3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/prepare-contract-review-v1.py` | `b56fa18990fb795043e4a8c4e5c912bf1ef933a1984e2a79dfbc2760867a23ff` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/prepare-readiness-v1-01-exit.json` | `fcc407b1b3e4f291ed22896258fc5d170912d661286026a9e6025174c34a4a05` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/prepare-readiness-v1-01.log` | `8cc4c5a35f479ccc7fd1fd9a65060b0ba657a12230537a4b359a289165844619` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/prepare-readiness-v1.py` | `84236b6a79eda0a1ec668e48fddd1d57d9d8d6e4f6ca711bde2e65c382ea1dcf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/prepare-readiness-v2-01-exit.json` | `a5fe9b4f96e4a5a8cedba007ee3e481aeb6c79f1fe9d935a0cb5e55bc967b558` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/prepare-readiness-v2-01.log` | `a5d4d9cd6de9d54358a63fa8f530b6a8a136750ad94be8bf748adbc206f81fda` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/prepare-readiness-v2.py` | `297c771500bdc3ffc68b80c91fdbd3f1cad10d4c7b335bbf50cc93af42c80252` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/prepare-readiness-v3-01-exit.json` | `f1f68c4ba1d6931dac51a62de213c6fb148cb140e2678cdee89a46ce3f9e2593` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/prepare-readiness-v3-01.log` | `20e023da450a96eee614afeb3be4f7852c3863f6101010218fd0dcf73838a41f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/prepare-readiness-v3.py` | `b0a9b11a7fd30d43a446730a4de755ea6849a7303860533e785306ea954356ea` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/private-workflow-binding-v1.json` | `304661e8d995449f936a7559d91607efea04b4ad42da974d773803dcec01f963` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/project-declarations-1-v1-exit.json` | `e377ea477b02088b18412de5cfb03f209d6764328aa5184e090c1cc083637427` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/project-declarations-1-v1.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/project-declarations-2-v1-exit.json` | `31a99b22f73ea46e6017f7364bd0efb7f5141d7b699a40915c027f36e83df9e3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/project-declarations-2-v1.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/project-declarations-3-v1-exit.json` | `0a40bbed796612bdc1329eca9e2942c66522eeb3621e4ace9affddb7d1565816` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/project-declarations-3-v1.log` | `95c3aca40895e67288bbf5a68248ef9c23cca7fe64dee0b0a48d998726deaee0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/readiness-API-repair-v3.json` | `4565be0b8731a05a38ad321756ae44f30d7f3be5ae9772a7a43fa9737b7e8517` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/readiness-CLI-repair-v2.json` | `b7077aba07a7441a6b970f6ce031c16e36d08a097d010fae09d7063613701009` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/readiness-v1.json` | `cfc37a9a8d54d1bdc5771191a8e0bad81e6afee9c5249d9693771a5cfcb0f33a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/reference-index-manifest-v1.md` | `5c3bcc3e2fecaecfc0f94e96955430b136be3c5026145ab5082bf4cb5ed1481e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/reference-index-scope-v1.json` | `3afe558d198c72e5410158daa7694c86f571df5b881c5dc4e6b8968db223e3bd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/reference-index-v1-01-exit.json` | `23d7128e9a27279dd0ab1d97190773353b5052689b08f8b531b19816a0c09b75` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/reference-index-v1-01.log` | `8dbfdb54606a934150edca19247b6dbce888a09ef37eeac22f440503cb762277` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/retrieval-index-v1.md` | `1677b785bdc69f25c71135fbc04a49f7e1c488a53f08f939919fd1c685ed5a15` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/retrieval-snapshot-v1/bandit_paper_cards.json` | `c99b7b59dbb6341c4a2a0077f2004215a2f6764de84d69cab16bc763408be37e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/retrieval-snapshot-v1/bandit_scenario_cards.json` | `acb19b3b62119a61dcd4b43542e1af63ea2ef95417946dc2ebeff33eed7bddfa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/retrieval-snapshot-v1/bandit_textbook_cards.json` | `5d71dc6709340e7704b0df9f52230c759ecc687f3ae1969c63cbb5e5b91e3dd3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/retrieval-snapshot-v1/lml_bandit_cards.json` | `fa149c38753544dc8a45fc3f12e4b3116de2661798285d0eea6f5960c7bd1959` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/retrieval-snapshot-v1/local_leaf_cards.json` | `c0464b4849a360238e047da824f6ec37b638adc96a241fcb6214eabc29f35508` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/retrieval-snapshot-v1/local_lean_declarations.json` | `f1d8764292ddc9aadc2deff3a8cd93fa73a1141e53e30ad01a642750929cd13a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/retrieval-snapshot-v1/mathlib_bandit_cards.json` | `824faf3db7ceeea04f8dfc39a72f308d5bef6bafe67751f6c1ac66da13fa39ae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/retrieval-snapshot-v1/proof_weapon_cards.json` | `7241cb21c7d5f8beacc394e2b35fda33282d251e6293bf852fe1cc41fcdc3c63` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/run-command.py` | `cb0e98401a104a6f0ad87f684a69a4e776e1de9de7d5b2a7848a394cad0a5db1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/scoped-reference-index-v1.py` | `e8b2fe1a107ba7fc21c52b390c956d82af465293f37017104e5a141305878078` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/snapshots/before-BanditRLProof--OnlineAffineSubgradient.lean.txt` | `fb45e9a58a84770594d4e88a5df04f18a73203406e82f4a48edffd6d4419ff80` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/snapshots/before-BanditRLProof--OnlineLipschitzSubgradient.lean.txt` | `c6891c7b868208d707f05652c17ea5948e1bea272f69a7c1da9303c48769e085` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/snapshots/before-BanditRLProof--OnlineSubgradientAbsolute.lean.txt` | `bf3e8d97f67b78e7ad230b8efd321948f4d7ba1a0e9cde31e8d85c1e9019442b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/snapshots/before-BanditRLProof--OnlineSubgradientDifferentiability.lean.txt` | `4f21c5d7fd0ef27a860390b698072d65527610d55e60c16568e82fa99215c1d3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/snapshots/before-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/snapshots/before-Tests--OnlineLipschitzSubgradientCanary.lean.txt` | `cef3492490f045f99bc0d4e7482075e185744a67f98aa4a8336200a7ec32bf99` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/snapshots/before-Tests.lean.txt` | `cd21ef4e7cea89c7d245eaf4dff14be8baa34f2d336e40d6f6bbb16011678340` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/snapshots/before-docs--contracts--online-book-v1--source-inventory.json.txt` | `a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/snapshots/before-lake-manifest.json.txt` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/snapshots/before-lakefile.lean.txt` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/snapshots/before-lean-toolchain.txt` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/snapshots/before-runs--active_frontier.json.txt` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/snapshots/before-website--content--chapters.json.txt` | `02305d1201f824f4a697eab5204945179892c156638dfbec9204d737df630445` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/snapshots/before-website--content--highlights.json.txt` | `deaebdcc37e3e993e382338c07610fd2bb52f9484fcb18264ec6a10495b0d0cf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/snapshots/before-website--content--readings.json.txt` | `c93e16dc7aede3f47ecbdbbaa9f54c8effbad6fcce6ce82f1d9916fe757068a8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/source-context-obligations-v1.json` | `1883ad6a43b74d5980a0c002dc84901801fed05872ecfb58ae5ccc0ea31ef3e3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/source-contract-packet-v1.md` | `c129af0328efd78b329bb67f5b9875ee16d1a8d2e4330986625049048832dc29` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/source-printed19-pdf31.txt` | `7709a706da7b5320555f5ef19e07fa798affde6a077363425b929c07af0b9a99` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/source-visual-read-v1.json` | `8d82ecf77a559544d7ca0f4dfeb62f07572eb90829c109ce8d15f07dab2ce4dc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/target-types-v1-01-exit.json` | `8ae4de1e2c16606f99669a987e24743a4ca1f61de01870738e7b1e69626a4de0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-convex-nondifferentiability-20261007/target-types-v1-01.log` | `eef32f85f92343a2a03982f4130efb1dd243b22e05290fed65dd6fb1efac9ad3` |
| `Tests.lean` | `cd21ef4e7cea89c7d245eaf4dff14be8baa34f2d336e40d6f6bbb16011678340` |
| `Tests/OnlineLipschitzSubgradientCanary.lean` | `cef3492490f045f99bc0d4e7482075e185744a67f98aa4a8336200a7ec32bf99` |
| `conversion-windows/ONLINE-CONVEX-NONDIFFERENTIABILITY-20261007.md` | `0df2c1f40a9ecdc502f65025c7c8d2912be156975e4f4c9fb1effa74d0a831b9` |
| `docs/contracts/online-book-v1/source-inventory.json` | `a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7` |
| `docs/contracts/online-convex-nondifferentiability-v1/complete-definition.lean` | `9d565ed2a0d9ac8a616fb6cacd41d56d4a81ed59470ea1761128ab77c0c05554` |
| `docs/contracts/online-convex-nondifferentiability-v1/contract.md` | `0df2c1f40a9ecdc502f65025c7c8d2912be156975e4f4c9fb1effa74d0a831b9` |
| `docs/contracts/online-convex-nondifferentiability-v1/headers.json` | `a453fe9c6392056cef9fa6086628b05feb539419286fc5c6b79de45789a0d46b` |
| `docs/contracts/online-convex-nondifferentiability-v1/initial-dependency-DAG.json` | `89fafe735aab0dd82d5450d67432c00969ebc0b0df9aa2db41d84cb29aa3a908` |
| `docs/contracts/online-convex-nondifferentiability-v1/native-statement-fingerprints-v1.json` | `c2191db8fb5a3b7057ee3ff56e747b509febfb6d61bafb9ff9f7871ff70965ea` |
| `docs/contracts/online-convex-nondifferentiability-v1/source-card.json` | `d3b564001e5e27cd06416a530a300930aaadce86dcff97060b59e764907cc210` |
| `docs/contributor-codex-contract.md` | `d7dfa3406def35de292b202f45ff8303b9a550310bd00979be838e5a2348a498` |
| `docs/theorem-publication-protocol.md` | `b1e5ac73cfe0a90742567736b422787c90a51e6b6ff007cc1dc8d598948f687e` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `proof-obligations/ONLINE-CONVEX-NONDIFFERENTIABILITY-20261007.md` | `0df2c1f40a9ecdc502f65025c7c8d2912be156975e4f4c9fb1effa74d0a831b9` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `runs/lifecycle_sessions.jsonl` | `7769eceea45a9b44c31e05df71a4bc5eece83080cc5cbe017c9bda494aa0e7b1` |
| `runs/trials.jsonl` | `adad12f96ed0761538a2cf4e20819e9439cf8cf0bf741573123662d0fa7d797e` |
| `tasks/ONLINE-CONVEX-NONDIFFERENTIABILITY-20261007.md` | `0df2c1f40a9ecdc502f65025c7c8d2912be156975e4f4c9fb1effa74d0a831b9` |
| `tmp/online-lipschitz-source-pdf31-v1.png` | `2bbee9757947abda7e3d0173a6caef36bf3053ad5d4a9c737e213df0da9f2328` |
| `website/content/chapters.json` | `02305d1201f824f4a697eab5204945179892c156638dfbec9204d737df630445` |
| `website/content/highlights.json` | `deaebdcc37e3e993e382338c07610fd2bb52f9484fcb18264ec6a10495b0d0cf` |
| `website/content/readings.json` | `c93e16dc7aede3f47ecbdbbaa9f54c8effbad6fcce6ce82f1d9916fe757068a8` |
| `runs/online-convex-nondifferentiability-20261007/source-contract-inputs-v1.json` | `fc00a927bd0653cec03ac742803b63e44936a9cef1a55b390f4d7d307a7ac6d2` |
