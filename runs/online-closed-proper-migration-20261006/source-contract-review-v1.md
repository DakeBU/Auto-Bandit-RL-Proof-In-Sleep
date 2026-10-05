# Closed/proper migration: distinct source-contract review

Verdict: **accepted-with-explicit-delta**, all three exact theorem contracts and two full definitions. Mathematical repairs: none. This is contract stabilization only; separate body replay/semantic review and integrated reader/package gates remain required.

Actor `/root/source_reviewer`, distinct automated source-review role; requested GPT-6 Astra / medium. No human/external-model review or independent runtime-model attestation. Supplied history is not erased; the20261003 verdict was not used as authority.

## Evidence and independent binding

All126 fixed raw rows independently hashed and matched; fixed manifest additionally bound, yielding127 rows below. Read original module complete proofs/definitions, shared actual extendedIndicator, all three actual @types and frozen headers/scoped contexts, restricted reconstruction, pinned source page, mathlib API locations, compiled scoped graph, complete six-proof canary and current selected reader. Independently extracted all3 headers and matched frozen statements. Ancillary logs/scripts/history are integrity/provenance bindings, not proof acceptance or recertification of unrelated sources.

Original PDF SHA `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`; freshly extracted physical28/printed16. Definition2.16 uses real thresholds, followed by the necessary unnumbered closed/LSC equivalence in Euclidean and more generally Hausdorff spaces. Example2.17 is indicator closedness; Definition2.18 is nowhere-bottom plus finite somewhere; Example2.19 is indicator properness/nonemptiness. These four numbered anchors plus unnumbered consequence are faithfully distinguished from the three library proof declarations.

## Definitions: seven slots

### `BanditRL.OnlineConvex.SourceClosed`

- **model**: Topological E,f:E→EReal.
- **assumptions**: TopologicalSpace only.
- **information**: Static definition.
- **object**: forall real r,IsClosed{x|f x<=coe r}.
- **parameters**: Non-strict finite real cuts, not allEReal cuts by definition.
- **quantifiers**: Every r; every f including bottom/top values and empty domain.
- **guarantee**: Exact source Definition2.16 generalized to arbitrary topology; no domain-closedness or finiteness claim.

### `BanditRL.OnlineConvex.SourceProper`

- **model**: Arbitrary type E,f:E→EReal.
- **assumptions**: No topology or algebra class binder.
- **information**: Static conjunction of global exclusion and existential witness.
- **object**: (forall x,f x!=bottom) and exists x,r real,f x=coe r.
- **parameters**: Finite-real equality, not toReal value or below-top alone.
- **quantifiers**: All x for noBottom; some actual x/r for finiteness.
- **guarantee**: Exact Definition2.18 notion; positive infinity allowed elsewhere; empty E never proper.

## Three target judgments: seven slots

### `BanditRL.OnlineConvex.sourceClosed_iff_lowerSemicontinuous`

Accepted-with-explicit-delta, contract only.

- **model**: Arbitrary topological E; f:E→EReal.
- **assumptions**: Only TopologicalSpace; no T2, properness, noBottom, convexity or nonemptiness.
- **information**: Static deterministic equivalence; no algorithm/time/probability.
- **object**: Actual SourceClosed real-cut predicate and mathlib lower semicontinuity.
- **parameters**: Real finite sublevels; all EReal strict superlevels recovered.
- **quantifiers**: Every E/topology/f, including empty E and either infinite value.
- **guarantee**: Exact iff; stronger domain generality than source Euclidean/Hausdorff sufficient scope, not sequential or epigraph-closure substitute.

### `BanditRL.OnlineConvex.sourceClosed_indicator_iff`

Accepted-with-explicit-delta, contract only.

- **model**: Arbitrary topological E and set V.
- **assumptions**: TopologicalSpace only; no nonempty/convex/closed V premise.
- **information**: Static; independent proof from first terminal.
- **object**: Shared extendedIndicator:0 inside,top outside.
- **parameters**: Finite cut r:V if r>=0,empty otherwise; cut0 recovers V.
- **quantifiers**: Every V, empty/full/nonclosed/nonconvex allowed.
- **guarantee**: SourceClosed indicator iff IsClosed V, not automatic properness.

### `BanditRL.OnlineConvex.sourceProper_indicator_iff`

Accepted-with-explicit-delta, contract only.

- **model**: Actual theorem retains TopologicalSpace E; SourceProper definition itself does not.
- **assumptions**: No premise that V nonempty,closed,convex or bounded.
- **information**: Static finite-witness equivalence; no temporal/probability semantics.
- **object**: Same canonical0/top extendedIndicator and genuine real-valued witness.
- **parameters**: Member supplies real0; top cannot equal finite real.
- **quantifiers**: Every V and ambient type with topology, including empty E.
- **guarantee**: Proper iff V.Nonempty; full-set proper requires nonempty E. Topological binder retained despite mathematical irrelevance.

## Anti-anchored source and edge-case assessment

Arbitrary topology is an explicit valid strengthening of the source scope, not assumption equivalence. For real cuts, complements give open strict real superlevels. At bottom, every value strictly above bottom admits a real number strictly between by EReal.exists_between_coe_real; the union over all real thresholds therefore exactly covers that superlevel. At top it is empty. The pinned lowerSemicontinuous_iff_isOpen_preimage/isClosed_preimage interfaces need no Hausdorff domain. Reverse implication directly gives every real closed sublevel. This covers bottom-valued functions; no improper-function exclusion is smuggled in. It is a topological LSC assertion, not merely a sequential test or a proof of epigraph closedness.

The reused indicator body is exactly if x∈V then0 else top. For every real r, membership and sign cases give V when r>=0 and empty otherwise. Cut0 proves necessity, and these exact cuts prove sufficiency. This proof never calls the closed/LSC equivalence. Properness necessity extracts a genuine embedded real value; assuming the witness is outside V contradicts top=coe r. Sufficiency gives nowhere-bottom by membership cases and a member with value0. Neither a toReal-at-infinity convention nor an assumed desired predicate is used.

SourceProper's actual constant type has no topology parameter. The proper-indicator theorem nevertheless retains TopologicalSpace E in its actual type, and the review preserves that API context rather than silently removing it. On empty E, no finite witness exists, so SourceProper is false; all finite cuts are empty/closed and LSC is vacuous. The full-set indicator is zero everywhere but only proper when E is nonempty. Constant bottom on the real line is closed/LSC and improper; constant top is closed and improper. Nonclosed/nonconvex nonempty V still produces a proper indicator, without being SourceClosed. No convexity, optimization or subgradient existence follows from these claims.

The actual scoped graph contains5 nodes/213 direct type/value edges including definitions. There are no value edges from any of the three terminal proofs to either other terminal. Generated internal simp declarations are not edges between these terminal theorems. The current three-step teaching flow can be an explanatory order but must not be described as a successive proof dependency chain. This is not a full/canary graph export.

Actual canary inspection finds six proofs: bottom closed, bottom LSC, bottom improper, nonconstant real interval indicator closed/proper and empty indicator improper. All are mathematically meaningful, but this contract phase does not freshly accept their bodies. The old #print list omits bottom_closed, so later complete named audit must include it among11 names (3 proofs+2 definitions+6 canaries). No named empty-ambient Lean canary is claimed; that boundary follows from the definitions/theorem quantifiers and is reviewed mathematically here.

## Reader corrections, separate from mathematical repairs

The current reader already correctly states real cuts, either infinity, the zero/top indicator and real-line examples. Repeated generic card text blurs actual binder and independent-proof distinctions; the following are required integration corrections/qualifications:

1. Explicitly contrast source Euclidean and stated Hausdorff sufficient scope with actual arbitrary-topological generalization; do not say source assumes arbitrary topology or that T2 is necessary.

2. Separate per-card assumptions rather than reuse closedness wording for properness: SourceClosed requires topology; SourceProper definition has none; actual sourceProper_indicator_iff still retains TopologicalSpace.

3. Keep finite real cuts and both infinities explicit; bottom strict superlevel is derived by real-density union, top superlevel empty. No noBottom/properness/convexity premise and no closed-effective-domain/epigraph substitute.

4. Use the same0/top extendedIndicator; describe its direct cut calculation and finite witness separately. The three terminal proofs have no mutual theorem-to-theorem value dependencies; teaching order is not a proof dependency chain.

5. Explain empty ambient/empty/full-set boundaries: every function on empty E is SourceClosed and none is SourceProper; full indicator is proper iff ambient nonempty. Retain real-line scope for bottom-improper examples.

6. Distinguish source definitions, two numbered indicator examples and required unnumbered semicontinuity equivalence from three new source results; retain3 proofs/2 definitions/0new nodes and incomplete Chapter2/book boundary.

7. Keep six actual canaries and require all11 named axiom checks, including bottom_closed omitted by the old print list. Build/graph readiness is not final integrated acceptance; update current candidate status only with actual later gates.

No mathematical header or body repair is requested. Fresh distinct body review, complete axiom/native guards, explicit shared root/Tests/full harness, corrected reader/site/shared registry/contributor, immutable acceptance and delivery remain pending. Three retained proofs/two definitions/zero new mathematical nodes cannot count as three new printed results. Only after applicable acceptance may this single OnlineClosedProper legacy path move10→9. Chapter1 migrations, Chapter2 mandatory totalnull/incomplete and whole-book active Goal remain outside scope. No main/merge/live or external review claim.

## Exact raw inventory

| Path | Raw SHA-256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean` | `bf69a9ed4bc39134bbefac1a43b187e2f1e66fd43f352d0810ab89474f054922` |
| `.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean` | `b9f72ca970c076ce6d466a3f0efd05306c4f9dc0df6e7eb52329e66414410065` |
| `BanditRLProof.lean` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `BanditRLProof/OnlineConvexExtended.lean` | `bd30bb95a46ccdc3f6d25f808c175af5fee71d075c2b46ffcf6508f15f1ed66a` |
| `Tests.lean` | `1c60f84f3e4d6d778ac8374b46e47b27559d802986459533517034c97a30f048` |
| `Tests/OnlineClosedProperCanary.lean` | `6119ddd60320e8c61cf5aa820b495624499921eb9969598692778d0e19d65ec5` |
| `conversion-windows/ONLINE-CLOSED-PROPER-MIGRATION-20261006.md` | `345f55a7d75aa2c59c7e5ce1205c234dc27358952c3da4db97027a34c43c2191` |
| `docs/contracts/online-closed-proper-migration-v1/dependency-DAG-v1.json` | `3659660c05afa78390cd8ea3fc7e8158e5f52d2471980a1d976bba15a5f136dd` |
| `docs/contracts/online-closed-proper-migration-v1/headers.json` | `ecc8b8932b44fca5a1ba8864823b3efa92987ba9e5d716b0e94d1d3d28839fc2` |
| `docs/contracts/online-closed-proper-migration-v1/scoped-contexts.json` | `79fab5a659166c38133c8c3c9dd818af16a14995199df8f241f3131b145dbf7b` |
| `docs/contracts/online-closed-proper-migration-v1/source-card.json` | `d34ab01cb96ead6bcef78188908af12bd27ace1c825b6ba8e1fa918adf1b4db4` |
| `docs/contracts/online-closed-proper-migration-v1/source-intent.md` | `3da680aaec30807ecabfdfa2ac6e23d16ded2d8f230d75fd70777790b37c89aa` |
| `docs/contracts/online-closed-proper-public-v1/contract.md` | `80c297fea4ca8f5009267b121d2031cadb019a5100061718627630e703fa4738` |
| `docs/contracts/online-closed-proper-public-v1/integration.json` | `3871e3c5e935deddf9994d340ae0113ea5cd3af5790f1ea02482046364c7658b` |
| `docs/contracts/online-closed-proper-public-v1/sourceClosed_iff_lowerSemicontinuous.json` | `74fe7a5a257779325dce86592e3464028955fdf54b666f0a9535e1afe398c2eb` |
| `docs/contracts/online-closed-proper-public-v1/sourceClosed_indicator_iff.json` | `250242beeb4401b063a0ba0b951bdb7a2281fad8c27a2c4518b42fb6a5d6ee68` |
| `docs/contracts/online-closed-proper-public-v1/sourceProper_indicator_iff.json` | `7b6192e9974f34aa944325abe5b68d7dbbcf395769971be23d462357c1628ad6` |
| `docs/contracts/online-closed-proper-v1/context.json` | `2aab5889ceb472515bd4d6ce040c6bf0bd2c38fd87532295a9fca1cd89ab574f` |
| `docs/contracts/online-closed-proper-v1/contract.md` | `2abe4da7049d5582af0f2dd341987fef8f5798b4327b8cc7dc78161299c198f8` |
| `docs/contracts/online-closed-proper-v1/headers.json` | `189dd5c9b05fcc16f1411191866f8d2fc895f57c987b3732e192c2a5844aa3f6` |
| `docs/contracts/online-closed-proper-v1/sourceClosed_iff_lowerSemicontinuous.json` | `0818c0eb91546b4edd0be2825830295aa955fe70533052d84cbd3287ce17c95f` |
| `docs/contracts/online-closed-proper-v1/sourceClosed_indicator_iff.json` | `7448b28090f52ed24c2d86ca249fecdfb12c4b4fb2a063940ea03a19ad7bd03c` |
| `docs/contracts/online-closed-proper-v1/sourceProper_indicator_iff.json` | `72aa764c3bc05b08cd305d21aaf8c19e3597aa4a58d21d27727c59306ddf28b7` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `proof-obligations/ONLINE-CLOSED-PROPER-MIGRATION-20261006.md` | `9a35ccb475ed43b3e88620b156a6504942f2de08f2a9dc0e6e16c0aaaf7f9fce` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `runs/online-closed-proper-20261003/acceptance-evidence.json` | `1c2dfe5af0d4756c3b7488f5623c5d60215f7f2587a9bd7912821cc0728cc5d6` |
| `runs/online-closed-proper-20261003/independent-source-review.md` | `b958a202628aae0adab58685307cee2f5265b641b285d2cae884753030a5eff5` |
| `runs/online-closed-proper-20261003/roundtrip-bindings.json` | `79367d5d184d30ff302f9992a3f0de094db79be32d493d6ba7f63edde592eb32` |
| `runs/online-closed-proper-migration-20261006/.gitattributes` | `997ec76df2f8fcfad33bd0ce2ca95045ac236364b7f16f9a6d28471e8b7dee9c` |
| `runs/online-closed-proper-migration-20261006/00_context.md` | `ebcd08734942c7f3c5ec5bef4317167e116466f813aa6eda72c0838163bc7656` |
| `runs/online-closed-proper-migration-20261006/10_upper_director-v1.md` | `0fb2e3f137963295fc7c9b273018af52a8d2daa3099c17144f1acd7d1eca5906` |
| `runs/online-closed-proper-migration-20261006/20_architect-v1.md` | `3aaa93b35b5ad78b6b68fa2309c73d1c790654c662e51d763f1ec7cb82cb52e6` |
| `runs/online-closed-proper-migration-20261006/CLI-help-v1-01-exit.json` | `63afdf8268c044e64127cb481a03ba3fffe9cfd0e064c7d891298f536ab5f4ff` |
| `runs/online-closed-proper-migration-20261006/CLI-help-v1-01.log` | `daacf23e36eec4898dce3b3de02a07b71fb0f80f08e33e8dfe00722e7572970c` |
| `runs/online-closed-proper-migration-20261006/actual-types-readable-v2-01-exit.json` | `65cb75041de952a641d36847d759afe3b1e4d566d370ceba373941d6f9136e13` |
| `runs/online-closed-proper-migration-20261006/actual-types-readable-v2-01.log` | `2e8855acfbf2a2b8519f9866d248e0ae640324880c036d549bb6362cd6ffb562` |
| `runs/online-closed-proper-migration-20261006/actual-types-v1-01-exit.json` | `5c91bffed1ca4c695fb69ead8b8dc1d20089d89413579bffdc857191f44aca59` |
| `runs/online-closed-proper-migration-20261006/actual-types-v1-01.log` | `cf32d7622052c3eae65e0af5c72ced91a1010d60c0214ccac2cb2ca22a65da99` |
| `runs/online-closed-proper-migration-20261006/blind-packet-v1.md` | `57b4976077e542841f6564a229b1072c7a0d8dd1953ad019803b1e6f6189bf3b` |
| `runs/online-closed-proper-migration-20261006/blind-receipt-v1.json` | `d5750bbf941f120c99f4bf238fe5bd5b2d8f2fce7242e32f22c5946c7a09b275` |
| `runs/online-closed-proper-migration-20261006/blind-reconstruction-v1.md` | `7d84be90cf522cc85f1f7d94927a4bf6e062b5e0ff35807edd4a97c6b2f48f32` |
| `runs/online-closed-proper-migration-20261006/bootstrap-before-use-v1.json` | `678590c139e6c9ae270b3f96a8c495a6243a3d4c673426212d423659bb8dcc0d` |
| `runs/online-closed-proper-migration-20261006/bootstrap-generated-before-use-v1.json` | `8a322dc652a793feaeb1675c2921420aef65485ce134bcba335fa37da6776713` |
| `runs/online-closed-proper-migration-20261006/bootstrap-v1.py` | `f520b0374f21d29024b1cee1cf0e5b285e0e2d38211371987eff84e60465629b` |
| `runs/online-closed-proper-migration-20261006/compiled-retained-graph-v1.json` | `89b49faa610e4905d3f53c9c1b599aaca6d57e4aa2a549287e6e0ce2c6462d55` |
| `runs/online-closed-proper-migration-20261006/compiled-scoped-graph-v1-01-exit.json` | `941ba1cfa6b3807aa132384d7e7d110df9daa6eac6559a16e05e8be23b924307` |
| `runs/online-closed-proper-migration-20261006/compiled-scoped-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-closed-proper-migration-20261006/draft-fence-sourceClosed_iff_lowerSemicontinuous-v1-exit.json` | `af75392d018877148e47a7f0585f81bca0fbb5fa830880a1dc1230085e24db38` |
| `runs/online-closed-proper-migration-20261006/draft-fence-sourceClosed_iff_lowerSemicontinuous-v1.log` | `46d4e90d1df389c3db186b70ce8e33d9582aee6a85e6a3a9045da8b7ca5c00bc` |
| `runs/online-closed-proper-migration-20261006/draft-fence-sourceClosed_indicator_iff-v1-exit.json` | `100b396b915ff119245287a6b1d3bdfaf1bdee76fe27ee5d13ea22d8d5566594` |
| `runs/online-closed-proper-migration-20261006/draft-fence-sourceClosed_indicator_iff-v1.log` | `aa7b4ec7b6926b79d85183ccaa5d6980ec14fcdbf12e85e2a747a28ba9814156` |
| `runs/online-closed-proper-migration-20261006/draft-fence-sourceProper_indicator_iff-v1-exit.json` | `58d88df20867279e3f9bb8c27617171070f215ad165192979067fcd12ec67222` |
| `runs/online-closed-proper-migration-20261006/draft-fence-sourceProper_indicator_iff-v1.log` | `6a85f38a7ce3e731f393706030c2b492e633b639b2fdfd2dc51cdeb064208793` |
| `runs/online-closed-proper-migration-20261006/draft-freeze-v1.json` | `864a7e5413398fdad40c64cd8a119ebd9a1048258059c8bf9334d8045c38b58f` |
| `runs/online-closed-proper-migration-20261006/draft-generated-before-use-v1.json` | `d3e9aae825ea0ef02268b731c7f5c4b90e848fd994a6cd0c3a2c57db934d5d3f` |
| `runs/online-closed-proper-migration-20261006/draft-helper-before-use-v1.json` | `48c4048c8ffc2d329e0375f01ccb1190b78a6e62b88260f224088725ddc388de` |
| `runs/online-closed-proper-migration-20261006/draft-lifecycle-v1-exit.json` | `8a494fe842f405f3aa5d7fce1378e09cc51c34b5eae7b4ac906205aeed460a55` |
| `runs/online-closed-proper-migration-20261006/draft-lifecycle-v1.log` | `0a7e1162734df245505c6432f1f8b8bcaaa1098e2440121cc40c5d3a89598587` |
| `runs/online-closed-proper-migration-20261006/fence-help-v1-01-exit.json` | `87ef2918c07c9c0e9ab713d361a18e369bf45fec3cda5934387e1fda5ade39f0` |
| `runs/online-closed-proper-migration-20261006/fence-help-v1-01.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |
| `runs/online-closed-proper-migration-20261006/historical-raw-supersession-v1.json` | `b02018870ba835a957a8fbf58e10345d4f6eecf70c29e8fac30f3ec62fa8a756` |
| `runs/online-closed-proper-migration-20261006/leaves/actual-types-readable-v2.lean` | `4f7f8b0b2c500992f7a0feaed71b8d7ae270250b2ee5e68434d7142aea833718` |
| `runs/online-closed-proper-migration-20261006/leaves/actual-types-v1.lean` | `df7d90e8eff3c02c9bda82f1c32caa486ed14b3d886cc83113b46b0eb183bec5` |
| `runs/online-closed-proper-migration-20261006/leaves/export-scoped-dependencies-v1.lean` | `131840e5c540892b1d8c8128651b0e1ae620e04b9c5aeb3c8ca57230f569e46f` |
| `runs/online-closed-proper-migration-20261006/leaves/pre-integration-BanditRLProof--OnlineClosedProper.lean.txt` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `runs/online-closed-proper-migration-20261006/leaves/pre-integration-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-closed-proper-migration-20261006/leaves/pre-integration-MANIFEST.md.txt` | `9835fdca22cc28b7eb085244c1ec7dfcaf90c4e1ea5f679085e311625ddc49ec` |
| `runs/online-closed-proper-migration-20261006/leaves/pre-integration-Tests.lean.txt` | `1c60f84f3e4d6d778ac8374b46e47b27559d802986459533517034c97a30f048` |
| `runs/online-closed-proper-migration-20261006/leaves/pre-integration-runs--lifecycle_sessions.jsonl.txt` | `3f41252880d4d8eec88de0444723cd0bd9f262ca8a33c7057b78382325143839` |
| `runs/online-closed-proper-migration-20261006/leaves/pre-integration-runs--trials.jsonl.txt` | `ec0f7f2c31eb042de64f2dc7731fbff3fd18c8dbc8919985481cae20e53d5810` |
| `runs/online-closed-proper-migration-20261006/leaves/pre-integration-website--content--chapters.json.txt` | `d9e122eaf3a2cd72cca56083c8c77aa6dbb78d9d4ff9c48fb67a217098150c7c` |
| `runs/online-closed-proper-migration-20261006/leaves/pre-integration-website--content--highlights.json.txt` | `edbd57312b77313e0a854344690741fb5b7c6f4e8fc555358a97d680db8c42d7` |
| `runs/online-closed-proper-migration-20261006/leaves/pre-integration-website--content--readings.json.txt` | `2844ac6d78e6eb72ef5619661a88beee6e6d16f28007260b63072f91f35e706c` |
| `runs/online-closed-proper-migration-20261006/lifecycle-help-v1-01-exit.json` | `f5c4e842ecc8939b3c89570aa39942043afa1141cb95882b50b51b8265f96129` |
| `runs/online-closed-proper-migration-20261006/lifecycle-help-v1-01.log` | `b1e8b438a9b725793b9888d206e98a971ace3df200ec90ed9cb63eab26b28507` |
| `runs/online-closed-proper-migration-20261006/list-mathlib-v1-01-exit.json` | `37fa2014eae0cde5933fb134aaaf8a4eee6945e4439de9d2cd91a912b7b0d159` |
| `runs/online-closed-proper-migration-20261006/list-mathlib-v1-01.log` | `884fab88619a3d1adcafe89eecddd2d98f4be5c6fa61262862134dde9e51d225` |
| `runs/online-closed-proper-migration-20261006/list-papers-v1-01-exit.json` | `4867ad0274521098a4e1c6d1b2e8575289f4560654a94d08a020ca0c2100d45d` |
| `runs/online-closed-proper-migration-20261006/list-papers-v1-01.log` | `9acd333996a893a7b5ccad3e674ece26ef05c8b737e7816b33043b121583a619` |
| `runs/online-closed-proper-migration-20261006/list-weapons-v1-01-exit.json` | `0a95101c591fd0ba7f9270a7494d1051aa1ef8684fa1a5a76fb88cc2d4b50ff7` |
| `runs/online-closed-proper-migration-20261006/list-weapons-v1-01.log` | `a6e4b78de1a30fcf5a0ee66b868eb3ac1bfa68d2250c713f61e690ae064f7ef6` |
| `runs/online-closed-proper-migration-20261006/local-lookup-closed-v1-01-exit.json` | `67afdfac1d66cc30a31ecf6624bc09fd117b4dd3b594115c8e0e98437d98252f` |
| `runs/online-closed-proper-migration-20261006/local-lookup-closed-v1-01.log` | `e03281eaf16ddb3b7734381f87b5301395ec061c2fe56acd1c5b1ff3e98c739e` |
| `runs/online-closed-proper-migration-20261006/local-lookup-proper-v1-01-exit.json` | `05deadc8ed9c552d6b2b63f88d9860b510babc00451445200ff2742da6380a72` |
| `runs/online-closed-proper-migration-20261006/local-lookup-proper-v1-01.log` | `9497dde7e88dd81e82f53e64bec15fabe9cc21f2ef909eb7ec4d97247760edbb` |
| `runs/online-closed-proper-migration-20261006/local-retrieval-help-v1-01-exit.json` | `ee08b51c03d3d808f6679d5c60669b5d22fd6ea40a1fd7896e720288bc500d00` |
| `runs/online-closed-proper-migration-20261006/local-retrieval-help-v1-01.log` | `258218f16a12b1a530d85ae83e6c2449237af8a0a1153bb35de40245d665b131` |
| `runs/online-closed-proper-migration-20261006/native-draft-fences/sourceClosed_iff_lowerSemicontinuous.json` | `46d4e90d1df389c3db186b70ce8e33d9582aee6a85e6a3a9045da8b7ca5c00bc` |
| `runs/online-closed-proper-migration-20261006/native-draft-fences/sourceClosed_indicator_iff.json` | `aa7b4ec7b6926b79d85183ccaa5d6980ec14fcdbf12e85e2a747a28ba9814156` |
| `runs/online-closed-proper-migration-20261006/native-draft-fences/sourceProper_indicator_iff.json` | `6a85f38a7ce3e731f393706030c2b492e633b639b2fdfd2dc51cdeb064208793` |
| `runs/online-closed-proper-migration-20261006/original-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-closed-proper-migration-20261006/original-OnlineClosedProper.lean.txt` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `runs/online-closed-proper-migration-20261006/original-OnlineClosedProperCanary.lean.txt` | `6119ddd60320e8c61cf5aa820b495624499921eb9969598692778d0e19d65ec5` |
| `runs/online-closed-proper-migration-20261006/original-Tests.lean.txt` | `1c60f84f3e4d6d778ac8374b46e47b27559d802986459533517034c97a30f048` |
| `runs/online-closed-proper-migration-20261006/prepare-draft-v1-01-exit.json` | `f756fd6e561cc34ca0f65fda2551adbeaaeb1572b5e66c0fbc790d04096686d8` |
| `runs/online-closed-proper-migration-20261006/prepare-draft-v1-01.log` | `bb01ff98b0fc8f72dd2bdbab12f2b7a03f5537e7e59e95ae64a58ede3f4e5b21` |
| `runs/online-closed-proper-migration-20261006/prepare-draft-v1.py` | `0977012b4a46b83041ad9a257dcb5f87592c587f8176dc835dca48db60f329ea` |
| `runs/online-closed-proper-migration-20261006/prepare-source-review-v1.py` | `c790c6b2531be4aeaaad93f95d331792141adb0278d007232060bb2f0ab02e17` |
| `runs/online-closed-proper-migration-20261006/proof-obligations-v1.json` | `5c74db7fa4c40f08a2317ed35ce2b626dfe4a52a7438bedc5da5ad27ecccd309` |
| `runs/online-closed-proper-migration-20261006/public-named-declarations-v1.json` | `9e163ad405c36ee879ebdd12d391a1835d9f57be3485b816a0992290945aaf32` |
| `runs/online-closed-proper-migration-20261006/read-only-command-errors-v1.md` | `44d7ea26f96e147754f57722d33bd05333c1aff96b4359ebbf0570786f8feab7` |
| `runs/online-closed-proper-migration-20261006/ready-dependencies-v1.json` | `8b0ae979210ce637e4fc0b6caa192034996bf3188435c7137680e37d3d730e7d` |
| `runs/online-closed-proper-migration-20261006/retained-module-v1-01-exit.json` | `b0ead2ee7efd0c12b27210137a364d3478d648fd1ba9e9bf7f536f2c3240c806` |
| `runs/online-closed-proper-migration-20261006/retained-module-v1-01.log` | `0dfdf67ebb5a2e70eaa9ccc868bcd9dabcf2532b2deafb3630dda3ab999f143d` |
| `runs/online-closed-proper-migration-20261006/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `runs/online-closed-proper-migration-20261006/search-memory-v1-01-exit.json` | `6e9941ddac4b9672c1350c6b8371e67d7ae48c19df864cfa439330482a8e3391` |
| `runs/online-closed-proper-migration-20261006/search-memory-v1-01.log` | `a9a63b9d3278701ae8862f0b03d627ffe4bd89f918cba0fddc8fd11acf375620` |
| `runs/online-closed-proper-migration-20261006/source-extraction-selection-error-v1.md` | `bb103ae4370dea0f636169af6c95a1aad5e3c0a6dc35acbde72f131c7bbdab2f` |
| `runs/online-closed-proper-migration-20261006/source-printed16-pdf28.txt` | `fc5f1c36f2124f1a4c04c2b56159420778760dc35f58924907058720a09214f5` |
| `runs/online-closed-proper-migration-20261006/source-review-helper-before-use-v1.json` | `027cdf0b2055dcfe677e02c3e5365b0febe94439ca1b08cc2abc4b0994ada48a` |
| `runs/online-closed-proper-migration-20261006/source-review-packet-v1.md` | `13da5bc152dee7d4b307bc62ebde8eb95a954de73ccabb683b811050ef2de562` |
| `runs/online-closed-proper-migration-20261006/workspace-audit-v1.json` | `1f237e155795d3c3c0436d9a60a3a66bf8ec279a9d5fe2231e965ee9810192bd` |
| `runs/online-huber-migration-20261006/accepted-decision-v1.json` | `2869fce031fe54ceb41df49770f02905b053f4abd845c56268e8aaddcad2020e` |
| `runs/online-huber-migration-20261006/delivery-v1.md` | `4c97e0e70fae23a79f65c670fac432387bbaaacfa05ba98155828885825b69d4` |
| `runs/online-huber-migration-20261006/native-acceptance-overlay-v1.json` | `7118e35449bd4f9f3569390bb3c8dde6a2fd046631c53e44fe5bb628bdc11246` |
| `tasks/ONLINE-CLOSED-PROPER-MIGRATION-20261006.md` | `34ccf3f454b9ef9839e5d4eb0d9c5c2a080c192f33f8ae293748044fa914b4c0` |
| `tmp/online-closed-proper-migration-compiled-retained-graph-v1.json` | `89b49faa610e4905d3f53c9c1b599aaca6d57e4aa2a549287e6e0ce2c6462d55` |
| `website/content/chapters.json` | `d9e122eaf3a2cd72cca56083c8c77aa6dbb78d9d4ff9c48fb67a217098150c7c` |
| `website/content/highlights.json` | `edbd57312b77313e0a854344690741fb5b7c6f4e8fc555358a97d680db8c42d7` |
| `website/content/readings.json` | `2844ac6d78e6eb72ef5619661a88beee6e6d16f28007260b63072f91f35e706c` |
| `runs/online-closed-proper-migration-20261006/contract-source-inputs-v1.json` | `f880287fe8aae0c8c787a3a9d0b9d9fbb721793ff5c5e8ba0cd966f12259e4c0` |
