# Interior subgradients: distinct source contract review

**Verdict: accepted-with-explicit-delta.** No mathematical repair identified. Two relative-interior proofs remain planned/uncompiled; this is not body or package acceptance.

Actor `/root/source_reviewer`, requested GPT-6 Astra / medium, distinct automated source reviewer; no human/external-model/runtime attestation. All170 fixedv2 rows independently raw-rehashed with no mismatch; manifest additionally bound. Prior historical verdicts are not source authority.

Original Orabona v10 printed17/PDF29 re-extracted; PDF SHA `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. The main unnumbered assertion states proper convex subdifferentiability on ambient domain interior. Footnote1 explicitly strengthens this to relative interior. Both are mandatory here, zero numbered anchors.

## Three target seven-slot comparisons

### BanditRL.OnlineConvex.subgradient_exists_of_domain_interior

accepted-with-explicit-delta; retained; contract only

- **objects_spaces**: Finite-dimensional real inner-product F, EReal f; source Euclidean representation.
- **quantifiers**: For every proper convex f and specified x in AMBIENT interior, ∃g ∀ambient y global support.
- **assumptions**: SourceProper and IsConvexExtended and ambient interior membership; completeness derives from finiteD, not new binder.
- **conclusion**: Nonempty full SourceSubdifferential at x. Relative-interior footnote is not covered by this premise.
- **constants**: Exact coefficient1, no error/norm bound/nonzero slope requirement.
- **information**: Static deterministic existence, no measurable/computable/causal selection or probabilistic statement.
- **boundaries**: No closedness/lsc/boundedness/differentiability/full-dimensional premise. Normed carrier has zero and is nonempty; dimension0 permitted. No general boundary-point or infinite-dimensional claim.
### BanditRL.OnlineConvex.affine_support_of_relative_domain_interior

accepted-with-explicit-delta; planned-uncompiled; contract only

- **objects_spaces**: Finite-dimensional real NORMED E, no inner-product binder; continuous linear functional and real intercept.
- **quantifiers**: For each specified x in intrinsicInterior(domain), ∃a,b with CONTACT AT THAT x and ∀ambient y bound.
- **assumptions**: Global nowhere-bottom, convex real-height epigraph, specified ri point; no separately supplied properness witness. ri⊆domain plus noBottom produces properness.
- **conclusion**: ↑(a x+b)=f x AND ∀y,↑(a y+b)≤f y. Pure minorant or contact at another chosen point is insufficient.
- **constants**: Exact coefficient1, no error/norm bound/nonzero slope requirement.
- **information**: Static deterministic existence, no measurable/computable/causal selection or probabilistic statement.
- **boundaries**: No closedness/lsc/boundedness/differentiability/full-dimensional premise. Normed carrier has zero and is nonempty; dimension0 permitted. No general boundary-point or infinite-dimensional claim.
### BanditRL.OnlineConvex.subgradient_exists_of_relative_domain_interior

accepted-with-explicit-delta; planned-uncompiled; contract only

- **objects_spaces**: Finite-dimensional real inner-product F and proper extended-real convex f.
- **quantifiers**: For every specified x in intrinsicInterior(domain), ∃g fixed before ∀ambient y, including outside affine span/domain.
- **assumptions**: SourceProper, IsConvexExtended, actual intrinsicInterior; no ambient interior/closedness or supplied support oracle.
- **conclusion**: Nonempty global SourceSubdifferential at prescribed x: the mandatory stronger relative-interior footnote.
- **constants**: Exact coefficient1, no error/norm bound/nonzero slope requirement.
- **information**: Static deterministic existence, no measurable/computable/causal selection or probabilistic statement.
- **boundaries**: No closedness/lsc/boundedness/differentiability/full-dimensional premise. Normed carrier has zero and is nonempty; dimension0 permitted. No general boundary-point or infinite-dimensional claim.

## Definitions, hypotheses and producer route

Full shared SourceProper=noBottom+finite witness; effectiveDomain=f<top; IsConvexExtended=convex real-height epigraph; SourceSubdifferential={g|∀y,f x+↑inner(g,y-x)≤f y}. Properness excludes generic bottom/top support degeneracies. intrinsicInterior is image of interior in affineSpan subtype, independently inspected in pinned Mathlib.

intrinsicInterior_subset yields f(x)<top; hbot x excludes bottom. EReal.coe_toReal then supplies finite witness at x, hence SourceProper. Missing explicit finite-witness premise is derivable, not an unresolved assumption.

The helper is a library refinement/generalization to finite-dimensional normed spaces, not a separately printed source result. Describing its explicit premises as weaker than properness is acceptable only with the derivation above: given the specified ri point, properness is already implied. No broader improper-function claim is licensed.

Existing donor chooses arbitrary ri point and drops contact. Planned proof must instead retain supplied x as affine origin, use affine_support_of_domain_interior at0, extend linear map, adjust b-Gp and transport equality to original x. Riesz follows only after this exact contact producer.

The retained ambient body indeed takes a contacting functional, applies toDual.symm and uses map_sub/contact to prove the inequality for every y. The donor convex_affine_minorant proves only a lower bound and cannot establish prescribed contact on its own. Pinned API probe shows complete_of_proper synthesizes completeness and toDual requires it; finite-dimensional real normed instances provide it rather than adding a source hypothesis. intrinsicInterior definition and membership API match the affine-span topology exactly. No mathematical contradiction was found in the planned signatures.

Adequate discriminating plan, not evidence yet: nonclosed plane ray with differing finite values tests nonconstant lower-dimensional contact, normed product sufficient; singleton real indicator tests relative support despite empty ambient interior. Must actually derive ri/proper/convex/empty-interior facts, not assume them.

## Reader corrections and evidence limits

1. Add mandatory relative-interior footnote explicitly beside ambient assertion; neither is a numbered theorem. Keep2new targets planned until actual bodies/gates; do not present3targets as3printed results.
2. Distinguish ambient interior from mathlib intrinsicInterior in affineSpan, not closure/full-dimensional substitution. Lower-dimensional domains can have empty ambient interior but nonempty ri.
3. Display affine helper exact prescribed-x contact AND global bound, normed versus vector-inner classes; pure convex_affine_minorant is only method donor, not adequate endpoint.
4. Explain helper noBottom plus ri point implies finite witness/properness; nominally fewer explicit hypotheses do not enlarge admissible functions at a fixed ri point. Preserve source-facing properness.
5. Explain finite-dimensional-derived completeness for Riesz, zero-dimensional/nonempty-carrier cases, no supplied CompleteSpace/closedness/lsc/loss differentiability.
6. State global all-ambient queries and proper specialization of wider generic SourceSubdifferential; outside-domain top handled, no bottom/toReal shortcut.
7. Show actual dependency route: prescribed-point affine-span restriction → accepted ambient contact helper → linear extension/intercept → contact at original x → Riesz vector; not unproved oracle or compiled dependency edge for new targets.
8. After implementation, include real nonclosed lower-dimensional nonconstant contact canary and singleton relative vector canary with proved empty ambient interior; preserve old interval canary. Freeze exactcanary headers before bodies.
9. Keep actual scopes/gate counts separate: retained2node258reference readiness is not new proof/canary/full export; full integrated gates and Chapter2/wholeGoal boundaries remain.

Current reader covers the old ambient route only and must not be accepted for the mandatory footnote until corrected after implementation. The restricted current neutral reconstruction accurately preserves global support, prescribed contact, separate normed/inner classes and planned/retained status; it is not proof/source acceptance. Retained2node258reference graph and pinned probes are readiness only. Planned TXT empty-by parser slots are not compiled theorem bodies. Original preparer failure on a guessed historical path and earlier CLI option error remain history; v2 correct retrieval does not constitute mathematical progress.

No header weakening is needed or authorized. Future acceptance requires actual new producers, canaries, integrated gates and final reader review. Zero-dimensional carrier allowed, empty carrier impossible through zero; empty effective domain contradicts properness or ri membership. No closedness, lsc, boundedness, full dimension or nonzero output slope added. Chapter2/wholeGoal remain incomplete/ACTIVE; no merge/live/retirement claim.

## Raw inventory

All fixed files opened for raw validation; mathematical inspection targets source, full declarations/definitions, scoped contexts, neutral reconstruction, retained bodies/donor, pinned APIs and selected reader. Historical/admin files provide provenance, not current semantic acceptance.

| Path | Raw SHA256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `.lake/packages/mathlib/Mathlib/Analysis/Convex/Intrinsic.lean` | `18a4430e0da13f6a6df60fc55c7461d1fbd0e47b3733bbba955444b643a24046` |
| `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean` | `6e25613a0a200590fe3510cb618efd1addac49928d5b6361c2be2cf3951908c3` |
| `.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean` | `924331d5d45705496da51396e437b8b2d99f0c8672436240bd42506368aa81f3` |
| `.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean` | `bf69a9ed4bc39134bbefac1a43b187e2f1e66fd43f352d0810ab89474f054922` |
| `.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean` | `adcc636be22ad37643e008cb82b513b0b53eaadc2b5c4b7fcc38f1c74bf1dfdb` |
| `BanditRLProof.lean` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `BanditRLProof/OnlineClosedProper.lean` | `c66f00c33b45fb8a0e11583eeadf506e176c16166ce2af02f41f0674507cebe7` |
| `BanditRLProof/OnlineConvexExtended.lean` | `bd30bb95a46ccdc3f6d25f808c175af5fee71d075c2b46ffcf6508f15f1ed66a` |
| `BanditRLProof/OnlineConvexMinorant.lean` | `8ca81ca0b79248a15df47556057175fd6b4712d33a082508c543bd7760a15742` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `BanditRLProof/OnlineSubgradientInterior.lean` | `514491262bfef44d495b7173fc4a2de119dd4f17b054fde41ae1b09ff2701e85` |
| `Tests.lean` | `1c60f84f3e4d6d778ac8374b46e47b27559d802986459533517034c97a30f048` |
| `Tests/OnlineConvexBarycenterCanary.lean` | `55c0367f7302b5a6963aca4420f1d91cf4ae9cea97d270097a1506f3e7188ee5` |
| `Tests/OnlineConvexMinorantCanary.lean` | `6155e01119b5fe11ccce85dce9954302fb6868a05579c44a4df13b3a571d0bee` |
| `Tests/OnlineSubgradientInteriorCanary.lean` | `6f80f819bb7a6f9632b80596af7eeb2b84808929fef4dd41195a046ef826b085` |
| `conversion-windows/ONLINE-SUBGRADIENT-INTERIOR-MIGRATION-20261006.md` | `492707056b21ff952763bcfb920487cc9cf347e4203d719928f52c96cff5ebfd` |
| `docs/contracts/online-minorant-migration-v1/affine_minorant_of_domain_interior-header.txt` | `e16cefb3e30853d0df6ec288ce03a4758d780c6a9a2f8a86706ac69c22b5572e` |
| `docs/contracts/online-minorant-migration-v1/affine_minorant_of_domain_interior.json` | `dd9b877532e0a48c63b85c836cb6e44335e7da0825aeddf229b41cc5101ea388` |
| `docs/contracts/online-minorant-migration-v1/affine_support_of_domain_interior-header.txt` | `fda28878ba9fa50df397d14a5e84a77633b65ff0eae910d7400d9117ffa14411` |
| `docs/contracts/online-minorant-migration-v1/affine_support_of_domain_interior.json` | `5db5c71696ae56c4503ad5676f7e508d5b312920624d6b582c05c0a6937a8cc3` |
| `docs/contracts/online-minorant-migration-v1/affine_support_of_finite_neighborhood-header.txt` | `ee5209701c49ae62f99ee486fd7770167a64f2de81877feb1c03edbaff66bbb2` |
| `docs/contracts/online-minorant-migration-v1/affine_support_of_finite_neighborhood.json` | `4f824209315e12bc1bb44e352e92a4fccce4ddfb573dbdfc9235333cc862a025` |
| `docs/contracts/online-minorant-migration-v1/convex_affine_minorant-header.txt` | `d15bc60b7b96d4ecd80fe67518dd4fabfdda6aace2dcb240b0dfb11af38a6b7f` |
| `docs/contracts/online-minorant-migration-v1/convex_affine_minorant.json` | `7599f9bcb7e91849b9fed7a2296f58c4edd2897e624712babafe60f25eb19d37` |
| `docs/contracts/online-minorant-migration-v1/scoped-contexts.json` | `3ccb611c3c7f88afdcd9a8dd8622df32391751715e3aaabd4a68e8e164566273` |
| `docs/contracts/online-minorant-migration-v1/source-card.json` | `db310db9797d1f84248fc7b0acd4cc020ae4d653d09d9401ead4bbdc79c2b9e8` |
| `docs/contracts/online-minorant-migration-v1/source-intent.md` | `78f3c4ee825b9a11b7b07e479cd7577d3d117b54478da8d4d8e309ad08ca025d` |
| `docs/contracts/online-subgradient-basic-migration-v1/dependency-DAG-v1.json` | `bd14bcd04f062212ea2ee12502e6778b99a1b348fe4ebf29986703e138f82259` |
| `docs/contracts/online-subgradient-basic-migration-v1/headers.json` | `c7b60223ad97ffd4ea481e6b320252b31fbd3f373aa85413be671bbf2b09b83d` |
| `docs/contracts/online-subgradient-basic-migration-v1/scoped-contexts.json` | `8f9505e35d08a2a20a5896dc765157d19c6e8edfc0641271121cd1b9fddbd86f` |
| `docs/contracts/online-subgradient-basic-migration-v1/source-card.json` | `e7870fade027b927a69475c040536c95a1ffb64041d2538165f74872603e80bc` |
| `docs/contracts/online-subgradient-basic-migration-v1/source-intent.md` | `d49174fb1d280462c0d22ab43c7cb2d8f5f834ea62929274063960a0bcb359aa` |
| `docs/contracts/online-subgradient-interior-migration-v1/dependency-DAG-v1.json` | `d93bb5987013b55f996672264284e36201eeeb70139ca6ddc74ed4d1988ef523` |
| `docs/contracts/online-subgradient-interior-migration-v1/headers.json` | `50dab3f99b37bff7e3bc757d00aaf54f531e340dce515685f1c7d04bb426b900` |
| `docs/contracts/online-subgradient-interior-migration-v1/planned-headers-only-v1.lean.txt` | `35a9fa661f36c0222af4ccc262f06c06cb79d5608a54f11a5f9173bca3e41902` |
| `docs/contracts/online-subgradient-interior-migration-v1/scoped-contexts.json` | `1331836519e6588247feece22bfdfaed12ca1e199fac933a814c0ac9352a3b59` |
| `docs/contracts/online-subgradient-interior-migration-v1/source-card.json` | `ee4c6abc77f9039d6a34d291fcee7b54e5c5142631625d7c60a46202ae413651` |
| `docs/contracts/online-subgradient-interior-migration-v1/source-intent.md` | `92e6bf6e817336f96790c6cbe3948f2d3f94cd7642b6af480818a2a4e5d4caf4` |
| `docs/contracts/online-subgradient-interior-v1/affine_support_of_domain_interior.json` | `b01ee313212e2995abe06a8f7c8afe5dd405272bb536e12ace93c2fc7cf5aa0c` |
| `docs/contracts/online-subgradient-interior-v1/context.txt` | `f7dd252bd193cc58d12f2ef1ae08055c71af2a661af25b574bef317c44fa85a1` |
| `docs/contracts/online-subgradient-interior-v1/contract.md` | `04a619843500d38b3ea4b9659d3e8d4f42b61de3110b1053cb71dd3897b56516` |
| `docs/contracts/online-subgradient-interior-v1/header.txt` | `56a9c3eab86e530ce017e28b42bc5590ea6011b32a0d56ea5a01e4c64e53fb91` |
| `docs/contracts/online-subgradient-interior-v1/producer-header.txt` | `8d5488d016c69775e21f31eb3834202b958e8981121698377845e08663cab180` |
| `docs/contracts/online-subgradient-interior-v1/subgradient_exists_of_domain_interior.json` | `c516b96596831cc85ac7f3aa51aba912653f41e4916fc84a26a99016d7b7c01b` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `proof-obligations/ONLINE-SUBGRADIENT-INTERIOR-MIGRATION-20261006.md` | `492707056b21ff952763bcfb920487cc9cf347e4203d719928f52c96cff5ebfd` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `runs/online-subgradient-basic-migration-20261006/accepted-decision-v1.json` | `5647a4b1f5fab20af3a7d95e5fe3f3a7d84f38224f54563315ee3099dd1eede0` |
| `runs/online-subgradient-basic-migration-20261006/delivery-v1.md` | `ac0de1b57abcb42eb56219967f8c7aa721f934722e05ada4650130933dbb4252` |
| `runs/online-subgradient-interior-migration-20261006/.gitattributes` | `8b9c3028d6467ff3be7c793141927841d70f47f52d0590677438f488ca154992` |
| `runs/online-subgradient-interior-migration-20261006/00_context.md` | `a054a1825a947968880e0306ff3f637dfbaff02cac7c109300a1a4f16f0be961` |
| `runs/online-subgradient-interior-migration-20261006/10_upper_director-v1.md` | `be8cab411c924097b2d3711e680ef78988e9c23199a4953863211a0856c78b4b` |
| `runs/online-subgradient-interior-migration-20261006/20_architect-v1.md` | `034bc720ea5b8b0fee9e3e401fecd1a6c6e0af05ff195fc5810342b2bfec9828` |
| `runs/online-subgradient-interior-migration-20261006/CLI-help-v1-01-exit.json` | `0fd0f0bb92b206bc13cb59ecbaee88902480344f5dce500aecd6784e016429e0` |
| `runs/online-subgradient-interior-migration-20261006/CLI-help-v1-01.log` | `daacf23e36eec4898dce3b3de02a07b71fb0f80f08e33e8dfe00722e7572970c` |
| `runs/online-subgradient-interior-migration-20261006/authoritative-private-workflow-binding-v1.json` | `46c85785482713393e206ea3549cb11bf5cebe7e9234a5e08cf78575b11f7aa6` |
| `runs/online-subgradient-interior-migration-20261006/blind-packet-v1.md` | `b2cfdb707039e302b15baadf4d8a17f46197594b40755e63f3a6e8879c41d16a` |
| `runs/online-subgradient-interior-migration-20261006/blind-receipt-v1.json` | `3f9980a24074b4cbe24133a74e37e437377501319a2ab2df2afc529793c3fac1` |
| `runs/online-subgradient-interior-migration-20261006/blind-reconstruction-v1.md` | `167ec1c838ee007ae89630e70a9de19e99488c839544f83d3857e03addaeedf8` |
| `runs/online-subgradient-interior-migration-20261006/bootstrap-before-use-v1.json` | `368ec2429774cf390bfcd864d2901fccdfcb7892b2a22f0758b9feea713f9066` |
| `runs/online-subgradient-interior-migration-20261006/bootstrap-generated-before-use-v1.json` | `e567a9a47333e27ccd19b2f33bc9c745ea6d9a7a224cb957d6a3d00206bfae65` |
| `runs/online-subgradient-interior-migration-20261006/bootstrap-v1.py` | `04034863f6dc9ab0648da3d668dbd1d27a2dfd528bb8ee84285acf0c6c938563` |
| `runs/online-subgradient-interior-migration-20261006/compiled-retained-graph-v1-01-exit.json` | `57d8bdb233d11da40f7af84a40a0b0c06fcd8208b152f745992e45215caa70ba` |
| `runs/online-subgradient-interior-migration-20261006/compiled-retained-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-subgradient-interior-migration-20261006/compiled-retained-graph-v1.json` | `f63ab478b5de80d500d97679fa393d97493af57bd177f0c48cc772d8aea08990` |
| `runs/online-subgradient-interior-migration-20261006/compiled-retained-graph-v2.json` | `f63ab478b5de80d500d97679fa393d97493af57bd177f0c48cc772d8aea08990` |
| `runs/online-subgradient-interior-migration-20261006/draft-fence-affine_support_of_relative_domain_interior-v1-exit.json` | `b46670688767848304937fbc6582cdb34d49150828050d2b6a62984077c8fa6f` |
| `runs/online-subgradient-interior-migration-20261006/draft-fence-affine_support_of_relative_domain_interior-v1.log` | `f15c926f240b9232d6d95c4bf466232707d212d47d65d9522af386d0b65e3efa` |
| `runs/online-subgradient-interior-migration-20261006/draft-fence-subgradient_exists_of_domain_interior-v1-exit.json` | `531bcc615b29fbeab816a26962c201762881348a0141d223b40ef6886eaf83ac` |
| `runs/online-subgradient-interior-migration-20261006/draft-fence-subgradient_exists_of_domain_interior-v1.log` | `8dd733e3bb867ade023fb799116befa4108db2935fd637d2cb274750f9f50ecf` |
| `runs/online-subgradient-interior-migration-20261006/draft-fence-subgradient_exists_of_relative_domain_interior-v1-exit.json` | `34c4a0b3727ed90a877fa484af2e119560d3e3200a64cd0d747e92c0eea3a550` |
| `runs/online-subgradient-interior-migration-20261006/draft-fence-subgradient_exists_of_relative_domain_interior-v1.log` | `69727a5de08b654490be60edf865a791458e4d2df510104f932479789e6ab314` |
| `runs/online-subgradient-interior-migration-20261006/draft-freeze-v1.json` | `c3cee0191e44f691c1620302fd11c1a7dfd1fdcc4d62b43d2117f8e43dd6fa04` |
| `runs/online-subgradient-interior-migration-20261006/draft-generated-before-use-v1.json` | `dd135229dcf9355d2046dc322e441f5974fb05ce229da3ef75095c95b75d05a3` |
| `runs/online-subgradient-interior-migration-20261006/draft-lifecycle-v1-exit.json` | `4f6734f96bf7359de1326e1777839dbac44e8e6e9994763cf7df3befe55be082` |
| `runs/online-subgradient-interior-migration-20261006/draft-lifecycle-v1.log` | `af441795b1a071a4dc92bceaa0c5f01cf3fbb69c36b90c6154564f391fe5cf72` |
| `runs/online-subgradient-interior-migration-20261006/draft-preparer-before-use-v1.json` | `c1dae1f6b85a797d165683c6cbe475a3afb7707759030d4f238019a1a952daf1` |
| `runs/online-subgradient-interior-migration-20261006/fence-help-v1-01-exit.json` | `38f1568aadf6b9780517cab694d44780ac156846220baa2600a6e85bfa1b13f4` |
| `runs/online-subgradient-interior-migration-20261006/fence-help-v1-01.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |
| `runs/online-subgradient-interior-migration-20261006/historical-raw-supersession-v1.json` | `409c033203e1bad7a5c10a3d2f2ccbfa7ad37a509a1fed655c323930cf01b9e9` |
| `runs/online-subgradient-interior-migration-20261006/historical-raw-supersession-v2.json` | `09eec6a69a8eded10f0dade4c171b31b4e4659cf26ce5325dfdc636ae358d038` |
| `runs/online-subgradient-interior-migration-20261006/leaves/export-retained-dependencies-v1.lean` | `acde71b80b13931ae9042f28411fb6fe1d66f1c763e8f1e577a9986fcfebddb5` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pinned-required-APIs-v1.lean` | `4e68a91954d944d8b49fefe951ba122f8f15641ab639c2419ad0020d84622379` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-BanditRLProof--OnlineConvexMinorant.lean.txt` | `8ca81ca0b79248a15df47556057175fd6b4712d33a082508c543bd7760a15742` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-BanditRLProof--OnlineSubgradientBasic.lean.txt` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-BanditRLProof--OnlineSubgradientInterior.lean.txt` | `514491262bfef44d495b7173fc4a2de119dd4f17b054fde41ae1b09ff2701e85` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-MANIFEST.md.txt` | `0002cb850d2acea35b9cbe08e67bcf483e08bb4913bd0b0b888a975f64a02023` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-Tests--OnlineSubgradientInteriorCanary.lean.txt` | `6f80f819bb7a6f9632b80596af7eeb2b84808929fef4dd41195a046ef826b085` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-Tests.lean.txt` | `1c60f84f3e4d6d778ac8374b46e47b27559d802986459533517034c97a30f048` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-runs--lifecycle_sessions.jsonl.txt` | `5f4fa0faa717e905c05aa1a355bb1cacbf3ea16af86066d15f6d3c6808ab0167` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-runs--trials.jsonl.txt` | `cb6e8dc72423e62e4e5ff992947be6219a6625b3ece240e51d0a3ccbe4a78d8c` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-v2-BanditRLProof--OnlineConvexMinorant.lean.txt` | `8ca81ca0b79248a15df47556057175fd6b4712d33a082508c543bd7760a15742` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-v2-BanditRLProof--OnlineSubgradientBasic.lean.txt` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-v2-BanditRLProof--OnlineSubgradientInterior.lean.txt` | `514491262bfef44d495b7173fc4a2de119dd4f17b054fde41ae1b09ff2701e85` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-v2-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-v2-MANIFEST.md.txt` | `0002cb850d2acea35b9cbe08e67bcf483e08bb4913bd0b0b888a975f64a02023` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-v2-Tests--OnlineSubgradientInteriorCanary.lean.txt` | `6f80f819bb7a6f9632b80596af7eeb2b84808929fef4dd41195a046ef826b085` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-v2-Tests.lean.txt` | `1c60f84f3e4d6d778ac8374b46e47b27559d802986459533517034c97a30f048` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-v2-runs--lifecycle_sessions.jsonl.txt` | `5f4fa0faa717e905c05aa1a355bb1cacbf3ea16af86066d15f6d3c6808ab0167` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-v2-runs--trials.jsonl.txt` | `cb6e8dc72423e62e4e5ff992947be6219a6625b3ece240e51d0a3ccbe4a78d8c` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-v2-website--content--chapters.json.txt` | `cbe5b02fd50660944495a2a3a355cffefeb8cd523371738087c050f4cf2b29eb` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-v2-website--content--highlights.json.txt` | `8e4560255e5fd7d9a8ae28e3a4ef760155b9b11ff4d3cb481a912b4b8dade634` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-v2-website--content--readings.json.txt` | `241cdf9adedbfa0a502dc91e7413f875f6c5e21350487169310ca73fd4a655f9` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-website--content--chapters.json.txt` | `cbe5b02fd50660944495a2a3a355cffefeb8cd523371738087c050f4cf2b29eb` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-website--content--highlights.json.txt` | `8e4560255e5fd7d9a8ae28e3a4ef760155b9b11ff4d3cb481a912b4b8dade634` |
| `runs/online-subgradient-interior-migration-20261006/leaves/pre-integration-website--content--readings.json.txt` | `241cdf9adedbfa0a502dc91e7413f875f6c5e21350487169310ca73fd4a655f9` |
| `runs/online-subgradient-interior-migration-20261006/leaves/retained-actual-types-v1.lean` | `589606143432e050d81a1f77160155b666902648c318e9035058cffeb74eb22e` |
| `runs/online-subgradient-interior-migration-20261006/lifecycle-help-v1-01-exit.json` | `ca4b8d2401ad042b61f4945489399a05b6e4b4f00f182ffb796e091a617fe07e` |
| `runs/online-subgradient-interior-migration-20261006/lifecycle-help-v1-01.log` | `b1e8b438a9b725793b9888d206e98a971ace3df200ec90ed9cb63eab26b28507` |
| `runs/online-subgradient-interior-migration-20261006/list-mathlib-v1-01-exit.json` | `e51ba1d30d86df4657477495ce996f32d6050e0c69f93e7cdd2c3112cc1a1b89` |
| `runs/online-subgradient-interior-migration-20261006/list-mathlib-v1-01.log` | `884fab88619a3d1adcafe89eecddd2d98f4be5c6fa61262862134dde9e51d225` |
| `runs/online-subgradient-interior-migration-20261006/list-papers-v1-01-exit.json` | `faed7ae7d97bac6fd6c20a80ae4c43361d398e0d3d803bcff0639bd9fed4b4f8` |
| `runs/online-subgradient-interior-migration-20261006/list-papers-v1-01.log` | `9acd333996a893a7b5ccad3e674ece26ef05c8b737e7816b33043b121583a619` |
| `runs/online-subgradient-interior-migration-20261006/list-weapons-v1-01-exit.json` | `087694ae4f4af4b3096b9cf03a90901e262d0bee9ada7bc1345d3483f61ad1ce` |
| `runs/online-subgradient-interior-migration-20261006/list-weapons-v1-01.log` | `a6e4b78de1a30fcf5a0ee66b868eb3ac1bfa68d2250c713f61e690ae064f7ef6` |
| `runs/online-subgradient-interior-migration-20261006/local-intrinsic-lookup-v1-01-exit.json` | `bb1512d4f3ae06759bd908871d68f5f03ca7975a31d7aa5f47787d1e19a22a9d` |
| `runs/online-subgradient-interior-migration-20261006/local-intrinsic-lookup-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-subgradient-interior-migration-20261006/local-lookup-v1-01-exit.json` | `29268055efd2dd00f6382e5b587c4b0f77826d10e92fc72345355c6b1a3a4f34` |
| `runs/online-subgradient-interior-migration-20261006/local-lookup-v1-01.log` | `b385876eccad57ef0bccfb1d2320e64c4d74538cbac862b42c860420c202b109` |
| `runs/online-subgradient-interior-migration-20261006/local-lookup-v2-01-exit.json` | `c659cd8a40fa4897ceb93e50c9f545810b5f4fbacd516763615f4f56fec7163a` |
| `runs/online-subgradient-interior-migration-20261006/local-lookup-v2-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-subgradient-interior-migration-20261006/local-retrieval-help-v1-01-exit.json` | `fd43d67761f660f7d42bdd51b4dc4bf94de7f61029999a343463a258830a345b` |
| `runs/online-subgradient-interior-migration-20261006/local-retrieval-help-v1-01.log` | `258218f16a12b1a530d85ae83e6c2449237af8a0a1153bb35de40245d665b131` |
| `runs/online-subgradient-interior-migration-20261006/local-support-lookup-v1-01-exit.json` | `acdde85b17f47114d7b22f3a65d771d6488e13b67d54e107ca1c5fadcc361a06` |
| `runs/online-subgradient-interior-migration-20261006/local-support-lookup-v1-01.log` | `b567eaa22223254271d12ff02de79242ebd82638f151d65288b15ef94f836c7f` |
| `runs/online-subgradient-interior-migration-20261006/native-draft-fences/affine_support_of_relative_domain_interior.json` | `f15c926f240b9232d6d95c4bf466232707d212d47d65d9522af386d0b65e3efa` |
| `runs/online-subgradient-interior-migration-20261006/native-draft-fences/subgradient_exists_of_domain_interior.json` | `8dd733e3bb867ade023fb799116befa4108db2935fd637d2cb274750f9f50ecf` |
| `runs/online-subgradient-interior-migration-20261006/native-draft-fences/subgradient_exists_of_relative_domain_interior.json` | `69727a5de08b654490be60edf865a791458e4d2df510104f932479789e6ab314` |
| `runs/online-subgradient-interior-migration-20261006/original-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-subgradient-interior-migration-20261006/original-OnlineConvexMinorant.lean.txt` | `8ca81ca0b79248a15df47556057175fd6b4712d33a082508c543bd7760a15742` |
| `runs/online-subgradient-interior-migration-20261006/original-OnlineSubgradientBasic.lean.txt` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `runs/online-subgradient-interior-migration-20261006/original-OnlineSubgradientInterior.lean.txt` | `514491262bfef44d495b7173fc4a2de119dd4f17b054fde41ae1b09ff2701e85` |
| `runs/online-subgradient-interior-migration-20261006/original-OnlineSubgradientInteriorCanary.lean.txt` | `6f80f819bb7a6f9632b80596af7eeb2b84808929fef4dd41195a046ef826b085` |
| `runs/online-subgradient-interior-migration-20261006/original-Tests.lean.txt` | `1c60f84f3e4d6d778ac8374b46e47b27559d802986459533517034c97a30f048` |
| `runs/online-subgradient-interior-migration-20261006/pinned-required-APIs-v1-01-exit.json` | `a3d88b25ae2f736d30d10e0235b23eec266299fbe8118299704b526e037d023e` |
| `runs/online-subgradient-interior-migration-20261006/pinned-required-APIs-v1-01.log` | `3e3cf8e3dc04c584dc745c9d497834895d9b127a3f170742077dd2e4d62cb705` |
| `runs/online-subgradient-interior-migration-20261006/preparation-path-repair-v2.md` | `9fd2bd1635022ff363fee8292c540655212444df65e5945a6b78df7e0f2f2438` |
| `runs/online-subgradient-interior-migration-20261006/prepare-draft-v1-01-exit.json` | `9e75c8a33913ec99ec84e7f2254158cf4d84d03db36832824d560690911daa3a` |
| `runs/online-subgradient-interior-migration-20261006/prepare-draft-v1-01.log` | `5925cc2a8109db9df91fc0d0db937b26060699669260cf665f16af16c2976ff5` |
| `runs/online-subgradient-interior-migration-20261006/prepare-draft-v1.py` | `a7ea3c89087a8dcdf304b14b63ed5201184671d0c8ea589e14d30ed090b95b76` |
| `runs/online-subgradient-interior-migration-20261006/prepare-source-review-v1-01-exit.json` | `667626ce047a8f25c1ac965361177c3dcb25bd8b09925811458135a6b2043926` |
| `runs/online-subgradient-interior-migration-20261006/prepare-source-review-v1-01.log` | `5638ba9944b028d58faabaeb37b98ebf2804f756fa524f7eb8dd31efda18c257` |
| `runs/online-subgradient-interior-migration-20261006/prepare-source-review-v1.py` | `12b136b044260b29ee83c6ea38e203ef376df72c195e3f21fb2ab54617b0956e` |
| `runs/online-subgradient-interior-migration-20261006/prepare-source-review-v2.py` | `31b94e4fd7df99fa71ad356389dbfaba82f5b6701e8d958bf36bee2a32c06dbd` |
| `runs/online-subgradient-interior-migration-20261006/proof-obligations-v1.json` | `f8cdaad0ab5d0d367873bb123384ca75863661af263cb33bc9b09a68a3e6c20e` |
| `runs/online-subgradient-interior-migration-20261006/ready-dependencies-v1.json` | `0dc664a8c5c1d164d83413a8e95672c4aa7039e0f9480de13faecdccb1ff9ab5` |
| `runs/online-subgradient-interior-migration-20261006/ready-dependencies-v2.json` | `0dc664a8c5c1d164d83413a8e95672c4aa7039e0f9480de13faecdccb1ff9ab5` |
| `runs/online-subgradient-interior-migration-20261006/retained-declarations-v1.json` | `c0d7eb51d2a12fe492ebdbff9da8cfd953667f37cbec978defb0a22249bd9cc1` |
| `runs/online-subgradient-interior-migration-20261006/retained-exporter-before-use-v1.json` | `b6037e1605f64160b81573f07cc04bdc24ed5006b7630ff98e85e2729e6a3e2b` |
| `runs/online-subgradient-interior-migration-20261006/retained-module-v1-01-exit.json` | `9459580d54058db33f14ee8c16709316747169c93e7d9640f84f511178a54b33` |
| `runs/online-subgradient-interior-migration-20261006/retained-module-v1-01.log` | `7008472d37c034afaa4d3dfbc05dfe3eab9b1d91071ba1a5ae611ea546105178` |
| `runs/online-subgradient-interior-migration-20261006/retained-types-v1-01-exit.json` | `c94eb95ece9af768c201b7f2ed8367a2af664d1d33e7e37097872adb67e046ef` |
| `runs/online-subgradient-interior-migration-20261006/retained-types-v1-01.log` | `874a56f808d08d729d106df86e1dd57e6606a1d00b77114592e27c429cad0f1d` |
| `runs/online-subgradient-interior-migration-20261006/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `runs/online-subgradient-interior-migration-20261006/source-printed17-pdf29.txt` | `a86a6e16b70801b7c17134841e9f2fb222aecc9fd919f2b7e8f840c27ca08ece` |
| `runs/online-subgradient-interior-migration-20261006/source-review-helper-before-use-v1.json` | `842f1c636b4d338fc1b6e1d1a902e10a22c878b32a87a91363d7de8175cb246d` |
| `runs/online-subgradient-interior-migration-20261006/source-review-helper-before-use-v2.json` | `b1978fa16086f22086f33b4c476b973e9dff231e3a3823f089e082d14440bbf7` |
| `runs/online-subgradient-interior-migration-20261006/source-review-packet-v1.md` | `cc80074270e8bf0095affff3f36e2af441d3a5a540568e7d6e6048217bab425a` |
| `runs/online-subgradient-interior-migration-20261006/source-review-packet-v2.md` | `26b2ac693fedefeba1f2863848326afa09980d443badf1def2666612e667c04d` |
| `runs/online-subgradient-interior-migration-20261006/workspace-audit-v1.json` | `fd2f3e477f67b24b43feb4403b245c6655631c655df4184a74a8c2233e9d9d8e` |
| `tasks/ONLINE-SUBGRADIENT-INTERIOR-MIGRATION-20261006.md` | `492707056b21ff952763bcfb920487cc9cf347e4203d719928f52c96cff5ebfd` |
| `tmp/online-subgradient-interior-migration-retained-graph-v1.json` | `f63ab478b5de80d500d97679fa393d97493af57bd177f0c48cc772d8aea08990` |
| `website/content/chapters.json` | `cbe5b02fd50660944495a2a3a355cffefeb8cd523371738087c050f4cf2b29eb` |
| `website/content/highlights.json` | `8e4560255e5fd7d9a8ae28e3a4ef760155b9b11ff4d3cb481a912b4b8dade634` |
| `website/content/readings.json` | `241cdf9adedbfa0a502dc91e7413f875f6c5e21350487169310ca73fd4a655f9` |
| `runs/online-subgradient-interior-migration-20261006/contract-source-inputs-v2.json` | `b1a8f039b83f797120c941690e0cbe593ca82b97fd2ab03f22157bed733590d4` |
