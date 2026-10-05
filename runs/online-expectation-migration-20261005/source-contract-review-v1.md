# Expectation migration source-contract review v1

Verdict: **accepted-with-explicit-delta**, ten retained representation interfaces only: three actual definitions and seven proof contracts. Mathematical repairs: none. Required reader corrections below. Theorem2.9 is the parent dependency endpoint and is NOT accepted by this receipt.

Actor `/root/source_reviewer`, distinct automated source reviewer; requested GPT-6 Astra / medium. No human/external-model review or independently attested runtime-model claim. Existing bodies are contradiction/readiness context, not fresh body/package acceptance.

All122 fixed raw inputs independently read/hash-checked, no mismatch; inventory and used header extractor additionally bound (124 rows). All10 actual declaration headers match frozen statements/native hashes. Actual three definition bodies match the scoped context. Fresh neutral reconstruction correctly preserves arbitrary-measure/general-function scope; actual pinned APIs independently resolve its imported-convention caveats.

Original PDF SHA256 `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` verified; directly read physical23/printed11 Theorem2.9. It concerns measurable convex f:R^d→(-infinity,+infinity], a random vector with existing mean and a.e. domain membership under a probability space. None of these ten foundation declarations states Jensen. They intentionally generalize representation machinery to arbitrary measures; source application needs separate hypotheses and producers.

## Ten-target seven-slot comparison

Every row below has verdict **accepted-with-explicit-delta**, with names qualified by `BanditRL.OnlineConvex.`. Slots are object, quantification, assumptions, guarantee/definition, normalization, information/probability and boundaries respectively.

| Target | Objects | Quantifiers | Assumptions | Guarantee/definition | Normalization | Information/probability | Boundaries |
|---|---|---|---|---|---|---|---|
| positiveIntegral | EReal f, ENNReal output | Every μ,f on measurable Ω | No function measurability/integrability | lintegral of f.toENNReal | Positive truncation; no mass divisor | Deterministic arbitrary-measure functional | ±∞ input allowed; +∞ output; total lower integral is not measurability evidence |
| negativeIntegral | EReal f, ENNReal output | Every μ,f | Same type-only context | lintegral of (-f).toENNReal | Magnitude of negative part, not signed negative integral | No probability or sigma-finite restriction | -∞ input gives +∞ integrand; positive input gives0; output may∞ |
| signedExpectation | Embedded positive/negative integrals in EReal | Every μ,f | Neither part assumed finite | P-M as total EReal subtraction | Unnormalized unit difference | Not automatically a probability expectation | P=M=∞ gives formal⊥, not legitimate signed integral; finite-part and measurability conditions external |
| positiveIntegral_coe | Real f embedded into EReal | Every μ,real f | No measurability/integrability | P=lintegral ofReal(f) | Exact positive truncation identity | Arbitrary measure | Pointwise finite values may have infinite integral |
| negativeIntegral_coe | Real f embedded, negative magnitude | Every μ,real f | No measurability/integrability | M=lintegral ofReal(-f) | Negate before positive truncation | Arbitrary measure | Negative values allowed; finite value does not ensure finite part integral |
| positiveIntegral_coe_ne_top | Real f and P | Every μ,f with Integrable | Actual AEStronglyMeasurable and HasFiniteIntegral | P≠∞ | Finiteness, not numerical bound | No mass restriction | Zero part allowed; no claim for nonintegrable f or converse |
| negativeIntegral_coe_ne_top | Real f and M | Every μ,f with Integrable | Actual integrability retained | M≠∞ | Negative magnitude finite | Arbitrary measure | Negative losses allowed; no nonintegrable/default-zero extension |
| signedExpectation_coe_integrable | Signed difference and embedded real Bochner integral | Every μ,integrable real f | Actual Integrable f μ | Exact equality with embedded integral | No normalization | Legitimate integrable signed integral, probability only if separately supplied | Both parts finite, no both-infinite case; not arbitrary EReal/nonintegrable input |
| signedExpectation_of_nonneg | EReal f, signed/P | Every μ,f a.e. nonnegative | Only μ-a.e.0≤f | Signed=P | Negative integral0 | A.e. relative to arbitrary μ, not necessarily probability | No measurability/integrability demanded; positive∞ allowed; null-set negative values permitted |
| signedExpectation_eq_top | EReal f, P,M | Every μ,f with stated parts | P=∞ and M≠∞ | Signed=⊤ | Exact EReal top | Algebraic arbitrary-measure branch | Both-infinite explicitly excluded; measurability separate; no symmetric branch theorem claimed |

## Actual semantic checks

Pinned Integrable is AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ. Thus finite-parts/Bochner compatibility do not assume merely finite point values or an available total integral expression. Actual Bochner positive-minus-negative identity carries Integrable. Actual EReal toENNReal maps nonpositive values to0 and top to∞. Pinned sub_top states x-top=bottom, including top-top; this total arithmetic is not a solution to undefined signed expectation. The actual definitions enforce none of the external semantic conditions at runtime.

The nonnegative reduction needs no extra measurable premise as a formal identity: actual lower integral respects a.e. equality, negative integrand vanishes a.e. This must not be restated as a universal classical signed expectation without its interpretation conditions. Infinite-positive/finite-negative retains hn; dropping it would admit the wrong both-infinite arithmetic branch. Arbitrary measure includes zero/empty/nonfinite cases without normalization, and no probability-mass assertion is smuggled into a.e. notation.

Source-facing future Jensen work must prove finite negative loss part under its source assumptions (via the global affine minorant and integrable random vector), not assume whole loss integrability and silently discard infinite-positive cases. Historical parent compilation does not discharge that separate distinct migration review. This package supplies necessary representation machinery only.

Actual existing canaries were inspected for scope contradictions: twoAtoms=dirac(-1)+dirac3 has mass2 and identity integral2, not normalized expectation1. Counting-measure n+1 has finite nonconstant values, positive part∞ and negative0. It is not a probability-law infinite-loss Jensen example. Fresh canary/body acceptance remains pending; the contract review makes no new execution claim. Current10-node compiled environment graph/type/API evidence is readiness, not full/canary graph or proof acceptance.

Mathematical repairs: none.

Required reader corrections:
1. State arbitrary measure/sample space, no mass normalization or probability assumption for these interfaces. Preserve mass-two identity integral2 and counting-measure infinite branch as nonprobability canaries, not Jensen probability instances.
2. Explain total lower integrals need no supplied function measurability; signedExpectation is total EReal arithmetic. Legitimate signed-integral interpretation needs appropriate measurability and at least one finite part; both infinite yields formal bottom in this library and is not a valid signed expectation.
3. State actual Integrable real f includes a.e. strong measurability and finite norm integral for the two finite-part results and Bochner compatibility. Do not extend compatibility to nonintegrable Bochner default zero.
4. Label all seven proofs and three definitions as library representation dependencies, Theorem2.9 only as the separately mapped parent source terminal. This migration does not accept Jensen or prove its negative-part-finiteness obligation.
5. Replace still-unproved Jensen target wording with accurate retained historical parent-proof status requiring separate distinct revalidation; distinguish historical compilation from this bounded review. Keep source loss-integrability absent and affine-minorant negative-part producer obligation explicit.
6. Distinguish a.e.-nonnegative algebraic reduction without measurability/integrability from measurable signed-integral semantics; keep positive infinity and the explicit finite-negative premise of signedExpectation_eq_top visible.

Remaining: fresh retained-body/canary/axiom/native guards, combined root/Tests/full harness, corrected reader/site/registry/contributor/final review, immutable binding and PR. Three retained definitions/seven retained proofs, no new code or nodes. Chapter2 null/incomplete, Whole Goal active; parent Jensen, other migrations, whole chapter/book/main/live are not certified.

## Exact raw reviewed files

| Path | SHA256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean` | `bf69a9ed4bc39134bbefac1a43b187e2f1e66fd43f352d0810ab89474f054922` |
| `.lake/packages/mathlib/Mathlib/Data/EReal/Operations.lean` | `50717cddbcd70f8650cf25c4bd37f07e07de14ee8117099a4d9f7aee6d36a791` |
| `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean` | `e38fe37ad58e7a3d606e87419f5e02972526c4b7ac84378b85dac1148c34a437` |
| `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` | `ce6b984f1a4b0ba00688574d9e90785a5d5a7f7c27c3230c501909792d0e2495` |
| `BanditRLProof/OnlineExpectation.lean` | `ce10963bc29809cea19e0904c4a75ef4913eb2a4920d667cd823e51b84542d80` |
| `BanditRLProof/OnlineJensen.lean` | `7b4ff2c15f08288c47499673842d334e0a719efcccc90a59a41cf3ed40d62a98` |
| `Tests/OnlineExpectationCanary.lean` | `b90fae27377bfbc4c244abe48e0efea9558d5c012a4f8bb7d562e897795cf001` |
| `conversion-windows/ONLINE-EXPECTATION-MIGRATION-20261005.md` | `7338d784ec4a4fee4abd1f51d082c29f2367cceaafd6db98f375a1b3fa97dcda` |
| `docs/contracts/online-expectation-migration-v1/context-definitions.lean.txt` | `b4add744a1c71aa45aa145b3c3f899b74af27bc1a8b4987c723d980a04420908` |
| `docs/contracts/online-expectation-migration-v1/negativeIntegral-header.txt` | `80db1ff0d75a619e4a43ff65781bc9188e8e12aaeaa77e635446ceeacc0dd943` |
| `docs/contracts/online-expectation-migration-v1/negativeIntegral.json` | `5ecb36208f8626d8cb6b9f872440e18fef0445787914d85c18cb3a6def5977ea` |
| `docs/contracts/online-expectation-migration-v1/negativeIntegral_coe-header.txt` | `b2e6256d4c48006679dbde8129bceddffff1f1123c04e0a691bb2386c41b8e0b` |
| `docs/contracts/online-expectation-migration-v1/negativeIntegral_coe.json` | `b995c66de6ffb72b4b3a199c99255ca4543e83d3283160a100ae7b75fd7675b1` |
| `docs/contracts/online-expectation-migration-v1/negativeIntegral_coe_ne_top-header.txt` | `809d697eb2ba16f4dc9d04a37cd6984f46d976f2bc9acdcb2e738af4da7f4101` |
| `docs/contracts/online-expectation-migration-v1/negativeIntegral_coe_ne_top.json` | `da95663eb6dff5a2cc78bb66ca014da899958547f9d99017123e20df483aca89` |
| `docs/contracts/online-expectation-migration-v1/positiveIntegral-header.txt` | `f534a63981360789fb084c37b72c1f7d4124bcde888d14b21992f896ec993f85` |
| `docs/contracts/online-expectation-migration-v1/positiveIntegral.json` | `33aa1060a566ecf8d61f09bdd38dc607951b9cae1ee0f70a2f8c9089e45442a4` |
| `docs/contracts/online-expectation-migration-v1/positiveIntegral_coe-header.txt` | `ec9568c1e93e8603619cbcc5ac1d538742f9e9c10b699c7b0eba9bbf643147fd` |
| `docs/contracts/online-expectation-migration-v1/positiveIntegral_coe.json` | `8529ed8e5bed4b614433a759d5f9e2b9675d9ee07fc1fd5f53dd4e657af87118` |
| `docs/contracts/online-expectation-migration-v1/positiveIntegral_coe_ne_top-header.txt` | `9dd1918c5b2a56b3fb245839a5ad785c78f8dcfcf74e38e513b571053ef2ef45` |
| `docs/contracts/online-expectation-migration-v1/positiveIntegral_coe_ne_top.json` | `884f64ba65069c9fdd3c8effb8493bc95512192b63ce475caa0490867f5c5176` |
| `docs/contracts/online-expectation-migration-v1/signedExpectation-header.txt` | `6a70ed5af4f9f0874c9418bb92912b58360d1bfd73724768d66dc9c905fc95cc` |
| `docs/contracts/online-expectation-migration-v1/signedExpectation.json` | `b75b7c5ad3e2dc0d2ca6025fbcb4ccda859e4b36395c6e5decb0df5af3db88a6` |
| `docs/contracts/online-expectation-migration-v1/signedExpectation_coe_integrable-header.txt` | `0c6827d02aeacb107a66ee13a10970f61cfa4bd6c8f3a7bf6bf85cc280c4e6d3` |
| `docs/contracts/online-expectation-migration-v1/signedExpectation_coe_integrable.json` | `52e869d5886aa1567888e595386b927eb05e000e25163a5ad57037e54d0e0c70` |
| `docs/contracts/online-expectation-migration-v1/signedExpectation_eq_top-header.txt` | `579b7d010c646ead466624df107f2195d1f5755a3ba0fb31992d505cbfc34c1d` |
| `docs/contracts/online-expectation-migration-v1/signedExpectation_eq_top.json` | `1fc4639ae9258114c3d7ada56d40b426a87e0d62ef4b54afd6663f0aeff0527f` |
| `docs/contracts/online-expectation-migration-v1/signedExpectation_of_nonneg-header.txt` | `9a3e1af799e06d8977e13b08e8b5ce675119eec5d8bf268cafd09c7a441def80` |
| `docs/contracts/online-expectation-migration-v1/signedExpectation_of_nonneg.json` | `e3a1ff1fa025a9a39f675be6049e3d3acf493ac801e122d95d58697b24cfad19` |
| `docs/contracts/online-expectation-migration-v1/source-card.json` | `40547194f377d01e4ab8a7f9bba8832cbec124faff261d9ced0821c1d6bcf03d` |
| `docs/contracts/online-expectation-migration-v1/source-intent.md` | `2d645a42aefe4045662d99420972f17cc48cf4095d9fd8c88bd1dac7439c60da` |
| `docs/contracts/online-expectation-v1/context.json` | `de78009b31ba4db24220088f8a3c19b41aa6e6d185b46a5085e6f138ce504d57` |
| `docs/contracts/online-expectation-v1/contract.md` | `6d0a144aa6b93aa1179c54496cca058c82fa40692c3fe611fb581cebbd988589` |
| `docs/contracts/online-expectation-v1/headers.json` | `f2cf64cb50d2cfc0df005da9dba7132a9316f780970c60d540ebdd236ef573d5` |
| `docs/contracts/online-expectation-v1/negativeIntegral_coe.json` | `29ad9af0128906261eac5f61a6a14df64ced6e24b6cde4d46e25367cf3807838` |
| `docs/contracts/online-expectation-v1/negativeIntegral_coe_ne_top.json` | `e1b16792d253db034736316bb6c115374661a013671266f3bd9398585cb2f5bc` |
| `docs/contracts/online-expectation-v1/positiveIntegral_coe.json` | `e999aae94ab6af1680b15b0c7bba560c56396282dd1515768114f5f4c7827d7d` |
| `docs/contracts/online-expectation-v1/positiveIntegral_coe_ne_top.json` | `dac341dad575e76aab8a52ba60a6a5488a845ed0824a60daa7de646608376d61` |
| `docs/contracts/online-expectation-v1/signedExpectation_coe_integrable.json` | `0c721cb77a9b716ebe3cb658ef0f74b0f63859f83e5b1279e444e7478eb8d393` |
| `docs/contracts/online-expectation-v1/signedExpectation_eq_top.json` | `e67a5b2b0d05a3a80af5556afe9e765c71ee85d93aaf1e204b2550797de121ea` |
| `docs/contracts/online-expectation-v1/signedExpectation_of_nonneg.json` | `8585efdefbfbfb66bf3c6e60c294793c1146a87342fe6181a5e35c2c3cf5925f` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `proof-obligations/ONLINE-EXPECTATION-MIGRATION-20261005.md` | `73d818dbae8722d28bdda34b22b57861ad32eb952ade1a8bfe2c2d4dbb55c4a2` |
| `runs/online-expectation-migration-20261005/00_context.md` | `fcb3cb2334bf2b0ed1bb8cbeeb2eaa3a9cd0f0b68dc215b97bc29e4d39fb684e` |
| `runs/online-expectation-migration-20261005/10_upper_director-v1.md` | `9ee37421c102aadea17012d5edc48f8b9c4a49eef827ab6774120f9ccd50873d` |
| `runs/online-expectation-migration-20261005/20_architect-v1.md` | `361ce1dae666e30b1f6f715a94caadbce064ba7d4b5f1055834eb1f271e096e6` |
| `runs/online-expectation-migration-20261005/actual-pinned-API-retrieval-v1-01-exit.json` | `2e43eb45dc6befc43bb414c216efa3371563240753db1f94647db2b687bd8b48` |
| `runs/online-expectation-migration-20261005/actual-pinned-API-retrieval-v1-01.log` | `6e3e99839a1ab524fc486f57ea71e46c315096d9a484e75123536f78a608aa40` |
| `runs/online-expectation-migration-20261005/actual-public-types-v1-01-exit.json` | `067e79802c3db3a8df2f0b028fefbd78f9a19533e7e13cb78b9882f04cb52bfe` |
| `runs/online-expectation-migration-20261005/actual-public-types-v1-01.log` | `4ddb579381c7ff9e615c0a00c199fd325b53e52c04c16229d3ce23f0dbdba062` |
| `runs/online-expectation-migration-20261005/actual-scoped-graph-v1-01-exit.json` | `6f2f1326e9cc81f2d0671e1f4177b71d7a0fd7c9d9caf6cc13fdd1eda259df76` |
| `runs/online-expectation-migration-20261005/actual-scoped-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-expectation-migration-20261005/auxiliary-workflow-preparation-v1.json` | `b8dbd869406d8fefae43990f681b17998ca9d401f4b7beffd1ddfb8769fba7f8` |
| `runs/online-expectation-migration-20261005/blind-packet-v1.md` | `7a4741c339916ebe40e7cc1821936f6d09a9b4621e4fef2231b327c610cf54ca` |
| `runs/online-expectation-migration-20261005/blind-receipt-v1.json` | `27190816569ba85616a7119c4b6f3641cb4e79817770d1493c7b709ae669c191` |
| `runs/online-expectation-migration-20261005/blind-reconstruction-v1.md` | `073febf735f627e89603ed67e3eec2d0ed4a83a4bf884e43f76c09c9d20207ba` |
| `runs/online-expectation-migration-20261005/check-scoped-diff-v1.py` | `a49642067fdb7d2058fc02d774bbe66bdc184a0710c3bdc0036300a9f377cfd7` |
| `runs/online-expectation-migration-20261005/commit-owned-v1.py` | `58d3cb5c1c738b971b9d8396e80a14d1bef7d5a98f49bc05dfcad214db2a5e2e` |
| `runs/online-expectation-migration-20261005/compiled-scoped-graph-v1.json` | `3148b15ebee61bc8d80ae104a4a538ed8586edb4d8b3772c6e90f5da6be2a68b` |
| `runs/online-expectation-migration-20261005/contract-source-inputs-v1.json` | `16176f6e146847310cf57a388b245cdf1bf46dec632f5f0b094af44c778c08f9` |
| `runs/online-expectation-migration-20261005/draft-fence-negativeIntegral-v1-exit.json` | `350878f370601eac2c701bc5dad7f0b825c952ad59c1e8e7be551c8c55737be5` |
| `runs/online-expectation-migration-20261005/draft-fence-negativeIntegral-v1.log` | `2edb95d7a15fe711c0ee38cfbc1ce89a50f078a966a13c9284aacefbd99b72a5` |
| `runs/online-expectation-migration-20261005/draft-fence-negativeIntegral_coe-v1-exit.json` | `40efbca3b430c04dccc103b3b2a7c68b43e18ee4236d4cb81458c53b4433ba29` |
| `runs/online-expectation-migration-20261005/draft-fence-negativeIntegral_coe-v1.log` | `12b0f20138410bdcc8c0fb2a42a97a23f02d1ff219e60086b3b0a67021f69b9c` |
| `runs/online-expectation-migration-20261005/draft-fence-negativeIntegral_coe_ne_top-v1-exit.json` | `7f60b6dac43acedbfc3e815ecb2945934a6f5e8b30b36e97321c0f4223653ef6` |
| `runs/online-expectation-migration-20261005/draft-fence-negativeIntegral_coe_ne_top-v1.log` | `e38309dfcf8386b989605665d14426983a440d8568b9e44589a4e7a422164169` |
| `runs/online-expectation-migration-20261005/draft-fence-positiveIntegral-v1-exit.json` | `bca9c30fea3d973d957ded5e1634fc0ad70a7bc74697d88a943258b04ed267a5` |
| `runs/online-expectation-migration-20261005/draft-fence-positiveIntegral-v1.log` | `a4a2af5004c665a0ded8a48707b2772f6f500360c4e6b69e79af0e4cce4a8c43` |
| `runs/online-expectation-migration-20261005/draft-fence-positiveIntegral_coe-v1-exit.json` | `85954bc25242f081f846db94064a68bf07c7494b8c2bba15fe576d67e82117c3` |
| `runs/online-expectation-migration-20261005/draft-fence-positiveIntegral_coe-v1.log` | `9559572214390523dbdbb9dc4e06938e75b19380f2efc334067e7d40f97c12bb` |
| `runs/online-expectation-migration-20261005/draft-fence-positiveIntegral_coe_ne_top-v1-exit.json` | `24200b7b4d13bbca923c201ea4cb86389be601b12353618ca7b65d34657545d4` |
| `runs/online-expectation-migration-20261005/draft-fence-positiveIntegral_coe_ne_top-v1.log` | `17230b068b5b63e31cd05764835f7addbc9649ba9fa123e9ea13e27764c685e1` |
| `runs/online-expectation-migration-20261005/draft-fence-signedExpectation-v1-exit.json` | `0b2f134ed2acf17648a002241b8206aac35b3bb76ad982df595a8d1afbafcf9b` |
| `runs/online-expectation-migration-20261005/draft-fence-signedExpectation-v1.log` | `5ebc8adcfa892131e3664b035e579b3ec1b549e40bb7a96651d4dc09f6bf7488` |
| `runs/online-expectation-migration-20261005/draft-fence-signedExpectation_coe_integrable-v1-exit.json` | `6c1869d5363c755c8569d3487f7d293760365536d25dc0b2d9117d06bbaceb2b` |
| `runs/online-expectation-migration-20261005/draft-fence-signedExpectation_coe_integrable-v1.log` | `34aa4963f91a27aec003c19eeab6187876cc32554c6d0cf3a347a2882a8f8320` |
| `runs/online-expectation-migration-20261005/draft-fence-signedExpectation_eq_top-v1-exit.json` | `6494fe704600e58f5df2328b501583c33cab3b1734f1767d8be4423fc118f04b` |
| `runs/online-expectation-migration-20261005/draft-fence-signedExpectation_eq_top-v1.log` | `e830ee0518e0eccaf5e324800d4c2c3bc4683231c0022d8e0f7581cc01f118c1` |
| `runs/online-expectation-migration-20261005/draft-fence-signedExpectation_of_nonneg-v1-exit.json` | `56e2097da8d3f684a4ce9a909a429568d946c5c5cb92ec9e7bbbdd3cc5fdf78c` |
| `runs/online-expectation-migration-20261005/draft-fence-signedExpectation_of_nonneg-v1.log` | `77daa259afc6732514374bce04bb85fdd29661a274a0c5b52a372db5359730de` |
| `runs/online-expectation-migration-20261005/draft-freeze-v1.json` | `807f16ceac00c20fd1dd4f850d44716b7a5b26b29547044a037a06b463580775` |
| `runs/online-expectation-migration-20261005/draft-lifecycle-v1-exit.json` | `ed71149d40a0bd50b60d0cbaf882e5abb2f48340aa92979df6a5df0c941f572c` |
| `runs/online-expectation-migration-20261005/draft-lifecycle-v1.log` | `b120bb5b7d1cea7ac0d71a85021f40d8cedaa036fce6d7a3348c0cb800aa9e43` |
| `runs/online-expectation-migration-20261005/existing-public-retrieval-v1-exit.json` | `f02ada6515d61f80b67a0b8cba40bce4dfcf3cb57f04a4977ca94e6fa762b31b` |
| `runs/online-expectation-migration-20261005/existing-public-retrieval-v1.log` | `f565cd4c4fe9163a1aa427167fad5cd882ce163f578ef6c280939981c2fb1247` |
| `runs/online-expectation-migration-20261005/leaves/actual-public-types-v1.lean` | `06442eaacab9a67bb0788c00417ac0ff92687ce445e8463528ef7f1be0ed26a5` |
| `runs/online-expectation-migration-20261005/leaves/export-scoped-dependencies-v1.lean` | `a547dc847558a2814b4b2c192be2a08dec491f4c2f16c903e23598549cf8ffc6` |
| `runs/online-expectation-migration-20261005/native-draft-fences/negativeIntegral.json` | `2edb95d7a15fe711c0ee38cfbc1ce89a50f078a966a13c9284aacefbd99b72a5` |
| `runs/online-expectation-migration-20261005/native-draft-fences/negativeIntegral_coe.json` | `12b0f20138410bdcc8c0fb2a42a97a23f02d1ff219e60086b3b0a67021f69b9c` |
| `runs/online-expectation-migration-20261005/native-draft-fences/negativeIntegral_coe_ne_top.json` | `e38309dfcf8386b989605665d14426983a440d8568b9e44589a4e7a422164169` |
| `runs/online-expectation-migration-20261005/native-draft-fences/positiveIntegral.json` | `a4a2af5004c665a0ded8a48707b2772f6f500360c4e6b69e79af0e4cce4a8c43` |
| `runs/online-expectation-migration-20261005/native-draft-fences/positiveIntegral_coe.json` | `9559572214390523dbdbb9dc4e06938e75b19380f2efc334067e7d40f97c12bb` |
| `runs/online-expectation-migration-20261005/native-draft-fences/positiveIntegral_coe_ne_top.json` | `17230b068b5b63e31cd05764835f7addbc9649ba9fa123e9ea13e27764c685e1` |
| `runs/online-expectation-migration-20261005/native-draft-fences/signedExpectation.json` | `5ebc8adcfa892131e3664b035e579b3ec1b549e40bb7a96651d4dc09f6bf7488` |
| `runs/online-expectation-migration-20261005/native-draft-fences/signedExpectation_coe_integrable.json` | `34aa4963f91a27aec003c19eeab6187876cc32554c6d0cf3a347a2882a8f8320` |
| `runs/online-expectation-migration-20261005/native-draft-fences/signedExpectation_eq_top.json` | `e830ee0518e0eccaf5e324800d4c2c3bc4683231c0022d8e0f7581cc01f118c1` |
| `runs/online-expectation-migration-20261005/native-draft-fences/signedExpectation_of_nonneg.json` | `77daa259afc6732514374bce04bb85fdd29661a274a0c5b52a372db5359730de` |
| `runs/online-expectation-migration-20261005/original-OnlineExpectation.lean.txt` | `ce10963bc29809cea19e0904c4a75ef4913eb2a4920d667cd823e51b84542d80` |
| `runs/online-expectation-migration-20261005/original-OnlineExpectationCanary.lean.txt` | `b90fae27377bfbc4c244abe48e0efea9558d5c012a4f8bb7d562e897795cf001` |
| `runs/online-expectation-migration-20261005/prepare-draft-v1.py` | `5bc41165f2d5d640734a99d50bfaed6d04833c4f5e19935714745e3f9ca180f0` |
| `runs/online-expectation-migration-20261005/prepare-source-review-v1.py` | `ee8262b5ce2e578455ce67c5e56b93e9f6f04175ebef0fae1ec8b84c3e81c6fe` |
| `runs/online-expectation-migration-20261005/proof-obligations-v1.json` | `01cac4a0cc68b6753e079cc81e75232975e34342df641ef57220611815b43a62` |
| `runs/online-expectation-migration-20261005/ready-dependencies-v1.json` | `c0690b0f190a6a8905796a57b3e8e9c83a95c932d0e0d64b77f49009c50d2b59` |
| `runs/online-expectation-migration-20261005/retained-module-types-v1-01-exit.json` | `f32f6fe26dc7ffacf80a86365307bf65b49877a5d1171a05e1bd4eb0611b7a12` |
| `runs/online-expectation-migration-20261005/retained-module-types-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-expectation-migration-20261005/retrieve-pinned-API-v1.py` | `bd8b247411bb6f6941cd0e98ecb43fd91a3a945e34ec508fb23ebb7177dcfbdb` |
| `runs/online-expectation-migration-20261005/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `runs/online-expectation-migration-20261005/source-printed11-pdf23.txt` | `34427f62320e4592569f9537025a692ffa127a39b1b8377d025b8655c8bb7781` |
| `runs/online-expectation-migration-20261005/source-review-packet-v1.md` | `fefe8e43c112035e97f81a71100f7a3188e828ce6f3a454b70ece867f96c0821` |
| `runs/online-expectation-migration-20261005/utility-audit-v1.md` | `9abf38f868d6fb4470ea7f79ed92c8f2fda2a3e4226efb2ccb77e436ac1775db` |
| `runs/online-expectation-migration-20261005/verify-public-fences-v1.py` | `e88166d8500e20357081c4fc10297cb4d2297a0da236525b594dee68b1d922e7` |
| `runs/online-optimality-migration-20261005/accepted-decision-v1.json` | `97657e6071bdabaeceb5e029c676e0fbd659e6b18a153b493d97f56476881da2` |
| `runs/online-optimality-migration-20261005/native-acceptance-overlay-v1.json` | `ddf9cecb60e70b05ee45e8cc553d1cbc950bc3d7ec7b79354f5948fc97cee7b8` |
| `runs/online-optimality-migration-20261005/pr-delivery-v1.json` | `c5f8e6356a193af998711fcb25f6d866f3ccc104e75bb2910da8792cda0ab7c3` |
| `tasks/ONLINE-EXPECTATION-MIGRATION-20261005.md` | `47293992469d5a5f6aae03dbce48b1071129ec8d3ad7603d006f5da4905b6e0e` |
| `tmp/online-expectation-migration-scoped-graph-v1.json` | `3148b15ebee61bc8d80ae104a4a538ed8586edb4d8b3772c6e90f5da6be2a68b` |
| `tools/abrl_lifecycle.py` | `7615541e66a372e939ea2d18684ce78a8f3d8f1202894840ef7fdfdc703c4310` |
| `website/content/chapters.json` | `a822e2f31582fd148c6fbc0d2277db8a543cbba3e435998b289ca13164c30b1a` |
| `website/content/highlights.json` | `00de2c7ca642dbe6ba1856968a0d3383de9424feea2ffaacbe0e35ce9baf3d0f` |
| `website/content/readings.json` | `2f4fb05c49a8fb97503572b77280dd651c1f8bc028aa2f6d57d525cc2074352b` |
