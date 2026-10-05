# Optimality migration source-contract review v1

Verdict: **accepted-with-explicit-delta**, for stabilization of four retained contracts only. No mathematical header repair found. Reader corrections below remain required. Existing bodies/canaries are available for contradiction checks, but are not freshly accepted in this contract phase.

Actor `/root/source_reviewer`, distinct automated source reviewer; requested GPT-6 Astra / medium. No human/external-model review or independent runtime-model attestation. Historical acceptance is not the authority for this decision.

All 89 fixed raw rows independently read/hash-checked without drift. Inventory, actual header extraction implementation and IsMinOn implementation additionally bound (92 rows). All four actual extracted headers match frozen statements and native hashes. Raw integrity coverage of ancillary administration is not a renewed semantic audit of earlier packages. Fresh restricted decoder reconstructs the four scopes correctly; imported conventions were separately checked against actual APIs.

Original pinned PDF SHA256 `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. Fresh direct physical page23 extraction read Theorem2.8, its proof and following unnumbered interior-zero equivalence, printed11. Source assumes nonempty convex V, candidate membership, convexity and differentiability over an open containing set. It asserts all feasible directions, then adds ambient interior for zero gradient. The unnumbered consequence is required source content.

## Per-target seven slots

### BanditRL.OnlineConvex.minOn_real_iff_gradient — accepted-with-explicit-delta

1. Objects: everywhere-real f and subset V in complete real inner-product E, ambient gradient at x.
2. Quantifiers: all such f,V,x satisfying hypotheses; all feasible y on right side.
3. Assumptions: ConvexOn V (including convex V), x membership and ambient DifferentiableAt f x. No open set, finite-part representation or differentiation at all feasible points.
4. Guarantee: IsMinOn f V x iff every inner(gradient f x,y-x) is nonnegative. Actual IsMinOn is the comparison predicate and does not supply membership.
5. Constants: non-strict zero threshold; gradient first, displacement y-x; no tolerance or scaling.
6. Information/probability: deterministic criterion, no optimizer selection, existence, uniqueness or convergence assertion.
7. Boundaries: boundary minima permitted with nonzero gradient; empty V has no given feasible x. Convexity only on V and one-point ambient differentiability make this a generalized library helper, not another printed theorem.

### BanditRL.OnlineConvex.minOn_finitePart_iff — accepted-with-explicit-delta

1. Objects: arbitrary EReal f, canonical F=toReal∘f, V and x.
2. Quantifiers: all such f,V,x; every comparator in V in each minimizer comparison.
3. Assumptions: x∈V and f finite at every point of V, explicitly both neTop and neBottom. No convexity, differentiability or topology of V; shared Hilbert context is unnecessary extra ambient structure for this order fact but includes source cases.
4. Guarantee: exact equivalence of original EReal and canonical real minimizer comparisons.
5. Constants: exact embedding/order transfer with no shift/scale.
6. Information/probability: deterministic order bridge, no existence claim.
7. Boundaries: both infinities allowed outside V; below-top alone is insufficient. Candidate membership ensures its value is also finite. This helper does not provide a neighborhood representation or use convexity.

### BanditRL.OnlineConvex.theorem_2_8 — accepted-with-explicit-delta

1. Objects: EReal f, canonical F, convex nonempty V, containing open U, candidate x; complete real inner-product ambient space explicitly generalizes Euclidean space.
2. Quantifiers: every f,V,U,x meeting premises, equivalence with every y∈V. No comparison outside V.
3. Assumptions: explicit hV/hne/hx retained; U arbitrary open with V⊆U, both infinities excluded on U, DifferentiableOn F U, ConvexOn V F. No convex U, no global noBottom, no global convexity or finiteness outside U.
4. Guarantee: IsMinOn original f V x iff nonnegative actual gradient inner product along every feasible displacement.
5. Constants: zero threshold and canonical gradient exactly. Finite U implies coe(F z)=f z on U, hence locally at feasible x; openness converts within differentiation to ambient differentiation.
6. Information/probability: deterministic constrained criterion, not an algorithm or existence/uniqueness result.
7. Boundaries/delta: boundary x allowed; no closedness or boundedness. Source neighborhood convexity restricts to convexity on V, while actual premise only requires the latter: a weaker premise and stronger theorem, not equivalent assumptions. Source real-valued neighborhood differentiability is represented by finite U; either infinity outside U is allowed.

### BanditRL.OnlineConvex.interior_min_iff_gradient_zero — accepted-with-explicit-delta

1. Objects: same f,F,V,U and ambient gradient vector, with x∈interior V.
2. Quantifiers: every such configuration at the given interior candidate; no existence of an interior minimum claimed.
3. Assumptions: same retained premises as theorem_2_8 plus ambient interior. Membership is also explicitly retained; relative interior is not substituted.
4. Guarantee: IsMinOn f V x iff gradient F x equals the zero vector; this is the required following unnumbered source consequence.
5. Constants: vector zero, not minimum loss zero. No uniqueness or strict-convexity inference.
6. Information/probability: deterministic equivalence, not a numerical stopping criterion.
7. Boundaries: no admissible x when ambient interior empty; zero-dimensional spaces allowed. Boundary gradient need not vanish. Pinned IsLocalMin.fderiv_eq_zero includes a nondifferentiable fallback-to-zero branch, but frozen hd and open U ensure actual differentiability at x, so the contract does not misuse fallback zero as source stationarity. Outside U infinities remain unrestricted.

## Anti-anchoring assessment

The source-to-target implication is legitimate by restricting neighborhood convexity to the already convex V; no converse or equality of regularity predicates is justified. A convenient interpretation using ConvexOn U entails convexity of U, but the actual target must not acquire that extra premise. No unproved claim of existence of arbitrary ambient extensions is made: the contract takes the supplied f and canonical F. Local finite equality makes derivative notation meaningful near feasible x, without importing Theorem2.7's global noBottom requirement.

Actual API inspection confirms IsMinOn is an order comparison; tangent-cone derivative nonnegativity consumes a genuine derivative, and Fermat's total fderiv has the stated fallback. Existing proof terms are consistent with composition of these APIs. Their fresh body/canary/axiom/native guard audit remains a separate required phase; scoped four-node graph and current type elaborations establish readiness only.

Existing canary designs are meaningful: positive-half-line loss on V=[1,infinity), U=(0,infinity) explicitly constructs source ConvexOn U then restricts it, has gradient1 at the boundary minimum and a smaller value at0.5 outside V; quadratic on open nonclosed V=(-1,infinity) has interior candidate0, gradient0, distinct values0/1. This source-contract review does not certify fresh canary execution or all boundary cases.

Mathematical repairs: none.

Required reader corrections:
1. Label the real criterion and finite-order bridge as library helpers, Theorem 2.8 as the printed theorem, and interior_min_iff_gradient_zero as its mandatory following unnumbered source consequence; do not imply four printed theorems.
2. Replace generic real-helper notes with its exact everywhere-real ConvexOn V, x membership and ambient derivative at x assumptions; no open set or finite-part bridge is required.
3. Replace generic finite-bridge notes: only x membership and both-infinities exclusion on V are required; no convexity, open neighborhood or derivative premise.
4. Describe ConvexOn V as a weaker convexity requirement giving a stronger theorem, not a strengthening of the source premise or an equivalence of assumptions. Source convexity on a neighborhood implies this restriction; actual target does not require convex U.
5. Make canonical F, finiteness on arbitrary open U and local embedded equality explicit; no global noBottom/finite/convex F condition outside U. Preserve ambient-interior qualification for gradient-zero, membership separate from IsMinOn, and retained differentiability despite the total derivative fallback.

Remaining: fresh retained-body/canary/axiom/guard review, combined root/Tests/full harness, corrected reader/site/registry/contributor, final independent reader and immutable package/PR gates. Four retained proofs, zero new definitions/proof code/registry nodes. Whole Goal remains active, Chapter2 incomplete with null total, other legacy migrations mandatory; no chapter/book/main/live/merge acceptance.

## Exact raw reviewed files

| Path | SHA256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean` | `c7a80e952f6f577c441b92802fc5020fa63b564b75418fb96e29d4f6813020ca` |
| `.lake/packages/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean` | `ec09dfe037c654dc65051e22fd9e1d76055ef340089a631c304b700d0406109e` |
| `.lake/packages/mathlib/Mathlib/Analysis/Convex/Deriv.lean` | `2022754e5f0c541b8ca4271231c95713996d9f4ac1f997e3973ec9e6c7bec7c4` |
| `.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean` | `bf69a9ed4bc39134bbefac1a43b187e2f1e66fd43f352d0810ab89474f054922` |
| `.lake/packages/mathlib/Mathlib/Order/Filter/Extr.lean` | `02b73ed141a3bc3e38da7a237f369cbdf8aad80dfa155572cc13e588334a4679` |
| `BanditRLProof/OnlineConvexExtended.lean` | `bd30bb95a46ccdc3f6d25f808c175af5fee71d075c2b46ffcf6508f15f1ed66a` |
| `BanditRLProof/OnlineConvexFirstOrder.lean` | `f2fcaccf9273a9b2a37e820da9885fbebc7f0e2693e84d073c1e32949073eb6c` |
| `BanditRLProof/OnlineConvexOptimality.lean` | `d344a22aca81221f865f3af1ccef6bb2bf445ae6f2f7cf7e97bfe5f88805ac1b` |
| `Tests/OnlineConvexFirstOrderCanary.lean` | `031451c1602cdcb5bd79054c589f6b9c9045d43273b2b1540b77d7bef768af6c` |
| `Tests/OnlineConvexOptimalityCanary.lean` | `9b6f671e8a528cdfe51dc7db7dd6de9340ce6ec1af1d1866a93dcb5b32b00e3d` |
| `conversion-windows/ONLINE-OPTIMALITY-MIGRATION-20261005.md` | `4fa2f342b338e8aebe298c9d3caa747b798a3f19e6bffe31dfaec5a866d1f84d` |
| `docs/contracts/online-optimality-migration-v1/context.lean.txt` | `1a34342fc7afc4552b6657071b9d1ac4a77796b5fdf66e57c2817dc3e3f8adb6` |
| `docs/contracts/online-optimality-migration-v1/interior_min_iff_gradient_zero-header.txt` | `c8232f23a0343f7e95ee9c6aadd2edd1d230e8a21ad3b37eab4aa07bdbdd3a92` |
| `docs/contracts/online-optimality-migration-v1/interior_min_iff_gradient_zero.json` | `e0c3a75ee1fc6172c64a71e2ead5de767ddb17fc4c34249c86fc9dee07773d3c` |
| `docs/contracts/online-optimality-migration-v1/minOn_finitePart_iff-header.txt` | `57b9f05b4fc060e74b5c8ca80357a23adf5d6a11bd1086289f5a41e36566c485` |
| `docs/contracts/online-optimality-migration-v1/minOn_finitePart_iff.json` | `4564cae4edafeeb28c00a2fa6445ebbd1e7c25fedc00de4a29206c233157ff21` |
| `docs/contracts/online-optimality-migration-v1/minOn_real_iff_gradient-header.txt` | `04d48f3b50142e7b5934205f465ed4e1de5ad82c7f445de86e079c455ef3f635` |
| `docs/contracts/online-optimality-migration-v1/minOn_real_iff_gradient.json` | `10bf50f16b5a8a84681df9cb23970a269fc277d75f7752b3046f206888ced553` |
| `docs/contracts/online-optimality-migration-v1/source-card.json` | `d30da5aafd465a8d59e3fa122d335969bfd66f412729b5573db4736eb4851181` |
| `docs/contracts/online-optimality-migration-v1/source-intent.md` | `57e6af9274912f62f233bebf106f706c883713eb13d77e99e26ff9e33dd2a960` |
| `docs/contracts/online-optimality-migration-v1/theorem_2_8-header.txt` | `a645cdfc0f759f4d6acbde11c7a921a866633f9b1b4bb0890a6ae3ebe5c5cb35` |
| `docs/contracts/online-optimality-migration-v1/theorem_2_8.json` | `d773c935a5133cc6e01a48fe99fcb33da712180b7accb0f26b86bbb908382966` |
| `docs/contracts/online-optimality-v1/context.json` | `8d78d606eca8f126630da4cb2c7eea6899d16f0cdf57367df22c734eb95bb741` |
| `docs/contracts/online-optimality-v1/contract.md` | `3b7207dee5f5b4c3e3b52415feb3178db49506f5214de62a6e56870085bb7e4e` |
| `docs/contracts/online-optimality-v1/headers.json` | `98760c94f2d8a7b0aba28d62e2231c98b4869a66f504b5f461d203c9ad1287b4` |
| `docs/contracts/online-optimality-v1/interior_min_iff_gradient_zero.json` | `cc495aa4dbd7f321ca28f26b7eb559c5522dd01fb9af2bbacc4e859a48fe887c` |
| `docs/contracts/online-optimality-v1/minOn_finitePart_iff.json` | `a345b2d4abd508bcfff85ccc532891029fa6045b28d8bd51f6b92de9b6ba6c48` |
| `docs/contracts/online-optimality-v1/minOn_real_iff_gradient.json` | `6b21f0b535a07a413a3428c1f4f351924949a5e22b9954ab8a430d5d53d72f42` |
| `docs/contracts/online-optimality-v1/theorem_2_8.json` | `cccaab81f91388e53c1a2d1be8be56e6e52e1a48e726024e09a6c1fdc2214f7c` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `proof-obligations/ONLINE-OPTIMALITY-MIGRATION-20261005.md` | `d7dab595a605b72218cd747334c49bf6826b67fd8c092c28f25289defed87fe2` |
| `runs/online-first-order-migration-20261005/accepted-decision-v1.json` | `2b5d59dbc78014ffc8c85e6fb333d9879cd833a0dba1223b46be59678abc4a8f` |
| `runs/online-first-order-migration-20261005/native-acceptance-overlay-v1.json` | `4c149fc45ec50d98c2190f51f5a7730e57d327c6d4900a37dda55329e591fb14` |
| `runs/online-first-order-migration-20261005/pr-delivery-v1.json` | `e5b057ceace37a4454366b4a2197dc481ce3fdf0b5f02755c79be51c0246acce` |
| `runs/online-optimality-migration-20261005/00_context.md` | `0da664cbbdb379a67134afbe7d0134efa8c6036c5aed64da1e7fcd3c81110a09` |
| `runs/online-optimality-migration-20261005/10_upper_director-v1.md` | `6edaf614e112f08a5dd285374ff009a745e616303b22516f73ec1cd05205cb03` |
| `runs/online-optimality-migration-20261005/20_architect-v1.md` | `5df33984127a58a26ae5baef2b51ac075cc1a722b4aebf2330dddf494a0d08e5` |
| `runs/online-optimality-migration-20261005/actual-pinned-API-retrieval-v1-01-exit.json` | `860965f1972aaa0e2b2cd06061b8c9b6450c8f09242ec86398bac24b38430e1a` |
| `runs/online-optimality-migration-20261005/actual-pinned-API-retrieval-v1-01.log` | `f1721d711ddb6aaa952d260d6f88144b52dcf10284fdc5e46eac899c68f00f79` |
| `runs/online-optimality-migration-20261005/actual-public-types-v1-01-exit.json` | `f4858add9c165f5ff0d19f84c28dcd83639c1407ed530e41b1e2e5bbabae9f47` |
| `runs/online-optimality-migration-20261005/actual-public-types-v1-01.log` | `f70a4e2d4b4b548dafef9314097aa320a12d18c8748da47e60e59097824e7553` |
| `runs/online-optimality-migration-20261005/actual-scoped-graph-v1-01-exit.json` | `238be44f13bfe5e92b064db8dae402835a4514dd266beaadca55e1a6abceffde` |
| `runs/online-optimality-migration-20261005/actual-scoped-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-optimality-migration-20261005/blind-packet-v1.md` | `4e1e1518278ede435073f62a8a238a3174119f653870b9ef07b02ef9532eb326` |
| `runs/online-optimality-migration-20261005/blind-receipt-v1.json` | `4d1fa15ba5abec1749ffeb2f8d579899a512adc9c193a552b2badbe39a842f5d` |
| `runs/online-optimality-migration-20261005/blind-reconstruction-v1.md` | `a70e98140df6d6c726027a7c1158b5d9e53ef43ee1f743fdb19b14876217f5aa` |
| `runs/online-optimality-migration-20261005/compiled-scoped-graph-v1.json` | `258457366c2b0300d34ac3f2bf44b8b54658073b5bc2bac79172579a683827ea` |
| `runs/online-optimality-migration-20261005/contract-source-inputs-v1.json` | `1e66a046cf03902392af7f030a86d23aa1ff0c5f5b023cafb15a6bf42ad96196` |
| `runs/online-optimality-migration-20261005/draft-fence-interior_min_iff_gradient_zero-v1-exit.json` | `04bd5f982f5a8590927205a831452185712cf674c832933e5eb519c53f978da9` |
| `runs/online-optimality-migration-20261005/draft-fence-interior_min_iff_gradient_zero-v1.log` | `410d0d0b7a229adc0cf71c1fdbe5450fcbe4a7b5180e2aafafe6d9138d3d569c` |
| `runs/online-optimality-migration-20261005/draft-fence-minOn_finitePart_iff-v1-exit.json` | `6aabcd68f494acf5330f2c1b89249090f930c8c6ca0f9f773c377c20f6f52384` |
| `runs/online-optimality-migration-20261005/draft-fence-minOn_finitePart_iff-v1.log` | `c4675971fd93d56f0104ce9fc4152b5b9cfc44642abfc64ec72cd08190697356` |
| `runs/online-optimality-migration-20261005/draft-fence-minOn_real_iff_gradient-v1-exit.json` | `cab11ef44496bbf2c5972a7e665fccebf493a9bd17f464da2bb894e3b82768c2` |
| `runs/online-optimality-migration-20261005/draft-fence-minOn_real_iff_gradient-v1.log` | `ba6ff48e7999244bfcb152da514acb687baedbf5fdfdc24843d69a765e9fc407` |
| `runs/online-optimality-migration-20261005/draft-fence-theorem_2_8-v1-exit.json` | `0144ecb602655add073cadf5cd1b4d322a2d31fdc59a318bb895306b78679a45` |
| `runs/online-optimality-migration-20261005/draft-fence-theorem_2_8-v1.log` | `50f19f116f024d75ffb15a1930ae71ecb2e925d0119a59eb7093bb5a95b61e52` |
| `runs/online-optimality-migration-20261005/draft-freeze-v1.json` | `1a4b16162a6da2361b5dfc9e595fab250fd9423500d10212915654a35532108e` |
| `runs/online-optimality-migration-20261005/draft-lifecycle-v1-exit.json` | `a6bb666682681464660a1d7f31be522d4f14b4ac6526b542b1809fd18d5b2a72` |
| `runs/online-optimality-migration-20261005/draft-lifecycle-v1.log` | `057d03f4150ad8f51b8647f84cc1e1536ce7980834b3f7205348583550a8af6f` |
| `runs/online-optimality-migration-20261005/existing-public-retrieval-v1-exit.json` | `8d1d13eaa82ab2772c7a8270ecdaa1e9ca01cec2ac6d201e3de0035cf268dcba` |
| `runs/online-optimality-migration-20261005/existing-public-retrieval-v1.log` | `5bfe436222dcba53f64eeb756930ae3adf2b3c0af29f7df2c1cb289360730097` |
| `runs/online-optimality-migration-20261005/leaves/actual-public-types-v1.lean` | `43b8d2817e36354b9f3e33277faa87cbc82f716b66db8e211db4702517ae3b27` |
| `runs/online-optimality-migration-20261005/leaves/export-scoped-dependencies-v1.lean` | `3275d519824797f901159c6c9a649e0177f7c71d92356d4f81aea0583cfa400c` |
| `runs/online-optimality-migration-20261005/native-draft-fences/interior_min_iff_gradient_zero.json` | `410d0d0b7a229adc0cf71c1fdbe5450fcbe4a7b5180e2aafafe6d9138d3d569c` |
| `runs/online-optimality-migration-20261005/native-draft-fences/minOn_finitePart_iff.json` | `c4675971fd93d56f0104ce9fc4152b5b9cfc44642abfc64ec72cd08190697356` |
| `runs/online-optimality-migration-20261005/native-draft-fences/minOn_real_iff_gradient.json` | `ba6ff48e7999244bfcb152da514acb687baedbf5fdfdc24843d69a765e9fc407` |
| `runs/online-optimality-migration-20261005/native-draft-fences/theorem_2_8.json` | `50f19f116f024d75ffb15a1930ae71ecb2e925d0119a59eb7093bb5a95b61e52` |
| `runs/online-optimality-migration-20261005/new-task-v1-01-exit.json` | `f7b1b59b98995c952d67ae34c299c6c0a8cca6b89741e44f68f8f07d5153dd49` |
| `runs/online-optimality-migration-20261005/new-task-v1-01.log` | `261ddf3f6a5d2d69d9cd57f3035070010b3cec4e5bf774d5a91d5c8f3034bd48` |
| `runs/online-optimality-migration-20261005/original-OnlineConvexOptimality.lean.txt` | `d344a22aca81221f865f3af1ccef6bb2bf445ae6f2f7cf7e97bfe5f88805ac1b` |
| `runs/online-optimality-migration-20261005/original-OnlineConvexOptimalityCanary.lean.txt` | `9b6f671e8a528cdfe51dc7db7dd6de9340ce6ec1af1d1866a93dcb5b32b00e3d` |
| `runs/online-optimality-migration-20261005/prepare-draft-v1-01-exit.json` | `ef9e013ba7ffc43f399ad205387af57568e16b80282148c721b8ada4ff238019` |
| `runs/online-optimality-migration-20261005/prepare-draft-v1-01.log` | `26cba334670492ed6f9ff1c5cea9488fd26b59b99c0705903de80ae8dc700e2b` |
| `runs/online-optimality-migration-20261005/prepare-draft-v1.py` | `c871ca66683cbc4cccfe56f5be541766a9f9f530c101b96e8efed66445fce5db` |
| `runs/online-optimality-migration-20261005/prepare-source-review-v1.py` | `19e047cc6b2a75cf4e3710bee9e32e2b82dc49a50475fb721cdc558219906747` |
| `runs/online-optimality-migration-20261005/proof-obligations-v1.json` | `e1504fe40e6e7b41ef81b02bdb5804d202b56e5d8c0273369ba553813ee66ee8` |
| `runs/online-optimality-migration-20261005/ready-dependencies-v1.json` | `c2fddee2d8453bfcdc38fab9338a390ad6ba679b464d84e35ae0510abfc51666` |
| `runs/online-optimality-migration-20261005/retained-module-types-v1-01-exit.json` | `f96d4e6beba0eaff5430f160afd9d275aaa36257796074cc01ccfe3a312dcad5` |
| `runs/online-optimality-migration-20261005/retained-module-types-v1-01.log` | `9b112e6daa6b3de9a6eeb488a1dd00209bbce0f64911dee43a1fe1580aec524c` |
| `runs/online-optimality-migration-20261005/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `runs/online-optimality-migration-20261005/source-printed10-11-pdf22-23.txt` | `aa1beb88cb259fd36ccd1131074d331b44cf2d0e8fd768c0c60023881d0071da` |
| `runs/online-optimality-migration-20261005/source-review-packet-v1.md` | `e5ee7ea073e9e0d3dc53fdd5c0f0ea7ff3e46767e5e2e7845d1ce9ab2fcf7da3` |
| `tasks/ONLINE-OPTIMALITY-MIGRATION-20261005.md` | `1baab747439a4c987079657150b7ebf8d7ca14abd2ea34c19ad0d9fc52395be9` |
| `tmp/online-optimality-migration-scoped-graph-v1.json` | `258457366c2b0300d34ac3f2bf44b8b54658073b5bc2bac79172579a683827ea` |
| `tools/abrl_lifecycle.py` | `7615541e66a372e939ea2d18684ce78a8f3d8f1202894840ef7fdfdc703c4310` |
| `website/content/chapters.json` | `b5a628fe0ea139e68800b76b6a758718107aef653b13ae3a5689365af7f0e258` |
| `website/content/highlights.json` | `bb1b125ec8102d7f37732b8380c40c39b942d4a13852ea85e4cbd390d2251181` |
| `website/content/readings.json` | `c0e6b55ff60780ed82eba4585f2e105c75b152b43842e775ccd8e138dc15a8d2` |
