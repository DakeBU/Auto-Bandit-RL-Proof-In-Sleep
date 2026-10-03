# Theorem 2.28 candidate body source review

Verdict: **accepted-with-explicit-delta** for actual affine-full-01 and affine-canary-03 scratch bodies. No mathematical repair required. Actor `/root/source_reviewer`; requested GPT-6 Astra / medium; distinct automated reviewer, not external-human.

Read scope: entire candidate and entire canary03, success logs/exit records, frozen fence/stabilization and this actor's source/blind contract package. All prior source-contract receipt rows were freshly rehashed and unchanged. Original pinned PDF remains `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`; Theorem2.28 is printed18/PDF30. Imported interfaces reviewed include the actual adjoint definition/inner identity, shared global support/proper definitions, absolute-value zero-support interval and affine constant-support helper. Whole dependency files are bound below, without a new audit of all unrelated declarations. Failed canary01/02 tail diagnostics were inspected as rejected history.

## Seven semantic slots

1. **Objects/model.** Actual A:E->L F and actual A.adjoint represent arbitrary finite-dimensional Euclidean matrices and their transposes. The composition is literally fun y=>f(Ay+b). Both finite dimensions and arbitrary f,b,x remain in the exact frozen statement; zero dimensions are not excluded. Completeness is inherited, not an additional source premise.
2. **Hypotheses.** SourceProper f is explicitly retained, although the direct global-inequality proof does not use hp. This harmless unused-variable warning does not remove the hypothesis or add convexity. No rank, nonzero-map, query-finiteness, h-properness, continuity of f or nonempty-support assumption is introduced.
3. **Actual producer.** The inclusion destructs an arbitrary actual image witness q=A.adjoint g and its source support hg. For every y, it invokes hg at A y+b. The proven identity (Ay+b)-(Ax+b)=A(y-x) uses map_sub and additive cancellation. The genuine adjoint_inner_left rewrites the real inner product inside the EReal inequality. The transported inequality is exactly the target support. No oracle, selected support, differentiability or consumer decomposition supplies the conclusion.
4. **Quantifiers/globality.** The proof handles every image vector via its witness and every ambient y. It does not restrict tests to finite values or a feasible set. It neither assumes existence of source supports nor constructs one unnecessarily. Proper f may have an empty source subdifferential; the set inclusion remains meaningful.
5. **Guarantee/direction.** Only adjoint image inclusion is proved, in the source direction. No reverse inclusion or equality is smuggled in. The concrete strict-inclusion canary separately proves its left set empty and right set {0}, plus inequality of sets; those fixture equalities do not strengthen the general terminal.
6. **Actual canaries.** doubleMap is 2 times identity; double_adjoint derives A.adjoint g=2g from the actual adjoint identity. The shifted absolute-value fixture has nonzero map and translation, evaluates at -1/2 where 2x+1=0, takes the genuine absolute-value support1/2 and uses theorem2.28 to obtain support1 for |2y+1|. negAbsLoss=-|y| is proved proper. Its supports at0 are empty by evaluating global inequalities at +1 and -1. Nonconvexity is independently proved from the epigraph points (1,-1),(-1,-1), whose midpoint would force 0<=-1. The zero-map composition is actually identified with finite constant0; the affine helper proves its subdifferential {0}. The source theorem is truly instantiated with this proper nonconvex f, and empty versus singleton proves strictness. All five printed audit targets are genuine theorems.
7. **Source/conventions/evidence.** Exact frozen fingerprint `82587fe92f5705cd28adb86e7e554c97855a1930f46f660d79a5fc0a6fca2f76` matches the source-fence result. The source proper-only inclusion and blind reconstruction agree. For an improper identically-top composition, the literal global-support convention yields all target vectors, but source properness makes the source support empty at that infinite query. This vacuous boundary remains explicit; no h-properness or improper-loss optimization claim is added.

## Deltas, compilation evidence and limits

Accepted deltas remain coordinate-free finite-dimensional spaces, automatic-continuity CLM packaging and actual adjoint as transpose, plus EReal with properness excluding bottom. The general inclusion covers zero-dimensional spaces but these five fixtures do not separately instantiate zero-dimensional types.

Full01 and canary03 recorded scratch command exits are0. The terminal and all five printed canary targets list only propext, Classical.choice and Quot.sound. Canary03 includes a nonfatal ring diagnostic and sequencing warning; these are accurately retained and not represented as a clean public OLEAN build. Failed canary01/02 logs contain sorryAx recovery artifacts and are rejected, not accepted axioms. Prior failed API retrieval is also still failed history.

This receipt certifies candidate-body source fidelity with the recorded scratch evidence only. Public OLEAN integration, public axiom/header checks, roots/Tests/full harness, final reader/site/graph/registry, immutable binding and PR acceptance remain pending. No native trial/global mutation or production edit was performed. Chapter2/book and later Lipschitz/OSD/linearization/older migration remain incomplete.

## Raw SHA256 inventory

Exact raw bytes; no normalization or JSON reserialization. File hashes bind the scoped inspection stated above.

| File | Raw SHA256 |
|---|---|
| `docs/contracts/online-affine-subgradient-v1/context.txt` | `a342da47300bae3633d237c96013bd9edcdef874d8d52d3b3e1bc9b5179dc4b9` |
| `docs/contracts/online-affine-subgradient-v1/contract-manifest.json` | `c0540d686c86f11a9bca48bb2376a7c300cf07a085aa858743744f0bef57ace4` |
| `docs/contracts/online-affine-subgradient-v1/contract.md` | `bb647512bf5dcd2bdacf4da11132e257fb57d0f8beed912fccb0b38cf86ae6b2` |
| `docs/contracts/online-affine-subgradient-v1/theorem_2_28-header.txt` | `1c7fff1f7dbd471b029a7aed7d47d3d0b5d3f8ae828429774bb11ccc8e4849fb` |
| `docs/contracts/online-affine-subgradient-v1/theorem_2_28.json` | `2ee307d726ce4619233cfc972b596f5505e547b26e252e1994b7d7de0d1cb67d` |
| `runs/online-affine-subgradient-20261003/source-pages.txt` | `9e93fc254cfc06e8a62823cddffef15342a66b894950eb1e6c663b573018138f` |
| `runs/online-affine-subgradient-20261003/blind-packet.txt` | `15f8efe0e055c0a7a31d98797820e2ee2f16c76fe2b2fee68b6416e5898109d1` |
| `runs/online-affine-subgradient-20261003/blind-reconstruction.md` | `d0c5bc057fe415437c69a6967161c819bf36103891b0834339666398dde6b42b` |
| `runs/online-affine-subgradient-20261003/blind-receipt.json` | `0e23cab3d8f1fab90d14db62d3b45c564527ff76bf464946c727154a9614b7fe` |
| `runs/online-affine-subgradient-20261003/api-probe-01.log` | `9d76b077a82c1110269c729221d8a9b13c2c158a8733cb3988d1a59f272f2bea` |
| `runs/online-affine-subgradient-20261003/api-probe-01-exit.json` | `da2ebddd3f12621d330c409c87f0fc1c01fc2a5f464671bdbddddb03b85b9988` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean` | `ffa28bc6ab970495e53c01337b42aee7b047644eb954a253b491a5104e409735` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `runs/online-affine-subgradient-20261003/source-contract-review.md` | `6e80a7242b2bc93ea461ff5b425100738b151200ef33cee9eefe1c622fb6907d` |
| `runs/online-affine-subgradient-20261003/source-contract-receipt.json` | `e48bad7a598f6759154bbcb904de3114a8902c61779d02686a25acc88e2112c9` |
| `runs/online-affine-subgradient-20261003/stabilization.json` | `3767c0fbd90f120cd8417d9379076b097000f3782b9dc5f51762cc014d6dcdee` |
| `runs/online-affine-subgradient-20261003/source-fence-check.json` | `d66948bea34f30ed169cb6a965ef5943b46f4f403af806cf739de412e3e9ba5e` |
| `runs/online-affine-subgradient-20261003/attempts/affine-full-01.lean` | `202753092b792ee86d69b6ce34cecaf9496656ab13e356e93cd2631e9c3db6d3` |
| `runs/online-affine-subgradient-20261003/attempts/affine-full-01.log` | `b423e596db130e5a349ba2d51ccf26c1e4697ba72b53fb284e08a7b0eb566292` |
| `runs/online-affine-subgradient-20261003/attempts/affine-full-01-exit.json` | `9e45588c8029b26b3a727dfefa20526f44db1fa14f1ad73eab8af5683315ea22` |
| `runs/online-affine-subgradient-20261003/attempts/affine-canary-03.lean` | `73caa720f02ab7b8658ffe13afda5a986b8163a75d65220a75bc28f09108c68d` |
| `runs/online-affine-subgradient-20261003/attempts/affine-canary-03.log` | `4c97514352c6045bd48ce33d44246a5581e7581a40f0c31a51482324548dc2a9` |
| `runs/online-affine-subgradient-20261003/attempts/affine-canary-03-exit.json` | `c723089da0a1df05dfbf5349b89840db07a5ea4547cb02f6851202a240a80515` |
| `runs/online-affine-subgradient-20261003/attempts/affine-canary-01.log` | `48e8f163ba071906b6cfeb7ca2482a0d3e20039789c35785bf7147107d3cabd3` |
| `runs/online-affine-subgradient-20261003/attempts/affine-canary-02.log` | `005073df62108995aefc61aeafed968834056b8fa5efb47e9ffbb08223f2dbe0` |
| `BanditRLProof/OnlineSubgradientAbsolute.lean` | `17157c976889f078d02f183b55edf2821e29efa5aa32d4bfff309c2b3713db0c` |
| `BanditRLProof/OnlineHinge.lean` | `118d28177c11b0ff113fba5ab34a6bbd9190fee5fb05af644b7b2207c05b020b` |
