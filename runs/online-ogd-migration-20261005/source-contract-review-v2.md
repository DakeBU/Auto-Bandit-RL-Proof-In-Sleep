# OGD migration v2 source-contract review

**Verdict: accepted-with-explicit-delta for contract stabilization only.** The two definitions and twelve unproved target signatures repair the v1 source-regularity obstruction without changing the actual learner. No required header repair found. This does not accept any new proof body or declare the old source-coverage gap already closed by compiled mathematics.

Actor `/root/source_reviewer`, distinct automated source reviewer. Requested GPT-6 Astra / medium; runtime model not independently attested. No external-human or external-model review claim.

All 215 fixed raw rows were independently read and rehashed with no drift. The actual two new definitions, twelve native headers/fences, source-intent, fresh restricted blind reconstruction/receipt, original source and v1 rejection were inspected. The frozen native statements were independently extracted and match all twelve hashes. Context SHA256: `4b6e9596c4a88142cc735be1a0c09ce8537223fcf16f4357a7bc02701a0b19c3`. Original PDF hash independently remains `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`; physical20 and23–27 were freshly extracted. Physical20 is printed8 and declares losses V→R; Algorithm2.1 on physical24 requires the specified differentiable ambient behavior. Type probes native/neutral exit0 elaborate Prop definitions, not the twelve proof bodies. Empty by slots in target text are not accepted Lean proofs.

## Repair scrutiny

`SourceRegularLoss` asks for an arbitrary open U containing V, convexity of f on V, and DifferentiableOn on U. It does not require ConvexOn U or convex U. `FeasibleRegularLoss` asks for ConvexOn V and ambient DifferentiableAt at every feasible point. For x in V, openness of U supplies a neighborhood at x, allowing DifferentiableOn to imply the ambient derivative. Thus source_to_feasible is a correct proposed implication; it remains a required unproved producer. The reverse implication is neither claimed nor needed. regular_to_feasible restricts the old convex neighborhood to convex V and takes derivatives locally, preserving compatibility without reviving the false source-to-old-RegularLoss assertion.

The v1 globally convex max(exp(-x),y) example on the horizontal line meets the new source predicate and feasible predicate, despite lacking an open convex differentiability neighborhood. Therefore this repair genuinely addresses the unbounded obstruction. It does not rely on bounded finite-dimensional compactness and remains meaningful for the declared complete-Hilbert generalization. The compact-neighborhood caveat in v1 remains true, but is not needed here.

Source losses are real on V. The formal function is a supplied ambient real extension with the specified derivative. Values outside its open differentiability neighborhood can be totalized without affecting the derivative on V, and need not be convex there. This representation is legitimate for the source's differentiability setting, but is not an extension-existence theorem for every arbitrary function on V. For a thin V, restriction alone does not determine the full ambient gradient; the contract fixes the extension and does not claim all extensions have identical gradients or trajectories. The source algorithm's gradient is interpreted using that same supplied extension. No EReal/toReal finiteness conversion occurs.

## Per-target seven-slot comparison

All rows use the same complete real inner-product space (source R^d specialization), nonempty closed convex Domain, and real-valued losses unless the row is a linear/vector helper. Verdict for every row: accepted-with-explicit-delta as an unproved contract. Slots are objects, quantifiers, assumptions, conclusion, constants/indexing, information order, and boundaries.

| Target | Objects | Quantifiers | Assumptions | Conclusion | Constants/indexing | Information | Boundary/delta |
|---|---|---|---|---|---|---|---|
| source_to_feasible | V,f, two predicates | every V,f | source arbitrary open U | feasible regularity | no numerical terms | deterministic local derivative implication | forward only; U need not convex; proof required |
| regular_to_feasible | V,f, old/new predicates | every V,f | old RegularLoss | feasible regularity | none | compatibility implication | no reverse and no unrestricted source-to-old implication |
| linear_regular | V, inner(g,·) | every g,V | domain/space only | old regularity for true linear function | coefficient1 | constructed linear model | g=0 and unbounded V allowed; helper not source theorem |
| gradient_linear | g,x | every ambient pair | space only | actual gradient=g | no factor2 | actual deterministic gradient | all points/zero vectors; no oracle assumption |
| first_order | f,x,u in V | every feasible pair | feasible regularity | loss gap ≤ inner gradient displacement | coefficient1 | gradient of same f at x | ambient derivative, including boundary/thin V; support must be proved |
| lemma_2_12 | same f, actual step | every feasible x,u,eta | feasible regularity, eta>0 | both source inequalities | eta, eta²/2, both distance halves | current gradient then same old projection step | no boundedness or assumed one-step certificate |
| theorem_2_13_fixed | old iterate/regret | every T,u in V | eta>0, feasible init, regular losses before T | sharp source bound | terminal iterateT, negative/(2eta) | same current-loss recursion and gradients | T0 allowed, no diameter/gradient bound |
| variable_one_step | old scheduled iterate | every t,u | feasible init, local regularity and eta_t>0 | actual current gap upper bound | t+1 and current eta_t | same prescribed schedule/run | other-time positivity not required; no horizon bound |
| theorem_2_13_variable_bound | scheduled run and D | every positive T,u | positive nonincreasing used steps, regularity, pairwise D | sharp decreasing-step bound | eta(T-1), individual eta_t weights | actual scheduled gradients | D0 permitted; nonempty V forces D≥0; no bounds after horizon |
| theorem_2_13_variable | scheduled run, Metric.diam | every positive T,u | bounded V plus previous horizon hypotheses | exact finite-diameter bound | same last eta(T-1), negative terminal | same trajectory | boundedness explicit; zero diameter valid; no compactness premise |
| equation_2_1_distance | actual tuned run,u | each positive D,G,T, feasible u | feasible regularity, distance≤D, same tuned-run gradient≤G | regret≤DG sqrtT | eta=D/(G sqrtT) | given horizon-prescribed run | D,G,T0 excluded; no all-domain distance requirement |
| equation_2_1 | one tuned run | parameters first, then all u in V | positive D,G,T, pairwise D, actual tuned gradients | simultaneous comparator bound | exact coefficient1 | no comparator-dependent rerun | no anytime/optimizer/future-energy claim; G is source L |

The definitions, algorithm names and terminal formulas align with the fresh blind reconstruction M01–M12. In particular, the output at Lean t precedes use of loss t; source round1 is Lean0, and outputT is source x_(T+1). Fixed and variable regularity premises cover only t<T. All gradient-energy terms refer to the same trajectory as regret. Prescribed exogenous schedule is not a claim about how an external caller chose it; the existing conditional prefix behavior remains the relevant information boundary.

## Proposed proof route, not proof acceptance

The existing convex_gradient_lower_bound has exactly convexity on V and DifferentiableAt at x, so it is a genuine dependency-ready first-order producer. The quadratic part can be obtained from the old true lemma on the actual linear function inner(g,·), after proving linear_regular and gradient_linear and identifying its projected update. This uses the old theorem in a regime where its assumptions really hold, rather than assuming the desired inequality or falsely converting the new loss to old RegularLoss. Cumulative endpoints must still perform actual telescoping/weighted potential on the old iterates; tuning must still establish positive denominators and actual-run energy bounds. These are mandatory body obligations, not certified by plausible route or Prop elaboration.

No assumption of global real convexity outside V, convex open neighborhood, bounded fixed domain, or equality of independently chosen extension gradients has been silently inserted. Hilbert generalization, local feasible regularity stronger-in-conclusion interfaces, real ambient extension representation, positive tuning parameters and T0 structural extension are explicit deltas from printed presentation. Twelve declarations are library refinements, not twelve numbered source results. `FeasibleRegularLoss` is weaker than source neighborhood regularity; accepted scope relies on the forthcoming forward adapter, never an equivalence assertion.

## Required follow-through and limits

No versioned-header correction required. Prove all twelve targets, including source_to_feasible and compatibility/linear producers; test the repaired source regime and nonzero sharp residuals. Preserve v1 rejection and old bodies. Later qualify the old RegularLoss source comment and reader attribution with an explicit historical raw snapshot/supersession; this review does not authorize rewriting historical evidence as if it were already correct. Public integration, new body/canary audit, root/Tests/full harness, actual axioms and proof graph, contributor coverage, final reader, immutable binding and PR remain separate future gates. Chapter2/book/Goal/main/live are not accepted.

## Frozen statement fingerprints

| Target | Native statement SHA256 |
|---|---|
| `source_to_feasible` | `f8e1e9a9fa54be0ce5c0a475cd2eb9f1cb4e6d5952232c4504e7dd61da8fe51a` |
| `regular_to_feasible` | `e0e5d3a46190ba3a8141e949a812289323ce72ca58f57d39c5ae94df738e78b6` |
| `linear_regular` | `649ee8af6916b37981f379dde4c347e5fa1cb50856f9ee83745bc7df3e8eb984` |
| `gradient_linear` | `67caaee1c88c722aa87c5bf75bdfb30a3e1f133fbdedc53546577d2d71dbcbd9` |
| `first_order` | `a7a5b6ce779055f0fab88f539e643279297322fb8e0f10ad7826e4068223680f` |
| `lemma_2_12` | `eed9c690eb624b6e8e1f1f536900ae25126a901ac7039bc62bcd89dfba76382b` |
| `theorem_2_13_fixed` | `bc812920a17ad0120087fd3c0cec8adcd137a7331f385c411894c87e3c6c8986` |
| `variable_one_step` | `44b9e27a41e32289642634e77b5337b194414f1fb285c44b44d675f24dba8763` |
| `theorem_2_13_variable_bound` | `6c560c38b4703eaec4c7ece312373d8aa32246b7e8de5b163801ce07b26bb845` |
| `theorem_2_13_variable` | `a2e245b1ae6956dbe503326db11d53a1a2f509ddec20c9f6de3fb7684f177119` |
| `equation_2_1_distance` | `5993e955540d98b50be715bfd21535428398b536d6bdc6d7043d3319f8516f2a` |
| `equation_2_1` | `bdc8c47e546e74414ee64ddaff58accf743448efed02575e136fcc650da28d02` |

## Actual raw inventory

Raw hashes include integrity checks of retained history, not semantic re-certification of every historical workflow. No normalized JSON and no receipt self-hash.

| Path | Raw SHA256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `BanditRLProof.lean` | `ec4c531329bc808fa055e92c5d3035fb318b92c58c62948cd218c52f157a29e1` |
| `BanditRLProof/OnlineConvexFirstOrder.lean` | `9921bf1ed9391ddf01221be77f0321cc72a3caa4c1c97b058da3e145d8b2c60e` |
| `BanditRLProof/OnlineGradientDescent.lean` | `e7edba540c2f60032bb4a34aaf0768b3107b94276b67b6f41fc289009c8924c1` |
| `BanditRLProof/OnlineGradientDescentVariable.lean` | `674bbb07ace34bfb03019fa6a933d3ea02cf7ebf0972e1e36a9c65b82efe772f` |
| `Tests.lean` | `da5f0b84ea0ff79ed17f276ee8283ae7222b82b7771a3f75fdb49b8a92c8aeb5` |
| `Tests/OnlineGradientDescentCanary.lean` | `f2a05231cbbb2b1428d7d2924a9f83e45042c769603784abb9e53a19916344f0` |
| `Tests/OnlineGradientDescentVariableCanary.lean` | `0a7b69d9674c2b3a15e2932c048c2f4ee0fc0be81ff7ba338320ddf63a7eb7c2` |
| `docs/contracts/online-book-v1/coverage.json` | `fd7580c2d0ec040352317d3c53dc583a6b9b75a68b4026ebf3b38f7010a98f1e` |
| `docs/contracts/online-book-v1/source-inventory.json` | `a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7` |
| `docs/contracts/online-ogd-migration-v1/context-v1.json` | `4897851d8f4a67381ce700a24f8610cee20842df334682de8f63dec5a1e9ff1c` |
| `docs/contracts/online-ogd-migration-v1/equation_2_1.json` | `c4f2f9c33cd277d1ccbf4f45950ce2a4d569f1a80e1ff85d326f7422db78403a` |
| `docs/contracts/online-ogd-migration-v1/equation_2_1_distance.json` | `45395d003416e824027e8e3af83bc1df69ab2b4efa2f0e42841c44c18cc63de9` |
| `docs/contracts/online-ogd-migration-v1/first_order.json` | `b484652655535a19a005cd7da8ff85f506984510f35613c030043ea4ca1009a5` |
| `docs/contracts/online-ogd-migration-v1/iterateVariable_mem.json` | `7f06f8225162d692fe1624d773f86b1f1463efe2108b731e496c06fdb7a324c6` |
| `docs/contracts/online-ogd-migration-v1/iterateVariable_prefix.json` | `0f39d1de20afb510af5af07d064689c85cc72b19e05cb7e041cb4c57f52311ed` |
| `docs/contracts/online-ogd-migration-v1/iterate_mem.json` | `5f803bc1d8834f7c348152fe3a5bb95676763790112ea9e22e96cd747857e2de` |
| `docs/contracts/online-ogd-migration-v1/iterate_prefix.json` | `135b5263edd9d3b088cf34e4a82667d7bc9f067a87ab4c7c477f43d0a9d62505` |
| `docs/contracts/online-ogd-migration-v1/lemma_2_12.json` | `f8cc148cdb719994f0996816622fa2166eb133274924dfd3bf866062ec96dd0e` |
| `docs/contracts/online-ogd-migration-v1/native-headers-v1.json` | `0a8605af476c48110b65dd5a5aff2c5ed64c38860577b6d9eb39305f7504d97d` |
| `docs/contracts/online-ogd-migration-v1/project_eq_of_variational.json` | `5172dbfe4e2371cd662d59d32fcd015478d2d98e34eaed6a1066797129745ea5` |
| `docs/contracts/online-ogd-migration-v1/project_spec.json` | `bc576e4c4705238e110df193df082de0a6b474059613f4c2a49f8f3931169567` |
| `docs/contracts/online-ogd-migration-v1/proposition_2_11.json` | `48cb5e0874829d7a8461bb908afc9839842b66df037de5bfab04ae1822bab743` |
| `docs/contracts/online-ogd-migration-v1/theorem_2_13_fixed.json` | `83a5f6f9cbd2ff3da3f418163c12344dd10febee358dcefa54080c6f3c0df8f4` |
| `docs/contracts/online-ogd-migration-v1/theorem_2_13_variable.json` | `201c0db249a79a6de27187392f02c341cad6dafca092bbbdd105a6c2a59e5b0a` |
| `docs/contracts/online-ogd-migration-v1/theorem_2_13_variable_bound.json` | `077151a91a30e56162b2ad3b14b9123e1379a663715e2aeea20befca07304c73` |
| `docs/contracts/online-ogd-migration-v1/variable_one_step.json` | `77e93054fd1f5e23d9b81bf58d3801f48747a65a26bfc0d57951e82f192359ca` |
| `docs/contracts/online-ogd-migration-v1/weighted_potential_sum.json` | `9da4d9998d3b4f1e90169b2ad6671a6884b2ea66213fb296bf49af74e8680c5d` |
| `docs/contracts/online-ogd-migration-v2/context.lean.txt` | `4b6e9596c4a88142cc735be1a0c09ce8537223fcf16f4357a7bc02701a0b19c3` |
| `docs/contracts/online-ogd-migration-v2/equation_2_1-header.txt` | `0301191a23ac3e0fe9828a113b5769aea78c57541b9841b2bdbedbfe6f2e804d` |
| `docs/contracts/online-ogd-migration-v2/equation_2_1.json` | `19bac5f0365ba8be887a7e97e12ef670b18a7a1213c6602ce8c2811e861245a8` |
| `docs/contracts/online-ogd-migration-v2/equation_2_1_distance-header.txt` | `e5ded7289866b99f08704cada7841a8143de5edd585ffe02d335db48a01cf90f` |
| `docs/contracts/online-ogd-migration-v2/equation_2_1_distance.json` | `3de760f330648569c8bb68e997294938e79f8ccda182b3839d07fcfd3b5dfb65` |
| `docs/contracts/online-ogd-migration-v2/first_order-header.txt` | `2f4103e0201a1d071b21481218d654145de1d48acf71b4a94097b45252a52f9a` |
| `docs/contracts/online-ogd-migration-v2/first_order.json` | `e14747f836da70dec4e28bdd9da2596bada0d365fa99875454f76cd2b4778881` |
| `docs/contracts/online-ogd-migration-v2/gradient_linear-header.txt` | `2444b9a653dcea019aca3a569c78b540d3a9e4a13ba5c2ac5aefe3381b763803` |
| `docs/contracts/online-ogd-migration-v2/gradient_linear.json` | `6b1e8906d6efb0af6533a0bceb5a19bb36d13b28d0fee350e08a09be6557d19c` |
| `docs/contracts/online-ogd-migration-v2/lemma_2_12-header.txt` | `9987e67b542faa0743b00187961832e4e26cc91543c175015b7eed9360252390` |
| `docs/contracts/online-ogd-migration-v2/lemma_2_12.json` | `14a0b2c99b458603e81d4c5bfc3ae8bd50ce2c5382048f09b37cc79c43474a50` |
| `docs/contracts/online-ogd-migration-v2/linear_regular-header.txt` | `501894dc2346032efeb7b3bc8cb786b754cee0c132e3c23d4623d3ded94abaeb` |
| `docs/contracts/online-ogd-migration-v2/linear_regular.json` | `69017ba1fbe4a31fcc4985662b3a75d984539662c35a9838892a38afa7935f16` |
| `docs/contracts/online-ogd-migration-v2/regular_to_feasible-header.txt` | `c1bc9cb051d5021ba461480d75eaca7af7bce3cc7335ab8a663deff730aa1a06` |
| `docs/contracts/online-ogd-migration-v2/regular_to_feasible.json` | `9475db7a26bb4f50b4e19230f15a1da0d8aaf3b773f5ce3e508bf06274e6c873` |
| `docs/contracts/online-ogd-migration-v2/source-intent.md` | `0f533b904ad6cf7b28a3cfaa4e1ca3a2959fbef04aead61c088fc90c972290b7` |
| `docs/contracts/online-ogd-migration-v2/source_to_feasible-header.txt` | `97e6a163bd25e684f08c9f15b9afa2bf449d8439ed2bf11848ae32658d6f7b2f` |
| `docs/contracts/online-ogd-migration-v2/source_to_feasible.json` | `fcda5ce964eb00a3aca3df9bbf16bb6db6a9916af122a55c8c72804d0f2468a5` |
| `docs/contracts/online-ogd-migration-v2/theorem_2_13_fixed-header.txt` | `1d81128b3f5defa7c65d900616a5ad39c9ad854e3477210b2d4838771e2ecbce` |
| `docs/contracts/online-ogd-migration-v2/theorem_2_13_fixed.json` | `f1d4a2237017c6a14a15461e834dbad9aa39b6f8273a38e5929d9da1dc85d29e` |
| `docs/contracts/online-ogd-migration-v2/theorem_2_13_variable-header.txt` | `11a925a53057617a72ab63e347b0ec6a0f2b8b8ae065be59858c0c32dd783eaf` |
| `docs/contracts/online-ogd-migration-v2/theorem_2_13_variable.json` | `f17d2160dc9a6e23aebb0e0eadb34b37896331a53cea8f44af118932848641d4` |
| `docs/contracts/online-ogd-migration-v2/theorem_2_13_variable_bound-header.txt` | `32d5a7bd5da5385ce548d2d88ca2edfde18bf31b475272cd27415a635dd259ae` |
| `docs/contracts/online-ogd-migration-v2/theorem_2_13_variable_bound.json` | `cfe0c8e50b23cbe57384f85f87e4315897dc363d6841835808ab752d0f882818` |
| `docs/contracts/online-ogd-migration-v2/variable_one_step-header.txt` | `c7f54770285f3ee91a5d2f2332e3e14ed0430f26a68e993e2bd2426f5fe8c279` |
| `docs/contracts/online-ogd-migration-v2/variable_one_step.json` | `9f0b2e66e0592ff70cff8445b8f218b32312e5b31001158e5ed371ed4cc75d44` |
| `docs/contracts/online-ogd-v1/contract.md` | `31988e3576d234159fdefc04a3419348172093aee9c6bd9cd9b0930664f48573` |
| `docs/contracts/online-ogd-v1/definitions.json` | `45a542906cd85313976016d7152cb818dc4b4f750408d081467c87aa0c490d94` |
| `docs/contracts/online-ogd-v1/equation_2_1.json` | `9035ac957a26ceb6258106470f06b1b0cea356989936a0f071f849323cd5312c` |
| `docs/contracts/online-ogd-v1/equation_2_1_distance.json` | `2bed4fc53ca0456ead937a7a68cff03a558223bd0ff108d43958787662a0ca61` |
| `docs/contracts/online-ogd-v1/fences/equation_2_1.json` | `043ca7b6ec89f813472e9772fdf933728b5e903775808912edf42621c80e871e` |
| `docs/contracts/online-ogd-v1/fences/equation_2_1_distance.json` | `a0bde215610a4248b09a07039d9d3d9351293c92e1f08c3003a941c9bb48f900` |
| `docs/contracts/online-ogd-v1/fences/first_order.json` | `e2ed4c2d973d6a1fa8454a5362f1e8fca70b5cac3ef67e380e078ca97d4d6728` |
| `docs/contracts/online-ogd-v1/fences/iterate_mem.json` | `6e7b2ddac97325b5b2e5a52a02243218f5a375d6e7b96f2f3f4b76189836c9e7` |
| `docs/contracts/online-ogd-v1/fences/iterate_prefix.json` | `e49431af5150a4c1331a46882d98861ea66a25e62b31db8d7b886b5cc38d4f55` |
| `docs/contracts/online-ogd-v1/fences/lemma_2_12.json` | `b5c2e6f6664618f373adeea4f59f43701cc679384f2b60dbaf45442e6143e8b5` |
| `docs/contracts/online-ogd-v1/fences/project_eq_of_variational.json` | `b725adf21a69f1d0cbcbad200c13dc1c4c7517f81e7db6ecb25692b6be75d7cc` |
| `docs/contracts/online-ogd-v1/fences/project_spec.json` | `4f6e7736809304382fbcf047b87bd1d77a4413d8573f4916366a3aedcc2b1e32` |
| `docs/contracts/online-ogd-v1/fences/proposition_2_11.json` | `9bf043466cf796a769973e6fb0a7bbbeae32660917675f885ab33040e4f8b660` |
| `docs/contracts/online-ogd-v1/fences/theorem_2_13_fixed.json` | `a88e9321b0f23ce94af8ff8a21011e3cb8cad2292480d39a14c111fb09e9ed12` |
| `docs/contracts/online-ogd-v1/first_order.json` | `85e2a08c6687ff57fd4c2532f9e9f952b38b4e8811bff107ebdc8839837b24df` |
| `docs/contracts/online-ogd-v1/iterate_mem.json` | `b660174a863a764f88a6e617adc69125034d9d0f178a89c531101068a496d029` |
| `docs/contracts/online-ogd-v1/iterate_prefix.json` | `db03f9ee56b4d300bba2508d5bd333b1498e300978d43e30bab3c80c9d9aeaa2` |
| `docs/contracts/online-ogd-v1/lemma_2_12.json` | `db106ff2118a564ac48b34b01745839e73ff5178070800c2924a4f4776a9d9cd` |
| `docs/contracts/online-ogd-v1/project_eq_of_variational.json` | `f5bdea3349e5e19ea0ae8c9e28c154e800e5b85ba3f651bb8502eaff2e69944e` |
| `docs/contracts/online-ogd-v1/project_spec.json` | `7ff65c546ba6b4225a7c8fd92e9c73a91f58cc9125bcf07c8b19c5f4601bbecd` |
| `docs/contracts/online-ogd-v1/proposition_2_11.json` | `5906fb0cbf862ffdbbd31bf0c1f3ab40e7b297ad6a6d383ad9f04df001ea5ed0` |
| `docs/contracts/online-ogd-v1/theorem_2_13_fixed.json` | `ae81194f3ea41d8b030e9d6e19bcf9251e22f508c0e448107d86e97c20a3fdd4` |
| `docs/contracts/online-ogd-variable-v1/context.json` | `c8bf260793a4501c17fdafa0a1b02b62f5a640f2be96373d7868e4415e92699f` |
| `docs/contracts/online-ogd-variable-v1/contract.md` | `212227a1abd3a93bc3fd08c901f25e999883c262142d7680a1a6c20695cc48e8` |
| `docs/contracts/online-ogd-variable-v1/dag.json` | `c386faff04699def3568d6c6742f087720b79a096816301feae88be927801905` |
| `docs/contracts/online-ogd-variable-v1/headers.json` | `4bae2c09fb60deb6c4c4bf6076a6c543edb406ce0d006ef1bdea7dc6166624f3` |
| `docs/contracts/online-ogd-variable-v1/iterateVariable_mem.json` | `c93135e36e21abcfc6b058eed65fcd80a5429929b26f4454d4eade4c90a3b64c` |
| `docs/contracts/online-ogd-variable-v1/iterateVariable_prefix.json` | `9b015711bdb4637a40e7c8db252db3128801b2af2f2d5349b81868da03ae9406` |
| `docs/contracts/online-ogd-variable-v1/theorem_2_13_variable.json` | `62fae40fafb67d71ad57f4bfdf910701d37a7f385b00274f71c342275413e8a2` |
| `docs/contracts/online-ogd-variable-v1/theorem_2_13_variable_bound.json` | `3338dfda4514ae2cc5bb01b1d1548bd041e85d1e080a4ded310fc5a780a5eb5c` |
| `docs/contracts/online-ogd-variable-v1/variable_one_step.json` | `299f18c7f48c2028d5bc65704e5f489857b828c46b045b6b75daec83dd06622a` |
| `docs/contracts/online-ogd-variable-v1/weighted_potential_sum.json` | `900519cfd7ee4252b155a2f64871aa9eb810170a914ba31311ec6acd3b5df8dc` |
| `runs/online-ogd-migration-20261005/00_context.md` | `bd0068ac22026947ae9b9370e48f9c6ae46bc839e1a49d5d1e3689dc9b78c402` |
| `runs/online-ogd-migration-20261005/10_upper_director.md` | `7f3743180eda051ae059880032b542b6882d867937bd98cbb761e99541262e42` |
| `runs/online-ogd-migration-20261005/20_middle_architect-v2.md` | `89aa227e43973e563b0bcf7007543a66593a4bbb510d0400ac7edde2fe020a87` |
| `runs/online-ogd-migration-20261005/20_middle_architect.md` | `6743087559714ee3c7a76f6a3f31557dfcd6deac817a8192128ee870197b39f2` |
| `runs/online-ogd-migration-20261005/api-v2-01-exit.json` | `d198b6f714d1a9a7e01400481b8f42c72d1cd1ad5b5c7407ce2f1f204cf7fcce` |
| `runs/online-ogd-migration-20261005/api-v2-01.log` | `23838f77c526af863c7cdd472c2d266e016d70a4e8e59b11a73b7110b065430d` |
| `runs/online-ogd-migration-20261005/blind-packet-v1.md` | `789c382de3c4a7a58a08c8d4c6f716bbcfa10eb7b84a5339c3cbdc880df2cbff` |
| `runs/online-ogd-migration-20261005/blind-packet-v2.md` | `3cd9ab15cb1287b7575f9bd334c12555af05d3ea6995e8cda82731143fd5c79e` |
| `runs/online-ogd-migration-20261005/blind-receipt-v1.json` | `a916f1985ba1e6780b3409db65b0b9a57a81bfa53df3fde5cd81c60c4453268e` |
| `runs/online-ogd-migration-20261005/blind-receipt-v2.json` | `50506c2037bb783cbd7fb3d3e008ca317f6e93fe2812fc3c4c0899616b44129e` |
| `runs/online-ogd-migration-20261005/blind-reconstruction-v1.md` | `ff54b7e475dfdc1b04a8dfa88e93da9aa24659288269d8ae1f97384f1acd3888` |
| `runs/online-ogd-migration-20261005/blind-reconstruction-v2.md` | `64a58051449089360fb843a3b9b2ad18f0ca17a6911981f2bb70b37026ab33c8` |
| `runs/online-ogd-migration-20261005/chapter2-lexical-enumeration-draft.json` | `8259b600ba9f709d1e6b48c3916551639bf18c8944d4620ffba3f78b9ce9b96d` |
| `runs/online-ogd-migration-20261005/contract-source-inputs-v1.json` | `a076f8e49da50cd85790d8e30b15f4c94ec80116527d374154486b206dd1c3a7` |
| `runs/online-ogd-migration-20261005/contract-source-inputs-v2.json` | `3fde9f0222666b8e56261911317f70d3710dd574953c3265477652b0e488d327` |
| `runs/online-ogd-migration-20261005/draft-existing-v1-exit.json` | `af7a3df02046f33a803843b208f6022765395cc6e52852338b122f60529a1df6` |
| `runs/online-ogd-migration-20261005/draft-existing-v1.log` | `93be7b7e75dfe561b3de94510165d2f3ef39e13b71320c2ab280b178d53a54a0` |
| `runs/online-ogd-migration-20261005/draft-freeze-v2.json` | `1d5f0331b96723e74f3fb234456ea42ced679b4f463d624f4012953b6464abca` |
| `runs/online-ogd-migration-20261005/draft-prepare-02-exit.json` | `1aa80350a2c80f25fa853a92b67046ca9d3f33fbe53a3e840ebdceab73fc8ed0` |
| `runs/online-ogd-migration-20261005/draft-prepare-02.log` | `f1803de7b523e5cdf8784012f233ad1f60c2b7ddddedf117af1ce54b56a6f96f` |
| `runs/online-ogd-migration-20261005/draft-python-01-exit.json` | `fd72d6b430ec53376b3a322dd736a5dd00ee516de7e1acffa7112c91a21dee5c` |
| `runs/online-ogd-migration-20261005/draft-python-01.log` | `afdc74a35f4891197edbfb525bd47eeeded8bd01241e51b7422858e9e4757873` |
| `runs/online-ogd-migration-20261005/fence-equation_2_1-exit.json` | `7b0475b1efef6bb887fc72580ca673b22f1775f3da66e9509280f95ddb985b22` |
| `runs/online-ogd-migration-20261005/fence-equation_2_1.log` | `c4f2f9c33cd277d1ccbf4f45950ce2a4d569f1a80e1ff85d326f7422db78403a` |
| `runs/online-ogd-migration-20261005/fence-equation_2_1_distance-exit.json` | `33fd2f8157098c83558a3dd571dcb70292948835593c2c721d73f8a1d9d6f56d` |
| `runs/online-ogd-migration-20261005/fence-equation_2_1_distance.log` | `45395d003416e824027e8e3af83bc1df69ab2b4efa2f0e42841c44c18cc63de9` |
| `runs/online-ogd-migration-20261005/fence-first_order-exit.json` | `cae0d6059aacc2d9419bfa005472ede2827cd81d129180c1cb0c4384b7831949` |
| `runs/online-ogd-migration-20261005/fence-first_order.log` | `b484652655535a19a005cd7da8ff85f506984510f35613c030043ea4ca1009a5` |
| `runs/online-ogd-migration-20261005/fence-iterateVariable_mem-exit.json` | `c4b3a42e7e3d5368620ffbd336f4dbd9c196866269db67c0a1b6c0a9974e374b` |
| `runs/online-ogd-migration-20261005/fence-iterateVariable_mem.log` | `7f06f8225162d692fe1624d773f86b1f1463efe2108b731e496c06fdb7a324c6` |
| `runs/online-ogd-migration-20261005/fence-iterateVariable_prefix-exit.json` | `1a01516c8198ebb7219f2b796f3b0015f4e9e729a714c675ff0ec387a0881f25` |
| `runs/online-ogd-migration-20261005/fence-iterateVariable_prefix.log` | `0f39d1de20afb510af5af07d064689c85cc72b19e05cb7e041cb4c57f52311ed` |
| `runs/online-ogd-migration-20261005/fence-iterate_mem-exit.json` | `ceb7ece76121869fd0841785fba6dbd5279451b28681b500acb322778261423f` |
| `runs/online-ogd-migration-20261005/fence-iterate_mem.log` | `5f803bc1d8834f7c348152fe3a5bb95676763790112ea9e22e96cd747857e2de` |
| `runs/online-ogd-migration-20261005/fence-iterate_prefix-exit.json` | `d1219da76d99ccf622790de592ce996b171d2961aa88a566cd7125be6c445a60` |
| `runs/online-ogd-migration-20261005/fence-iterate_prefix.log` | `135b5263edd9d3b088cf34e4a82667d7bc9f067a87ab4c7c477f43d0a9d62505` |
| `runs/online-ogd-migration-20261005/fence-lemma_2_12-exit.json` | `1a896e6fbfee7b217651407bdf30e63528ddd14609360c2241c6f04275cfa720` |
| `runs/online-ogd-migration-20261005/fence-lemma_2_12.log` | `f8cc148cdb719994f0996816622fa2166eb133274924dfd3bf866062ec96dd0e` |
| `runs/online-ogd-migration-20261005/fence-project_eq_of_variational-exit.json` | `5552f6e31256d1f0da11e398abe56206b5b9811942d139e6bde14fa8f1ccd0c5` |
| `runs/online-ogd-migration-20261005/fence-project_eq_of_variational.log` | `5172dbfe4e2371cd662d59d32fcd015478d2d98e34eaed6a1066797129745ea5` |
| `runs/online-ogd-migration-20261005/fence-project_spec-exit.json` | `77a9f1674d24853f2049cae7a15c3af45aa908a70e547b08a9a6e63735929858` |
| `runs/online-ogd-migration-20261005/fence-project_spec.log` | `bc576e4c4705238e110df193df082de0a6b474059613f4c2a49f8f3931169567` |
| `runs/online-ogd-migration-20261005/fence-proposition_2_11-exit.json` | `d8249ed2fec4960adc78e1089926a36644f5173d070bc5f3226334c9e4c6bcb4` |
| `runs/online-ogd-migration-20261005/fence-proposition_2_11.log` | `48cb5e0874829d7a8461bb908afc9839842b66df037de5bfab04ae1822bab743` |
| `runs/online-ogd-migration-20261005/fence-theorem_2_13_fixed-exit.json` | `8a2ee5664639adce9b553ae7f39e3c583a343fe65d823f6fb8ebbdada050ee51` |
| `runs/online-ogd-migration-20261005/fence-theorem_2_13_fixed.log` | `83a5f6f9cbd2ff3da3f418163c12344dd10febee358dcefa54080c6f3c0df8f4` |
| `runs/online-ogd-migration-20261005/fence-theorem_2_13_variable-exit.json` | `2c98ee9616a9ac264c5d15c29df81c277118c4cb91a1620b60c58d481f03ac5d` |
| `runs/online-ogd-migration-20261005/fence-theorem_2_13_variable.log` | `201c0db249a79a6de27187392f02c341cad6dafca092bbbdd105a6c2a59e5b0a` |
| `runs/online-ogd-migration-20261005/fence-theorem_2_13_variable_bound-exit.json` | `c03ce843d9fdffddf4a429ee1302d4bd1fd22e0a61e572525f83ebf67ad9166c` |
| `runs/online-ogd-migration-20261005/fence-theorem_2_13_variable_bound.log` | `077151a91a30e56162b2ad3b14b9123e1379a663715e2aeea20befca07304c73` |
| `runs/online-ogd-migration-20261005/fence-v2-equation_2_1-exit.json` | `601f7235dcd0766ab45df007a1b327700a71dc66c2144196043a82a2f26d8b74` |
| `runs/online-ogd-migration-20261005/fence-v2-equation_2_1.log` | `19bac5f0365ba8be887a7e97e12ef670b18a7a1213c6602ce8c2811e861245a8` |
| `runs/online-ogd-migration-20261005/fence-v2-equation_2_1_distance-exit.json` | `b5586667d1904fd130625e2c75d5773015dfbff932405250b309e47769666353` |
| `runs/online-ogd-migration-20261005/fence-v2-equation_2_1_distance.log` | `3de760f330648569c8bb68e997294938e79f8ccda182b3839d07fcfd3b5dfb65` |
| `runs/online-ogd-migration-20261005/fence-v2-first_order-exit.json` | `a5bf47c1946b397e474e6627f4dad967ab345ffaad7623a6616d378da5fee9fc` |
| `runs/online-ogd-migration-20261005/fence-v2-first_order.log` | `e14747f836da70dec4e28bdd9da2596bada0d365fa99875454f76cd2b4778881` |
| `runs/online-ogd-migration-20261005/fence-v2-gradient_linear-exit.json` | `6ff8f24f49cd16cf74acc5abfd25b214ba6ffeb50e6defb4767d12e4e80dd4bf` |
| `runs/online-ogd-migration-20261005/fence-v2-gradient_linear.log` | `6b1e8906d6efb0af6533a0bceb5a19bb36d13b28d0fee350e08a09be6557d19c` |
| `runs/online-ogd-migration-20261005/fence-v2-lemma_2_12-exit.json` | `3b81e0cb0ebb03d0ffc287a2baf9c45e1e77d46279a87c95a2ebcb18c454907c` |
| `runs/online-ogd-migration-20261005/fence-v2-lemma_2_12.log` | `14a0b2c99b458603e81d4c5bfc3ae8bd50ce2c5382048f09b37cc79c43474a50` |
| `runs/online-ogd-migration-20261005/fence-v2-linear_regular-exit.json` | `17f3a130b6ac80b5be86cb5b37501580d6af523edbaf5b74fec7e9b6736e0310` |
| `runs/online-ogd-migration-20261005/fence-v2-linear_regular.log` | `69017ba1fbe4a31fcc4985662b3a75d984539662c35a9838892a38afa7935f16` |
| `runs/online-ogd-migration-20261005/fence-v2-regular_to_feasible-exit.json` | `d011e6e9d0501649bea01e383e2567a1765a499546b43118a23ba3f5d5bd27fe` |
| `runs/online-ogd-migration-20261005/fence-v2-regular_to_feasible.log` | `9475db7a26bb4f50b4e19230f15a1da0d8aaf3b773f5ce3e508bf06274e6c873` |
| `runs/online-ogd-migration-20261005/fence-v2-source_to_feasible-exit.json` | `1cde54da5dbaf3bef3bbad3b4fda414cdd4afcf588e8f078dd8fdc0481318083` |
| `runs/online-ogd-migration-20261005/fence-v2-source_to_feasible.log` | `fcda5ce964eb00a3aca3df9bbf16bb6db6a9916af122a55c8c72804d0f2468a5` |
| `runs/online-ogd-migration-20261005/fence-v2-theorem_2_13_fixed-exit.json` | `b8c8b4348df026f8ce09448b760856ace1d0504f2fb3f7ab16d0dd74da48efb0` |
| `runs/online-ogd-migration-20261005/fence-v2-theorem_2_13_fixed.log` | `f1d4a2237017c6a14a15461e834dbad9aa39b6f8273a38e5929d9da1dc85d29e` |
| `runs/online-ogd-migration-20261005/fence-v2-theorem_2_13_variable-exit.json` | `576a242761c8b1767407ba5d7d49f1f06043aef771a6e787587def3ed9821b92` |
| `runs/online-ogd-migration-20261005/fence-v2-theorem_2_13_variable.log` | `f17d2160dc9a6e23aebb0e0eadb34b37896331a53cea8f44af118932848641d4` |
| `runs/online-ogd-migration-20261005/fence-v2-theorem_2_13_variable_bound-exit.json` | `e97f7b436538923986df9211a7d602fb09e598bea5d6c2c6d2bb06a6088e37c4` |
| `runs/online-ogd-migration-20261005/fence-v2-theorem_2_13_variable_bound.log` | `cfe0c8e50b23cbe57384f85f87e4315897dc363d6841835808ab752d0f882818` |
| `runs/online-ogd-migration-20261005/fence-v2-variable_one_step-exit.json` | `ae4d7ef4699c8b9100bdbcf46791e4d32dddb0a9b7a7dee98dfc87eb0461a643` |
| `runs/online-ogd-migration-20261005/fence-v2-variable_one_step.log` | `9f0b2e66e0592ff70cff8445b8f218b32312e5b31001158e5ed371ed4cc75d44` |
| `runs/online-ogd-migration-20261005/fence-variable_one_step-exit.json` | `dcf5cfb5fec50dc2cacee15a2a5a388c6754525ad118b7bfddd5ef678f2cb398` |
| `runs/online-ogd-migration-20261005/fence-variable_one_step.log` | `77e93054fd1f5e23d9b81bf58d3801f48747a65a26bfc0d57951e82f192359ca` |
| `runs/online-ogd-migration-20261005/fence-weighted_potential_sum-exit.json` | `f20d002ba363a6b99862925d0ea0ced3e3086d12e933be85fb90f292d500abc7` |
| `runs/online-ogd-migration-20261005/fence-weighted_potential_sum.log` | `9da4d9998d3b4f1e90169b2ad6671a6884b2ea66213fb296bf49af74e8680c5d` |
| `runs/online-ogd-migration-20261005/freeze-review-v2.json` | `f1eeba6b4b6bc40782c896fd6b26de9ad50bff8bbbfaef10779963e091e95da8` |
| `runs/online-ogd-migration-20261005/help-fence-exit.json` | `b99f5ebde5b82fd97984311dc9c2e94c7c8b9d40edcded9fd6cc398c90ab56e7` |
| `runs/online-ogd-migration-20261005/help-fence.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |
| `runs/online-ogd-migration-20261005/help-new-task-exit.json` | `4fe71aa3a40c77d1a423340425855dca4e6bf126405a84190cf4fe7f9b4bd6c4` |
| `runs/online-ogd-migration-20261005/help-new-task.log` | `25eb9342c3094bee57187630bd149d2c522fc9f7ac7e65bebe5c198eba60ed99` |
| `runs/online-ogd-migration-20261005/leaves/api-v2.lean` | `5847ea70ea9f209e67b7c08bc277023a600bd3662a3350734e325605484e53fa` |
| `runs/online-ogd-migration-20261005/leaves/native-types-v2.lean` | `3aefbef2891905a5bd248ecdf733286d15e0bed6cbe3f4ffcdba25c74016a737` |
| `runs/online-ogd-migration-20261005/leaves/neutral-types-v1.lean` | `4cd74e3cda451df79328dcfe7eebd3da3489619e858978cdbc1d6fab8c0fe95a` |
| `runs/online-ogd-migration-20261005/leaves/neutral-types-v2.lean` | `0e8052d8d9b250dc235723b201e46f75748a362e6be8c17f98368b370be36491` |
| `runs/online-ogd-migration-20261005/leaves/prepare-draft-attempt01.py` | `ee47ec0b990d4da3d338f1ce057ad68523e7ccf8edadf91d789d29ab69d0eaa5` |
| `runs/online-ogd-migration-20261005/leaves/targets-v2.lean.txt` | `f58f18208967cb31598421244ddf6b3c93745406f1c5524702a25fabcf441c22` |
| `runs/online-ogd-migration-20261005/main-contributor-baseline-exit.json` | `05d6fac26ae146ed135db544f66334548b653fe621a8f4642b35fe7fcde6e3f9` |
| `runs/online-ogd-migration-20261005/main-contributor-baseline.log` | `3414ad18414c64dc11dafa6438516e1f01c1c691850a7c9ac69df0361f531eb1` |
| `runs/online-ogd-migration-20261005/migration-baseline-reconciliation.json` | `95fa63b27511719353bcdaf66f35e558021b8dbd12f3d1a620b7e03c11aa2766` |
| `runs/online-ogd-migration-20261005/native-types-v2-01-exit.json` | `244430e09233d78912189fb3cc9d4dbf04da0ccbec1c14d4019dea81557ed5d8` |
| `runs/online-ogd-migration-20261005/native-types-v2-01.log` | `e2ffb420ce0fb2e90f37c6a233b44ed36181f7817ba7a16d75a0304a5c6049fd` |
| `runs/online-ogd-migration-20261005/neutral-context.lean.txt` | `ad0541bfdd238f30789a8406e9771f3d9be40118170480c0997ccb2c93ff2d72` |
| `runs/online-ogd-migration-20261005/neutral-types-01-exit.json` | `73d108a39a019c6a04f14850320af05f592a2791dfe2ab590b35523e47fd104e` |
| `runs/online-ogd-migration-20261005/neutral-types-01.log` | `237cfa2924cd24fe69a77c50c8ac2c2f830fd0f3fd1ea452e059cc99d97a8d19` |
| `runs/online-ogd-migration-20261005/neutral-types-v2-01-exit.json` | `a5ae8f53fafbba95da5b33f4b8869441d836fec372103d3f1039fee5e2d8e800` |
| `runs/online-ogd-migration-20261005/neutral-types-v2-01.log` | `6aefcbe2bd9371f71bcfe41e0f9630c0546814992235ad954006fdfad634c77a` |
| `runs/online-ogd-migration-20261005/new-task-exit.json` | `41149ab2e718a1ebf0e9472381782c0edc46ad3611947f4087b427b84603e39f` |
| `runs/online-ogd-migration-20261005/new-task.log` | `621c76235dda32d63a823dce433ab927c92d05b4db8f9c6bc5d368bbc9b695a5` |
| `runs/online-ogd-migration-20261005/predecessor-delivery.json` | `9a59bc974678848ba6e28ed8c226dc096f9555824e6aa6c2662bfbd639310794` |
| `runs/online-ogd-migration-20261005/prepare-draft.py` | `65653f575ae7474f0355a929e93ac05ea2eb2b0afd20641f3cc3a328223fcfb8` |
| `runs/online-ogd-migration-20261005/prepare-repair-v2.py` | `b453c288377b4b9b398642d0ffc20df02208d65279ff2c3971e50c92ee09cf69` |
| `runs/online-ogd-migration-20261005/private-neutral-name-map-v2.json` | `0d2885b9ccd87884002645e6e254ebe64dab849860e5df38fe3dcd6a79c59260` |
| `runs/online-ogd-migration-20261005/private-neutral-name-map.json` | `9689750b8ba8c98333d61cf776956af3b0dba156cc7d5306cd655ca0b69468b1` |
| `runs/online-ogd-migration-20261005/proof-obligations-v2.json` | `ab39616e87a97ad6e47fc9f410f8e0b5dd363c5f94f4916d16aef0d1f8ee62e2` |
| `runs/online-ogd-migration-20261005/proof-obligations.json` | `cf66c2de4f5e057dfb08fec76ae601882e63f7d01da05946e5de40f3fe41ceb8` |
| `runs/online-ogd-migration-20261005/repair-prepare-v2-exit.json` | `d92ffd26849fa3523098619861a746f5723dce0e97c7a6004d37a93e0bc337fa` |
| `runs/online-ogd-migration-20261005/repair-prepare-v2.log` | `40c34956ee3dcd55438e508f95e6c0faee6edff180d933236200bd27c23b9737` |
| `runs/online-ogd-migration-20261005/repair-regularity-v1-exit.json` | `db0a49f9209655daf011a4f684b4028afa6be8ed5bbc2b8045c98db49c65e4b2` |
| `runs/online-ogd-migration-20261005/repair-regularity-v1.log` | `e5d8a1e74e3b070f21089b9f001d2ebe749b0fc1d885b3513edf5c80e5074864` |
| `runs/online-ogd-migration-20261005/retrieve-gradient-exit.json` | `e06c20927526cdfd84ba41f91e9b98adac3158e3d14f85a672075af4a0097035` |
| `runs/online-ogd-migration-20261005/retrieve-gradient.log` | `90939348f58966a96dbd600141ca52c8993b4cd956e8477a5363f53779816c94` |
| `runs/online-ogd-migration-20261005/retrieve-ogd-memory-exit.json` | `20cbc828583ba14d75e918ff737d282bd20327ca8513d14fb86d75495cae59ce` |
| `runs/online-ogd-migration-20261005/retrieve-ogd-memory.log` | `bace2a52476b6bf1cc28f55910e1d2c5763a6ca9f7d49c0b7bd25524c0634b99` |
| `runs/online-ogd-migration-20261005/retrieve-projection-exit.json` | `064c3f2e75b4bc528eae816a576d81ac9fcaf83cb144d43fe9311659cc891bbc` |
| `runs/online-ogd-migration-20261005/retrieve-projection.log` | `95c02a3525c4abe67c862a8028f6a66eb0265ab2ebb655d729b991fef72a927d` |
| `runs/online-ogd-migration-20261005/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `runs/online-ogd-migration-20261005/source-card.md` | `dff2c3aadc1aa7a91ad84dea89db8cb851124c63333b92da6c60353fb5cbdfbd` |
| `runs/online-ogd-migration-20261005/source-contract-receipt-v1.json` | `c1ff865465626c4ecfc373ceebde24406e79aefa2696c382e823235616e92233` |
| `runs/online-ogd-migration-20261005/source-contract-review-v1.md` | `000aeed3fb5cbbc7505be4d794383bbe996c228aed3d52633ad474e0344d4288` |
| `runs/online-ogd-migration-20261005/source-regularity-repair-proposal-v1.md` | `fa89c54733a2f2b2d27a1178bf905ce7d339f32e06043fa00130d390fe370e59` |
| `runs/online-ogd-migration-20261005/source-review-packet-v1.md` | `2249a068e4095919ec1c3762dfb5b74d19a2af0f225be6517bb0324d3bfa3e8d` |
| `runs/online-ogd-migration-20261005/source-review-packet-v2.md` | `26b486ede53e63e050d20628d336a2f8cd6d496a2011acf3ec9517782dc7e076` |
| `runs/online-ogd-migration-20261005/workspace-workflow-audit.json` | `788bdc096434e794b40bedf89fe48e4574378df75b22fe52219a8952d8adade7` |
| `tasks/ONLINE-OGD-MIGRATION-20261005.md` | `420705c0f0458feb1b3606d3252a56347ec4cd9c74ac2a8e7b53e745e524aae2` |
| `tmp/online-ogd-migration-source-pages23-27.txt` | `f7282af39a2e476ef5a7c216f2256e4b106792677777bba5a3858ac2bdc80a03` |
| `tmp/online-ogd-migration-source-v2-game-and-results.txt` | `2617057edbb7aeec19d4d715a1ce39e1b518d3f5f292215c81c4cf44fb3b5fa9` |
