# Existing OGD source/contract/body audit v1

**Verdict: rejected as a complete source-faithful OGD migration.** The existing statements and proof bodies remain valid under their written stronger predicate. The general implication from the source loss assumptions to `RegularLoss` is false. Projection Proposition 2.11 and the regularity-independent structural results receive separate acceptance below. No old acceptance label is authority for this new judgment.

Actor `/root/source_reviewer`, distinct automated source reviewer; requested GPT-6 Astra / medium, runtime model identity not independently attested. Not external-human or external-model review. Only this report and its receipt were written.

## Actual scope and integrity

All 134 fixed raw input rows match independently computed SHA256; no drift. The current two OGD modules were read in full, including all sixteen bodies and eight context definitions/structure. All sixteen native declarations were extracted from their actual files and checked against the frozen statement text/hash. Fresh restricted-input blind reconstruction N01–N16 and receipt were read, alongside actual source extract, old contracts as historical artifacts, current first-order producer and relevant canary/baseline evidence. Ancillary rows are raw preservation checks, not independent certification of every old workflow. The neutral type probe has exit0; it is not a new proof build.

Original pinned PDF independently hashes to `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. Physical 23–27 / printed 11–15 were read through the bound extract, with fresh original physical24–25 extraction checking Algorithm2.1, Proposition2.11, Lemma2.12 and Theorem2.13 wording. Algorithm2.1 explicitly says a convex loss differentiable on an open set containing V; it does not demand one convex open differentiability neighborhood for an unbounded V.

## Confirmed counterexample, with limits

Take Euclidean R², the whole horizontal line V={(x,0)}, and f(x,y)=max(exp(-x),y). Both branches are globally finite convex functions, so f is globally finite convex. V is nonempty closed convex. U0={(x,y): y<exp(-x)} is open, contains V because exp(-x)>0, and on U0 the function equals the smooth first branch. Thus the source convexity and open-neighborhood differentiability assumptions hold.

Suppose an open convex U contains V and f is differentiable on U. Openness at (0,0) gives (0,b) in U for some b>0. For every real x, (2x,0) belongs to V, and its midpoint with (0,b) is (x,b/2) in U. Choose x sufficiently large that 0<a=exp(-x)<b/2. Convexity of the vertical segment from (x,0) to (x,b/2) puts (x,a) in U. Along the vertical line through that point, f(x,a+t)=a+max(0,t). Left and right derivatives are 0 and 1. Ambient differentiability would imply a two-sided derivative of this line restriction, a contradiction. Consequently no such U exists and `RegularLoss V f` fails.

This independently confirms the proposal mathematically. It is NOT a Lean-compiled counterexample, and no source regularity theorem has been proved by this audit. In particular, taking the convex hull of U0 is not a valid repair: it crosses the kink.

The proposal needs one qualification: this counterexample uses an unbounded domain and does not disprove the bounded finite-dimensional adapter. For a closed bounded convex V in R^d and open differentiability set O containing V, compactness gives epsilon>0 with V+B(0,epsilon) contained in O. This tubular set is open convex and contains V. Global convexity of f restricts to it. Hence the bounded source regime can imply the old predicate via a genuine compactness adapter. No such adapter is supplied here; infinite-dimensional Hilbert bounded sets need not be compact. `equation_2_1_distance` does not bound the whole domain, so it remains in the genuinely restricted group. Do not assert all bounded source instances are excluded.

## Seven semantic slots

| Slot | Audit result |
|---|---|
| Objects/spaces | Actual complete real inner-product space generalizes source R^d; nonempty closed convex Domain and actual nearest-point choice are genuine. Losses are globally real-valued here; no EReal-toReal infinity shortcut occurs. |
| Quantifiers | Projection uses arbitrary ambient z and all feasible comparators. First-order/one-step use feasible x,u. Fixed regret uses every natural T including0; variable and tuned bounds require T>0. Equation2.1 quantifies all comparators after one tuned run, while its distance helper is one-comparator. |
| Assumptions | ConvexOn U includes convexity of U. Existing RegularLoss therefore adds a genuine convex-neighborhood restriction for unbounded source domains. Proper replacement is convexity on V plus ambient DifferentiableAt at relevant feasible points, or an exact source-premise interface with a proved implication. Bounded finite-dimensional source can alternatively use the compact-neighborhood adapter described above. |
| Conclusions/metric | Both one-step inequalities and exact factors are retained. Fixed and variable regret bounds keep the negative terminal squared distance. Projection conclusion is comparator-distance decrease, not full two-input nonexpansiveness. No desired regret inequality is an input. |
| Constants/indexing | Lean0=source round1; terminal iterateT=source x_(T+1). Variable denominator eta(T-1) is the last used source eta_T. Metric.diam wrapper explicitly requires boundedness; generic D is a pairwise bound. Source L is G. Tuned D,G,T>0 excludes singular denominator cases; no claim to cover zero-scale tuning. |
| Information order | Both recursions evaluate the current loss only when constructing next output. Strict-loss-prefix proofs hold for identical exogenous schedule/initial point. Variable prefix does not compare two different schedules with equal prefixes and does not certify how a caller chose eta. Tuning uses gradients of the actual tuned trajectory; no future-energy optimizer or probabilistic claim. |
| Excluded regimes/source delta | Hilbert extension and structural T0 are explicit generalizations. Arbitrary unbounded source regularity is not covered by old loss-dependent endpoints. Bounded source adapters remain required, although mathematically available. These are sixteen library declarations, not sixteen separately printed source results. |

## Per-target verdict and body scrutiny

Each row inherits all applicable seven-slot checks above; irrelevant loss or time slots are absent, not hidden hypotheses.

| Target | Verdict | Actual producer / remaining source gap |
|---|---|---|
| project_spec | accepted-with-explicit-delta | Classical choice specification from genuine Hilbert nearest-point existence; finite-dimensional source specialization exact. |
| project_eq_of_variational | accepted-with-explicit-delta | Two variational inequalities force zero squared separation; library characterization adapter. |
| proposition_2_11 | accepted-with-explicit-delta | Actual variational projection inequality plus norm-square expansion; full source comparator decrease covered, Hilbert generalization explicit. |
| first_order | rejected for full source coverage; valid written theorem | Actual affine-line derivative/secant proof; too restrictive RegularLoss input for unbounded source. |
| lemma_2_12 | rejected for full source coverage; valid written theorem | Real first-order producer plus genuine projected norm expansion; both inequalities intact. Feasible x is the Algorithm2.1 context, not a theorem for arbitrary nondifferentiable ambient x. |
| iterate_mem | accepted-with-explicit-delta | Feasible initialization and actual project_spec, independent of loss regularity or step positivity. |
| iterate_prefix | accepted-with-explicit-delta | Actual recursion induction under equal strict-past whole losses and common parameters. |
| theorem_2_13_fixed | rejected for full source coverage; valid written theorem | Finite telescoping of actual one-step bounds, no diameter premise, negative terminal kept; unbounded RegularLoss gap is real. |
| equation_2_1_distance | rejected for full source coverage; valid written helper | Positive tuned denominator, actual-run gradient-energy bound and initial-distance bound; whole-domain regularity adapter still false in general. |
| equation_2_1 | rejected as presently complete source endpoint; adapter required | Uniform comparator wrapper of actual tuned run; finite-dimensional bounded source has compact-neighborhood repair, not the unbounded counterexample. |
| iterateVariable_mem | accepted-with-explicit-delta | Actual projection feasibility, arbitrary prescribed schedule. |
| iterateVariable_prefix | accepted-with-explicit-delta | Strict loss-prefix induction with the identical schedule; no broader adaptive-schedule assertion. |
| variable_one_step | rejected for full source coverage; valid written helper | Actual lemma2.12 instantiated at the actual iterate; division by positive current step. Domain need not be bounded in this helper. |
| weighted_potential_sum | accepted-with-explicit-delta | Genuine scalar induction, positivity and decreasing-step denominator comparison, terminal aT retained; no a>=0 or terminal upper bound needed. Library helper, not standalone source regret. |
| theorem_2_13_variable_bound | rejected as presently complete source endpoint; adapter required | Actual one-step sum and weighted potential at actual squared distances; diameter pairwise bound implies bounded source domain. Finite-dimensional source adapter missing. |
| theorem_2_13_variable | rejected as presently complete source endpoint; adapter required | Actual bounded Metric.diam supplies pairwise norm bound, then prior producer. Source finite-dimensional compactness can repair regularity input. |

No proof-body falsity was found under the stated assumptions. In particular, tuning bounds use the same eta-dependent iterate; source future-gradient warning is respected. Existing linear-loss canaries exercise clipping/nonzero residuals but cannot establish the missing general source implication. Compilation or type reconstruction cannot close that logical gap.

## Required versioned repairs

1. Preserve the old frozen statements, bodies and historical reports. Add a new versioned source interface and fresh blind/source stabilization before proof work. It must not assert the false unrestricted source-to-RegularLoss implication.
2. Preferred uniform route: convexity on V plus ambient differentiability at every point of V, with a proved adapter from the source's global convexity and arbitrary open differentiability neighborhood. Reuse the same Domain/project/step/iterate/iterateVariable and gradient. The inspected `OnlineConvex.convex_gradient_lower_bound` already accepts ConvexOn V and DifferentiableAt at x, so first-order support need not require convex ambient neighborhood.
3. Produce new exact source-facing one-step, fixed, variable and tuned endpoints with this interface, preserving both inequalities, negative terminal residuals, last eta(T-1), actual tuned-run gradient bounds and all-comparator ordering. Alternatively a separately proved compact-neighborhood adapter may cover bounded finite-dimensional branches, but cannot repair fixed/unbounded scope.
4. Clearly qualify the current RegularLoss comment and future reader attribution through a new reviewed repair; do not present it as equivalent source regularity. Keep full source obligations open until actual adapter/producers and independent body/reader gates exist. A concrete formal counterexample would be useful evidence but is not supplied or required to recognize the mathematical obstruction here.
5. Current migration does not have package acceptance: root/Tests/full harness, actual axioms/graph, canaries for repaired scope, contributor coverage, final reader and immutable binding remain separate. The actual origin/main baseline fails with23 missing production paths; the older26 audit is historical and a new three-path manifest is not retroactive source acceptance.

No chapter/book/Goal/main/live closure; no old files edited and no native trial or compilation run by this reviewer.

## Exact raw inventory

All rows read and independently hashed; detailed semantic scope versus ancillary preservation checks is stated above. No normalization and no self-hash.

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
| `runs/online-ogd-migration-20261005/20_middle_architect.md` | `6743087559714ee3c7a76f6a3f31557dfcd6deac817a8192128ee870197b39f2` |
| `runs/online-ogd-migration-20261005/blind-packet-v1.md` | `789c382de3c4a7a58a08c8d4c6f716bbcfa10eb7b84a5339c3cbdc880df2cbff` |
| `runs/online-ogd-migration-20261005/blind-receipt-v1.json` | `a916f1985ba1e6780b3409db65b0b9a57a81bfa53df3fde5cd81c60c4453268e` |
| `runs/online-ogd-migration-20261005/blind-reconstruction-v1.md` | `ff54b7e475dfdc1b04a8dfa88e93da9aa24659288269d8ae1f97384f1acd3888` |
| `runs/online-ogd-migration-20261005/contract-source-inputs-v1.json` | `a076f8e49da50cd85790d8e30b15f4c94ec80116527d374154486b206dd1c3a7` |
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
| `runs/online-ogd-migration-20261005/fence-variable_one_step-exit.json` | `dcf5cfb5fec50dc2cacee15a2a5a388c6754525ad118b7bfddd5ef678f2cb398` |
| `runs/online-ogd-migration-20261005/fence-variable_one_step.log` | `77e93054fd1f5e23d9b81bf58d3801f48747a65a26bfc0d57951e82f192359ca` |
| `runs/online-ogd-migration-20261005/fence-weighted_potential_sum-exit.json` | `f20d002ba363a6b99862925d0ea0ced3e3086d12e933be85fb90f292d500abc7` |
| `runs/online-ogd-migration-20261005/fence-weighted_potential_sum.log` | `9da4d9998d3b4f1e90169b2ad6671a6884b2ea66213fb296bf49af74e8680c5d` |
| `runs/online-ogd-migration-20261005/help-fence-exit.json` | `b99f5ebde5b82fd97984311dc9c2e94c7c8b9d40edcded9fd6cc398c90ab56e7` |
| `runs/online-ogd-migration-20261005/help-fence.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |
| `runs/online-ogd-migration-20261005/help-new-task-exit.json` | `4fe71aa3a40c77d1a423340425855dca4e6bf126405a84190cf4fe7f9b4bd6c4` |
| `runs/online-ogd-migration-20261005/help-new-task.log` | `25eb9342c3094bee57187630bd149d2c522fc9f7ac7e65bebe5c198eba60ed99` |
| `runs/online-ogd-migration-20261005/leaves/neutral-types-v1.lean` | `4cd74e3cda451df79328dcfe7eebd3da3489619e858978cdbc1d6fab8c0fe95a` |
| `runs/online-ogd-migration-20261005/leaves/prepare-draft-attempt01.py` | `ee47ec0b990d4da3d338f1ce057ad68523e7ccf8edadf91d789d29ab69d0eaa5` |
| `runs/online-ogd-migration-20261005/main-contributor-baseline-exit.json` | `05d6fac26ae146ed135db544f66334548b653fe621a8f4642b35fe7fcde6e3f9` |
| `runs/online-ogd-migration-20261005/main-contributor-baseline.log` | `3414ad18414c64dc11dafa6438516e1f01c1c691850a7c9ac69df0361f531eb1` |
| `runs/online-ogd-migration-20261005/migration-baseline-reconciliation.json` | `95fa63b27511719353bcdaf66f35e558021b8dbd12f3d1a620b7e03c11aa2766` |
| `runs/online-ogd-migration-20261005/neutral-context.lean.txt` | `ad0541bfdd238f30789a8406e9771f3d9be40118170480c0997ccb2c93ff2d72` |
| `runs/online-ogd-migration-20261005/neutral-types-01-exit.json` | `73d108a39a019c6a04f14850320af05f592a2791dfe2ab590b35523e47fd104e` |
| `runs/online-ogd-migration-20261005/neutral-types-01.log` | `237cfa2924cd24fe69a77c50c8ac2c2f830fd0f3fd1ea452e059cc99d97a8d19` |
| `runs/online-ogd-migration-20261005/new-task-exit.json` | `41149ab2e718a1ebf0e9472381782c0edc46ad3611947f4087b427b84603e39f` |
| `runs/online-ogd-migration-20261005/new-task.log` | `621c76235dda32d63a823dce433ab927c92d05b4db8f9c6bc5d368bbc9b695a5` |
| `runs/online-ogd-migration-20261005/predecessor-delivery.json` | `9a59bc974678848ba6e28ed8c226dc096f9555824e6aa6c2662bfbd639310794` |
| `runs/online-ogd-migration-20261005/prepare-draft.py` | `65653f575ae7474f0355a929e93ac05ea2eb2b0afd20641f3cc3a328223fcfb8` |
| `runs/online-ogd-migration-20261005/private-neutral-name-map.json` | `9689750b8ba8c98333d61cf776956af3b0dba156cc7d5306cd655ca0b69468b1` |
| `runs/online-ogd-migration-20261005/proof-obligations.json` | `cf66c2de4f5e057dfb08fec76ae601882e63f7d01da05946e5de40f3fe41ceb8` |
| `runs/online-ogd-migration-20261005/retrieve-gradient-exit.json` | `e06c20927526cdfd84ba41f91e9b98adac3158e3d14f85a672075af4a0097035` |
| `runs/online-ogd-migration-20261005/retrieve-gradient.log` | `90939348f58966a96dbd600141ca52c8993b4cd956e8477a5363f53779816c94` |
| `runs/online-ogd-migration-20261005/retrieve-ogd-memory-exit.json` | `20cbc828583ba14d75e918ff737d282bd20327ca8513d14fb86d75495cae59ce` |
| `runs/online-ogd-migration-20261005/retrieve-ogd-memory.log` | `bace2a52476b6bf1cc28f55910e1d2c5763a6ca9f7d49c0b7bd25524c0634b99` |
| `runs/online-ogd-migration-20261005/retrieve-projection-exit.json` | `064c3f2e75b4bc528eae816a576d81ac9fcaf83cb144d43fe9311659cc891bbc` |
| `runs/online-ogd-migration-20261005/retrieve-projection.log` | `95c02a3525c4abe67c862a8028f6a66eb0265ab2ebb655d729b991fef72a927d` |
| `runs/online-ogd-migration-20261005/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `runs/online-ogd-migration-20261005/source-card.md` | `dff2c3aadc1aa7a91ad84dea89db8cb851124c63333b92da6c60353fb5cbdfbd` |
| `runs/online-ogd-migration-20261005/source-regularity-repair-proposal-v1.md` | `fa89c54733a2f2b2d27a1178bf905ce7d339f32e06043fa00130d390fe370e59` |
| `runs/online-ogd-migration-20261005/source-review-packet-v1.md` | `2249a068e4095919ec1c3762dfb5b74d19a2af0f225be6517bb0324d3bfa3e8d` |
| `runs/online-ogd-migration-20261005/workspace-workflow-audit.json` | `788bdc096434e794b40bedf89fe48e4574378df75b22fe52219a8952d8adade7` |
| `tasks/ONLINE-OGD-MIGRATION-20261005.md` | `420705c0f0458feb1b3606d3252a56347ec4cd9c74ac2a8e7b53e745e524aae2` |
| `tmp/online-ogd-migration-source-pages23-27.txt` | `f7282af39a2e476ef5a7c216f2256e4b106792677777bba5a3858ac2bdc80a03` |
