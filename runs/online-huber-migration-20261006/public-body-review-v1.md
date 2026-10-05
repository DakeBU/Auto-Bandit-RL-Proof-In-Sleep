# Huber migration: distinct public body review v1

Verdict: **accepted-with-explicit-delta** for the actual19 retained proofs,3 complete definitions and whole14-proof canary. Mathematical repairs: none. This decision follows actual producer/body inspection, not the prior contract verdict or compilation alone. ONE printed Example2.15, zero new proof code/nodes; integrated package acceptance remains pending.

Actor `/root/source_reviewer`, distinct automated source reviewer, requested GPT-6 Astra / medium. No human/external-model or independently attested runtime-model review. Prior supplied history is acknowledged.

## Exact integrity, execution and actual dependency evidence

Independently verified all325 fixed raw inputs and all195 prior contract receipt rows through their exact resolved files/snapshots; no mismatch. Independently extracted all19 statements and matched frozen headers. Retained whole-module comment-stripped tokens and entire canary raw bytes are unchanged. Three full definition bodies/context are included, not replaced by short declaration hashes. Manifest itself additionally bound below. Ancillary historical/script/raw rows are integrity and provenance evidence, not a semantic reacceptance of unrelated packages.

Actual focused gate, direct public-body elaboration, whole public-canary elaboration and complete named axiom probe all exited0. Focused log reports9089 jobs with cached work; it is not the subsequently required explicit combined acceptance root/Tests gate. Parsed36 unique named axiom entries:19 proofs+3 definitions+14 canary proofs, all only propext/Classical.choice/Quot.sound, no sorryAx. Nonfatal unused hZ/section-variable and style warnings do not weaken retained hypotheses. Nineteen native guards are separate statement/placeholder checks, not compilation. Actual scoped compiled graph has22 nodes/2954 direct type/value edges, including definitions; not full/canary export. Its real value references confirm the gluing→derivative→convex/gradient→RegularLoss→shared fixed-OGD→average→eventual chain; numeric rate has no regret dependency.

Source PDF remains raw-bound at `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`, Example2.15 printed15–16/PDF27–28. Current source text, definitions and restricted reconstruction retain the source half-square normalization, full predictor space and bounded features. Decoder uncertainty about imported RegularLoss was resolved by direct inspection of its actual fields and huber_regular producer, not silently inferred.

## Per-target seven slots and actual producer decisions

### `BanditRL.OnlineHuber.hasDerivAt_ite_le`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Real scalar f,g.
- **assumptions**: Derivatives at c both d; f(c)=g(c).
- **information**: Deterministic local data.
- **algorithm**: Actual left-closed piecewise function.
- **parameters**: Join c; derivative d.
- **quantifiers**: All f,g,c,d with premises.
- **guarantee**: Exact derivative at seam; generic library helper, no global regularity premise.

Actual producer: Constructs left derivative on Iic c and right derivative on Ioi c; value equality repairs the right representative at c; their union is univ. Does not assume derivative of the glued loss.

### `BanditRL.OnlineHuber.huber_three_pieces`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Real scalar Huber.
- **assumptions**: delta>=0.
- **information**: Pointwise deterministic.
- **algorithm**: Same half-quadratic/linear definition.
- **parameters**: Seams -delta,+delta; intercept -delta²/2.
- **quantifiers**: All residuals.
- **guarantee**: Exact three-piece identity; seams and coincident delta0 covered.

Actual producer: Cases r<=-delta then r<=delta, handles boundary equality by substitution, and expands absolute value with correct sign; no seam excluded.

### `BanditRL.OnlineHuber.huber_zero`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Real scalar Huber.
- **assumptions**: Threshold exactly0.
- **information**: No feedback dependence.
- **algorithm**: Actual huber0 function.
- **parameters**: Any residual.
- **quantifiers**: All real r.
- **guarantee**: Identically zero, including seam; degenerate library refinement.

Actual producer: If abs(r)<=0 then r=0; otherwise the outer coefficient0 annihilates the expression. Both cases truly yield0.

### `BanditRL.OnlineHuber.hasDerivAt_join`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Real scalar f,g and derivative profiles.
- **assumptions**: Both global derivative profiles; values and derivatives match at c.
- **information**: Deterministic profiles.
- **algorithm**: Actual glued function, not an assumed derivative oracle for Huber.
- **parameters**: c and query x.
- **quantifiers**: Every x and eligible functions.
- **guarantee**: Exact derivative profile; library gluing generalization.

Actual producer: For x<c and x>c uses neighborhood eventual equality; at x=c invokes local seam lemma with actual derivative matching. Global profile premises apply only to the two component functions.

### `BanditRL.OnlineHuber.huber_hasDerivAt`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Real scalar Huber.
- **assumptions**: delta>=0.
- **information**: No residual restriction.
- **algorithm**: Actual scalar derivative constructed by two joins.
- **parameters**: Saturated piecewise derivative.
- **quantifiers**: All real residuals.
- **guarantee**: HasDerivAt including both seams and delta0; not merely a total deriv equality.

Actual producer: Builds polynomial and affine derivatives, first glues at +delta then at -delta. Nonnegative delta orders seams, and matching identities also hold when they coincide. Converts the genuine three-piece equality.

### `BanditRL.OnlineHuber.huber_deriv_clamp`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Real scalar Huber.
- **assumptions**: delta>=0.
- **information**: Pointwise.
- **algorithm**: Actual deriv, supported by differentiability producer.
- **parameters**: max(-delta,min(r,delta)).
- **quantifiers**: All residuals.
- **guarantee**: Exact clamp identity, no residual bound.

Actual producer: Rewrites the proved HasDerivAt derivative then resolves the three min/max regions. Total deriv is not used as evidence of differentiability.

### `BanditRL.OnlineHuber.huber_convex`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Real full line.
- **assumptions**: delta>=0.
- **information**: Deterministic.
- **algorithm**: Actual globally differentiable loss; monotone derivative criterion.
- **parameters**: No strong-convexity constant.
- **quantifiers**: Every nonnegative threshold.
- **guarantee**: Global ConvexOn univ, not strong/strict convexity.

Actual producer: Uses actual everywhere differentiability and monotonicity of max/min derivative to produce global convexity.

### `BanditRL.OnlineHuber.huber_deriv_bound`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Real scalar derivative.
- **assumptions**: delta>=0.
- **information**: No observations needed.
- **algorithm**: Actual derivative clamp.
- **parameters**: Bound delta.
- **quantifiers**: All residuals.
- **guarantee**: Absolute derivative <=delta; not a bound on loss values.

Actual producer: Uses clamp lower bound -delta and upper bound delta, then abs_le; no bounded residual needed.

### `BanditRL.OnlineHuber.huber_deriv_source`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Real scalar derivative.
- **assumptions**: delta>=0.
- **information**: Pointwise.
- **algorithm**: Actual same Huber derivative.
- **parameters**: Inside residual; outside delta*sign(r).
- **quantifiers**: All residuals.
- **guarantee**: Exact printed branch expression, inner equality included.

Actual producer: Rewrites clamp and separates inner residual interval and positive/negative exterior. Sign at0 never produces an invalid branch.

### `BanditRL.OnlineHuber.huber_linear_hasGradientAt`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: delta>=0; no label/feature/predictor bound.
- **information**: Current z,y define actual loss.
- **algorithm**: Chain rule for huber(delta,<z,w>-y).
- **parameters**: Gradient deriv(H)(residual) times z.
- **quantifiers**: Every y,z,x.
- **guarantee**: HasGradientAt actual ambient loss, zero features and threshold allowed.

Actual producer: Composes innerSL derivative minus constant with actual Huber derivative, then identifies the continuous linear derivative with the inner-product dual of the proposed vector.

### `BanditRL.OnlineHuber.huber_linear_convex`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: delta>=0; CompleteSpace remains in actual type.
- **information**: Deterministic feature/label.
- **algorithm**: Actual affine composition.
- **parameters**: Whole unbounded space.
- **quantifiers**: Every z,y.
- **guarantee**: Global convexity; no finite-dimensional, bounded-domain or strictness premise.

Actual producer: Constructs actual affine map innerSL minus constant and applies proved scalar convexity under affine composition.

### `BanditRL.OnlineHuber.huber_linear_gradient_bound`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: delta>=0.
- **information**: Current actual loss only.
- **algorithm**: True gradient from preceding producer.
- **parameters**: delta*norm(z).
- **quantifiers**: Every z,y,x.
- **guarantee**: Uniform-in-x,y gradient bound; no supplied gradient-bound oracle.

Actual producer: Uses uniqueness of actual gradient from HasGradientAt, norm_smul, scalar absolute derivative bound and nonnegative feature norm.

### `BanditRL.OnlineHuber.project_fullSpace`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: No numeric assumptions.
- **information**: No feedback.
- **algorithm**: Actual chosen Hilbert projection on fullSpace.
- **parameters**: Full-space carrier, no ball/radius.
- **quantifiers**: Every x.
- **guarantee**: Projection identity; definition preserves closed/nonempty/convex carrier.

Actual producer: Invokes actual shared variational characterization with candidate x in univ; displacement is0. No selected projection identity is assumed.

### `BanditRL.OnlineHuber.huber_regular`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: delta>=0.
- **information**: Current z,y only.
- **algorithm**: Produces imported RegularLoss with U=univ.
- **parameters**: Actual global convexity and differentiability.
- **quantifiers**: Every z,y.
- **guarantee**: Stronger historical neighborhood API discharged, not extra source hypothesis.

Actual producer: Constructs U=univ, open/domain inclusion, actual global convexity, and pointwise differentiability from HasGradientAt. Stronger historical RegularLoss is produced.

### `BanditRL.OnlineHuber.huber_step`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: delta>=0; eta unrestricted real.
- **information**: Current loss updates next state after output.
- **algorithm**: Actual shared step/full-space projection identity.
- **parameters**: eta and saturated residual scalar.
- **quantifiers**: Every eta,y,z,x.
- **guarantee**: Exact update; negative eta allowed only for this identity, not regret guarantee.

Actual producer: Unfolds shared step, substitutes actual full-space projection, gradient identity and scalar source-sign formula. eta remains arbitrary in this algebraic identity.

### `BanditRL.OnlineHuber.huber_regret_fixed`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: delta,Z>=0; eta>0; norm(z_t)<=Z for t<T.
- **information**: Strict-prefix iterate; current features available for prediction; label for next update.
- **algorithm**: Same actual constant-eta iterate/regret.
- **parameters**: Any natural T; x0,u arbitrary.
- **quantifiers**: All prefixes and fixed comparators under stated feature bound.
- **guarantee**: R<=initial/(2eta)+eta*T(delta Z)²/2-terminal/(2eta); T0 exact cancellation; no diameter premise.

Actual producer: Applies actual shared theorem_2_13_fixed with produced RegularLoss. Bounds actual iterate gradient norms by delta*Z, squares with nonnegative norms, sums T terms, multiplies by positive eta/2, and preserves the negative terminal distance.

### `BanditRL.OnlineHuber.huber_average_bound`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: delta,Z>=0; T>0; finite-prefix feature bound.
- **information**: Known T fixed before run, not comparator/future-gradient tuning.
- **algorithm**: Actual same-run regret with eta_T=1/sqrtT.
- **parameters**: Coefficient1 instance of source proportional choice.
- **quantifiers**: Every T>0, x0,u, eligible streams.
- **guarantee**: One-sided upper (norm(x0-u)²+(delta Z)²)/(2sqrtT); negative residual dropped only here.

Actual producer: Produces T>0 real/sqrt/reciprocal positivity; applies fixed bound for that exact eta, proves terminal fraction nonnegative, and verifies square-root algebra before dividing by T. Only the nonpositive residual contribution is dropped.

### `BanditRL.OnlineHuber.huber_rate_tendsto`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: No signs on delta,Z; no algorithm/feature premises.
- **information**: Pure numeric sequence.
- **algorithm**: Envelope only, contains no iterate or regret.
- **parameters**: Fixed delta,Z,x0,u; natural T→infinity.
- **quantifiers**: All real delta,Z and fixed x0,u.
- **guarantee**: Numeric Tendsto0; does not license negative-threshold algorithm guarantee.

Actual producer: Composes natural-cast divergence, square-root divergence and reciprocal convergence to0, then multiplies by the fixed numeric coefficient. No regret expression occurs.

### `BanditRL.OnlineHuber.huber_average_eventually`

Verdict: accepted-with-explicit-delta, actual body scope.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: delta,Z>=0; global feature bound; epsilon>0.
- **information**: Family of independently horizon-tuned constant-step runs.
- **algorithm**: Actual shared regret at each horizon, fixed same initialization/streams.
- **parameters**: eta_T=1/sqrtT; comparator u fixed.
- **quantifiers**: Each u,epsilon has eventual cutoff; no uniform cutoff on unbounded u.
- **guarantee**: Eventually actual regret/T<epsilon only; no signed Tendsto0, absolute difference or anytime claim.

Actual producer: Combines numeric envelope eventually<epsilon and eventual T>0, applies actual average bound with global feature bound restricted to t<T, then transitivity gives strict one-sided actual inequality.

## Assumptions and information-order challenge

Nonnegative threshold is a disclosed source-implicit convention, not a source-printed inequality or arbitrary-real extension. Negative delta=-1 makes the specified loss -abs(r)-1/2, neither convex nor differentiable at0. Actual producers retain delta0, coincident seams, zero gradient and constant loss. Pure numeric rate accepts any real delta,Z, but its use as an algorithm envelope requires the separate nonnegative hypotheses.

Complete real Hilbert generality properly includes source finite Euclidean spaces; vector theorem class binders, including completeness where mathematically unnecessary, remain unchanged. fullSpace and linearLoss definition types themselves need no completeness. No label/residual/predictor norm/diameter premise is introduced. Source stock-history features are an illustrative predictable input; the proof handles arbitrary deterministic supplied feature/label sequences, without a probability or stock-generative claim.

Shared iterate0=x0 and iterate(t+1)=step(loss_t,iterate_t) plus actual iterate_prefix establish that the played vector uses strict past losses. Current z_t is used to form the prediction, then y_t supplies the residual and gradient for the next point. A total sequence argument in Lean is not itself an oracle reading future labels; the recursive equations and prefix theorem supply the actual information boundary. Comparator never selects eta or updates. This does not add a theorem about existence of an arbitrary feedback-generating environment.

Fixed endpoint permits T0 with exact initial/terminal cancellation, delta0 and Z0; it retains negative terminal distance and requires eta>0. Exact huber_step permits negative eta only as an identity. Average theorem uses a constant eta=1/sqrtT for each positive known-horizon run, coefficient1 of source proportional choice, not one anytime eta_t schedule. No future-gradient tuning appears.

Actual average performance is one-sided. With scalar z=1,y=0,delta1,x0=0 and comparator1, all actual iterates remain0 while comparator H1(1)=1/2 each round, hence regret/T=-1/2 at every positive horizon. This simple semantic argument is not a new Lean counterexample artifact. It confirms why no actual Tendsto0/absolute difference claim follows. The implemented eventual endpoint correctly permits such improvement over comparator; each fixed u and epsilon has its own cutoff, with no uniformity over unbounded u.

## Actual canary nonvacuity

All14 actual proof bodies were inspected: generic upper join; lower and upper seams; zero threshold; quadratic interior and affine exterior; actual nonzero vector gradient6, zero-threshold gradient0, norm bound6 and global convexity; genuine shared update2→3/2; actual sharp residual for every T; actual tuned T4 average upper5/4; and eventual actual average<1/10. The feature3/residual5 example exercises the saturated nonzero branch. The canary residual theorem includes T0 but no separate named zero-horizon evaluation is claimed. Bound5/4 is an upper bound, not realized-loss equality; eventual_tenth is the actual one-sided endpoint. No canary assumes the desired gradient or regret inequality.

## Reader corrections and remaining acceptance

No mathematical repair. The following eight source-contract reader obligations remain for the separate reader/integration phase, including preservation of qualifications already correctly present:

1. Keep delta>=0 as explicit source-implicit convention and delta0 as valid degeneracy; explain negative thresholds are not covered, rather than suggesting source prints the sign assumption.

2. Keep actual Hilbert-space generalization distinct from finite-dimensional source; three full definitions and retained CompleteSpace contexts matter, not only short headers.

3. Explain arbitrary deterministic feature/label streams generalize the illustrative stock-history construction; z_t is available before prediction, y_t after, without a stochastic stock model claim.

4. Publish produced global RegularLoss and actual full-space projection identity; no bounded predictor domain, labels/residual bounds, supplied desired gradients or regularity assumption.

5. Display the sharp fixed-step negative terminal residual, eta>0 and T>=0; explain T0 cancellation and delta0/Z0 compatibility. Separate unrestricted-eta update identity.

6. Distinguish coefficient1 known-horizon instance from all proportionality constants or a single eta_t schedule; comparator/future losses do not select eta.

7. State the numeric envelope alone tends0 and actual average regret is only eventually below every positive epsilon for each fixed comparator. Cutoffs need not be uniform; actual regret may stay negative.

8. Retain genuine seam/nonzero-gradient/update canaries and separate bound5/4 from realized equality. Count one printed example,19 retained proofs,3 definitions,0 new nodes; distinguish already compiled but unaudited remaining obligations from all-unproved wording.

Explicit combined root/Tests/full harness, contributor, clean site/shared registry, final reader and immutable binding/PR gates remain pending. This body decision does not change legacy counts, Chapter1 migration, Chapter2 totalnull/incomplete or whole-book active Goal. No merge, deployment, live, Chapter4/strongly-convex logarithmic result or broad source acceptance is granted. No production, contracts, old receipts or global frontier were edited by this reviewer.

## Exact raw inventory

| Path | Raw SHA-256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean` | `c7a80e952f6f577c441b92802fc5020fa63b564b75418fb96e29d4f6813020ca` |
| `.lake/packages/mathlib/Mathlib/Analysis/Convex/Deriv.lean` | `2022754e5f0c541b8ca4271231c95713996d9f4ac1f997e3973ec9e6c7bec7c4` |
| `.lake/packages/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean` | `2eb62a121ba6baca46b2722149d287f4ca5d58a6aeb81d24ce671d59b51a2337` |
| `BanditRLProof.lean` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `BanditRLProof/OnlineGradientDescent.lean` | `9300cb2735da9f125e404f78b86509df47fe65a5f4d89abc469e071bdffdb871` |
| `BanditRLProof/OnlineHuber.lean` | `dd7c6b4c41e5fee804196bbccfec493df37ae56294f32cddf3d11be27646de86` |
| `Tests.lean` | `1c60f84f3e4d6d778ac8374b46e47b27559d802986459533517034c97a30f048` |
| `Tests/OnlineHuberCanary.lean` | `aa5def531637c89f77f70e6b26f9fdc678c5e4ae4ebadb8334599f34575f4837` |
| `conversion-windows/ONLINE-HUBER-MIGRATION-20261006.md` | `5d3b459ec57c8e6f4ee9f8ed8c8b30b5c152b4039b63171d7babc034d8a90ac6` |
| `docs/contracts/online-huber-average-v1/context.json` | `603c601d1f3459232e060e99bec0b345f4e1374b038bf7a67f41cc69a0a2685e` |
| `docs/contracts/online-huber-average-v1/contract.md` | `10a31ace185e8855addef8490146455e31c14f9159222db0e05b2a88d803cfd6` |
| `docs/contracts/online-huber-average-v1/headers.json` | `adbfce20875e83dbdb46fedda055960329fec614b5503c13c427bb88e506fee5` |
| `docs/contracts/online-huber-average-v1/huber_average_bound.json` | `0e56def76942bcf0b3a136ac564f12880592fc052d46a0fce9d81028da53f425` |
| `docs/contracts/online-huber-average-v1/huber_average_eventually.json` | `194ee9200d3211f3f9ec17d2742507f77a9ef4c5c9b5c1e69389cc47a862fa5c` |
| `docs/contracts/online-huber-average-v1/huber_rate_tendsto.json` | `bf3439875a4eb6344f724e1f7cdcb4116e83e886a8a4b147e43024c85e9d4712` |
| `docs/contracts/online-huber-derivative-v1/context.json` | `501deeb610d4f3ced2919adc1f8af98ace98f88629cae55db9768fc38e206053` |
| `docs/contracts/online-huber-derivative-v1/contract.md` | `1f4926f0bdd225b5ec07d1fcce9177d6cc56ad01dc1ef20ae255860360f3bc9e` |
| `docs/contracts/online-huber-derivative-v1/hasDerivAt_join.json` | `9a94650e38c93247e04852bed7e897b47db894907809df38bcced058c96e277b` |
| `docs/contracts/online-huber-derivative-v1/headers.json` | `f812a8c8da5f529cb939c930434629833f340dc00b27b7ce393dce7146867344` |
| `docs/contracts/online-huber-derivative-v1/huber_hasDerivAt.json` | `02097251cda0eb767bcb82772320eeb0717a4d7d51d18a0303cea54361dde3b1` |
| `docs/contracts/online-huber-migration-v1/dependency-DAG-v1.json` | `27e68f557d807260dd4949a5fde59cd016a1419289cf92c4b3324159aa45987e` |
| `docs/contracts/online-huber-migration-v1/headers.json` | `350d790d61ee195ff32be914fceab33a9fb73938cb71835402de5b4fbcac600f` |
| `docs/contracts/online-huber-migration-v1/scoped-contexts.json` | `d26eb9e6687e0f3f92835b57002240ee870b8d774031c7d9a446f4ec66d8e373` |
| `docs/contracts/online-huber-migration-v1/source-card.json` | `5656d7352c0888681f243f597db20ef7bd2ee28f988e4978734d232a0a26d0f2` |
| `docs/contracts/online-huber-migration-v1/source-intent.md` | `fb5371035b10785f4ef4e974ab0da1e03a7a06ddfc34ab65b370dda6751fd901` |
| `docs/contracts/online-huber-ogd-v1/context.json` | `5e7578f48d1ccaa894079e44fc72bfb3c040a4ab1fec18a6bd19b275741a5c82` |
| `docs/contracts/online-huber-ogd-v1/contract.md` | `d2736e2df308e95ff05c78c7341a00c68a6d8d2df1c60b2b391aa06096025076` |
| `docs/contracts/online-huber-ogd-v1/headers.json` | `48de15430923031fd301df5535698d24847557f96ec0ed79fa1bf4f160cf080a` |
| `docs/contracts/online-huber-ogd-v1/huber_regret_fixed.json` | `2160b7c7f6835466cd0846432cda807a457337484d2280d29c70d53409448fc8` |
| `docs/contracts/online-huber-ogd-v1/huber_regular.json` | `6d9f900a2fdc18aa0f385bf99706e9aeb3da91ff2ea5379ae90c9421f6f99fdf` |
| `docs/contracts/online-huber-ogd-v1/huber_step.json` | `d77e87b2a85aa9e5151e04d64448f33c31187fbbd34ddda4ec587c59bd7696e6` |
| `docs/contracts/online-huber-ogd-v1/project_fullSpace.json` | `95946357555e7f3ecbf6baf82f3ce60e36a4e03998eaae6ae32a1c56dbfdcf47` |
| `docs/contracts/online-huber-scalar-v2/context.json` | `5b4c14824e2b7947a667d4651be6706209dd5a87f4945301f9fb5efa5426ce77` |
| `docs/contracts/online-huber-scalar-v2/contract.md` | `f4b9eea18b1c546315ac748282ad29dff5c748a17e5f04a87e07b32be8b0293d` |
| `docs/contracts/online-huber-scalar-v2/headers.json` | `ca695a50310070b8a58b6794d21f7ee3315999dc4e086e545ef80c0d94524334` |
| `docs/contracts/online-huber-scalar-v2/huber_three_pieces.json` | `ab2ca7fbf2e99eb21302e5ebbc371b7936253ed2cf86ec6129aa962e13a28ff2` |
| `docs/contracts/online-huber-scalar-v2/huber_zero.json` | `621d8ee81fb6fdff564bd777a3405830d4b1129f91ea136ff322477f6fbebe84` |
| `docs/contracts/online-huber-seam-v1/context.json` | `195882f52d827f125bdf75674af9d79d1d336cf7f945923dffa63ec1aafb7f8c` |
| `docs/contracts/online-huber-seam-v1/contract.md` | `27f479bcc0a2beeab8ec489e03afa8079db1bdd19af94607255c170682f29628` |
| `docs/contracts/online-huber-seam-v1/hasDerivAt_ite_le.json` | `45bf63ee614fa4e19a4e9859d6988fd26707348990eca520b70ee066b57fe174` |
| `docs/contracts/online-huber-seam-v1/headers.json` | `4ef87c91f8c827c729013c1b7154a8f057dd3d41ec4b75a5a73fd83a4b87d97d` |
| `docs/contracts/online-huber-vector-v1/context.json` | `2619efd9905b5c4c50da57d4418a04585cda6ff7cb5c45b1446caa4d22d6d281` |
| `docs/contracts/online-huber-vector-v1/contract.md` | `fb73b1ffe7f83f2a0e7e885a78bd912fbaf6d9f7959cef4503b31d802c4d61a7` |
| `docs/contracts/online-huber-vector-v1/headers.json` | `8c3e09f24e51541da3f49508376c226a2fcecfeb72883db3d8066fbbda018312` |
| `docs/contracts/online-huber-vector-v1/huber_linear_convex.json` | `dc7717005c426020a0d7a464af599df19774c2e6d12b8831e42f599cff8ac7a6` |
| `docs/contracts/online-huber-vector-v1/huber_linear_gradient_bound.json` | `3281295395720cec18e621ca89c53068de92ca175bbf720bdca9d7e1029f613f` |
| `docs/contracts/online-huber-vector-v1/huber_linear_hasGradientAt.json` | `fd1e0e65463bea2778e1768d9f42afe85e920b8abf4b5fcafdca4620c37fd136` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `proof-obligations/ONLINE-HUBER-MIGRATION-20261006.md` | `1d082a8bbc8b6deae770627a6f8889acc20dcdd31ba7519a2996645b98cc51fe` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `runs/online-guessing-migration-20261006/accepted-decision-v1.json` | `5c0fbeb8ea5aff99f9496a977e130fc1e3a9ea16faf8243f219c3fab054e7b9c` |
| `runs/online-guessing-migration-20261006/delivery-v1.md` | `a92bdc1b4f952bc378a62bad005ef3bf378aa787f0b82306af24c66dcd3866f8` |
| `runs/online-guessing-migration-20261006/native-acceptance-overlay-v1.json` | `8db2de754200595f4bcf705b0334f464da104ef790bae94be675e1e34ef055a6` |
| `runs/online-huber-20261003/independent-source-review.md` | `5f3d6b4b1d38afa01f8805963901ca1d5f896a8306d1310cbcdcd47718acd59c` |
| `runs/online-huber-20261003/roundtrip-bindings.json` | `865e3afa5ea7f0fb958410c4e4cb0ee84c45c509f013203582b99c22544cfd1d` |
| `runs/online-huber-20261003/source-audit.json` | `558ca3a72df7bc99a2000d97134b45364627240f22d185bfd3a243af434e85b2` |
| `runs/online-huber-migration-20261006/.gitattributes` | `d040b3211edd2ab15825c93a94734457d1c3e395803f10eeef3e9ba9ef858a74` |
| `runs/online-huber-migration-20261006/00_context.md` | `464dbf9508c1d4033b55c191ae402d18488b1b6a04d9d2e501461f798b4571ea` |
| `runs/online-huber-migration-20261006/10_upper_director-v1.md` | `cace9a0414f0f315d6c31fcd948e945be33dafe269f73d6866586607326b458d` |
| `runs/online-huber-migration-20261006/20_architect-v1.md` | `2ec8c8cb3842d681798cff1a8d4d2da3aebb3f7c9ffe7de6dce5bb2229058274` |
| `runs/online-huber-migration-20261006/30_lower_worker-body-audit-v1.md` | `638000840ff8ab215e0dfab911f4140249cfb1e1bb3ac0752ab6480207750f05` |
| `runs/online-huber-migration-20261006/CLI-help-v1-01-exit.json` | `7e85645af38c412b3f18f250011e36114ac8b3a3c365e2d416d0689c33752136` |
| `runs/online-huber-migration-20261006/CLI-help-v1-01.log` | `daacf23e36eec4898dce3b3de02a07b71fb0f80f08e33e8dfe00722e7572970c` |
| `runs/online-huber-migration-20261006/actual-types-readable-v2-01-exit.json` | `ea3c3b4d76cc0ec261f3fcc8a14b292a55493472701321b0ae68e1f22f648051` |
| `runs/online-huber-migration-20261006/actual-types-readable-v2-01.log` | `5baa4358ff052d15660866ca8b161b9c538f6ed011ab3727eacfeb6d18ef0b61` |
| `runs/online-huber-migration-20261006/actual-types-v1-01-exit.json` | `ece3b3303756f34094bc94c9ab0cbfb9ddf53468f5426dfe2552b89b8740b4df` |
| `runs/online-huber-migration-20261006/actual-types-v1-01.log` | `82cb22fb8f56b18cb165ad9c257ca02bc929effc1a302014f6d9f54fcff57810` |
| `runs/online-huber-migration-20261006/blind-packet-v1.md` | `fd3374ac3f548f8c577c7dd0cfc6a77733196ff40fad041b5ee7869e1c4246f7` |
| `runs/online-huber-migration-20261006/blind-receipt-v1.json` | `92af3e10e6da6940ea8fa5414c982c5d79bd635f8aa0e36e6fc9d2d2b6ad8aea` |
| `runs/online-huber-migration-20261006/blind-reconstruction-v1.md` | `80a182bbdb6ce6ecd9faf1f89947775f752b4ce6a614069611296da2c09c6040` |
| `runs/online-huber-migration-20261006/body-review-helper-before-use-v1.json` | `9598b24b575a1745fa6505bb96004ad9ad10608a358b3d8e17e68eb8537e2cee` |
| `runs/online-huber-migration-20261006/bootstrap-before-use-v1.json` | `b4fcc6064d97448667e0564d9c19d07d01c120d2fd0f87f237a4173dd65bd902` |
| `runs/online-huber-migration-20261006/bootstrap-generated-before-use-v1.json` | `31b964fd8abcbcf6a6b90330779ae6a78eec91958eccf5fac5f340ca08a8ee05` |
| `runs/online-huber-migration-20261006/bootstrap-v1.py` | `2f2ffa79f60c56254129d17b8e3389aa203bdf8886f9a3b5fe96c08ec49440bc` |
| `runs/online-huber-migration-20261006/compiled-retained-graph-v1.json` | `7135a53ca48c7fe831f5dfb8b9a0347e42b1629e39a7b807cd9bccb94883bd9a` |
| `runs/online-huber-migration-20261006/contract-binding-audit-v1.json` | `ad869e50482c288a42ec281a8af6248ff3c12d77ece534b2550b46c6a5f188e4` |
| `runs/online-huber-migration-20261006/contract-source-inputs-v1.json` | `5efbc49401938a6e2ca75fe2737a3304291744e0fa255300cce15adbaefb1345` |
| `runs/online-huber-migration-20261006/draft-fence-hasDerivAt_ite_le-v1-exit.json` | `8dddc936f7f946a9a05d44e6e5f018492608f489f3eadb089e6d0d8594c0cd88` |
| `runs/online-huber-migration-20261006/draft-fence-hasDerivAt_ite_le-v1.log` | `29f50484e415ab375f45d8651d679dd2ca31fb293d770de8ec1a47a9d071fd8e` |
| `runs/online-huber-migration-20261006/draft-fence-hasDerivAt_join-v1-exit.json` | `7f2b23446a3ad2ae292643b83e4e47a61a54e4bc2779f75f460a10fece15d6b3` |
| `runs/online-huber-migration-20261006/draft-fence-hasDerivAt_join-v1.log` | `26134e0d8b08f55f196327dfa92eb4fc5208ebf23b67dceed8c24928fcacb880` |
| `runs/online-huber-migration-20261006/draft-fence-huber_average_bound-v1-exit.json` | `51f9df454ad6b363503ae738172b45d31728bd041267859921fe484d057dc4d8` |
| `runs/online-huber-migration-20261006/draft-fence-huber_average_bound-v1.log` | `2102682c315da34cb3708e33d058d8ed57b8e86df75af61ed3a5dc3409133fcb` |
| `runs/online-huber-migration-20261006/draft-fence-huber_average_eventually-v1-exit.json` | `921239559b57666997ec965515cf60e78cf264af2187328b1e825b9ae5434953` |
| `runs/online-huber-migration-20261006/draft-fence-huber_average_eventually-v1.log` | `4c145bf9828b7ad4351063f3d763f7fc1d57a2d94131c7bb9612f7c24a1a7774` |
| `runs/online-huber-migration-20261006/draft-fence-huber_convex-v1-exit.json` | `f602d624511f41a0e5e482aab5db9918a8462f55d9a8b44cdf762f0bc22b3e8c` |
| `runs/online-huber-migration-20261006/draft-fence-huber_convex-v1.log` | `e87b4afae14c918270dc1016d2c43e27838587ec62b72458b8ec15277406fc1f` |
| `runs/online-huber-migration-20261006/draft-fence-huber_deriv_bound-v1-exit.json` | `7a5a0c9db7ccba19dc4e3341c65954b355f2e77425c20d6ac15b78f430e98a9e` |
| `runs/online-huber-migration-20261006/draft-fence-huber_deriv_bound-v1.log` | `d7a66c29bf320d737d415443b4bdb3c352af6be7014aa32400cba9bf7144353f` |
| `runs/online-huber-migration-20261006/draft-fence-huber_deriv_clamp-v1-exit.json` | `741fb63b1fa523f188cf7083ab75cbb1ff1a7b2a73f3fea83ba187b2d621bfe5` |
| `runs/online-huber-migration-20261006/draft-fence-huber_deriv_clamp-v1.log` | `4d487b7b827fb358a196bebdb0d65745e259a6bbdb6de5c5ef4bca7075d2384b` |
| `runs/online-huber-migration-20261006/draft-fence-huber_deriv_source-v1-exit.json` | `49055cfa78f516763fded04823489fcc2a195539e681836df4bf1e207e55fe3f` |
| `runs/online-huber-migration-20261006/draft-fence-huber_deriv_source-v1.log` | `27af67579a8b25ee5a023ac5d76248d9f8dab91e9bc834722b49c262dccf6ee5` |
| `runs/online-huber-migration-20261006/draft-fence-huber_hasDerivAt-v1-exit.json` | `d6ccb20dda6b169dbfd28e304e610aea705867b1aa555ed7d3205507c63c8ada` |
| `runs/online-huber-migration-20261006/draft-fence-huber_hasDerivAt-v1.log` | `d676fe2759c38e22009827ee9cb22ef8b3a60d1ec575cfdf3951bbc4e123cd4b` |
| `runs/online-huber-migration-20261006/draft-fence-huber_linear_convex-v1-exit.json` | `be680c09d433b406aa95765d1d48c62269801b4c29527c629d70ebb03ab47ce2` |
| `runs/online-huber-migration-20261006/draft-fence-huber_linear_convex-v1.log` | `9db6837bea2b4f7bca48dc1d7d334076d9a2554e7173672ec3060da7cffa4075` |
| `runs/online-huber-migration-20261006/draft-fence-huber_linear_gradient_bound-v1-exit.json` | `3bd28c849ec2dc965c5987a6426963331d4405b86a4e8fb38823cfbf4b1135f9` |
| `runs/online-huber-migration-20261006/draft-fence-huber_linear_gradient_bound-v1.log` | `f4fe585c422219f138966efb957c58e2f529f6b6fc0009b9625553c01227591e` |
| `runs/online-huber-migration-20261006/draft-fence-huber_linear_hasGradientAt-v1-exit.json` | `389663c6acf5f5e6dbc5bc4c69368113ea724d94cc8e52788514eb668f4ecf19` |
| `runs/online-huber-migration-20261006/draft-fence-huber_linear_hasGradientAt-v1.log` | `02f2694235760a9478ee56db453dd5534d33f0981bce904b6b9ff73e87c6e076` |
| `runs/online-huber-migration-20261006/draft-fence-huber_rate_tendsto-v1-exit.json` | `0c0738ddbfd1b89cf2a28d50f2e5c0152ed3edc7e806ec34b60f95a3972a9f70` |
| `runs/online-huber-migration-20261006/draft-fence-huber_rate_tendsto-v1.log` | `930016f901017b6b8834ea6eaf5b513159fd02e84543a1dfe2418a206697febd` |
| `runs/online-huber-migration-20261006/draft-fence-huber_regret_fixed-v1-exit.json` | `e8f2a99a21cc242568e9d1cd40435b72b4d34884ffd6f23c3b2b1363803711dd` |
| `runs/online-huber-migration-20261006/draft-fence-huber_regret_fixed-v1.log` | `8e3a793697c0abbb16ff2f76a4bfee7cae527d4cd8fbca37b996395c1d02ce7b` |
| `runs/online-huber-migration-20261006/draft-fence-huber_regular-v1-exit.json` | `3b2bd18efb4728ab23dd4ccf8501a14ed7fbf370c601e18468b431fc5c3ab421` |
| `runs/online-huber-migration-20261006/draft-fence-huber_regular-v1.log` | `41e2d8241b0c9322f7900cfe2e8555cff1ba6004277e9fc514aa80277c3dc51c` |
| `runs/online-huber-migration-20261006/draft-fence-huber_step-v1-exit.json` | `a5d7c30542a594ba0bba7ff6e9c1048f827d3d834f755a71410adf2ceabf5e24` |
| `runs/online-huber-migration-20261006/draft-fence-huber_step-v1.log` | `f9c324668cc97a0543c67043b02f96f451b8ee8eb3c7f65bdec86d22c864ba14` |
| `runs/online-huber-migration-20261006/draft-fence-huber_three_pieces-v1-exit.json` | `f909cf1ede93c20d8e37cbc310bd3e4af1539053a96db09016875d501b7c5255` |
| `runs/online-huber-migration-20261006/draft-fence-huber_three_pieces-v1.log` | `ed3e8770d93245f5873c3cdb2be6ecacb892b9aa907c01f7c87c3c364d05d863` |
| `runs/online-huber-migration-20261006/draft-fence-huber_zero-v1-exit.json` | `17b3accbf4b4c99da8466c4dbd6a1f17a1e4c9256fed17f141dcb6c30f6ea7ad` |
| `runs/online-huber-migration-20261006/draft-fence-huber_zero-v1.log` | `4142c76b92e856279489492d4153073692507fd3bcd8559029538fb267d492be` |
| `runs/online-huber-migration-20261006/draft-fence-project_fullSpace-v1-exit.json` | `7e33132d3c7cd032ac15633d8c022bf0936b1dff78d0cbf80f6a981b71dc6a48` |
| `runs/online-huber-migration-20261006/draft-fence-project_fullSpace-v1.log` | `02b0f1db1066c6533d330b610809fb8266a935ff066646656439dbbaecdec026` |
| `runs/online-huber-migration-20261006/draft-freeze-v1.json` | `5171cce83cfb46e942a52e4882252506df9df9489ba383045d7131306194c287` |
| `runs/online-huber-migration-20261006/draft-generated-before-use-v1.json` | `83c0ed76f242c89e977305d4bc030a96b97530f8674482b246296f730a319d1e` |
| `runs/online-huber-migration-20261006/draft-helper-before-use-v1.json` | `73da6dab2ce8cc6a011bdd261fcf0c1caeec8e59f7ff47a5a93cdd78751b30bd` |
| `runs/online-huber-migration-20261006/draft-lifecycle-v1-exit.json` | `54fdd2ef3e7a684e260643eec7bf856ebc13f1fab4b722c110c1d93d9e8b82a8` |
| `runs/online-huber-migration-20261006/draft-lifecycle-v1.log` | `893bc4454bfcaaf8ac9017c7f2802a89c31be1123d5dd1aed412f199e0103284` |
| `runs/online-huber-migration-20261006/fence-help-v1-01-exit.json` | `e6e37950031fc6a012b930ca54bf8b8ebf26294bb53c780efd70b5026d04ebb3` |
| `runs/online-huber-migration-20261006/fence-help-v1-01.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |
| `runs/online-huber-migration-20261006/focused-v1-01-exit.json` | `a774eb4fd71ee70704b770ee674ebe992d5486dd284565ccfe58298a792a1fd8` |
| `runs/online-huber-migration-20261006/focused-v1-01.log` | `74554cdba57a493a3c5721815ad03828705019e859867573934d8e6e8bb546d1` |
| `runs/online-huber-migration-20261006/historical-raw-supersession-v1.json` | `f2af08e0d00bf61704e15a459c97e2cdc795456fc60c7a5e0e2eb826144463bf` |
| `runs/online-huber-migration-20261006/leaves/actual-types-readable-v2.lean` | `36bda51865164e2aa127958148b136ce820c54ccc876e1684b5eee3ab166ff29` |
| `runs/online-huber-migration-20261006/leaves/actual-types-v1.lean` | `95e0fff76b0ea2eb9034ec8d737d1d73b6ffdf40225f48504a94d1fe89f457c4` |
| `runs/online-huber-migration-20261006/leaves/export-scoped-dependencies-v1.lean` | `ae405733a1da06895f0e9dd8414b9d571025ba759a49be76067487bbf47bc15e` |
| `runs/online-huber-migration-20261006/leaves/pre-integration-BanditRLProof--OnlineHuber.lean.txt` | `dd7c6b4c41e5fee804196bbccfec493df37ae56294f32cddf3d11be27646de86` |
| `runs/online-huber-migration-20261006/leaves/pre-integration-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-huber-migration-20261006/leaves/pre-integration-MANIFEST.md.txt` | `f8bec8d5d588a3d8ceba8a895f482a1b959c1b0130c5aeaef08c8944742a325b` |
| `runs/online-huber-migration-20261006/leaves/pre-integration-Tests.lean.txt` | `1c60f84f3e4d6d778ac8374b46e47b27559d802986459533517034c97a30f048` |
| `runs/online-huber-migration-20261006/leaves/pre-integration-runs--lifecycle_sessions.jsonl.txt` | `179bec296cceda02f99d4ff7ec52a7871c5c90b889b61f90c60effa0f3c5c940` |
| `runs/online-huber-migration-20261006/leaves/pre-integration-runs--trials.jsonl.txt` | `13fa462d91ca635dd9aafa7e24f8e6727835dcde119246a638c7f566086c5130` |
| `runs/online-huber-migration-20261006/leaves/pre-integration-website--content--chapters.json.txt` | `882959c8c0819f77df682331a139ac2e9f8f4d26d4a8a718c948c88b8ee751ef` |
| `runs/online-huber-migration-20261006/leaves/pre-integration-website--content--highlights.json.txt` | `ab30a70922444f721bda53de340961f2ad8ac8dae6d0cc10bd5e6d6d870c4cfa` |
| `runs/online-huber-migration-20261006/leaves/pre-integration-website--content--readings.json.txt` | `081ebbec0b07777bf678cbf9e0f6e513695ff012d0222e6a9cf2ea27b0de1ef4` |
| `runs/online-huber-migration-20261006/leaves/public-axioms-v1.lean` | `7f543bfaa85e4a6dc115a2df2c6365f248678705582256755ed52d4945963638` |
| `runs/online-huber-migration-20261006/lifecycle-help-v1-01-exit.json` | `2047762c183e598ff3ebf43b000dba39a6770e477a33291f123346fe1bda93c4` |
| `runs/online-huber-migration-20261006/lifecycle-help-v1-01.log` | `b1e8b438a9b725793b9888d206e98a971ace3df200ec90ed9cb63eab26b28507` |
| `runs/online-huber-migration-20261006/list-mathlib-v1-01-exit.json` | `cc9d0d010fa31e8247bba338d52fa921a2064773e28bb84499fa6bdae789e417` |
| `runs/online-huber-migration-20261006/list-mathlib-v1-01.log` | `884fab88619a3d1adcafe89eecddd2d98f4be5c6fa61262862134dde9e51d225` |
| `runs/online-huber-migration-20261006/list-papers-v1-01-exit.json` | `dffd2a0ba4c3f631cfa1586b439cbeba0f700ef48f04eae3a1fc997eb17aa757` |
| `runs/online-huber-migration-20261006/list-papers-v1-01.log` | `9acd333996a893a7b5ccad3e674ece26ef05c8b737e7816b33043b121583a619` |
| `runs/online-huber-migration-20261006/list-weapons-v1-01-exit.json` | `a107152ab3e057b38d61a2617605a5f70d54a7e760632eda9c33b9e7a3cfb572` |
| `runs/online-huber-migration-20261006/list-weapons-v1-01.log` | `a6e4b78de1a30fcf5a0ee66b868eb3ac1bfa68d2250c713f61e690ae064f7ef6` |
| `runs/online-huber-migration-20261006/local-lookup-v1-01-exit.json` | `0f58a3346ee8364bf8ce8cd012ed8a3db80b899b5bc4051ebbea019cb8e6f088` |
| `runs/online-huber-migration-20261006/local-lookup-v1-01.log` | `780555a22de32862b2418211bef6329a5342f91f9e13794e57b8f6bcdc76ba5a` |
| `runs/online-huber-migration-20261006/local-retrieval-help-v1-01-exit.json` | `dfe8f5bbbc68248e81caf7f2a65c73058c3996c719706b3f525428c8f952faa7` |
| `runs/online-huber-migration-20261006/local-retrieval-help-v1-01.log` | `258218f16a12b1a530d85ae83e6c2449237af8a0a1153bb35de40245d665b131` |
| `runs/online-huber-migration-20261006/native-draft-fences/hasDerivAt_ite_le.json` | `29f50484e415ab375f45d8651d679dd2ca31fb293d770de8ec1a47a9d071fd8e` |
| `runs/online-huber-migration-20261006/native-draft-fences/hasDerivAt_join.json` | `26134e0d8b08f55f196327dfa92eb4fc5208ebf23b67dceed8c24928fcacb880` |
| `runs/online-huber-migration-20261006/native-draft-fences/huber_average_bound.json` | `2102682c315da34cb3708e33d058d8ed57b8e86df75af61ed3a5dc3409133fcb` |
| `runs/online-huber-migration-20261006/native-draft-fences/huber_average_eventually.json` | `4c145bf9828b7ad4351063f3d763f7fc1d57a2d94131c7bb9612f7c24a1a7774` |
| `runs/online-huber-migration-20261006/native-draft-fences/huber_convex.json` | `e87b4afae14c918270dc1016d2c43e27838587ec62b72458b8ec15277406fc1f` |
| `runs/online-huber-migration-20261006/native-draft-fences/huber_deriv_bound.json` | `d7a66c29bf320d737d415443b4bdb3c352af6be7014aa32400cba9bf7144353f` |
| `runs/online-huber-migration-20261006/native-draft-fences/huber_deriv_clamp.json` | `4d487b7b827fb358a196bebdb0d65745e259a6bbdb6de5c5ef4bca7075d2384b` |
| `runs/online-huber-migration-20261006/native-draft-fences/huber_deriv_source.json` | `27af67579a8b25ee5a023ac5d76248d9f8dab91e9bc834722b49c262dccf6ee5` |
| `runs/online-huber-migration-20261006/native-draft-fences/huber_hasDerivAt.json` | `d676fe2759c38e22009827ee9cb22ef8b3a60d1ec575cfdf3951bbc4e123cd4b` |
| `runs/online-huber-migration-20261006/native-draft-fences/huber_linear_convex.json` | `9db6837bea2b4f7bca48dc1d7d334076d9a2554e7173672ec3060da7cffa4075` |
| `runs/online-huber-migration-20261006/native-draft-fences/huber_linear_gradient_bound.json` | `f4fe585c422219f138966efb957c58e2f529f6b6fc0009b9625553c01227591e` |
| `runs/online-huber-migration-20261006/native-draft-fences/huber_linear_hasGradientAt.json` | `02f2694235760a9478ee56db453dd5534d33f0981bce904b6b9ff73e87c6e076` |
| `runs/online-huber-migration-20261006/native-draft-fences/huber_rate_tendsto.json` | `930016f901017b6b8834ea6eaf5b513159fd02e84543a1dfe2418a206697febd` |
| `runs/online-huber-migration-20261006/native-draft-fences/huber_regret_fixed.json` | `8e3a793697c0abbb16ff2f76a4bfee7cae527d4cd8fbca37b996395c1d02ce7b` |
| `runs/online-huber-migration-20261006/native-draft-fences/huber_regular.json` | `41e2d8241b0c9322f7900cfe2e8555cff1ba6004277e9fc514aa80277c3dc51c` |
| `runs/online-huber-migration-20261006/native-draft-fences/huber_step.json` | `f9c324668cc97a0543c67043b02f96f451b8ee8eb3c7f65bdec86d22c864ba14` |
| `runs/online-huber-migration-20261006/native-draft-fences/huber_three_pieces.json` | `ed3e8770d93245f5873c3cdb2be6ecacb892b9aa907c01f7c87c3c364d05d863` |
| `runs/online-huber-migration-20261006/native-draft-fences/huber_zero.json` | `4142c76b92e856279489492d4153073692507fd3bcd8559029538fb267d492be` |
| `runs/online-huber-migration-20261006/native-draft-fences/project_fullSpace.json` | `02b0f1db1066c6533d330b610809fb8266a935ff066646656439dbbaecdec026` |
| `runs/online-huber-migration-20261006/native-public-fences/hasDerivAt_ite_le.json` | `14848bf2e339e957c5d27338d46084885174f959c0d75cfd2ec72a1ec0cb2289` |
| `runs/online-huber-migration-20261006/native-public-fences/hasDerivAt_join.json` | `e9a68b0767a8e11370226d0c9b1c5fc128365855e5630046a5bec4be64ee242b` |
| `runs/online-huber-migration-20261006/native-public-fences/huber_average_bound.json` | `b062296177f67b29b69b9a75a2fdaf4bf754e948012eb2a0101255f94e7a1038` |
| `runs/online-huber-migration-20261006/native-public-fences/huber_average_eventually.json` | `ba225f2f0c3b7d9cb8eb030bd518afb7afa74ee99e36d97ebb17272f0d13784e` |
| `runs/online-huber-migration-20261006/native-public-fences/huber_convex.json` | `1dcc8e29c004a0b6457a1d64e192765042b60ddcd514af70a8aedc91540922f0` |
| `runs/online-huber-migration-20261006/native-public-fences/huber_deriv_bound.json` | `1a5cd729b7682459bbd47ae91691267c8cfbc06dce6c1982682971a917d6f114` |
| `runs/online-huber-migration-20261006/native-public-fences/huber_deriv_clamp.json` | `00b7258e982baffafda1b7c296b284afdcbf3de8b4c543cb3d8f804c88e5283e` |
| `runs/online-huber-migration-20261006/native-public-fences/huber_deriv_source.json` | `2f7a6c362926eade96aaa46be8fed88914f2d65db3bd1ace164cdff8fb2fa10c` |
| `runs/online-huber-migration-20261006/native-public-fences/huber_hasDerivAt.json` | `7d589dfa72ec34897643226240365909ad77213c3f42a80b3a5979b498ae7060` |
| `runs/online-huber-migration-20261006/native-public-fences/huber_linear_convex.json` | `b8e3af8617adc453ac6a0e687015db9b0fa5d8a6da796a309469269045a00ac2` |
| `runs/online-huber-migration-20261006/native-public-fences/huber_linear_gradient_bound.json` | `0f231817d34aaf549ac1ca1dfc3041297070b65ce0ee200518e71b9a7b30697f` |
| `runs/online-huber-migration-20261006/native-public-fences/huber_linear_hasGradientAt.json` | `a83d3987d670a7e184ade5616fef2d99eb6de59f8f7af5e217b8c90b35436691` |
| `runs/online-huber-migration-20261006/native-public-fences/huber_rate_tendsto.json` | `fd47b834dd701a580dcce804a168379aca58ec81ef05f0baf3c6bfde2bbfaba8` |
| `runs/online-huber-migration-20261006/native-public-fences/huber_regret_fixed.json` | `622d45bf5b9aba980925b635300435d7c0cea0abd68bc058d74f6728e8fe0ed9` |
| `runs/online-huber-migration-20261006/native-public-fences/huber_regular.json` | `0590b98690a35d8bf7824921b225fd0dfadb2c4dc7a3e8288c8ce2bbbe49ff64` |
| `runs/online-huber-migration-20261006/native-public-fences/huber_step.json` | `aa694a2f4b3580007548bf35a400cd74ec6597d335ca8277bd8e030be07b9463` |
| `runs/online-huber-migration-20261006/native-public-fences/huber_three_pieces.json` | `20faf7e5f4185f101288222cd6aa7b838860de5d0b25635adde60cbd2e7b47e5` |
| `runs/online-huber-migration-20261006/native-public-fences/huber_zero.json` | `c580fe8e768f61d968bc6715a30f2aa16de7d2d2d6bdf21c144d032e743fc358` |
| `runs/online-huber-migration-20261006/native-public-fences/project_fullSpace.json` | `71181366071e424d25f8fbbd32f44160ca8cd43166ab55003d2a79b60c98d34c` |
| `runs/online-huber-migration-20261006/original-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-huber-migration-20261006/original-OnlineHuber.lean.txt` | `dd7c6b4c41e5fee804196bbccfec493df37ae56294f32cddf3d11be27646de86` |
| `runs/online-huber-migration-20261006/original-OnlineHuberCanary.lean.txt` | `aa5def531637c89f77f70e6b26f9fdc678c5e4ae4ebadb8334599f34575f4837` |
| `runs/online-huber-migration-20261006/original-Tests.lean.txt` | `1c60f84f3e4d6d778ac8374b46e47b27559d802986459533517034c97a30f048` |
| `runs/online-huber-migration-20261006/prepare-body-review-v1.py` | `d2076f1236c3686822e9111b97b17a6ac2b9f0631671c88e4caae3f59908a54b` |
| `runs/online-huber-migration-20261006/prepare-draft-v1-01-exit.json` | `3a5e60ff6d4b9554729fbce1fee89da10abeb59c1994f5c5760bc87778daaf45` |
| `runs/online-huber-migration-20261006/prepare-draft-v1-01.log` | `b3201aae5aef7ba406a78b0d5d4dd771100aca7c102b079bc1d8ba6e537a78cc` |
| `runs/online-huber-migration-20261006/prepare-draft-v1.py` | `11025fb56e5aff210f43c956f06c20625d790366ceefff6e11b7e37611c065f1` |
| `runs/online-huber-migration-20261006/prepare-proving-v1-01-exit.json` | `724f2bdef9e46094dd4630a6d630b88c488ccb2ffaa057e25214e3069cec7521` |
| `runs/online-huber-migration-20261006/prepare-proving-v1-01.log` | `e07c674986eaccd960f37c8947879bec441e589681923831b3eb84dd7b9276a1` |
| `runs/online-huber-migration-20261006/prepare-proving-v1.py` | `a4f322bd0671b9994f62404ce1b2f7fe6b81f51de66823f499846afad6cbba21` |
| `runs/online-huber-migration-20261006/prepare-source-review-v1-01-exit.json` | `9e82699d77086375c7c79c099736c156c0a519dc0b49ea83655e7100b4092bfc` |
| `runs/online-huber-migration-20261006/prepare-source-review-v1-01.log` | `ba4ca907a24ffe2239237b1fca9a36aecb570186453f56ac84908d01f398d8fb` |
| `runs/online-huber-migration-20261006/prepare-source-review-v1.py` | `d4bcb9a8a7f07411c478cdf14b133d27cbb0cf8227796ef6a323645950a6eab3` |
| `runs/online-huber-migration-20261006/prior-contract-binding-v1.json` | `42095bc6b23f6ba6483c5cc71feedd8bc9b7c0550944c8739f7a770951590540` |
| `runs/online-huber-migration-20261006/proof-obligations-proving-v1.json` | `d2bc6e713808bf931398efa64be3ea3beaa55368d38796aa4cf979c0142693a5` |
| `runs/online-huber-migration-20261006/proof-obligations-v1.json` | `90f425b08d4af7a516f872513c8468615048b6699b11bb9ee0e8978a2e32d3bc` |
| `runs/online-huber-migration-20261006/proving-helpers-before-use-v1.json` | `d030d43bb4ad53f8c8fa5a91e9ec903c271a0161b19fe84d59fa10d67ea396f0` |
| `runs/online-huber-migration-20261006/proving-lifecycle-v1-exit.json` | `85c1d38d94a9c38bbdf25a0b58dc28dcea95bc56006666e5e4ed3ed7acff367e` |
| `runs/online-huber-migration-20261006/proving-lifecycle-v1.log` | `3473525adc57ac597f68e1fc8abb8d3e3f265576a006a5d885fceaee13bf6ef1` |
| `runs/online-huber-migration-20261006/public-actual-bindings-v1.json` | `3b83474bcdfc1718fa2823eab2ba5b9e44bc21087a0c0f962d18f9ffee6b1c55` |
| `runs/online-huber-migration-20261006/public-axioms-v1-01-exit.json` | `edb24b4eca58f8879d7ad0f1c17c6bffd2c7d83a881e43f9fe85dff797527f06` |
| `runs/online-huber-migration-20261006/public-axioms-v1-01.log` | `bd16c3bc07935413622535fc8fe59ddcd3a19b0e039882ba6386bbef72f3ea98` |
| `runs/online-huber-migration-20261006/public-body-review-packet-v1.md` | `5d9cabef6d71473bf8fc88c876f516748747f10bc38106d031674a3876c98bc9` |
| `runs/online-huber-migration-20261006/public-body-v1-01-exit.json` | `c2343e34ed75178e79fb54a16d15ccfefb500bd98fe027c0ed7901f38797e658` |
| `runs/online-huber-migration-20261006/public-body-v1-01.log` | `82977348fc2013a6d383a2107939b1acd965973bae20cd07e256574e7cb2dba9` |
| `runs/online-huber-migration-20261006/public-canary-v1-01-exit.json` | `b1223f7846da8a6e69c87747ae0bcbe0be1d0505d6a99747efcfd184c3414192` |
| `runs/online-huber-migration-20261006/public-canary-v1-01.log` | `ec29937f2f8e0c76b830f831f228454746d396f3bd860384c791cc1a42f937e6` |
| `runs/online-huber-migration-20261006/public-fence-v1-hasDerivAt_ite_le-exit.json` | `9bfdf76a2576b0e6057cb5b25eff605123a263631ae4d53d672c71f29d9e7786` |
| `runs/online-huber-migration-20261006/public-fence-v1-hasDerivAt_ite_le.log` | `14848bf2e339e957c5d27338d46084885174f959c0d75cfd2ec72a1ec0cb2289` |
| `runs/online-huber-migration-20261006/public-fence-v1-hasDerivAt_join-exit.json` | `61ef056465d40c95766f99a7e04d80fe518f3437e9e57294d3c7099ac1294c5b` |
| `runs/online-huber-migration-20261006/public-fence-v1-hasDerivAt_join.log` | `e9a68b0767a8e11370226d0c9b1c5fc128365855e5630046a5bec4be64ee242b` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_average_bound-exit.json` | `00b26a5ceb45021310d33bb103ba363d155c5c7c8b0ccc4a2832d5e40ede9f7a` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_average_bound.log` | `b062296177f67b29b69b9a75a2fdaf4bf754e948012eb2a0101255f94e7a1038` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_average_eventually-exit.json` | `286489a8dbeeb5aa2af6eb4a41a9d76b01e976f64db7f7648ee128b9201d730a` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_average_eventually.log` | `ba225f2f0c3b7d9cb8eb030bd518afb7afa74ee99e36d97ebb17272f0d13784e` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_convex-exit.json` | `417840dc64fb04d95f99df3ae928776467f6135af0b41b02cdb1babf96dc1aef` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_convex.log` | `1dcc8e29c004a0b6457a1d64e192765042b60ddcd514af70a8aedc91540922f0` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_deriv_bound-exit.json` | `6b629b98b018b99cdb5d877cd3db191e3d3f3efbb486ad0136dadb56107e7acf` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_deriv_bound.log` | `1a5cd729b7682459bbd47ae91691267c8cfbc06dce6c1982682971a917d6f114` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_deriv_clamp-exit.json` | `e3cd8b0087afceb17fb221b57db9cc0f0ba76ff5fa8d24429a510f28cc6e5dcc` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_deriv_clamp.log` | `00b7258e982baffafda1b7c296b284afdcbf3de8b4c543cb3d8f804c88e5283e` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_deriv_source-exit.json` | `a6ccdc3138baf4639def08ad8b59436847e16469313c4db852cbf19c475ceff9` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_deriv_source.log` | `2f7a6c362926eade96aaa46be8fed88914f2d65db3bd1ace164cdff8fb2fa10c` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_hasDerivAt-exit.json` | `df785482c1e1a376bcb48033e38bd6be4c6f95e298f73414cf4011cf18955f32` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_hasDerivAt.log` | `7d589dfa72ec34897643226240365909ad77213c3f42a80b3a5979b498ae7060` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_linear_convex-exit.json` | `8a101e1db2f60ffcbc8caae24e581f422350e5c440ecded21da23309b35b7635` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_linear_convex.log` | `b8e3af8617adc453ac6a0e687015db9b0fa5d8a6da796a309469269045a00ac2` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_linear_gradient_bound-exit.json` | `17a9e336c0f15415d8524455c307084f4a3e3a10982651b8c79eeb3fc74a7080` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_linear_gradient_bound.log` | `0f231817d34aaf549ac1ca1dfc3041297070b65ce0ee200518e71b9a7b30697f` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_linear_hasGradientAt-exit.json` | `9f7e3098f802e1f9da17c8fe2338587dec77806460c60cd00c2cef7c59a3e6c0` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_linear_hasGradientAt.log` | `a83d3987d670a7e184ade5616fef2d99eb6de59f8f7af5e217b8c90b35436691` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_rate_tendsto-exit.json` | `1abace6972527b875aa2da9becb3df218e8ed4c9db9aba7f6f92bbb50be07e13` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_rate_tendsto.log` | `fd47b834dd701a580dcce804a168379aca58ec81ef05f0baf3c6bfde2bbfaba8` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_regret_fixed-exit.json` | `7a93ddb86ef9bf74ddaeede7f002e2cdc1ddff243c6e79bfc64287478fbda477` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_regret_fixed.log` | `622d45bf5b9aba980925b635300435d7c0cea0abd68bc058d74f6728e8fe0ed9` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_regular-exit.json` | `8258e5a065ac6add4ba3a31177a03c204d4c50736252ea7eaa8dc0eab00f6786` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_regular.log` | `0590b98690a35d8bf7824921b225fd0dfadb2c4dc7a3e8288c8ce2bbbe49ff64` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_step-exit.json` | `3a398d86abe42212bf3917d6aaf728ac24babed96f11c6727314d355b8c19043` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_step.log` | `aa694a2f4b3580007548bf35a400cd74ec6597d335ca8277bd8e030be07b9463` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_three_pieces-exit.json` | `803efcb025b35e37f72c8705568df85c28b9f51921e2752dc2866969f677ea06` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_three_pieces.log` | `20faf7e5f4185f101288222cd6aa7b838860de5d0b25635adde60cbd2e7b47e5` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_zero-exit.json` | `c8dd7b7b214c90ff894c0d6f36486c12d12a31342f7d44229101fbbaa6581009` |
| `runs/online-huber-migration-20261006/public-fence-v1-huber_zero.log` | `c580fe8e768f61d968bc6715a30f2aa16de7d2d2d6bdf21c144d032e743fc358` |
| `runs/online-huber-migration-20261006/public-fence-v1-project_fullSpace-exit.json` | `25ab9f0eba46f5facae3bfe4e2380becccedc8c2be3628d578c91b2eae5c3fb2` |
| `runs/online-huber-migration-20261006/public-fence-v1-project_fullSpace.log` | `71181366071e424d25f8fbbd32f44160ca8cd43166ab55003d2a79b60c98d34c` |
| `runs/online-huber-migration-20261006/public-named-declarations-v1.json` | `11281a10349a0d31a3f12b3845bb18b9d71119cecd28cb05b6df30fefa8a0ef3` |
| `runs/online-huber-migration-20261006/public-safe-guard-audit-v1.json` | `8c9c78657a0e57923b6bc950f64c8b32960f2a48f8cc7aa708c8e8c91dc7c736` |
| `runs/online-huber-migration-20261006/readable-type-probe-before-use-v2.json` | `40b9364941c3973af7013a2432c159e3779686fe6f2977b74d7dec71c375eee8` |
| `runs/online-huber-migration-20261006/ready-dependencies-v1.json` | `50baf0a2935cf550d8b81875eb7797a47cc33e147d04ef3c6f34e2ce61060af1` |
| `runs/online-huber-migration-20261006/retained-body-trial-v1-exit.json` | `ef11d254fa6e24f5b5dc6ab41cc053b488f777dbef67393248842eebeda0e027` |
| `runs/online-huber-migration-20261006/retained-body-trial-v1.log` | `4f384915acc19869eba1f44bd81799d476ab6972221c35b40aa772cdd6e85fed` |
| `runs/online-huber-migration-20261006/retained-module-v1-01-exit.json` | `dd1f16a928b2ca83f3e9aa12c55c9a712006071cba76a6369c908253af82703f` |
| `runs/online-huber-migration-20261006/retained-module-v1-01.log` | `77488228db45d23baa97c3c3b5d42a17955ffe6c405ecfa8a5084285d4953045` |
| `runs/online-huber-migration-20261006/retained-scoped-graph-v1-01-exit.json` | `66d57568e001cd9ee1434fff38ef360a11a203fceae0e118f245bec0eea7aba0` |
| `runs/online-huber-migration-20261006/retained-scoped-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-huber-migration-20261006/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `runs/online-huber-migration-20261006/safe-public-v1-hasDerivAt_ite_le-exit.json` | `8c64a272c45f9742a2a7d8c6036f2b21858eda07c4615d1393560dd994348854` |
| `runs/online-huber-migration-20261006/safe-public-v1-hasDerivAt_ite_le.log` | `74d73efa37de20347d6d966f6e8dff074e7e15b286696b649067f28fa0372b5b` |
| `runs/online-huber-migration-20261006/safe-public-v1-hasDerivAt_join-exit.json` | `21e4bd98ee9f94d565b50ccb0d4fd502d8714978baad57fe8d5901ce106ef376` |
| `runs/online-huber-migration-20261006/safe-public-v1-hasDerivAt_join.log` | `5369d4dcc0de207f9466f3c5b1c988d76620a63feb6052f7ea705cd1a5c06d61` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_average_bound-exit.json` | `832c8bb033adfe3a73f9d6650c10bf6a4d9074a3ee7a2de49a19e041ea62c2fa` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_average_bound.log` | `c4cc26826505269a4a6913e468737657c5d9ea97672c81f82083d8be7291b45a` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_average_eventually-exit.json` | `e5522540e54df7558cd72c60fda8339ed63eb6110b6e3ee38c33eae210aaab57` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_average_eventually.log` | `1b1bfeaafb3814bcc04a0d9348a5aef0ce9c6adec1d210b18e563d5353ed72f0` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_convex-exit.json` | `e9eb985f393c70d27332a9fffe63e684342721ef3bc67d4f1a2539349fb9aa19` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_convex.log` | `b7c1b802b51c84797e06d19bd202a755951c335119cf4ae2e349eff9ab4b4698` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_deriv_bound-exit.json` | `3fa3b325e89cb1b6888e6189c7e8a1f5aad07a646e04346fc3a005dd092b8852` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_deriv_bound.log` | `9430f36125016c9e68e0d42da2d86e211485766bc60da48380cb25d0f964d42d` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_deriv_clamp-exit.json` | `4dd71d8842737bf5e8bf205eb28f62787a8889cc8b20b062628099622c82d7a5` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_deriv_clamp.log` | `133664e61ea0a02c904205b22058c8363c2bc2f3fdd6d908548b6c31f3df7d94` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_deriv_source-exit.json` | `92eaf3fff566686f4e72c02677df45fce1cd81322117d788aaf9dc9ffc8ce835` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_deriv_source.log` | `cfadde5454651c93764d7a340ed6135770b516b91d81b7628d20fb3aa9f63414` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_hasDerivAt-exit.json` | `e04f3fe042049b37ce9b22e5aa31b57a9d2b53562e2d181730f03900589fb240` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_hasDerivAt.log` | `15c8fe5fdc5cbf42c659d0b5464537cec802f02638e132643aeb9c1163900d60` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_linear_convex-exit.json` | `5b37b898cd64797c1a43c4883afe9e7a069e07d8c446866313aa3a2f2ba66adb` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_linear_convex.log` | `9d7a441fecabe5462a797ee78f631f7eb9d79e7e2c921e840049d51a43716eae` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_linear_gradient_bound-exit.json` | `c5a7715dc33cf80c3e37a60acb2546fa750bdd89f80d88d41cbf5022a8c4c4e4` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_linear_gradient_bound.log` | `9d966c19b64df7c78642ffa9944a96fced66471c0e56ae7f60a28984a318afc5` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_linear_hasGradientAt-exit.json` | `328077ea17bb4dc8e78821eed2d02c2db8cdf3558de51486112f76abdf7073d8` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_linear_hasGradientAt.log` | `326ae039e11bf7032f489d8354e28101515f97c674b70e2244a06df2819dbebd` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_rate_tendsto-exit.json` | `9cdb63bdfa166ae73d5c22aefa848382c989af779650a7c2391872a8b805fea4` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_rate_tendsto.log` | `5f29a71589ca28af393f696219b6d4b5a7fe6b92262bea217d732057d8608577` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_regret_fixed-exit.json` | `3e51bd6bfce2ade018327191dd80ba1490ebf463d53d74034c235f5d521d7b4e` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_regret_fixed.log` | `9f12c03b22d1c717e7d9f76fff66bca3ce1ec864942c318809ab764bdb48956b` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_regular-exit.json` | `b265474196ce7c5feef0f71f8b1d806eb7e976e5c89e38993f40bd318d40bd67` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_regular.log` | `fa3980f519095d10a4c80ca83d19626b0df94eae90dfd48416b4a4d914a370c5` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_step-exit.json` | `09a508c4599f570340d3ca178cddf7fbbab2cd622d4ca64584d7177a7cc994ed` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_step.log` | `7cc3d3ca3d6744f7648258d284c21d4489310b4b63f0a24d0321442e456c26d3` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_three_pieces-exit.json` | `02b08234a910b7b94f96eee3338aed750c0030955bdd884c9c5f67af73ab6d9e` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_three_pieces.log` | `f765ecd570413c25cb9bd7b1db86c3980ce92aa3dc9f62e5f2ae2c74ad36ece4` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_zero-exit.json` | `6951b216045638fa7be5db44623933b9091b9f4e269717145e32ac2d552f8538` |
| `runs/online-huber-migration-20261006/safe-public-v1-huber_zero.log` | `7c92bd77f76e7280e34a5abb3648acda38c629587a0561a2b2fc609e3a7c8417` |
| `runs/online-huber-migration-20261006/safe-public-v1-project_fullSpace-exit.json` | `c7f9d57f43e4cd8cdb9b6af1facfb8fa40b11e3c2da8965e7ebc8b60e82146d2` |
| `runs/online-huber-migration-20261006/safe-public-v1-project_fullSpace.log` | `ca7c34f5b704738579ed55b97c8c5212425b1514590992477a7a27f08ad4a754` |
| `runs/online-huber-migration-20261006/search-memory-v1-01-exit.json` | `124151d22c659dbcfe59e0ee9c75aa72ce59bdd9361a3a27d3a6481ce61669fc` |
| `runs/online-huber-migration-20261006/search-memory-v1-01.log` | `8d3431205e5c23f1ed3fe371eba1d2f785e8170c563ead48905089acd79a6216` |
| `runs/online-huber-migration-20261006/source-contract-receipt-v1.json` | `42fbffec6f84808884802345c729de96cbad57d3482f97d23a87c46279933f38` |
| `runs/online-huber-migration-20261006/source-contract-review-v1.md` | `74e78587d9b1457e49f743c9c6fd26227915224c6792325eaba2aeda82f3a1a6` |
| `runs/online-huber-migration-20261006/source-printed15-16-pdf27-28.txt` | `55d4cef1d3b3b4a60f08511122a0c26b77bcbee6d23e104ac535e29953d39393` |
| `runs/online-huber-migration-20261006/source-review-helper-before-use-v1.json` | `d536c6332f31c124635c9cb1a54ea5d9337232c8d25a62b2a327260ff3286f34` |
| `runs/online-huber-migration-20261006/source-review-packet-v1.md` | `9de6f945f61619bd89f87348cead70ca42add55bec8209cd10d63120fbf8b397` |
| `runs/online-huber-migration-20261006/stabilized-lifecycle-v1-exit.json` | `9f2e53c6056570c21f4188ccefb99547fb41ff0acb30baac5c6868180bb1b152` |
| `runs/online-huber-migration-20261006/stabilized-lifecycle-v1.log` | `6e0cac290c24d8f115da621e5e3c280ebc9df288c391591271dee310b55696d3` |
| `runs/online-huber-migration-20261006/verify-public-fences-v1-01-exit.json` | `b051d2b4f6c970643e0c70aaaff3e53fb87841a2eb1a4133836244ef076abf5f` |
| `runs/online-huber-migration-20261006/verify-public-fences-v1-01.log` | `0d933623054c430b31cecda189521ed156e83a83835eee9fcc2ba615584de095` |
| `runs/online-huber-migration-20261006/verify-public-fences-v1.py` | `c4ec2dd3e40362ac3a4289c26f1e565ac57c6a4e4a1fe26ae88935bc0259844c` |
| `runs/online-huber-migration-20261006/workspace-audit-v1.json` | `f2b1c749c0f12215430fcb7443dd7b31f66c41e8c0838780738d4be72a5fd665` |
| `tasks/ONLINE-HUBER-MIGRATION-20261006.md` | `7209cc04217bb240cd5f4192ec9e3f452d3eebbae2c81dfe6c8d65ab18d927cc` |
| `tmp/online-huber-migration-compiled-retained-graph-v1.json` | `7135a53ca48c7fe831f5dfb8b9a0347e42b1629e39a7b807cd9bccb94883bd9a` |
| `website/content/chapters.json` | `882959c8c0819f77df682331a139ac2e9f8f4d26d4a8a718c948c88b8ee751ef` |
| `website/content/highlights.json` | `ab30a70922444f721bda53de340961f2ad8ac8dae6d0cc10bd5e6d6d870c4cfa` |
| `website/content/readings.json` | `081ebbec0b07777bf678cbf9e0f6e513695ff012d0222e6a9cf2ea27b0de1ef4` |
| `runs/online-huber-migration-20261006/public-body-inputs-v1.json` | `5ddabf2fc7d84b92f80636b94b2f6d9a34d314cca39ed58dda0eb95d350cc292` |
