# Huber migration: distinct contract review v1

Verdict: **accepted-with-explicit-delta** for all19 retained target contracts and their three complete definitions. Mathematical repairs: none. This stabilizes the present contracts only; it does not freshly accept bodies, integrated gates, readers, package delivery or any chapter/book/Goal completion.

Actor `/root/source_reviewer`, distinct automated source reviewer. Requested GPT-6 Astra / medium, without independent runtime-model attestation, human or external-model review. Prior history is not erased; the older Huber acceptance is not evidence for this decision.

## Raw evidence and source reading

Independently rehashed all194 fixed rows:194 matched, zero missing/drifted. The fixed manifest itself is additionally bound, yielding195 raw rows below. Read the actual full OnlineHuber module and whole14-proof canary; complete three definitions; shared Domain, RegularLoss, project/step/iterate/regret/iterate_prefix and fixed OGD interface; actual readable @types; frozen contexts/19 headers; restricted neutral reconstruction; pinned source and selected current reader. Independently extracted all19 public headers and matched the frozen statements exactly. Ancillary scripts/logs/historical artifacts are integrity/provenance bindings, not a claim to independently rerun every gate or reaccept old packages.

Pinned original PDF digest `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`; Example2.15 printed15–16/PDF27–28. The original physical28 page was freshly extracted, and preceding source page/example context read from the bound extraction. It states the half-quadratic/linear residual loss, feature-vector gradient, bounded features, full Euclidean predictor space and a constant learning rate proportional to1/sqrtT. The displayed19 lemmas are necessary library refinements/support, not19 printed results.

The actual scoped graph is22 nodes/2954 direct type/value edges including three definitions, not a full/canary export. Existing focused/type/graph readiness does not replace later fresh body/36-name axiom/native19/combined root/Tests/harness/site acceptance. The restricted decoder honestly leaves imported RegularLoss fields uncertain; direct inspection resolves them: an open neighborhood U containing the domain, ConvexOn on U and DifferentiableOn on U. huber_regular produces U=univ using proved global convexity and gradient existence, so the older stronger interface imposes no new consumer hypothesis here.

## Threshold decision

Accept explicit delta>=0 as the necessary ordinary threshold convention omitted as an inequality in source prose. It is not a claim of equivalence for arbitrary real thresholds. For delta=-1, the formula becomes -|r|-1/2 on every real residual: it is not convex and is not differentiable at0. Thus removing the sign premise would contradict the source's convex/differentiable claim. Delta0 is a valid included degeneration: H0=0, both seams coincide, derivative0, and the actual update stays fixed. The proof covers it rather than assuming positive threshold. This is a disclosed source delta, not silent target repair.

## Average-performance interpretation decision

Accept the source's informal approach-to-any-fixed-predictor prose as a one-sided no-regret performance comparison. It cannot faithfully mean signed regret/T tends0 for every comparator. Mathematical counterexample within this setting: real feature1 and label0 forever, delta1, initialization0, comparator2. Every actual gradient at0 is0, hence the iterate remains0 for every horizon and eta. Its loss is0; comparator loss H1(2)=3/2 each round. Therefore actual regret/T=-3/2 for every positive T, while the positive numeric upper envelope tends0. This is a semantic counterexample argument, not a newly Lean-compiled canary claimed by this receipt.

The literal terminal only says eventually regret/T<epsilon for each epsilon>0 and fixed u. It is correct and source-compatible under that interpretation. The separate Tendsto theorem concerns the numeric upper envelope alone and even allows arbitrary real delta,Z because they enter a square; those unrestricted scalar signs do not grant an algorithm guarantee. The known-horizon family must not become one anytime trajectory. No uniform cutoff over unbounded comparators or moving comparator is provided.

## Per-target seven-slot comparison

### `BanditRL.OnlineHuber.hasDerivAt_ite_le`

Accepted-with-explicit-delta, contract only.

- **model**: Real scalar f,g.
- **assumptions**: Derivatives at c both d; f(c)=g(c).
- **information**: Deterministic local data.
- **algorithm**: Actual left-closed piecewise function.
- **parameters**: Join c; derivative d.
- **quantifiers**: All f,g,c,d with premises.
- **guarantee**: Exact derivative at seam; generic library helper, no global regularity premise.

### `BanditRL.OnlineHuber.huber_three_pieces`

Accepted-with-explicit-delta, contract only.

- **model**: Real scalar Huber.
- **assumptions**: delta>=0.
- **information**: Pointwise deterministic.
- **algorithm**: Same half-quadratic/linear definition.
- **parameters**: Seams -delta,+delta; intercept -delta²/2.
- **quantifiers**: All residuals.
- **guarantee**: Exact three-piece identity; seams and coincident delta0 covered.

### `BanditRL.OnlineHuber.huber_zero`

Accepted-with-explicit-delta, contract only.

- **model**: Real scalar Huber.
- **assumptions**: Threshold exactly0.
- **information**: No feedback dependence.
- **algorithm**: Actual huber0 function.
- **parameters**: Any residual.
- **quantifiers**: All real r.
- **guarantee**: Identically zero, including seam; degenerate library refinement.

### `BanditRL.OnlineHuber.hasDerivAt_join`

Accepted-with-explicit-delta, contract only.

- **model**: Real scalar f,g and derivative profiles.
- **assumptions**: Both global derivative profiles; values and derivatives match at c.
- **information**: Deterministic profiles.
- **algorithm**: Actual glued function, not an assumed derivative oracle for Huber.
- **parameters**: c and query x.
- **quantifiers**: Every x and eligible functions.
- **guarantee**: Exact derivative profile; library gluing generalization.

### `BanditRL.OnlineHuber.huber_hasDerivAt`

Accepted-with-explicit-delta, contract only.

- **model**: Real scalar Huber.
- **assumptions**: delta>=0.
- **information**: No residual restriction.
- **algorithm**: Actual scalar derivative constructed by two joins.
- **parameters**: Saturated piecewise derivative.
- **quantifiers**: All real residuals.
- **guarantee**: HasDerivAt including both seams and delta0; not merely a total deriv equality.

### `BanditRL.OnlineHuber.huber_deriv_clamp`

Accepted-with-explicit-delta, contract only.

- **model**: Real scalar Huber.
- **assumptions**: delta>=0.
- **information**: Pointwise.
- **algorithm**: Actual deriv, supported by differentiability producer.
- **parameters**: max(-delta,min(r,delta)).
- **quantifiers**: All residuals.
- **guarantee**: Exact clamp identity, no residual bound.

### `BanditRL.OnlineHuber.huber_convex`

Accepted-with-explicit-delta, contract only.

- **model**: Real full line.
- **assumptions**: delta>=0.
- **information**: Deterministic.
- **algorithm**: Actual globally differentiable loss; monotone derivative criterion.
- **parameters**: No strong-convexity constant.
- **quantifiers**: Every nonnegative threshold.
- **guarantee**: Global ConvexOn univ, not strong/strict convexity.

### `BanditRL.OnlineHuber.huber_deriv_bound`

Accepted-with-explicit-delta, contract only.

- **model**: Real scalar derivative.
- **assumptions**: delta>=0.
- **information**: No observations needed.
- **algorithm**: Actual derivative clamp.
- **parameters**: Bound delta.
- **quantifiers**: All residuals.
- **guarantee**: Absolute derivative <=delta; not a bound on loss values.

### `BanditRL.OnlineHuber.huber_deriv_source`

Accepted-with-explicit-delta, contract only.

- **model**: Real scalar derivative.
- **assumptions**: delta>=0.
- **information**: Pointwise.
- **algorithm**: Actual same Huber derivative.
- **parameters**: Inside residual; outside delta*sign(r).
- **quantifiers**: All residuals.
- **guarantee**: Exact printed branch expression, inner equality included.

### `BanditRL.OnlineHuber.huber_linear_hasGradientAt`

Accepted-with-explicit-delta, contract only.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: delta>=0; no label/feature/predictor bound.
- **information**: Current z,y define actual loss.
- **algorithm**: Chain rule for huber(delta,<z,w>-y).
- **parameters**: Gradient deriv(H)(residual) times z.
- **quantifiers**: Every y,z,x.
- **guarantee**: HasGradientAt actual ambient loss, zero features and threshold allowed.

### `BanditRL.OnlineHuber.huber_linear_convex`

Accepted-with-explicit-delta, contract only.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: delta>=0; CompleteSpace remains in actual type.
- **information**: Deterministic feature/label.
- **algorithm**: Actual affine composition.
- **parameters**: Whole unbounded space.
- **quantifiers**: Every z,y.
- **guarantee**: Global convexity; no finite-dimensional, bounded-domain or strictness premise.

### `BanditRL.OnlineHuber.huber_linear_gradient_bound`

Accepted-with-explicit-delta, contract only.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: delta>=0.
- **information**: Current actual loss only.
- **algorithm**: True gradient from preceding producer.
- **parameters**: delta*norm(z).
- **quantifiers**: Every z,y,x.
- **guarantee**: Uniform-in-x,y gradient bound; no supplied gradient-bound oracle.

### `BanditRL.OnlineHuber.project_fullSpace`

Accepted-with-explicit-delta, contract only.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: No numeric assumptions.
- **information**: No feedback.
- **algorithm**: Actual chosen Hilbert projection on fullSpace.
- **parameters**: Full-space carrier, no ball/radius.
- **quantifiers**: Every x.
- **guarantee**: Projection identity; definition preserves closed/nonempty/convex carrier.

### `BanditRL.OnlineHuber.huber_regular`

Accepted-with-explicit-delta, contract only.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: delta>=0.
- **information**: Current z,y only.
- **algorithm**: Produces imported RegularLoss with U=univ.
- **parameters**: Actual global convexity and differentiability.
- **quantifiers**: Every z,y.
- **guarantee**: Stronger historical neighborhood API discharged, not extra source hypothesis.

### `BanditRL.OnlineHuber.huber_step`

Accepted-with-explicit-delta, contract only.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: delta>=0; eta unrestricted real.
- **information**: Current loss updates next state after output.
- **algorithm**: Actual shared step/full-space projection identity.
- **parameters**: eta and saturated residual scalar.
- **quantifiers**: Every eta,y,z,x.
- **guarantee**: Exact update; negative eta allowed only for this identity, not regret guarantee.

### `BanditRL.OnlineHuber.huber_regret_fixed`

Accepted-with-explicit-delta, contract only.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: delta,Z>=0; eta>0; norm(z_t)<=Z for t<T.
- **information**: Strict-prefix iterate; current features available for prediction; label for next update.
- **algorithm**: Same actual constant-eta iterate/regret.
- **parameters**: Any natural T; x0,u arbitrary.
- **quantifiers**: All prefixes and fixed comparators under stated feature bound.
- **guarantee**: R<=initial/(2eta)+eta*T(delta Z)²/2-terminal/(2eta); T0 exact cancellation; no diameter premise.

### `BanditRL.OnlineHuber.huber_average_bound`

Accepted-with-explicit-delta, contract only.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: delta,Z>=0; T>0; finite-prefix feature bound.
- **information**: Known T fixed before run, not comparator/future-gradient tuning.
- **algorithm**: Actual same-run regret with eta_T=1/sqrtT.
- **parameters**: Coefficient1 instance of source proportional choice.
- **quantifiers**: Every T>0, x0,u, eligible streams.
- **guarantee**: One-sided upper (norm(x0-u)²+(delta Z)²)/(2sqrtT); negative residual dropped only here.

### `BanditRL.OnlineHuber.huber_rate_tendsto`

Accepted-with-explicit-delta, contract only.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: No signs on delta,Z; no algorithm/feature premises.
- **information**: Pure numeric sequence.
- **algorithm**: Envelope only, contains no iterate or regret.
- **parameters**: Fixed delta,Z,x0,u; natural T→infinity.
- **quantifiers**: All real delta,Z and fixed x0,u.
- **guarantee**: Numeric Tendsto0; does not license negative-threshold algorithm guarantee.

### `BanditRL.OnlineHuber.huber_average_eventually`

Accepted-with-explicit-delta, contract only.

- **model**: Complete real inner-product E; source finite Euclidean space is a specialization.
- **assumptions**: delta,Z>=0; global feature bound; epsilon>0.
- **information**: Family of independently horizon-tuned constant-step runs.
- **algorithm**: Actual shared regret at each horizon, fixed same initialization/streams.
- **parameters**: eta_T=1/sqrtT; comparator u fixed.
- **quantifiers**: Each u,epsilon has eventual cutoff; no uniform cutoff on unbounded u.
- **guarantee**: Eventually actual regret/T<epsilon only; no signed Tendsto0, absolute difference or anytime claim.

## Complete definitions, producer plausibility and canary scope

huber is the exact real piecewise formula, defined even for negative thresholds but used with nonnegative threshold in regularity/algorithm results. fullSpace carries univ with actual nonempty/closed/convex witnesses. linearLoss composes huber with <z,x>-y. The latter two definition types do not require CompleteSpace, whereas the ten vector theorem types retain it, including some mathematically unnecessary instances; no finite-dimensionality is inserted.

Existing bodies were read for contradiction checks: local seam derivatives are joined via one-sided sets; global derivative profiles glue matching values/derivatives, including coincident seams. Monotone clamp yields global convexity, affine chain rule yields the actual gradient, and norm multiplication yields delta*norm(z). Projection identity and global RegularLoss are constructed. Fixed regret invokes the actual shared constant-step theorem with these facts and bounds actual gradient energy; it retains the final negative squared distance. Average bound drops only that nonpositive term and divides only at positive T. The eventual proof combines numeric convergence with the actual finite-horizon upper bound and eventually-positive horizons, not an assumed performance oracle.

Actual14 canary bodies cover generic seam joining, both Huber seams, zero threshold, quadratic interior and affine exterior, nonzero feature gradient6 and bound6, vector zero threshold/global convexity, actual update2→3/2, sharp residual for every natural T, tuned T4 average upper5/4, and eventual average<1/10. The generic residual canary admits T0 but no separate named T0 evaluation is claimed. None tests actual signed convergence; no such theorem is present. These are existing bodies/readiness for later fresh body review, not this phase's body acceptance.

## Reader disposition and required integration qualifications

Current selected reader already explicitly distinguishes source Euclidean/Lean Hilbert, nonnegative threshold including0, known-horizon coefficient1, actual versus numeric rate and negative residual in its proof bridge. Preserve those correct qualifications. The following requirements combine preservation with missing precision to be checked in the future integrated reader phase:

1. Keep delta>=0 as explicit source-implicit convention and delta0 as valid degeneracy; explain negative thresholds are not covered, rather than suggesting source prints the sign assumption.

2. Keep actual Hilbert-space generalization distinct from finite-dimensional source; three full definitions and retained CompleteSpace contexts matter, not only short headers.

3. Explain arbitrary deterministic feature/label streams generalize the illustrative stock-history construction; z_t is available before prediction, y_t after, without a stochastic stock model claim.

4. Publish produced global RegularLoss and actual full-space projection identity; no bounded predictor domain, labels/residual bounds, supplied desired gradients or regularity assumption.

5. Display the sharp fixed-step negative terminal residual, eta>0 and T>=0; explain T0 cancellation and delta0/Z0 compatibility. Separate unrestricted-eta update identity.

6. Distinguish coefficient1 known-horizon instance from all proportionality constants or a single eta_t schedule; comparator/future losses do not select eta.

7. State the numeric envelope alone tends0 and actual average regret is only eventually below every positive epsilon for each fixed comparator. Cutoffs need not be uniform; actual regret may stay negative.

8. Retain genuine seam/nonzero-gradient/update canaries and separate bound5/4 from realized equality. Count one printed example,19 retained proofs,3 definitions,0 new nodes; distinguish already compiled but unaudited remaining obligations from all-unproved wording.

No frozen header correction is required. Remaining gates: separate retained-body/canary review, fresh public36 named axiom outputs and19 native guards, shared root/Tests/full harness, accurate reader/site/registry/contributor and immutable final binding, then scoped delivery. Only after those gates may this single retained OnlineHuber migration move legacy11→10. Zero new proofs/definitions/nodes are claimed. Chapter1 migration, Chapter2 totalnull/incomplete, remaining mandatory source/appendix/legacy audits and whole-book active Goal remain outside acceptance. No main, merge, live, Chapter4, strongly convex/logarithmic-regret or stock-generative-model claim.

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
| `runs/online-huber-migration-20261006/CLI-help-v1-01-exit.json` | `7e85645af38c412b3f18f250011e36114ac8b3a3c365e2d416d0689c33752136` |
| `runs/online-huber-migration-20261006/CLI-help-v1-01.log` | `daacf23e36eec4898dce3b3de02a07b71fb0f80f08e33e8dfe00722e7572970c` |
| `runs/online-huber-migration-20261006/actual-types-readable-v2-01-exit.json` | `ea3c3b4d76cc0ec261f3fcc8a14b292a55493472701321b0ae68e1f22f648051` |
| `runs/online-huber-migration-20261006/actual-types-readable-v2-01.log` | `5baa4358ff052d15660866ca8b161b9c538f6ed011ab3727eacfeb6d18ef0b61` |
| `runs/online-huber-migration-20261006/actual-types-v1-01-exit.json` | `ece3b3303756f34094bc94c9ab0cbfb9ddf53468f5426dfe2552b89b8740b4df` |
| `runs/online-huber-migration-20261006/actual-types-v1-01.log` | `82cb22fb8f56b18cb165ad9c257ca02bc929effc1a302014f6d9f54fcff57810` |
| `runs/online-huber-migration-20261006/blind-packet-v1.md` | `fd3374ac3f548f8c577c7dd0cfc6a77733196ff40fad041b5ee7869e1c4246f7` |
| `runs/online-huber-migration-20261006/blind-receipt-v1.json` | `92af3e10e6da6940ea8fa5414c982c5d79bd635f8aa0e36e6fc9d2d2b6ad8aea` |
| `runs/online-huber-migration-20261006/blind-reconstruction-v1.md` | `80a182bbdb6ce6ecd9faf1f89947775f752b4ce6a614069611296da2c09c6040` |
| `runs/online-huber-migration-20261006/bootstrap-before-use-v1.json` | `b4fcc6064d97448667e0564d9c19d07d01c120d2fd0f87f237a4173dd65bd902` |
| `runs/online-huber-migration-20261006/bootstrap-generated-before-use-v1.json` | `31b964fd8abcbcf6a6b90330779ae6a78eec91958eccf5fac5f340ca08a8ee05` |
| `runs/online-huber-migration-20261006/bootstrap-v1.py` | `2f2ffa79f60c56254129d17b8e3389aa203bdf8886f9a3b5fe96c08ec49440bc` |
| `runs/online-huber-migration-20261006/compiled-retained-graph-v1.json` | `7135a53ca48c7fe831f5dfb8b9a0347e42b1629e39a7b807cd9bccb94883bd9a` |
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
| `runs/online-huber-migration-20261006/original-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-huber-migration-20261006/original-OnlineHuber.lean.txt` | `dd7c6b4c41e5fee804196bbccfec493df37ae56294f32cddf3d11be27646de86` |
| `runs/online-huber-migration-20261006/original-OnlineHuberCanary.lean.txt` | `aa5def531637c89f77f70e6b26f9fdc678c5e4ae4ebadb8334599f34575f4837` |
| `runs/online-huber-migration-20261006/original-Tests.lean.txt` | `1c60f84f3e4d6d778ac8374b46e47b27559d802986459533517034c97a30f048` |
| `runs/online-huber-migration-20261006/prepare-draft-v1-01-exit.json` | `3a5e60ff6d4b9554729fbce1fee89da10abeb59c1994f5c5760bc87778daaf45` |
| `runs/online-huber-migration-20261006/prepare-draft-v1-01.log` | `b3201aae5aef7ba406a78b0d5d4dd771100aca7c102b079bc1d8ba6e537a78cc` |
| `runs/online-huber-migration-20261006/prepare-draft-v1.py` | `11025fb56e5aff210f43c956f06c20625d790366ceefff6e11b7e37611c065f1` |
| `runs/online-huber-migration-20261006/prepare-source-review-v1.py` | `d4bcb9a8a7f07411c478cdf14b133d27cbb0cf8227796ef6a323645950a6eab3` |
| `runs/online-huber-migration-20261006/proof-obligations-v1.json` | `90f425b08d4af7a516f872513c8468615048b6699b11bb9ee0e8978a2e32d3bc` |
| `runs/online-huber-migration-20261006/public-named-declarations-v1.json` | `11281a10349a0d31a3f12b3845bb18b9d71119cecd28cb05b6df30fefa8a0ef3` |
| `runs/online-huber-migration-20261006/readable-type-probe-before-use-v2.json` | `40b9364941c3973af7013a2432c159e3779686fe6f2977b74d7dec71c375eee8` |
| `runs/online-huber-migration-20261006/ready-dependencies-v1.json` | `50baf0a2935cf550d8b81875eb7797a47cc33e147d04ef3c6f34e2ce61060af1` |
| `runs/online-huber-migration-20261006/retained-module-v1-01-exit.json` | `dd1f16a928b2ca83f3e9aa12c55c9a712006071cba76a6369c908253af82703f` |
| `runs/online-huber-migration-20261006/retained-module-v1-01.log` | `77488228db45d23baa97c3c3b5d42a17955ffe6c405ecfa8a5084285d4953045` |
| `runs/online-huber-migration-20261006/retained-scoped-graph-v1-01-exit.json` | `66d57568e001cd9ee1434fff38ef360a11a203fceae0e118f245bec0eea7aba0` |
| `runs/online-huber-migration-20261006/retained-scoped-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-huber-migration-20261006/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `runs/online-huber-migration-20261006/search-memory-v1-01-exit.json` | `124151d22c659dbcfe59e0ee9c75aa72ce59bdd9361a3a27d3a6481ce61669fc` |
| `runs/online-huber-migration-20261006/search-memory-v1-01.log` | `8d3431205e5c23f1ed3fe371eba1d2f785e8170c563ead48905089acd79a6216` |
| `runs/online-huber-migration-20261006/source-printed15-16-pdf27-28.txt` | `55d4cef1d3b3b4a60f08511122a0c26b77bcbee6d23e104ac535e29953d39393` |
| `runs/online-huber-migration-20261006/source-review-helper-before-use-v1.json` | `d536c6332f31c124635c9cb1a54ea5d9337232c8d25a62b2a327260ff3286f34` |
| `runs/online-huber-migration-20261006/source-review-packet-v1.md` | `9de6f945f61619bd89f87348cead70ca42add55bec8209cd10d63120fbf8b397` |
| `runs/online-huber-migration-20261006/workspace-audit-v1.json` | `f2b1c749c0f12215430fcb7443dd7b31f66c41e8c0838780738d4be72a5fd665` |
| `tasks/ONLINE-HUBER-MIGRATION-20261006.md` | `7209cc04217bb240cd5f4192ec9e3f452d3eebbae2c81dfe6c8d65ab18d927cc` |
| `tmp/online-huber-migration-compiled-retained-graph-v1.json` | `7135a53ca48c7fe831f5dfb8b9a0347e42b1629e39a7b807cd9bccb94883bd9a` |
| `website/content/chapters.json` | `882959c8c0819f77df682331a139ac2e9f8f4d26d4a8a718c948c88b8ee751ef` |
| `website/content/highlights.json` | `ab30a70922444f721bda53de340961f2ad8ac8dae6d0cc10bd5e6d6d870c4cfa` |
| `website/content/readings.json` | `081ebbec0b07777bf678cbf9e0f6e513695ff012d0222e6a9cf2ea27b0de1ef4` |
| `runs/online-huber-migration-20261006/contract-source-inputs-v1.json` | `5efbc49401938a6e2ca75fe2737a3304291744e0fa255300cce15adbaefb1345` |
