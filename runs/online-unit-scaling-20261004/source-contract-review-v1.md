# C2-unit-scaling source-contract review v1

Verdict: **accepted-with-explicit-delta**, solely stabilizing the four scoped definitions/alias and22 unproved target headers. No theorem body, canary, public module or combined package acceptance is certified. No contract repair is required.

Actor `/root/source_reviewer`, distinct automated source-review role; requested GPT-6 Astra / medium. Runtime model identity is not independently verified. No external human or external-model review claim. The formalizer is separate from the fresh restricted-input decoder `/root/normal_blind` and this source reviewer.

## Source and interpretation

The original cached Orabona arXiv1912.13213v10 PDF was independently raw-hashed to `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. Physical33–34 / printed21–22 were freshly extracted. The source fixes V=R^d, derives gradient units [loss]/[x], stepsize units [x]^2/[loss] and loss units for both coarse regret terms. Changing meters to kilometers uses y=x/1000, f'(y)=f(1000y), g'=1000g: corrected eta'=eta/1000² preserves the update, while retaining numerical eta changes the physical step by1000². This is an unnumbered dimensional argument and example, not22 printed theorems.

The contracts separate abstract unit-exponent algebra from numerical coordinate transport. An arbitrary additive commutative group is a formal algebra for multiplicative dimensions; it does not assert that physical quantities are arbitrary group elements, independent base dimensions, or that units alone determine a numerical step. Positive fixed c generalizes the source1000 example. The two real calculus helpers further allow arbitrary real c; that broader chain rule is explicit and does not relax invertibility elsewhere. Coordinate-free finite-dimensional real inner-product spaces include the source Euclidean setting and zero dimension.

The numerical context reuses the shared fullSpace Domain, scaledLoss f(c·y), scaledEta eta/c² and an explicit scaledPolicy. The policy reconstructs original-coordinate past whole functions/current whole function by inverse pullback, rescales its finite output tuple by c, queries the original fixed p, then scales the returned vector by c. This contains no future loss, comparator or horizon argument. It is essential that p itself is transported: no equivariance of an unrelated Classical.choose/canonicalPolicy is assumed. The statements do not enforce how external callers selected p,eta,initialization; their causal claim is the fixed exogenous finite-history/current-loss interface.

## Per-target seven semantic slots

Each row is accepted with the stated source/refinement boundary. Target order is exactly the clean N01–N22 map.

| Target | 1 Objects | 2 Quantifiers | 3 Assumptions | 4 Conclusion | 5 Constants | 6 Information/probability | 7 Boundary/delta |
|---|---|---|---|---|---|---|---|
| `unit_exponents` | AddCommGroup D; unit exponents X,L,H | all D,X,L,H | H+(L-X)=X | H=2X-L | two X exponents | deterministic dimension algebra | no physical numeric quantity/independence premise |
| `regret_unit_exponents` | same exponent group | all D,X,L | group only | both RHS dimensions equal L | 2X-(2X-L);(2X-L)+2(L-X) | no stochastic content | coherence, not numerical regret guarantee |
| `inverse_loss` | EReal f, coordinate pullback | all c,f | c>0 | inverse pullback equals f | c then reciprocal | no loss information | infinite values allowed; c0 excluded |
| `proper_scaled_loss` | EReal f | all c,f | c>0,proper f | scaled f proper | finite witness at original point/c | no policy | not finite everywhere |
| `subgradient_scaled` | global supports at cy/y | all c,f,y,g | c>0,proper f,g in global support at cy | cg in scaled global support at y | factor c,all-query inequality | pointwise transport | inclusion only; not chooser equality |
| `subdifferentiable_scaled` | full-space f | all c,f | c>0,proper+support at every point | same property for scaled f | same full-space carrier | existence producer only | not general constrained domain |
| `hasGradientAt_scaled` | real differentiable f on E | all real c,f,y,g | HasGradientAt f g at cy | composite gradient cg | factor c including sign | chain rule | c0/negative included; no convexity |
| `gradient_scaled` | real f and gradient operator | all real c,f,y | DifferentiableAt at cy | gradient composite=c gradient original | exact c | chain rule | c0/negative included; no EReal calculus |
| `step_scaling` | x,g in E | all c,eta,x,g | c>0 | corrected update equality | output1/c,step1/c²,vector c | arbitrary supplied vector | eta may be nonpositive; no legality |
| `wrong_step_scaling` | x,g in E | all c,eta,x,g | c>0 | back-converted step has c²eta | exact c² | single-update algebra | no regret/path-worsening claim |
| `scaled_eta_positive` | real schedule | all c,eta,t | c>0,eta_t>0 | scaled eta_t>0 | divide c² | no schedule-selection law | other times unconstrained |
| `history_scaling` | actual original/scaled histories | all run data and t | c>0 | whole Fin(t+1) history equality | all four run inputs transformed | finite past/current policy transport | arbitrary eta/improper losses algebraically; T0 |
| `output_scaling` | actual outputs | all run data and t | c>0 | scaled output=original/c | same index | same actual histories | no independent canonical-choice equivariance |
| `selected_scaling` | actual selected vectors | all run data and t | c>0 | scaled selected=c original selected | exact c | uses transformed observed functions/history | does not itself prove legality |
| `legal_feedback_scaling` | played support membership | all run data,horizon | c>0,proper losses beforeT,original played legality | transformed played legality | exact coupled supports | no universal off-path OracleLaw | arbitrary comparator need not be finite |
| `loss_value_scaling` | actual EReal loss values | all run data and t | c>0 | scaled played value=original value | loss unit unchanged | same played point correspondence | infinite values included; no finiteness claim |
| `regret_scaling` | toReal regret sums | all run data,u,T | c>0 | scaled regret at u/c=original | no loss multiplier | same matched trajectory | algebraic for improper losses; T0 allowed |
| `wrong_step_output` | uncompensated scaled run and effective original run | all run data,t | c>0 | back-converted output equals run at c²eta | entire effective schedule c²eta | feedback regenerated at changed run | not original eta feedback frozen; no universal worse path |
| `distance_square_scaling` | normed E,arbitrary x,u | all c,x,u | c>0 | scaled squared distance=distance²/c² | 1/c² | deterministic geometry | zero distance allowed; no diameter bound |
| `energy_scaling` | actual finite selected-norm sums | all run data,T | c>0 | scaled energy=c² original energy | exact c² | matched corrected runs | no legal feedback/norm bound needed; T0 |
| `upper_bound_scaling` | actual shared scalar upperBound | all c,A,B,eta | c>0,eta>0 | coarse expression invariant | A/c²,c²B,eta/c²;two factors1/2 | fixed scalar identity | A,B arbitrary inclnegative; not optimizer/regret bound |
| `regret_fixed_scaled` | actual legal constant-step runs | all c,eta,loss,x1,p,T,u | c,eta>0;full-space SubdifferentiableOn and original played legality | scaled regret bounded by original sharp potential/energy | initial/(2eta)+eta energy/2-terminal/(2eta) | reuse genuine same-run regret producer | T0 cancels; no boundedness/normbound/offpathlaw |

## Neutral correspondence and imported semantics

I read the complete neutral packet and all22×7 reconstruction slots, plus its receipt and private map. Packet raw SHA256 is `2d173e0575477e7e4c0be6f58f65b99dbe2f00ce8ad4ab0e876bee727957072e`; report raw SHA256 is `47e423de5c8d63d0ab406b2a4b88446c8f7956182cfa38ef94addd8e7c823980`. Both actual raw hashes match the receipt. I mechanically applied the stated symbol renaming to every actual native header and matched all22 neutral headers. The neutral packet imports mathematical APIs only and provides definitions, not source identity or target proof bodies. The decoder does not claim erasure of unrelated history or source/proof acceptance.

The possible domain mismatch was specifically checked: neutral H/Z/G/L/R have a dummy domain argument but always project with fixed full-space J. They are therefore not equivalent to the public general-domain interfaces on arbitrary k. Every trajectory target here, however, instantiates K; the actual target always instantiates V=Huber.fullSpace. On that specialization the same nearest-point definition/whole-space projection semantics apply, with the same Nat.rec/Fin.snoc history, actual selection and toReal regret. This restricted correspondence is sufficient; it must not be reused to decode future constrained-domain targets without repair.

Actual SourceProper is nowhere-bottom plus an explicit finite real witness; SourceSubdifferential is the same all-y EReal inequality; SubdifferentiableOn is properness and support nonemptiness at every carrier point. These exactly match Q,S,B at K. The actual shared projection/fullSpace and policy definitions were read. EReal.toReal sends either infinity to0; the decoder explicitly warns that unconditional regret_scaling is converted-expression algebra, not finite-loss regret semantics. This is accurate despite the packet not expanding that library definition. Under the sharp performance target, full-space SubdifferentiableOn gives finite comparator and played losses; actual played legality connects selected vectors. Properness plus played legality alone would not make every arbitrary comparator finite, and the weaker legality-transport target does not claim it does.

## Exact freeze and dependency route

All170 fixed raw inputs match independent SHA256 measurements. The four context definitions/alias match context hash `47aa298a466cd68e18e8fcb6ac91f31893d56c52ca33650d4b48e2597f682d6f`. Native extraction from the actual draft target reproduces all22 frozen hashes, matches every separate header, and verifies each fence's actual premise fragments. Empty arrays occur only for unconditional dimension coherence; unrestricted real-gradient helpers correctly have derivative premises without c>0.

Actual original draft-types01 and neutral-types01 each exit0 and print22 Prop elaborations, with harmless unused binder warnings. APIcheck01 exits0 and checks actual chain-rule, adjoint, scalar action, full-space projection and sharp policy regret interfaces. These are type/context checks, not theorem-body proofs. Empty `:= by` delimiters in the draft .txt are solely native-header syntax; they are not accepted Lean proof terms. No target body has been reviewed or certified.

The proposed producer DAG is appropriate: inverse pullback/properness and global affine support transport; actual real gradient chain rule separately; corrected update algebra and full-space projection identity; induction on the actual finite history with the supplied transformed policy; derived output/selected/loss/regret/energy correspondences; then existing sharp constant-step policy regret bound. That existing theorem has actual subdifferentiability/played legality and retains the negative terminal squared-distance term. Full-space initialization/comparator membership are automatic. The new target does not receive a desired regret/stability bound as a premise. Proving transformed support legality remains a distinct obligation, not inferred from structural selection equality alone.

For uncompensated steps, the right side is a genuinely rerun original-coordinate trajectory at c²eta, with its own actual feedback. It does not silently hold the original eta-run gradients fixed. No statement says every path changes or regret always worsens. The shared scalar coarse upperBound identity preserves both factors1/2; the abstract exponent identities separately show loss dimensions. Loss units are unchanged, so this is not a general joint coordinate/loss-unit conversion theorem.

## Required later evidence and scope

No header/context repair is needed. All22 bodies remain to be proved against the unchanged freeze. Required later canaries should realize c=1000 with actual full-space loss/support/policy/projection: corrected eta1/1,000,000 and physical next point-1, versus unchanged numerical eta1 and physical next point-1,000,000; a nonzero sharp regret instance with positive terminal residual; concrete unit exponents, c1, excluded c0, T0 and source positive-horizon boundaries. The supplied plan correctly demands actual coupled-run producers rather than scalar substitutions. It is not compiled evidence.

No general constrained-domain scaling, randomized law, loss-value-unit conversion, canonical-choice equivariance, future-energy optimizer, whole-chapter/book closure, main merge or live deployment is accepted. Public body/canary, actual axiom/graph, root/Tests/full harness, source-reader/site/registry/contributor, immutable binding and PR stages remain future work. WholeChapter2, old26 migration and the persistent whole-book Goal remain active/incomplete. No native trial or global frontier mutation was performed.

## Raw read inventory

All fixed170 byte streams were read for raw verification. Semantic inspection concentrated on original source, all actual/neutral headers and definitions, blind reconstruction, imported producer interfaces, freeze/fences/type logs and source/DAG/canary planning. Ancillary workflow/retrieval records remain provenance rather than accepted theorem evidence. The extra rows bind actual packet/inventory/extraction/library files where not already fixed. Report SHA is stored in the separate receipt; no self-hash or JSON normalization is used.

| Raw path | SHA256 |
|---|---|
| `runs/online-unit-scaling-20261004/00_context.md` | `404cc33cf2b50cc213c5ddf71dbfba3e571de502b9db03bb621830e63346220b` |
| `runs/online-unit-scaling-20261004/10_upper_director.md` | `136fc6cdaa8822dfe01ba7e252cff53355bb2b601582db08a05194eaf9c9bc5f` |
| `runs/online-unit-scaling-20261004/20_middle_architect.md` | `5058b493c229fffa363a0f2fa3c6cfabb81c24029e664a4711f8d68d7afcf625` |
| `runs/online-unit-scaling-20261004/api-check-01-exit.json` | `66602309e3e4df7ea1c7d1b055140b65a14a44df15833d6733988176a9a6ea75` |
| `runs/online-unit-scaling-20261004/api-check-01.log` | `322f5d9b3b1ff10d001c9cef66264df5aaf61ce7c26b7e6ea3b57eb3c7321fa2` |
| `runs/online-unit-scaling-20261004/author-draft.py` | `73134641ec9b86b23dd37c52ebf5ba854ce50fbe7e180fb83d7e9b60fe421e25` |
| `runs/online-unit-scaling-20261004/blind-packet-v1.md` | `2d173e0575477e7e4c0be6f58f65b99dbe2f00ce8ad4ab0e876bee727957072e` |
| `runs/online-unit-scaling-20261004/blind-receipt-v1.json` | `5e4b3c121f145655164a03d89d26a05c74adcbaa108ecb7b9d31dbbffaf3dd69` |
| `runs/online-unit-scaling-20261004/blind-reconstruction-v1.md` | `47e423de5c8d63d0ab406b2a4b88446c8f7956182cfa38ef94addd8e7c823980` |
| `runs/online-unit-scaling-20261004/canary-plan.md` | `ed33ea18a8fb95200a770f70424a7581c48b74f8294baf6ec11b8fe9d578f1ad` |
| `runs/online-unit-scaling-20261004/draft-freeze.json` | `3f2a5f06611ae817e9ca29988612bfec1eecc774859d7bbdd0f9ebe5620808e7` |
| `runs/online-unit-scaling-20261004/draft-headers-v1.json` | `88eca42725ba36fa4babe593a2f95abf8daa84e387fa329c43b575bf12fb5b8f` |
| `runs/online-unit-scaling-20261004/draft-types-01-exit.json` | `d502b32b360c774f58419a8b2bb2bb9ef1453d43b8ef3e11c05dddbac76fec7b` |
| `runs/online-unit-scaling-20261004/draft-types-01.log` | `62f2befb745ada48452742b12b99ee666a7bdb7a0d620208daf5f235168e8fdd` |
| `runs/online-unit-scaling-20261004/fence-distance_square_scaling-exit.json` | `27bb61753eca83ca217f716f4b3414688e679e65c389f8d2b7ad7d83cf11d333` |
| `runs/online-unit-scaling-20261004/fence-distance_square_scaling.log` | `bf24aafb7edcc6bf0188f16b7df25764ea518db7f281b1f7a530661443225160` |
| `runs/online-unit-scaling-20261004/fence-energy_scaling-exit.json` | `9776040bfc89980eb8fc04a65f5871fb7bd6b88b3a6c4a1cdcfeaeaf46981aae` |
| `runs/online-unit-scaling-20261004/fence-energy_scaling.log` | `3b02326fbc16d2365a15f9631132c49b84bc33a54446929120772e11bbfa0b20` |
| `runs/online-unit-scaling-20261004/fence-gradient_scaled-exit.json` | `98f4949326d7dee7cbdbbdeed845e1e0a9d339bb4afe0dcd5d796947a5d29246` |
| `runs/online-unit-scaling-20261004/fence-gradient_scaled.log` | `fb10af190441da7b0c1bab0497e9759429e8fa4a918ab5abbe6f291afe3acb7d` |
| `runs/online-unit-scaling-20261004/fence-hasGradientAt_scaled-exit.json` | `7a3255d7571d23114204d14510a5e54989fa5fdbdd95e7d3abcc14b0805ee917` |
| `runs/online-unit-scaling-20261004/fence-hasGradientAt_scaled.log` | `d0af619db7e1d156cc31c5188a6e38593e7319ca8827c80e8fc58a4b0488e260` |
| `runs/online-unit-scaling-20261004/fence-history_scaling-exit.json` | `e4f1866921e2644ed1fbabbb1567525c421fdd4606fa8d6d4c60a69d0828a5e3` |
| `runs/online-unit-scaling-20261004/fence-history_scaling.log` | `abb4d860869ccff1bafea7443c060172b9ad44aa24c8eeabe33948ed946e9252` |
| `runs/online-unit-scaling-20261004/fence-inverse_loss-exit.json` | `6b922840a341a2cfcadb5227d46b206d046c34b75c6f4ca62bd4f88601173507` |
| `runs/online-unit-scaling-20261004/fence-inverse_loss.log` | `c674e174d019341fbf3c20bf5c9dc5545133ebc0ec9f7954af50324392425910` |
| `runs/online-unit-scaling-20261004/fence-legal_feedback_scaling-exit.json` | `4e29fd66014dbf35de86e8f9226eb2be13a34bedb620214a68272b4d0d5c9d79` |
| `runs/online-unit-scaling-20261004/fence-legal_feedback_scaling.log` | `49b629d1658b828ecaf994c5d2ff568d255495ed6ecf1d6f3e076b7101f1a82e` |
| `runs/online-unit-scaling-20261004/fence-loss_value_scaling-exit.json` | `60896f3a3922be05b7052750804bc825254ae524898ce3e71e09515b005a25b0` |
| `runs/online-unit-scaling-20261004/fence-loss_value_scaling.log` | `fbfc061b23caf1f2982a2463873475caf4bbde067955f37a5c40eb9bd1a63cab` |
| `runs/online-unit-scaling-20261004/fence-output_scaling-exit.json` | `ea0df64a2725cccb8e6112b224de77cfa54179e719efdb09323d0d6d9b1f0fac` |
| `runs/online-unit-scaling-20261004/fence-output_scaling.log` | `9e8e6127024682e7ed457709316f76b105dfdd31a2e008d4e74c1c05203d35d5` |
| `runs/online-unit-scaling-20261004/fence-proper_scaled_loss-exit.json` | `15cb37050ed9ee9c2556e983cd52b4f4efc0eaceddf59472588f2831d3f03119` |
| `runs/online-unit-scaling-20261004/fence-proper_scaled_loss.log` | `9e47caeabe2ed867d0f5cc503f345722b305b6f1c3c23ea86bbef267070550d0` |
| `runs/online-unit-scaling-20261004/fence-regret_fixed_scaled-exit.json` | `3267ffb64a3c6f7f17519e14660194c27bb9886e10f375354245f2e1100c3b8e` |
| `runs/online-unit-scaling-20261004/fence-regret_fixed_scaled.log` | `e767d598ef80d7a24870c3fe7cd93b688ef6f734a1665960a47f93a411b3f5bd` |
| `runs/online-unit-scaling-20261004/fence-regret_scaling-exit.json` | `184800367091d3676c4d3155420eea235a8b0ef095d878f2047429cd2c18f3e3` |
| `runs/online-unit-scaling-20261004/fence-regret_scaling.log` | `f55007812fe734f6791ef078c18ce5124b6be4ca9f5bd729c36c02754257190a` |
| `runs/online-unit-scaling-20261004/fence-regret_unit_exponents-exit.json` | `578a11e9c08ed8f2625329046b7b5748d9ffd8bf4e769d84be210ea9a9876959` |
| `runs/online-unit-scaling-20261004/fence-regret_unit_exponents.log` | `bd5bea1cb79d077d835dc9e343a0f7d4547dd43efb5d0b8d19821ebd9fce64ce` |
| `runs/online-unit-scaling-20261004/fence-scaled_eta_positive-exit.json` | `c8721c18e128c8b0738233f7a6d2a35dbfa6c13617f997dae7b122d58e120ef7` |
| `runs/online-unit-scaling-20261004/fence-scaled_eta_positive.log` | `23e914fed72b7df5d95e3bb9c6197a1471a55fd04cbf0e61fd843f1c72ee9cbe` |
| `runs/online-unit-scaling-20261004/fence-selected_scaling-exit.json` | `403fc3323b48bf75993bdc763121ee2b0b443f787bd88ffbceecb72076fa9fd0` |
| `runs/online-unit-scaling-20261004/fence-selected_scaling.log` | `7a4861a9bfb70c954885cc95d40172861aafebd3999243bf9990feab8adbe857` |
| `runs/online-unit-scaling-20261004/fence-step_scaling-exit.json` | `b72e017c4158951bc2513e652e8b584ef18e03c2d5317ba449c06d759a5a0e07` |
| `runs/online-unit-scaling-20261004/fence-step_scaling.log` | `03ab738e9fedaae29f7d28e4e21e69fb5976b2cc0230d20c42b2a006ada0ad58` |
| `runs/online-unit-scaling-20261004/fence-subdifferentiable_scaled-exit.json` | `8c14c03caa2a2a9e96e3f70ecefca68c58aaecaa215bfe17c2033372682c0d8c` |
| `runs/online-unit-scaling-20261004/fence-subdifferentiable_scaled.log` | `5108fa3ee9af4c8f17e84202a101a8566e659ca169e537b52f6e3d7a689ddeba` |
| `runs/online-unit-scaling-20261004/fence-subgradient_scaled-exit.json` | `42ec4e0e0267be3a944784a49f72a3063a00f4b3f4b2dc07db6fd3ef50f5c18f` |
| `runs/online-unit-scaling-20261004/fence-subgradient_scaled.log` | `25aacb15f53d035c0879a732749e6134fe92a46af07a8688a3ddbe13e318427c` |
| `runs/online-unit-scaling-20261004/fence-unit_exponents-exit.json` | `5006ab37e30d42386369092f09bf827cf744097d0af1e17215b677ed99be47ff` |
| `runs/online-unit-scaling-20261004/fence-unit_exponents.log` | `b3840d2722e7db3fbd3226dcf96caddd378eb2601b9b58da4ec5c155d7819491` |
| `runs/online-unit-scaling-20261004/fence-upper_bound_scaling-exit.json` | `ef30093fc8a61a56562c85634f422d3ee3ceb75f411bbb7bc8756bc1d838a1e4` |
| `runs/online-unit-scaling-20261004/fence-upper_bound_scaling.log` | `fcec0b433cc54298bd3573934376cf5fff20ae79d5c439bf0e1b7b3d0b54394b` |
| `runs/online-unit-scaling-20261004/fence-wrong_step_output-exit.json` | `2da6d9b1aa2fb81e1abd73263c3286f667c61c980c93446d502e2866549b48b8` |
| `runs/online-unit-scaling-20261004/fence-wrong_step_output.log` | `34f48e9414d60d3674ac5eb207ff2f169a11ee01236c30b403d59b95f963ff98` |
| `runs/online-unit-scaling-20261004/fence-wrong_step_scaling-exit.json` | `eeb5205184a989855908e30bf685a3bf49f49b3cd5da1d5fe132cf6a642a6d5e` |
| `runs/online-unit-scaling-20261004/fence-wrong_step_scaling.log` | `976237bf049015f6e6d6000171e7cc2e97490dcd0b6058d1b5741662c3873f96` |
| `runs/online-unit-scaling-20261004/freeze-and-neutral.py` | `f05e965a2f276a6c1e1a70d2a5f3b0ed47bc6f5af33cf80af69ed16245c35f3d` |
| `runs/online-unit-scaling-20261004/help-declarations-exit.json` | `433930b650148a0c424a42801fc74ae858e0cb89b11b4995f689a44a39b52135` |
| `runs/online-unit-scaling-20261004/help-declarations.log` | `258218f16a12b1a530d85ae83e6c2449237af8a0a1153bb35de40245d665b131` |
| `runs/online-unit-scaling-20261004/help-fence-exit.json` | `7cd9d53fcdd9c0383b783a49b2f8e66af05753407f01e7036bcbf578342b3a1c` |
| `runs/online-unit-scaling-20261004/help-fence.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |
| `runs/online-unit-scaling-20261004/help-lifecycle-exit.json` | `5821518f6a0b507bea9c086d247945f4d4159a5453ff3862a46d864a92a04f72` |
| `runs/online-unit-scaling-20261004/help-lifecycle.log` | `b1e8b438a9b725793b9888d206e98a971ace3df200ec90ed9cb63eab26b28507` |
| `runs/online-unit-scaling-20261004/help-memory-exit.json` | `1dc163028353d40e52ce296012992ac4998c66caa0cda82e081a270e69279bc2` |
| `runs/online-unit-scaling-20261004/help-memory.log` | `b2f23faf2d0ee17c305335680ebdb2b83ca61999d18021e355d22587d712b79c` |
| `runs/online-unit-scaling-20261004/help-new-task-exit.json` | `52ba5e259d893f1020c2f87bcb91734c0b124a5e13b81f59cc073cb07cc29352` |
| `runs/online-unit-scaling-20261004/help-new-task.log` | `25eb9342c3094bee57187630bd149d2c522fc9f7ac7e65bebe5c198eba60ed99` |
| `runs/online-unit-scaling-20261004/memory-digest-draft.md` | `b34bc18faff5ba5dc3df5c460b9b27b886115ac8876b76370c9b6ceed4887836` |
| `runs/online-unit-scaling-20261004/neutral-context-correspondence.json` | `af18ba9d3a9a6238470c2ac71365191625cd822ab2454d2f2261dd46ee46d032` |
| `runs/online-unit-scaling-20261004/neutral-headers-v1.json` | `8a7262462f51848442f6eaeddd4a464ec6ac5181c5d60d1ec950d282ce5771f3` |
| `runs/online-unit-scaling-20261004/neutral-types-01-exit.json` | `230d46fb6e0cffbffe849391b1aee9993a6177a5c8c18a8ab124df3950f6620d` |
| `runs/online-unit-scaling-20261004/neutral-types-01.log` | `c361b1c70764360aeaf55d8d2308fd7cb8db78e53724b28df1e2ba6bfb3cce80` |
| `runs/online-unit-scaling-20261004/new-task-exit.json` | `3f7192db3685c8286f1c285943b9d6b9894b84301458854c14199de49b6b583a` |
| `runs/online-unit-scaling-20261004/new-task.log` | `e80e0d2146ff1f2fbfa3fa71b51c4808c39bac92c1ff69275cc33f42b63d3ff5` |
| `runs/online-unit-scaling-20261004/predecessor-delivery.json` | `83e1c5aef7aafb0eced8499063ce15cf39d220d53a6dede9f18c670ef5e86b83` |
| `runs/online-unit-scaling-20261004/private-neutral-name-map.json` | `3ebe0cdea3ae6d19661bdacaffb4fc9ecee2faf46914a1823ab644fd597e9f4f` |
| `runs/online-unit-scaling-20261004/proof-obligations.json` | `a3c93f7d5bd94c439f87931c5aaacba9726de9937f93a09dd3170771d6bbc025` |
| `runs/online-unit-scaling-20261004/retrieval-index.md` | `9545879f2fa17fab80b08a752fb00253cd0dc4c765681b9d517cc4701a8861bf` |
| `runs/online-unit-scaling-20261004/retrieve-policy-declarations-exit.json` | `7cd4e406242f7942dad9f640db3b48fdbbbab41471cd0153a44904db7ea893d0` |
| `runs/online-unit-scaling-20261004/retrieve-policy-declarations.log` | `9e1ba55cf5d2aa3ba9ccc80b365152964171721b91ddef9bbdd739d4441886e7` |
| `runs/online-unit-scaling-20261004/retrieve-unit-declarations-exit.json` | `014f9ab8f6e4f7aa1790fb745d27481934bb578f50f383fb5c5d98e4f7e65b35` |
| `runs/online-unit-scaling-20261004/retrieve-unit-declarations.log` | `91f6a8e3cc8f1196a8151a94e2a6d08177d7ff0ebcf5dc0828b7000aaaa71726` |
| `runs/online-unit-scaling-20261004/retrieve-unit-memory-exit.json` | `2697039ce28150c52ecfb0ddf82e28d1de559d18874f92dcd7b33cc0a8e1aee6` |
| `runs/online-unit-scaling-20261004/retrieve-unit-memory.log` | `74c36c086a5b51d71d5717e7aace22637e5b7bdb5bf86a2db7b0d80acad743a5` |
| `runs/online-unit-scaling-20261004/run-command.py` | `fc009e52bbc0ce6e76c84a314372c785950f0927befb1b0e8a19f5b093e1a837` |
| `runs/online-unit-scaling-20261004/source-binding.json` | `8e8f84791726ab7e033dc4cb0f99d635eed59a9a75e6be534ddcaa0ed94fd18c` |
| `runs/online-unit-scaling-20261004/source-card.md` | `2d235b452857c5ce91b197101c0fb85731a954754db6237fdef54fe8985a7840` |
| `runs/online-unit-scaling-20261004/source-pages.txt` | `6e3bd775f7d8ab9bd0ed03ca6bfa22a12a9c6179db5c772a6afaa5df20eb2d97` |
| `runs/online-unit-scaling-20261004/workflow-bindings.json` | `e9290e938ef6370d2bb9bb75c7ed42a58317d5839b68ed0f5c176f4dca37787a` |
| `runs/online-unit-scaling-20261004/workspace-audit.json` | `e87834744638e9a5888cdf6a8283cb3889237eb66130fdc57aabcf3cfa7dbf0a` |
| `runs/online-unit-scaling-20261004/leaves/api-check-01.lean` | `153a4266bb5288ac9d8ef11e7f3d91f66c5ea77216417a8aeb401c36000fbe11` |
| `runs/online-unit-scaling-20261004/leaves/context-v1.lean.txt` | `47aa298a466cd68e18e8fcb6ac91f31893d56c52ca33650d4b48e2597f682d6f` |
| `runs/online-unit-scaling-20261004/leaves/neutral-types-v1.lean` | `115d322c56e10a9b2012e0bfe9f675f4bf3495a5ebd83f9fac9a89a2989f0b87` |
| `runs/online-unit-scaling-20261004/leaves/target-v1.lean.txt` | `bd828f3d16777ad8a835f700f912c46ffc6a29f26a9e08e3ba0c82a34238a5d9` |
| `runs/online-unit-scaling-20261004/leaves/types-v1.lean` | `c6645e9152ab4386b10ba196671f1c96ad62e8be0966ee92ab25261a7de3dea4` |
| `docs/contracts/online-unit-scaling-v1/context.lean.txt` | `47aa298a466cd68e18e8fcb6ac91f31893d56c52ca33650d4b48e2597f682d6f` |
| `docs/contracts/online-unit-scaling-v1/distance_square_scaling-header.txt` | `c04822582f98297e83777cd705ea186720637d26b1be96b03b9219ca7939548c` |
| `docs/contracts/online-unit-scaling-v1/distance_square_scaling.json` | `bf24aafb7edcc6bf0188f16b7df25764ea518db7f281b1f7a530661443225160` |
| `docs/contracts/online-unit-scaling-v1/energy_scaling-header.txt` | `6547c311f5dac8531e47c4068dc2acf8063bcef75e951faeb84894b273601390` |
| `docs/contracts/online-unit-scaling-v1/energy_scaling.json` | `3b02326fbc16d2365a15f9631132c49b84bc33a54446929120772e11bbfa0b20` |
| `docs/contracts/online-unit-scaling-v1/gradient_scaled-header.txt` | `4d4a2f1cdb35caad421bae929b92e0d122edaf5220bb61e77c6db88a5b4503b3` |
| `docs/contracts/online-unit-scaling-v1/gradient_scaled.json` | `fb10af190441da7b0c1bab0497e9759429e8fa4a918ab5abbe6f291afe3acb7d` |
| `docs/contracts/online-unit-scaling-v1/hasGradientAt_scaled-header.txt` | `ed81ff707f30a7f802fd5c3ed4da9d2ccaf95438c9163889a5beeb5f9d9da181` |
| `docs/contracts/online-unit-scaling-v1/hasGradientAt_scaled.json` | `d0af619db7e1d156cc31c5188a6e38593e7319ca8827c80e8fc58a4b0488e260` |
| `docs/contracts/online-unit-scaling-v1/history_scaling-header.txt` | `4c9ccabbe2bc8e7c679ef491c6a1ec2d53a779776b719970f35f35909ba9825d` |
| `docs/contracts/online-unit-scaling-v1/history_scaling.json` | `abb4d860869ccff1bafea7443c060172b9ad44aa24c8eeabe33948ed946e9252` |
| `docs/contracts/online-unit-scaling-v1/inverse_loss-header.txt` | `8d2dd2a430aaf88183a8e18753e35943936a066efb8a806c07484a86a4055700` |
| `docs/contracts/online-unit-scaling-v1/inverse_loss.json` | `c674e174d019341fbf3c20bf5c9dc5545133ebc0ec9f7954af50324392425910` |
| `docs/contracts/online-unit-scaling-v1/legal_feedback_scaling-header.txt` | `f75c67671aa62664610ae223cc4bdab88119c75f80cf01f5b586f4dad7744a8f` |
| `docs/contracts/online-unit-scaling-v1/legal_feedback_scaling.json` | `49b629d1658b828ecaf994c5d2ff568d255495ed6ecf1d6f3e076b7101f1a82e` |
| `docs/contracts/online-unit-scaling-v1/loss_value_scaling-header.txt` | `4d44b4175f45bc060c73b9f22b385c324ab3c52e50be3fe09fd7ff821112ae92` |
| `docs/contracts/online-unit-scaling-v1/loss_value_scaling.json` | `fbfc061b23caf1f2982a2463873475caf4bbde067955f37a5c40eb9bd1a63cab` |
| `docs/contracts/online-unit-scaling-v1/output_scaling-header.txt` | `be52c1e204530474ed70c0d07b62a4c326e783c861bc182ebb73a74cfe27c5ab` |
| `docs/contracts/online-unit-scaling-v1/output_scaling.json` | `9e8e6127024682e7ed457709316f76b105dfdd31a2e008d4e74c1c05203d35d5` |
| `docs/contracts/online-unit-scaling-v1/proper_scaled_loss-header.txt` | `be1dc28c1faa5f5955d4e347af996ffc164021dc74eddece00ab8f8535916cfc` |
| `docs/contracts/online-unit-scaling-v1/proper_scaled_loss.json` | `9e47caeabe2ed867d0f5cc503f345722b305b6f1c3c23ea86bbef267070550d0` |
| `docs/contracts/online-unit-scaling-v1/regret_fixed_scaled-header.txt` | `ba3eea49c0bbee66f39489d0cbc98a5971f63508f5785be5008e21c90c9f4d0d` |
| `docs/contracts/online-unit-scaling-v1/regret_fixed_scaled.json` | `e767d598ef80d7a24870c3fe7cd93b688ef6f734a1665960a47f93a411b3f5bd` |
| `docs/contracts/online-unit-scaling-v1/regret_scaling-header.txt` | `01c580d3a69615559ed5dd5d7b4e9258ff292743c9a7d602c0c876bf1bf2fe60` |
| `docs/contracts/online-unit-scaling-v1/regret_scaling.json` | `f55007812fe734f6791ef078c18ce5124b6be4ca9f5bd729c36c02754257190a` |
| `docs/contracts/online-unit-scaling-v1/regret_unit_exponents-header.txt` | `ce574baae0cbf375310de1683aa14e988d507e38f12091c83df196474276474d` |
| `docs/contracts/online-unit-scaling-v1/regret_unit_exponents.json` | `bd5bea1cb79d077d835dc9e343a0f7d4547dd43efb5d0b8d19821ebd9fce64ce` |
| `docs/contracts/online-unit-scaling-v1/scaled_eta_positive-header.txt` | `2971048145af2947ee7c982a29c6dd5418e2e69f297cb9e45a193f42cbe0a8fa` |
| `docs/contracts/online-unit-scaling-v1/scaled_eta_positive.json` | `23e914fed72b7df5d95e3bb9c6197a1471a55fd04cbf0e61fd843f1c72ee9cbe` |
| `docs/contracts/online-unit-scaling-v1/selected_scaling-header.txt` | `ea27c16695d465a27188c5ab537a57d36cf2f2e0b9d36eb4894e90fc3c0ee3c0` |
| `docs/contracts/online-unit-scaling-v1/selected_scaling.json` | `7a4861a9bfb70c954885cc95d40172861aafebd3999243bf9990feab8adbe857` |
| `docs/contracts/online-unit-scaling-v1/step_scaling-header.txt` | `57bbbc370eca313cede1a45a18fc935d39607b8a4b9948591aae2ac307037f8b` |
| `docs/contracts/online-unit-scaling-v1/step_scaling.json` | `03ab738e9fedaae29f7d28e4e21e69fb5976b2cc0230d20c42b2a006ada0ad58` |
| `docs/contracts/online-unit-scaling-v1/subdifferentiable_scaled-header.txt` | `fb5ee90edc190bba7370e1da4f087d95641a6f0fbbc43d63f2f3c660a86cdd06` |
| `docs/contracts/online-unit-scaling-v1/subdifferentiable_scaled.json` | `5108fa3ee9af4c8f17e84202a101a8566e659ca169e537b52f6e3d7a689ddeba` |
| `docs/contracts/online-unit-scaling-v1/subgradient_scaled-header.txt` | `509e33485af3891f6d82d7a4d2e170c6d700e6557bf858d714f2bd9dbb0668fd` |
| `docs/contracts/online-unit-scaling-v1/subgradient_scaled.json` | `25aacb15f53d035c0879a732749e6134fe92a46af07a8688a3ddbe13e318427c` |
| `docs/contracts/online-unit-scaling-v1/unit_exponents-header.txt` | `78b949f2db4a1130781c062dee03858febb00571beb4503b0feb71ffb55dd50d` |
| `docs/contracts/online-unit-scaling-v1/unit_exponents.json` | `b3840d2722e7db3fbd3226dcf96caddd378eb2601b9b58da4ec5c155d7819491` |
| `docs/contracts/online-unit-scaling-v1/upper_bound_scaling-header.txt` | `57fda846c513aa20f0ef87f8e044654e3b5646f0bf3abc31e7a7f50e956166fd` |
| `docs/contracts/online-unit-scaling-v1/upper_bound_scaling.json` | `fcec0b433cc54298bd3573934376cf5fff20ae79d5c439bf0e1b7b3d0b54394b` |
| `docs/contracts/online-unit-scaling-v1/wrong_step_output-header.txt` | `65d252604aec31807cd78f98b8abf7abf12905e9731fd674151b9eea18d6b1f2` |
| `docs/contracts/online-unit-scaling-v1/wrong_step_output.json` | `34f48e9414d60d3674ac5eb207ff2f169a11ee01236c30b403d59b95f963ff98` |
| `docs/contracts/online-unit-scaling-v1/wrong_step_scaling-header.txt` | `ff015336715e7552a31ce207dcffda4150b2fcfba6c0f631cfde042d4594a18a` |
| `docs/contracts/online-unit-scaling-v1/wrong_step_scaling.json` | `976237bf049015f6e6d6000171e7cc2e97490dcd0b6058d1b5741662c3873f96` |
| `conversion-windows/ONLINE-UNIT-SCALING-20261004.md` | `44eb12f1dea49bfd402013adba22c45a9976d9bdb798fa39a6b1cf8c7ca63acd` |
| `proof-obligations/ONLINE-UNIT-SCALING-20261004.md` | `ba375bd405218df89199bf857f83864a3fd2b776dd668f0071827229e242a6b7` |
| `tasks/ONLINE-UNIT-SCALING-20261004.md` | `e30868a88f6dbe37e2e01c96adff4f4a6807df1eada33d9fc6f551579fdd5d68` |
| `BanditRLProof/OnlineSubgradientPolicy.lean` | `ac8fbfb3eee3c92ebb79b44f33beec33b500105bb7e54df5176c14e886c2c662` |
| `BanditRLProof/OnlineSubgradientDescent.lean` | `6ba8586e1691babc2db3e0c0fcddb69b4236e16f9f192c464b4c04262e854f1c` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `BanditRLProof/OnlineAffineSubgradient.lean` | `bb0f2bea722342c4255a57f38b68ce28436895ccb8cf703f3fdb420c97636278` |
| `BanditRLProof/OnlineGradientDescent.lean` | `e7edba540c2f60032bb4a34aaf0768b3107b94276b67b6f41fc289009c8924c1` |
| `BanditRLProof/OnlineHuber.lean` | `dd7c6b4c41e5fee804196bbccfec493df37ae56294f32cddf3d11be27646de86` |
| `BanditRLProof/OnlineHinge.lean` | `118d28177c11b0ff113fba5ab34a6bbd9190fee5fb05af644b7b2207c05b020b` |
| `BanditRLProof/OnlineOptimalStep.lean` | `621accb68aa788e4ae225fbe0c94ca86c0b26db6fb7ea23210b1aeffed69afa1` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `research-wiki/mathlib/theorem-cards.md` | `4656c1a8ccd4b2d8523cf5cf48bd1f966e7ba2c2237e2e578d6b8c2ecc6fbd97` |
| `.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean` | `c7a80e952f6f577c441b92802fc5020fa63b564b75418fb96e29d4f6813020ca` |
| `.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Linear.lean` | `f6704b13d83ced036654dad708479bf0a9f0424f0e4562be5c34b131c9479f0e` |
| `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean` | `ffa28bc6ab970495e53c01337b42aee7b047644eb954a253b491a5104e409735` |
| `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean` | `dc7d5a73e0938a3259223837aa2914034636d9042baba997fc9fb3221c8241ae` |
| `.lake/packages/mathlib/Mathlib/Algebra/Module/Basic.lean` | `cbc4b310852df81355ea0f836f4e0e072c6d7645e25bee4826a4353c000bdbde` |
| `tools/bandit.py` | `d4a5a27189b200ac977e5b6b3ce3bce5880dff1b7530461aab6860352199da9c` |
| `tools/abrl_lifecycle.py` | `7615541e66a372e939ea2d18684ce78a8f3d8f1202894840ef7fdfdc703c4310` |
| `E:/ABRL/papers/long/main/harness.tex` | `31370babc09de16f536d2f975902b035fe02ba3c290deb3380501efd24a848e6` |
| `docs/hierarchical_harness.md` | `6027004b33e316f5d47794ddbda01414ce6c811ba164163c7b2ece671b9468b7` |
| `docs/lifecycle_and_proof_frontier_hardening.md` | `335a861e00d13d59f88080ec54e6174722afc7534ad9e74f4261b4247f50165a` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `runs/online-unit-scaling-20261004/source-review-packet-v1.md` | `5e6ce530a4d349bb582594cc45479de3ad4ffa8f6a8a72c960f36e428510d2b7` |
| `runs/online-unit-scaling-20261004/contract-source-inputs-v1.json` | `13f1de6af2942f2c36591f14436e28a51146514e90f53181c1fbaa81b49645d5` |
| `.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean` | `bf69a9ed4bc39134bbefac1a43b187e2f1e66fd43f352d0810ab89474f054922` |
