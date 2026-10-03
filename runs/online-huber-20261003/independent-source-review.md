# Independent anti-anchored source review: Huber Example 2.15

Verdict: **accepted-with-explicit-delta**.

Actor: `/root/source_reviewer`, distinct from the formalizer and `/root/blind_decoder`. Requested review configuration: GPT-6 Astra, medium reasoning. Date: 2026-10-03. This reviewer searched for mismatches rather than confirming an earlier verdict. No historical acceptance review, acceptance decision, contribution manifest verdict, or reader repair review was read. The scope is semantic correspondence of the actual 19 public theorem targets; this report does not certify a compiler run, integration, deployment, or Chapter 2 completion.

## Read inventory and binding

Working repository: `E:/ABRL/worktrees/research-online-book`; branch `codex/research-online-huber`; inspected HEAD `638daa0b5f604b678b1b69a04e740e733033733c`. Working tree was dirty, including the reader JSON and review artifacts, so this report binds the file bytes below rather than claiming HEAD contains them.

- `.agents/skills/bandit-semantic-roundtrip/SKILL.md`: seven-slot review instructions.
- `README.md`: opening repository context.
- `BanditRLProof/OnlineHuber.lean`: entire actual file, including definitions, all 19 theorem statements and their proofs; SHA256 `dd7c6b4c41e5fee804196bbccfec493df37ae56294f32cddf3d11be27646de86`.
- `BanditRLProof/OnlineGradientDescent.lean`: entire shared definitions and proof file, especially `Domain`, `RegularLoss`, `project`, `step`, `iterate`, `regret`, `iterate_prefix`, and `theorem_2_13_fixed`; SHA256 `e7edba540c2f60032bb4a34aaf0768b3107b94276b67b6f41fc289009c8924c1`.
- `runs/online-huber-20261003/blind-reconstruction.md`: complete independent reconstruction; SHA256 `163938f250262e3d27681be6ef274e40df98a724cfb2219a31dd69eaabc16b27`.
- `website/content/readings.json`: current `online-huber` entry, including its four-step proof bridge; containing file SHA256 `8d2428322aca37f0415d6402a82b415af73b9b52b098d6973f24da170ca13201`.
- Source: `E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf`, Orabona arXiv:1912.13213v10, Example 2.15, printed pages 15–16 / physical PDF pages 27–28. Independently computed PDF SHA256 **matches** the supplied value: `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`.
- Read cached `full.txt` form-feed pages 26 and 27, then independently extracted physical pages 27–28 directly from that hash-checked PDF with `pdftotext`; the formulas and prose agree. The source interpretation therefore does not rely solely on an unbound cached text file.

## Source statement and actual formal target

The source uses unrestricted Euclidean linear predictors and loss `H_delta(<z_t,x>-y_t)`, with quadratic branch `r^2/2` for `|r|<=delta` and linear branch `delta*(|r|-delta/2)` otherwise. It prints the residual/clipped-sign gradient, assumes bounded feature norms, chooses a constant learning rate proportional to `1/sqrt(T)`, and describes average performance relative to any fixed linear predictor. It does not print the explicit average bound's constant used by this implementation.

The actual formal guarantee applies shared causal OGD to those exact losses on the full space. For fixed positive eta it proves

`R_T(u) <= ||x_0-u||^2/(2 eta) + eta*T*(delta Z)^2/2 - ||x_T-u||^2/(2 eta)`.

For each positive known horizon it chooses one constant `eta_T=1/sqrt(T)`, obtains

`R_T^(eta_T)(u)/T <= (||x_0-u||^2+(delta Z)^2)/(2 sqrt(T))`,

and proves that every positive epsilon eventually upper-bounds the left side, for each fixed comparator and globally bounded feature stream. Only the numerical upper envelope has a `Tendsto ... 0` theorem.

## Seven semantic slots

| Slot | Adversarial check and outcome |
| --- | --- |
| 1. Objects and spaces | Source is finite-dimensional real Euclidean space; Lean is any complete real inner-product space. This is a genuine extension, not literal source identity, and Euclidean spaces instantiate it. Full-space projection is proved identity. Arbitrary feature/label streams generalize the illustrative stock-price/history construction; no stock-specific generative claim is encoded. No bounded predictor set is substituted. |
| 2. Quantifiers | Parameters, arbitrary data, initialization and comparator precede the horizon result. The same run for a given horizon works for every fixed comparator because eta is independent of u. The eventual threshold may depend on u and epsilon; it is not uniform over the unbounded comparator space. No moving comparator or hindsight-dependent learning rate is introduced. |
| 3. Assumptions/regularity | `delta>=0` makes the source's implicit threshold convention explicit; the source does not print a sign inequality. This is required for convexity and the displayed derivative across zero: for negative delta, the formula becomes a negative multiple of absolute value plus a constant, invalidating convexity and differentiability at zero. Zero remains admitted, with identically zero loss. `Z>=0` expresses a norm bound; no positive Z, bounded labels, bounded residuals, or bounded decision domain is added. Convexity, differentiability and gradient boundedness are derived, not supplied as unexplained premises. |
| 4. Conclusion/metric | Regret is the actual sum of loss differences on the generated trajectory. The source's informal average-performance statement is implemented as a one-sided eventual upper guarantee. It is not an absolute difference, equality of limiting average losses, or convergence of actual average regret to zero. For example, constant scalar z=1,y=0, x0=0, delta=1 and comparator u=1 leave the algorithm at zero and give average regret -1/2 for every positive horizon, so literal zero convergence against every comparator would be false. Current reader text correctly makes this distinction. |
| 5. Constants/indexing/asymptotics | Both branches preserve the factor 1/2. Derivative saturation is delta and gradient bound is delta*Z, hence the squared bound is `(delta*Z)^2`. Source proportional eta is specialized to constant 1; this is a selected valid instance, not the whole family of proportionality constants. Lean round 0 is source round 1; terminal iterate T corresponds to source x_(T+1). The finite fixed-step theorem retains both initial and negative terminal terms. Positive horizon is required for the tuned bound; the asymptotic numerical theorem's totalized value at T=0 is irrelevant. |
| 6. Probability/feedback/causality | The result is deterministic and pathwise. Shared `iterate` uses loss t only for the next iterate, and `iterate_prefix` establishes strict-prefix loss dependence. The feature is available for the current scalar prediction; y_t enters only after that prediction through the update. No future losses or gradients determine eta. Knowing T does not mean knowing future losses. No expectation, independence, filtration, stopping-time, or stochastic claim is introduced. |
| 7. Boundary/excluded regimes | Delta=0 and Z=0 remain covered; fixed-step T=0 gives exact cancellation of the distance terms. The asymptotic claim is a family of separate known-horizon runs, not one anytime trajectory with eta_t=1/sqrt(t). Negative thresholds, time-varying comparators, uniformity over all comparators, and two-sided regret convergence are outside the result. |

## Inventory of all 19 actual public targets

| # | Target in `BanditRL.OnlineHuber` | Finding |
| --- | --- | --- |
| 1 | `hasDerivAt_ite_le` | Valid generic derivative gluing interface; source-supporting infrastructure, not a numbered book assertion. |
| 2 | `huber_three_pieces` | Correct algebraic decomposition including both seams; requires nonnegative threshold. |
| 3 | `huber_zero` | Correct degenerate threshold boundary, retained explicitly. |
| 4 | `hasDerivAt_join` | Valid generic global gluing interface with matching values and derivatives; no unwarranted continuity hypothesis. |
| 5 | `huber_hasDerivAt` | Correct derivative at interior points and seams, including coincident seams when delta=0. |
| 6 | `huber_deriv_clamp` | Equivalent clipped derivative under delta>=0. |
| 7 | `huber_convex` | Full scalar-domain convexity, matching source's convex loss convention. |
| 8 | `huber_deriv_bound` | Correct absolute derivative bound delta. |
| 9 | `huber_deriv_source` | Exact printed residual/sign form and branch inequality. |
| 10 | `huber_linear_hasGradientAt` | Exact source gradient by composition, generalized to the stated Hilbert space. |
| 11 | `huber_linear_convex` | Convexity of the actual affine-composed loss; no domain restriction. |
| 12 | `huber_linear_gradient_bound` | Correct delta times feature norm, independent of labels/predictor magnitude. |
| 13 | `project_fullSpace` | Connects the shared projection to the unconstrained source update. |
| 14 | `huber_regular` | Supplies the shared theorem's regularity using this actual loss on the full space. |
| 15 | `huber_step` | Exact source gradient update. Allowing arbitrary eta here is harmless algebra; regret results require eta>0. |
| 16 | `huber_regret_fixed` | Actual-trajectory bound with feature norms bounded only on the finite prefix; initial and terminal terms preserved. |
| 17 | `huber_average_bound` | Correct selected constant-step instance eta=1/sqrt(T), positive T, arbitrary fixed comparator. |
| 18 | `huber_rate_tendsto` | Correct numerical-envelope limit; sign assumptions unnecessary for this isolated squared expression. No regret convergence is asserted. |
| 19 | `huber_average_eventually` | Correct eventual strict upper inequality for every positive epsilon, pointwise in a fixed comparator, for globally bounded features and the horizon-indexed family. |

The blind reconstruction correctly exposes these definitions, quantifiers, seams, boundary cases, and the one-sided/horizon-family distinctions. I found no mismatch between that reconstruction and the actual declarations. I inspected proof bodies only to check that the consumer uses the actual shared loss/trajectory, not to substitute for independent compilation.

## Reader wording and required repairs

The inspected `online-huber` reader explicitly identifies the Hilbert/Euclidean delta, nonnegative threshold, retained zero threshold, constant-one proportionality choice, indexing, known-horizon family, and one-sided guarantee. Its displayed arrow applies to the numerical right-hand envelope; both fallback text and proof bridge say so. The source contract's Euclidean model is a valid specialization of the general Lean target. Its scalar update and horizon-four arithmetic are consistent with the formulas. The local compiled-status label was not independently verified in this semantic review.

Required Lean repairs: **none**. Required reader repairs for the inspected bytes: **none**. Required acceptance-record treatment: retain `accepted-with-explicit-delta`, enumerate the scope/threshold/schedule/indexing/one-sided interpretation above, and do not collapse this into an unqualified assertion that the source literally states the generalized explicit theorem or that average regret converges to zero. Compilation and broader acceptance evidence must remain separately verified. This verdict does not revalidate earlier reviews or certify later edits to the bound files.
