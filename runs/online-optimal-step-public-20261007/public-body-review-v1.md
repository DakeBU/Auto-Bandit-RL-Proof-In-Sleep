# Optimal-step public BODY review

Verdict: **accepted-with-explicit-delta**, actual existing bodies/canaries only. No required mathematical or metadata repairs found. Original R1–R8 remain future reader obligations verbatim below.

Actor `/root/source_reviewer`, requested GPT-6 Astra / medium; runtime identity/effort unverified. Prior staged source-review/CONTRACT history disclosed. This is not blind, external or human review. CONTRACT acceptance was not treated as proof-body acceptance.

All200 current fixed raw rows and all114 original CONTRACT rows independently match before/after. Original source receipt and report are unchanged. Fresh PDF hash is `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`; I again actually viewed physical27/printed15. Source warning about future energy depending on eta and unavailable comparator distance remains binding. Mathematical focus was all11 proof bodies, both complete definitions and all28 canary declarations (23proofs/4defs/1abbr), with exact actual headers checked separately.

Both definitions are total real arithmetic, while positive admissible eta and strictly positive coefficients are hypotheses of the optimizer results, not inferred from total definition existence. The exact square-gap is a genuine producer. The universal minimum compares the same fixed A,B at every positive eta, and uniqueness is a full iff. The one-zero strict improvements and both-zero extension do not smuggle in a positive optimizer at zero. Distance and diameter substitutions retain positiveR/positiveD,G and naturalT>0; source L=Lean G. No algorithm input, future observations or selected regret bound is assumed.

Actual evidence separately read: focused9093 jobs including caches, exit0/4.348s;41 distinct named standard-three kernel outputs (no sorryAx), full type log, eleven actual raw/native full-header/literal-assumption guards and safe results. The compiled TEST environment has41selected nodes (34proofs/7definitions including1abbr),2826direct constant references. I independently checked ALL27 prescribed pairs occur in value_dependencies, not merely types. These selected references are not full registry coverage or literature equivalence. Existing unused-tactic/simp lints are nonfatal and retained.

The scalar result minimizes the coarser two-term objective, not the sharp negative terminal-distance bound. Actual OGD/OSD regret applications still require their separate domain/initial/loss/support-or-gradient/bound/horizon hypotheses. The finite same-loss OGD canary genuinely derives different energies across two stepsizes and does not prove Chapter5 lower bounds/impossibility. Zero new proofs, definitions, source closures or nodes are credited in this migration of historical PR151. Current PR184 base is a separate stack reference.

Current combined root/Tests/full harness, reader/shared registry/site/pixels/FINAL/native acceptance/PR remain future. No package/chapter/book/Goal acceptance, merge/main/live/deploy/retirement. Unit-scaling, remaining Chapter1/2 and appendices, nine OTHERChapter1 gaps, incomplete/null Chapter2 and unenumerated3–16 remain required; whole Goal active/unbudgeted.

## Complete definitions

`upperBound A B eta = A/(2eta)+eta*B/2`; `optimalStep A B = sqrt A/sqrt B`. Both are real scalar functions with no extra context/classes, learner, domain or probability. Totalization is not positive-optimizer admissibility.

## Per-target seven slots and actual bodies

### gap_identity — accepted-with-explicit-delta

```lean
theorem gap_identity (A B η : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hη : 0 < η) :
    upperBound A B η - Real.sqrt A * Real.sqrt B =
      (Real.sqrt A - η * Real.sqrt B) ^ 2 / (2 * η)
```

- **objects**: Real scalar F(A,B,eta)=A/(2eta)+eta B/2 and S(A,B)=sqrtA/sqrtB; only diameter target additionally has natural T. No ambient space, domain or learner binder.
- **quantifiers**: All real A,B,eta.
- **assumptions**: A,B>=0; eta>0.
- **conclusion**: Exact excess equals (sqrtA-eta sqrtB)^2/(2eta).
- **constants_indices**: Both factors2 and squared residual exact.
- **operation_information**: Hold SAME supplied coefficients fixed for all compared eta. No future observations or trajectory-dependent recomputation are inputs.
- **source_delta_boundaries**: Zero coefficients included, signed negative coefficients excluded; identity is a library refinement.

Actual proof: Actual Real.sq_sqrt hA/hB identities, unfolding and field_simp with eta nonzero produce the exact squared gap through linear_combination. No inequality/minimum premise is consumed.

### lower_bound — accepted-with-explicit-delta

```lean
theorem lower_bound (A B η : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hη : 0 < η) :
    Real.sqrt A * Real.sqrt B ≤ upperBound A B η
```

- **objects**: Real scalar F(A,B,eta)=A/(2eta)+eta B/2 and S(A,B)=sqrtA/sqrtB; only diameter target additionally has natural T. No ambient space, domain or learner binder.
- **quantifiers**: All real A,B,eta.
- **assumptions**: A,B>=0; eta>0.
- **conclusion**: sqrtA sqrtB <= F(A,B,eta).
- **constants_indices**: Exact constant1; non-strict inequality.
- **operation_information**: Hold SAME supplied coefficients fixed for all compared eta. No future observations or trajectory-dependent recomputation are inputs.
- **source_delta_boundaries**: No attainment from merely nonnegative coefficients; lower-bound helper.

Actual proof: Calls actual gap_identity and derives nonnegative square divided by positive2eta, then linarith. Zero coefficients remain allowed.

### optimal_positive — accepted-with-explicit-delta

```lean
theorem optimal_positive (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    0 < optimalStep A B
```

- **objects**: Real scalar F(A,B,eta)=A/(2eta)+eta B/2 and S(A,B)=sqrtA/sqrtB; only diameter target additionally has natural T. No ambient space, domain or learner binder.
- **quantifiers**: All real A,B.
- **assumptions**: A,B>0.
- **conclusion**: sqrtA/sqrtB>0.
- **constants_indices**: Both roots separately positive.
- **operation_information**: Hold SAME supplied coefficients fixed for all compared eta. No future observations or trajectory-dependent recomputation are inputs.
- **source_delta_boundaries**: Admissibility only, not a minimum by itself; explicit positive regime.

Actual proof: Real.sqrt_pos and div_pos produce admissibility from both strict positive coefficients.

### optimal_value — accepted-with-explicit-delta

```lean
theorem optimal_value (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    upperBound A B (optimalStep A B) = Real.sqrt A * Real.sqrt B
```

- **objects**: Real scalar F(A,B,eta)=A/(2eta)+eta B/2 and S(A,B)=sqrtA/sqrtB; only diameter target additionally has natural T. No ambient space, domain or learner binder.
- **quantifiers**: All real A,B.
- **assumptions**: A,B>0.
- **conclusion**: F at sqrtA/sqrtB equals sqrtA sqrtB.
- **constants_indices**: Exact equality, no order or asymptotics.
- **operation_information**: Hold SAME supplied coefficients fixed for all compared eta. No future observations or trajectory-dependent recomputation are inputs.
- **source_delta_boundaries**: Evaluation helper; no competitor quantifier until source_argmin.

Actual proof: Obtains admissibility, nonzero sqrtB, cancellation of sqrtA-(sqrtA/sqrtB)*sqrtB, and zero gap. Does not assume attainment.

### optimal_unique — accepted-with-explicit-delta

```lean
theorem optimal_unique (A B η : ℝ) (hA : 0 < A) (hB : 0 < B) (hη : 0 < η) :
    upperBound A B η = upperBound A B (optimalStep A B) ↔ η = optimalStep A B
```

- **objects**: Real scalar F(A,B,eta)=A/(2eta)+eta B/2 and S(A,B)=sqrtA/sqrtB; only diameter target additionally has natural T. No ambient space, domain or learner binder.
- **quantifiers**: All real A,B and eta.
- **assumptions**: A,B,eta>0.
- **conclusion**: Equality with optimal value iff eta equals sqrtA/sqrtB.
- **constants_indices**: Full iff; same coefficients on both sides.
- **operation_information**: Hold SAME supplied coefficients fixed for all compared eta. No future observations or trajectory-dependent recomputation are inputs.
- **source_delta_boundaries**: Unique positive optimizer combined with argmin; no all-real minimization.

Actual proof: Forward equality makes the actual squared gap zero with nonzero2eta; pow_eq_zero gives linear relation and nonzero sqrtB permits ratio equality. Reverse substitution uses attained value; full iff retained.

### source_argmin — accepted-with-explicit-delta

```lean
theorem source_argmin (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    0 < optimalStep A B ∧
    upperBound A B (optimalStep A B) = Real.sqrt (A * B) ∧
    ∀ η : ℝ, 0 < η → upperBound A B (optimalStep A B) ≤ upperBound A B η
```

- **objects**: Real scalar F(A,B,eta)=A/(2eta)+eta B/2 and S(A,B)=sqrtA/sqrtB; only diameter target additionally has natural T. No ambient space, domain or learner binder.
- **quantifiers**: All positive A,B; every real eta>0 competitor.
- **assumptions**: A,B>0; competitor positivity inside implication.
- **conclusion**: Positive selected step, value sqrt(A*B), universal minimum.
- **constants_indices**: Three conjunctions; sqrt product agrees with product of roots here.
- **operation_information**: Hold SAME supplied coefficients fixed for all compared eta. No future observations or trajectory-dependent recomputation are inputs.
- **source_delta_boundaries**: Source scalar calculation plus explicit admissibility; not an adaptive learner.

Actual proof: Assembles actual positive step and attained value, rewrites sqrt multiplication, and introduces every positive eta using lower_bound for unchanged A,B.

### distance_energy_argmin — accepted-with-explicit-delta

```lean
theorem distance_energy_argmin (R B : ℝ) (hR : 0 < R) (hB : 0 < B) :
    optimalStep (R ^ 2) B = R / Real.sqrt B ∧
    upperBound (R ^ 2) B (R / Real.sqrt B) = R * Real.sqrt B ∧
    ∀ η : ℝ, 0 < η → upperBound (R ^ 2) B (R / Real.sqrt B) ≤ upperBound (R ^ 2) B η
```

- **objects**: Real scalar F(A,B,eta)=A/(2eta)+eta B/2 and S(A,B)=sqrtA/sqrtB; only diameter target additionally has natural T. No ambient space, domain or learner binder.
- **quantifiers**: All R,B positive; all positive real competitors.
- **assumptions**: R>0,B>0.
- **conclusion**: A=R^2, step R/sqrtB, value R sqrtB and universal minimum.
- **constants_indices**: R is distance not squared distance; positivity removes absolute value.
- **operation_information**: Hold SAME supplied coefficients fixed for all compared eta. No future observations or trajectory-dependent recomputation are inputs.
- **source_delta_boundaries**: Source specialization; distance/energy are supplied scalars, not produced run data.

Actual proof: Proves R^2 positive, calls source_argmin and optimal_value, uses sqrt_sq with R nonnegative to obtain R rather than absolute R, then retains all-positive-eta comparison.

### diameter_argmin — accepted-with-explicit-delta

```lean
theorem diameter_argmin (D G : ℝ) (T : ℕ) (hD : 0 < D) (hG : 0 < G) (hT : 0 < T) :
    optimalStep (D ^ 2) (G ^ 2 * (T : ℝ)) = D / (G * Real.sqrt (T : ℝ)) ∧
    upperBound (D ^ 2) (G ^ 2 * (T : ℝ)) (D / (G * Real.sqrt (T : ℝ))) =
      D * G * Real.sqrt (T : ℝ) ∧
    ∀ η : ℝ, 0 < η →
      upperBound (D ^ 2) (G ^ 2 * (T : ℝ)) (D / (G * Real.sqrt (T : ℝ))) ≤
      upperBound (D ^ 2) (G ^ 2 * (T : ℝ)) η
```

- **objects**: Real scalar F(A,B,eta)=A/(2eta)+eta B/2 and S(A,B)=sqrtA/sqrtB; only diameter target additionally has natural T. No ambient space, domain or learner binder.
- **quantifiers**: All real D,G and natural T; all real positive competitors.
- **assumptions**: D,G>0 and natural T>0.
- **conclusion**: A=D^2,B=G^2*T, step D/(G sqrtT), value DG sqrtT and minimum.
- **constants_indices**: Natural-to-real coercion explicit, T>=1; source L is Lean G.
- **operation_information**: Hold SAME supplied coefficients fixed for all compared eta. No future observations or trajectory-dependent recomputation are inputs.
- **source_delta_boundaries**: Second source calculation only; actual regret requires separate algorithm assumptions.

Actual proof: Nat.cast_pos produces positive realT, G^2*T is positive; sqrt_mul and sqrt_sq simplify to GsqrtT; applies actual distance_energy_argmin. No diameter or gradient premise magically produced.

### zero_distance_decreases — accepted-with-explicit-delta

```lean
theorem zero_distance_decreases (B η : ℝ) (hB : 0 < B) (hη : 0 < η) :
    0 < η / 2 ∧ upperBound 0 B (η / 2) < upperBound 0 B η
```

- **objects**: Real scalar F(A,B,eta)=A/(2eta)+eta B/2 and S(A,B)=sqrtA/sqrtB; only diameter target additionally has natural T. No ambient space, domain or learner binder.
- **quantifiers**: Every B,eta>0.
- **assumptions**: A=0,B>0,eta>0.
- **conclusion**: eta/2 stays positive and strictly improves F.
- **constants_indices**: Strict inequality, exact halving.
- **operation_information**: Hold SAME supplied coefficients fixed for all compared eta. No future observations or trajectory-dependent recomputation are inputs.
- **source_delta_boundaries**: No positive minimizer follows; finite improvement not an explicitly proved limit/infimum.

Actual proof: Unfolds zero first coefficient and derives strict comparison from eta*B>0; eta/2 positivity separately produced.

### zero_energy_decreases — accepted-with-explicit-delta

```lean
theorem zero_energy_decreases (A η : ℝ) (hA : 0 < A) (hη : 0 < η) :
    0 < 2 * η ∧ upperBound A 0 (2 * η) < upperBound A 0 η
```

- **objects**: Real scalar F(A,B,eta)=A/(2eta)+eta B/2 and S(A,B)=sqrtA/sqrtB; only diameter target additionally has natural T. No ambient space, domain or learner binder.
- **quantifiers**: Every A,eta>0.
- **assumptions**: B=0,A>0,eta>0.
- **conclusion**: 2eta stays positive and strictly improves F.
- **constants_indices**: Strict inequality, exact doubling.
- **operation_information**: Hold SAME supplied coefficients fixed for all compared eta. No future observations or trajectory-dependent recomputation are inputs.
- **source_delta_boundaries**: Totalized optimalStep(A,0)=0 is inadmissible; no infinity-valued candidate.

Actual proof: Unfolds zero second coefficient, uses positive denominators in div_lt_div_iff and A*eta>0;2eta positive. No zero-step minimizer inferred.

### zero_coefficients — accepted-with-explicit-delta

```lean
theorem zero_coefficients (η : ℝ) : upperBound 0 0 η = 0
```

- **objects**: Real scalar F(A,B,eta)=A/(2eta)+eta B/2 and S(A,B)=sqrtA/sqrtB; only diameter target additionally has natural T. No ambient space, domain or learner binder.
- **quantifiers**: Every real eta.
- **assumptions**: A=B=0; no eta sign premise.
- **conclusion**: F(0,0,eta)=0.
- **constants_indices**: Exact zero, includes eta0 and negative eta.
- **operation_information**: Hold SAME supplied coefficients fixed for all compared eta. No future observations or trajectory-dependent recomputation are inputs.
- **source_delta_boundaries**: Algebraic library extension; all positive steps minimize, none uniquely selected.

Actual proof: Direct simp of the complete upperBound definition establishes zero even at eta0/negativeeta; an algebraic extension only.

## Whole-canary nonvacuity

- **scalar_positive**: Actual9,4 chosen3/2,value6,strict1cost13/2; public_argmin/universal/unique invoke real universal production endpoints, not only arithmetic fixtures.

- **tuning**: Actual D3,G2,T4 and T1 invoke diameter_argmin, with values12 and6; natural positivity is explicit.

- **degenerate**: Explicit witnesses eta/2 and2eta call strict-improvement producers; bothzero, inadmissible division0 and named T0 boundary remain actual.

- **same_loss_run**: Actual unbounded shared real V, loss(x-1)^2/2 and iterate from0; derivative x-1 from HasDerivAt, projection identity from variational characterization; after_one=eta, feedback=-1 theneta-1, actual finite sum gives1+(eta-1)^2. At eta=1 energy=1; at eta=2 energy=2. Finite dependence witness only, not global impossibility/rerun-regret optimizer.

## Original R1–R8, unchanged and still future-mandatory

- **R1**: Attribute TWO unnumbered printed15/PDF27 scalar calculations, not eleven printed theorems; eleven existing proofs/two definitions and zero new mathematics or registry nodes.

- **R2**: Expose both complete real scalar definitions and totalized sqrt/division; positive admissible eta, nonnegative gap coefficients versus strictly positive attained-minimum coefficients. No signed-coefficient optimizer.

- **R3**: Preserve universal ALL positive competing eta for SAME fixed A,B, full equality/uniqueness iff and positive chosen step; numerical example alone is not universal optimization.

- **R4**: Explain distance R versus squared coefficient R^2, energy B, D/G/natural T>0 substitutions and source L=G; T1 valid, T0 outside diameter optimizer.

- **R5**: Show one-zero improving eta/2 or2eta, both-zero constant extension and eta0/T0 inadmissibility; do not apply positive optimizer to degenerate cases.

- **R6**: Keep source future-gradient/eta dependence and unavailable comparator-distance warning explicit. Scalar minimum is not a future-informed algorithm, across-rerun regret optimizer, anytime/minimax or Chapter5 lower-bound/impossibility proof.

- **R7**: Distinguish coarse two-term objective from unchanged sharp negative terminal residual; actual OGD/OSD regret needs its separate domain/initial/loss/gradient-or-support/bound/horizon assumptions. Actual same-loss energy canary is a finite dependence witness only.

- **R8**: Keep historical PR151 distinct from current PR184 stacked base, current BODY/kernel/guards/value/rootTests/harness/reader/site/pixels/FINAL/native/PR separate; preserve failures/raw snapshots. Unit analysis/maintext/appendices/nineOTHERChapter1 gaps and incomplete chapters/active Goal remain mandatory; inspect decoded math and actual future pixels without inferring escaping defects from JSON repr.

Decoded-math checks from CONTRACT do not certify future rendered pixels; no unsupported TeX escaping repair is proposed.

## Raw inventory

All fixed inputs raw-read/hashed; current proof, canary, source and actual gates inspected for this bounded BODY scope, not recursive acceptance of historical trees.

| Path | SHA-256 |
|---|---|
| `BanditRLProof/OnlineOptimalStep.lean` | `621accb68aa788e4ae225fbe0c94ca86c0b26db6fb7ea23210b1aeffed69afa1` |
| `Tests/OnlineOptimalStepCanary.lean` | `668e4ae89fa4a357009a3ceeccfb069b7c21e39efef77e096aa40f8bd4fbeb86` |
| `BanditRLProof.lean` | `7cdb1969bad2f7b42cfd7a25f6d15747d0d49178dadc244b70ab1f9b8c92c5ad` |
| `Tests.lean` | `2b3615efabe9c94eff5dade925783e7d0ebacd3139a7ab65a5d46ba2c695ef77` |
| `BanditRLProof/OnlineGradientDescent.lean` | `9300cb2735da9f125e404f78b86509df47fe65a5f4d89abc469e071bdffdb871` |
| `BanditRLProof/OnlineSubgradientDescent.lean` | `6ba8586e1691babc2db3e0c0fcddb69b4236e16f9f192c464b4c04262e854f1c` |
| `BanditRLProof/OnlineSubgradientPolicy.lean` | `ac8fbfb3eee3c92ebb79b44f33beec33b500105bb7e54df5176c14e886c2c662` |
| `BanditRLProof/OnlineLinearization.lean` | `ec231ef4d85c3b27744378d1c3d9f071b6177fa1535d5db440a787800111339e` |
| `Tests/OnlineLinearizationCanary.lean` | `0f62baa46017ec5fc3e8234248dbd2e03388eae62396689c8b7e44f93931f975` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `docs/contracts/online-book-v1/source-inventory.json` | `a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7` |
| `research-wiki/contribution-contracts/ONLINE-OPTIMAL-STEP-20261004.json` | `fc7472f29e4f4d7b326691f840c8c114806071af8e888f698ab6e81efe83e603` |
| `runs/online-optimal-step-20261004/accepted-decision.json` | `06b4b2c3912da899ecfd85a656ac23edde67f05a66d444c06c782c635113d939` |
| `runs/online-optimal-step-20261004/pr-delivery.json` | `4abeee76b8aafde3a785570b8d6fdbdc97b896319084b01c4440e1a9fb8efc66` |
| `runs/online-linearization-public-20261007/accepted-decision-v1.json` | `145b6c3685b0700379f71491598f14a77807067b9383da1c52e7fad31b903751` |
| `runs/online-linearization-public-20261007/delivery-obligations-overlay-v1.json` | `e00c220a660d091c857773e1e1dd6bcb76353554f6f37f2d31fb97104fee957b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-optimal-step-public-20261007/snapshots/before-website--content--readings.json.txt` | `415e64e6e0ccaa187e09e9bb2ba7244128a9499629781300074e4a13a450b4a8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-optimal-step-public-20261007/snapshots/before-website--content--highlights.json.txt` | `fea35d2a10e2c4dbcbba0cc5632621d15546116186e6de768a9e8ad3215cc650` |
| `E:/ABRL/worktrees/research-online-book/runs/online-optimal-step-public-20261007/snapshots/before-website--content--chapters.json.txt` | `8fba203f2eed651fea474fdee07934cf316a96a9809e45aa6ce15d4a19676e51` |
| `docs/contracts/online-optimal-step-v1/context.lean.txt` | `42bae9ad7fa258cc893299ab249a995a4d06618f3a137409fa1858add0b8b735` |
| `docs/contracts/online-optimal-step-v1/diameter_argmin-header.txt` | `05b15e1361c072141bc3b694b3f1515e4e9cd26daa6ea9979f44526af9866d79` |
| `docs/contracts/online-optimal-step-v1/diameter_argmin.json` | `3003ee62c18e37c39c5aecbd61d66f320482a9815dcafd3fc3340fed483b0a23` |
| `docs/contracts/online-optimal-step-v1/distance_energy_argmin-header.txt` | `9fbaed2f6d4d1682a856669d8469da7e3a4cc1c3a163c5b106f9070f302f844d` |
| `docs/contracts/online-optimal-step-v1/distance_energy_argmin.json` | `3b242f6272b3a7b00d8dba52ff54e26187e15ae733d3af0bfe60d4bd332a7c07` |
| `docs/contracts/online-optimal-step-v1/gap_identity-header.txt` | `7e063c3baf4ef3da9b3a4109c701834bf0c22ec47f9f2c12cfe1b483fe1cc0a6` |
| `docs/contracts/online-optimal-step-v1/gap_identity.json` | `57707824460261debe5e0e9ddd7c83545be2c3ac4438d64134efda098aa18fc1` |
| `docs/contracts/online-optimal-step-v1/lower_bound-header.txt` | `8b0d5b04af09d60f443a3848dd971ac8b0975edc76050d6b8282657c8f14bde6` |
| `docs/contracts/online-optimal-step-v1/lower_bound.json` | `b2a3082ca3bffe7e3164667c6d0f0b606136730cb0f8b7f8cf449cb73f441a41` |
| `docs/contracts/online-optimal-step-v1/optimal_positive-header.txt` | `2f715e2cb196c764486e435e1c8b15b5b0db86d7d800f62788e0898e3dc0f1e0` |
| `docs/contracts/online-optimal-step-v1/optimal_positive.json` | `08322b319e6f089e3dc12597ed2c55719741ca9edb8e04b30326742c047ef14b` |
| `docs/contracts/online-optimal-step-v1/optimal_unique-header.txt` | `0162aa7f74aeb11647b65f3121e51df865b8eac67a1bf56096f1368e0bb1d19c` |
| `docs/contracts/online-optimal-step-v1/optimal_unique.json` | `f877b52f82ab3699a5c02f4d6ad96cca10d98432b93ec899442268711a85cf49` |
| `docs/contracts/online-optimal-step-v1/optimal_value-header.txt` | `3b65937199f74b3c1cec48ea8ac14d05e0786c539c97481d20fe7d3c164f767b` |
| `docs/contracts/online-optimal-step-v1/optimal_value.json` | `06406a51137fd4e7852ae31c195c086f41078ef2aff4bc52a16f3ebcbcdf78a2` |
| `docs/contracts/online-optimal-step-v1/source_argmin-header.txt` | `0f57d41f5d99245b69dbcb952e35b9c78cef99bac166756294a669c07f8870e7` |
| `docs/contracts/online-optimal-step-v1/source_argmin.json` | `3d1e37b31c0a7e358f93989b857908dc6691541cae9c69de583aa60ef1d673fc` |
| `docs/contracts/online-optimal-step-v1/zero_coefficients-header.txt` | `a6cf5630042ef36ff5bf24aa78e6d33dc86bbe4c7483a97f018be83261e2212b` |
| `docs/contracts/online-optimal-step-v1/zero_coefficients.json` | `a8cf72d1abb27779b0d5e5ed28276c561282740c7bcd68cb3213cae24a4a6f5a` |
| `docs/contracts/online-optimal-step-v1/zero_distance_decreases-header.txt` | `3a8be54243cafb7c4b89e52eaf727de749a63368e2e1cd856f870f3dcde401af` |
| `docs/contracts/online-optimal-step-v1/zero_distance_decreases.json` | `80e9fd197fdafa0894a56f5ca2d4a2057f4b17de3a564e7893d6a05eb78fbbee` |
| `docs/contracts/online-optimal-step-v1/zero_energy_decreases-header.txt` | `13de39ac17349f1729184923f4494f6993a399f33fd41499fab3ec9b501e896f` |
| `docs/contracts/online-optimal-step-v1/zero_energy_decreases.json` | `437d05100cc6828dc0538ea27c94118fade3acbc7b23e7a98de313aa058b560b` |
| `docs/contracts/online-optimal-step-public-v1/actual-context-v1.txt` | `17bc4e2c49d5c6f27933de8fb700b45dd3a79a7b736894d5b5d2abf2f06b9cbf` |
| `docs/contracts/online-optimal-step-public-v1/contract-manifest-v1.json` | `50538d025a1e052aa1a2ad91912667e4f6e79369b6338e19ba2fe8f60aa4a624` |
| `docs/contracts/online-optimal-step-public-v1/contract-v1.md` | `444b18e760db3d1918a404b9bab400ca176f46b866ea8c7e2c66c6fff2a362e7` |
| `docs/contracts/online-optimal-step-public-v1/conversion-window-v1.md` | `31023a368738dea4ae4ec794076b6085498fc67f68e558f2051cb2bfb147c5a7` |
| `docs/contracts/online-optimal-step-public-v1/dependency-DAG-v1.json` | `8058654feeb292fb5278d924498f9c95024209ba1d56254423931ca63b992ca7` |
| `docs/contracts/online-optimal-step-public-v1/headers-v1.json` | `fb14990704d65c21a18b8cd2e7ba728b1943537ba469a9c9157f1f3c82b4aff4` |
| `docs/contracts/online-optimal-step-public-v1/native-statement-fingerprints-v1.json` | `24b691449bf3ff2975b842a8fd51489a52c43858893800e426aa5cab184821c2` |
| `docs/contracts/online-optimal-step-public-v1/raw-statement-fingerprints-v1.json` | `51bb0870d5fd518aea5d1bb12b898b4de95830f444364c3511e30f7a6d0b9037` |
| `docs/contracts/online-optimal-step-public-v1/semantic-signature-v1.json` | `7ef5637708ae931139c7ed7977a5073457d4aeb07e6f207c8f91df7de96acc23` |
| `docs/contracts/online-optimal-step-public-v1/source-card-v1.json` | `6a64c0178d00c53be246754ef03ee3d8d19e4c281faf59606dd994a5b802fe83` |
| `runs/online-optimal-step-public-20261007/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `runs/online-optimal-step-public-20261007/00_context.md` | `6db4336a050e676405257ac2b0fece0580ce384fb093d1a5f20bb8e45e077ab7` |
| `runs/online-optimal-step-public-20261007/10_upper_director-v1.md` | `df503071326558ae42c9baa001c5f019bad3c64ca19335ac09dcaa779edf1223` |
| `runs/online-optimal-step-public-20261007/20_architect-v1.md` | `4481834ce7cfe7240b94f8315d3a99bf190c4f16d9b8029c18aa3bf52aaad8c6` |
| `runs/online-optimal-step-public-20261007/actual-API-retrieval-v1-exit.json` | `23de79fe00d8fa43fcd9b124b8cf851db5950c72e3b6874050e122625245a6c5` |
| `runs/online-optimal-step-public-20261007/actual-API-retrieval-v1.log` | `50ff4ea38199a20062c1c6d157b152aa22e638c6b19e72b8ac15867fa5e98e6a` |
| `runs/online-optimal-step-public-20261007/base-PR184-fresh-v1.json` | `f71927316d5a627950bef5c8c8ca48ddf6c936c825ee0f7d0ba5ec29af83ad89` |
| `runs/online-optimal-step-public-20261007/blind-decoder-receipt-v1.json` | `aa96edf66504604467a1ca9bf2aba175e502e73ae86c0b2331e7d3637181c40d` |
| `runs/online-optimal-step-public-20261007/blind-decoder-v1.md` | `1fceb3c662c78c14a0f4192f3e8bf324a27ab9ffc77771cdc098cdfeec171cc5` |
| `runs/online-optimal-step-public-20261007/blind-packet-v1.md` | `bb45aa23ad9b3db0967c88f47ae25724ff5f5946c63cb2a5252e4728c958d926` |
| `runs/online-optimal-step-public-20261007/canonical-worktree-audit-v1.json` | `134fb21a350a4ae4b8ca05718a55d1332f916dbe6b77c41c65f7b00f3f4cf89c` |
| `runs/online-optimal-step-public-20261007/draft-event-v1-exit.json` | `ba16ad32760ac0f52506335392d791b571118682b4df384546c19c46df986722` |
| `runs/online-optimal-step-public-20261007/draft-event-v1.log` | `16e6d62a3fac94064fdce0c0d65b6972afaddbca65338af31ea3f0a228f5f533` |
| `runs/online-optimal-step-public-20261007/draft-freeze-v1.json` | `89b0104dae89472e90334702f1e009722092309c9408b6a715cf4c1e39ccced0` |
| `runs/online-optimal-step-public-20261007/fresh-fetch-v1-exit.json` | `3f34ba3376a788f283eeec1f13313ea5c02762b57e63f5e9cdfa5c55af5d8b99` |
| `runs/online-optimal-step-public-20261007/fresh-fetch-v1.log` | `c1e463496485131dcb282a1e770e1d48621af51e662c497f94c9a128c85415fb` |
| `runs/online-optimal-step-public-20261007/full-type-identities-v1-exit.json` | `630253259aa953f8dc44694d4554d6ce389b3f68342f1fbc758a9603ab4a086b` |
| `runs/online-optimal-step-public-20261007/full-type-identities-v1.log` | `238f2cd04205fdeabf7c56be0a5d32a0da0849a089c0771fd3f7a2729cd1ba93` |
| `runs/online-optimal-step-public-20261007/help-frontier-refresh-v1-exit.json` | `6cd7cd30e2ad0223b0bba3d694ecf98844ef82d9f3f15cf80524aed0ae0fcedc` |
| `runs/online-optimal-step-public-20261007/help-frontier-refresh-v1.log` | `bff73ff554907d7c5dd50b99f2491f5675e93afb29829e402ec383fb52fe3cdc` |
| `runs/online-optimal-step-public-20261007/help-frontier-shadow-v1-exit.json` | `b7da17ec97092a46bb7b5410ac7eebec8fb85fedfaeff6f06db0386421a6a154` |
| `runs/online-optimal-step-public-20261007/help-frontier-shadow-v1.log` | `ad548f6e24b3214fbf5796c632caa24debbaa21c6622f7dab8abe268f521de7d` |
| `runs/online-optimal-step-public-20261007/help-lifecycle-event-v1-exit.json` | `e94861bb4ca09264032f9278da234c2213c1f8a83f1909e90f2b06d5b6117c9c` |
| `runs/online-optimal-step-public-20261007/help-lifecycle-event-v1.log` | `b1e8b438a9b725793b9888d206e98a971ace3df200ec90ed9cb63eab26b28507` |
| `runs/online-optimal-step-public-20261007/help-memory-record-v1-exit.json` | `fc0b3a86e4bf7876c9977d9c2527ed01d6f7befb7955e3d8d44d8dfbd0b5742f` |
| `runs/online-optimal-step-public-20261007/help-memory-record-v1.log` | `89e8a7b2bb8d4fd593f0705289ca3c4c63015e48d0e8c9cbe5b71cf2c7cc44f4` |
| `runs/online-optimal-step-public-20261007/help-new-task-v1-exit.json` | `6b7b9b907f49e3f6881e073b4a4baa583c25702c3a2928cdd31d1fd742fd16f5` |
| `runs/online-optimal-step-public-20261007/help-new-task-v1.log` | `25eb9342c3094bee57187630bd149d2c522fc9f7ac7e65bebe5c198eba60ed99` |
| `runs/online-optimal-step-public-20261007/help-retrieval-record-v1-exit.json` | `5b670f9d8d64c39d8c91a5db77c767ae1b06774c5e0d42cb23b9952b5ff0739d` |
| `runs/online-optimal-step-public-20261007/help-retrieval-record-v1.log` | `73ac93f120215511ff0370d7ce100a9d0e83598ad882bcc5773cd1dc889b5321` |
| `runs/online-optimal-step-public-20261007/help-root-v1-exit.json` | `d2fd7f281a2ac718f6b6f85bae4ef697b3b1ed718e55d94f4a816c409db5f9e7` |
| `runs/online-optimal-step-public-20261007/help-root-v1.log` | `daacf23e36eec4898dce3b3de02a07b71fb0f80f08e33e8dfe00722e7572970c` |
| `runs/online-optimal-step-public-20261007/help-safe-verify-v1-exit.json` | `8d51c4ce9f9c165cd88e99d645a816d7dfcd9892e3d7c4f0275af4aea67ca1c9` |
| `runs/online-optimal-step-public-20261007/help-safe-verify-v1.log` | `1773541c625f225e5a9abc61985c3ad19e871cf31aa0cf89cc440b3d8398862c` |
| `runs/online-optimal-step-public-20261007/help-statement-fence-v1-exit.json` | `001fe6143e97ff3a9bd4500bd25fa62ec313545d4d4156da4b8e0c72354287ae` |
| `runs/online-optimal-step-public-20261007/help-statement-fence-v1.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |
| `runs/online-optimal-step-public-20261007/help-trial-log-v1-exit.json` | `20c5ce1adaabe29bf9d83e19bea20c373dfde735746634a2419a5ddb1b10b5d6` |
| `runs/online-optimal-step-public-20261007/help-trial-log-v1.log` | `ea7bd7e4d64216b46f554a90e02a3d58b4fcbe72766c2f7b316b656b94d19b32` |
| `runs/online-optimal-step-public-20261007/historical-PR151-fresh-v1.json` | `d323f32cf983361f9898a218f5a83575bb5624adc9759da3b0ab32993a2c900e` |
| `runs/online-optimal-step-public-20261007/leaves/full-type-identities-v1.lean` | `6bfca0fc0dfb7acc13265b0aed27bb554814657bff28b3a07223d416f82091e7` |
| `runs/online-optimal-step-public-20261007/leaves/neutral-closed-props-v1.lean` | `10f38f675eb940f49c21b418bde55fe7455c553fd0ccdfea1a50f6233854881a` |
| `runs/online-optimal-step-public-20261007/memory-digest-draft-v1.md` | `1bca081a5023dca133188366275b351b83f561af2723499d8974a97d51d3e243` |
| `runs/online-optimal-step-public-20261007/neutral-closed-props-v1-exit.json` | `9747e07481ef9db1413f3bdee55ed1ab17f40b966cf14914cfeb268228ab9e56` |
| `runs/online-optimal-step-public-20261007/neutral-closed-props-v1.log` | `930edbd7854d02533419f8b9f1aac2697c23e632efd2d50681cc3a21df82b0a7` |
| `runs/online-optimal-step-public-20261007/neutral-map-v1.json` | `065799cb8b2e8dcce3032304da76418525bef54f6aeb5a00946a33c7aafe59d0` |
| `runs/online-optimal-step-public-20261007/neutral-type-bindings-v1.json` | `5571b6ef1f8ef09106a306aacfdd413e66040fbfd1c0bad4d222899f81e9046e` |
| `runs/online-optimal-step-public-20261007/new-task-v1-exit.json` | `12f67b45dfab6aef4505cfa708235a5c1b05ffafd9e46f43218fcfa9bd899b65` |
| `runs/online-optimal-step-public-20261007/new-task-v1.log` | `0c2c69a3d83f56a47e9033b0b90f51d0fa07e44b859a630b106a6cebeb26f965` |
| `runs/online-optimal-step-public-20261007/paper-boundary-v1.json` | `dae89e7ae9e0499b4d371a595aea19637b9e6430ce98331ca4ae4388b5747155` |
| `runs/online-optimal-step-public-20261007/proof-obligations-draft-v1.json` | `1be0735cca555f7194f5d29610474e8ac8d5ed9682b7830b03c724586f476820` |
| `runs/online-optimal-step-public-20261007/source-pdf26-v1.txt` | `aac2d6da936e483c239e6bc4db9079e411ed9372f803a19e2cde6982ce77a522` |
| `runs/online-optimal-step-public-20261007/source-pdf27-v1.png` | `075802794b7c8ba4fc21d52962c3f9054b9f44e4ffc22ef083c95f88b2bed902` |
| `runs/online-optimal-step-public-20261007/source-pdf27-v1.txt` | `aed61245f25b365224da1ea1ca3a2d3f8439365707e6cca6e1f08b05087eaf42` |
| `runs/online-optimal-step-public-20261007/source-pdf28-v1.txt` | `a9d4910e2c687a25babd24d5b4c30f4e6c4d1fdc4018c29ad239c327bacfd87c` |
| `runs/online-optimal-step-public-20261007/source-pixel-inspection-v1.json` | `00df873c7f38fccab50c2bdf5c8740542740f1ac5ea94e6a323a86e4db822abe` |
| `runs/online-optimal-step-public-20261007/source-render-v1.json` | `88b40abf406d7e364f74760e6e676657ac52a728767f3e6ef9d110422b100d89` |
| `tasks/ONLINE-OPTIMAL-STEP-PUBLIC-20261007.md` | `9d2b05650a21b73e902f135be8a9a14abe3b3a357133525fd7f0677b7c21bbe5` |
| `conversion-windows/ONLINE-OPTIMAL-STEP-PUBLIC-20261007.md` | `9d2b05650a21b73e902f135be8a9a14abe3b3a357133525fd7f0677b7c21bbe5` |
| `proof-obligations/ONLINE-OPTIMAL-STEP-PUBLIC-20261007.md` | `9d2b05650a21b73e902f135be8a9a14abe3b3a357133525fd7f0677b7c21bbe5` |
| `runs/online-optimal-step-public-20261007/30_lower_worker-v1.md` | `6d2b72a22c5f5a62e69ef0c8fb7c06f40191308c18267474afb5adafab51c10f` |
| `runs/online-optimal-step-public-20261007/all-axioms-v1-exit.json` | `345015ab9b91dd4a631a1257c23afe6f96001089407ef5a94b799d1afdd06126` |
| `runs/online-optimal-step-public-20261007/all-axioms-v1.log` | `b606998a0aceeaf1150b24ebc95873af29daa269efd9cc7a489e29f32857d604` |
| `runs/online-optimal-step-public-20261007/all-public-types-v1-exit.json` | `ca304ae1c6a4509982a64451c68b2b87fb423e826afbc5aeab2a103975ba6659` |
| `runs/online-optimal-step-public-20261007/all-public-types-v1.log` | `9b598cf519c30797590da834d0f7c6d975d019ab255d0cccdca97fff620b4dd2` |
| `runs/online-optimal-step-public-20261007/body-bindings-v1.json` | `c252e3a7ddc6e39f6b2a295ef26c321efc9c15ec26a1aba5c987aa40fe6f5777` |
| `runs/online-optimal-step-public-20261007/candidate-event-v1-exit.json` | `e3ddfc9f259b7065c00c7849c3c979f193162d493a3484f30302e3bba22cd382` |
| `runs/online-optimal-step-public-20261007/candidate-event-v1.log` | `54232d3b918ca3ddb9872427985c67a80ed995c613f5efd0bb9586494f91e79b` |
| `runs/online-optimal-step-public-20261007/compiled-value-graph-v1-exit.json` | `936d54f64ebfe601b6e8b71054c96b93e5be4e977320142f43808db33ad7fe9d` |
| `runs/online-optimal-step-public-20261007/compiled-value-graph-v1.json` | `e3dd61b2340f38b2d088af5c6e1c708ef16dfad9d49a438e193aa7e9b60950a4` |
| `runs/online-optimal-step-public-20261007/compiled-value-graph-v1.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-optimal-step-public-20261007/compiled-worker-trial-v1-exit.json` | `3ffa4fb84048cc44d897028c4156cc11b495a91e2af2c4417dfe73c08e7559ad` |
| `runs/online-optimal-step-public-20261007/compiled-worker-trial-v1.log` | `36cd9d18ba0e58d87517d28cf78044aafe11c6e3010f039015f07e41a38ae448` |
| `runs/online-optimal-step-public-20261007/leaves/all-axioms-v1.lean` | `ef76ec011a32a4d1308f7e2372a18a109af430bbd5016be97f61084bcd9ba787` |
| `runs/online-optimal-step-public-20261007/leaves/all-public-types-v1.lean` | `b2bb8b5d401e8b202ba53cb7d346ac472e9793ebd879e0b0ac2b38a2fac6b463` |
| `runs/online-optimal-step-public-20261007/leaves/export-actual-dependencies-v1.lean` | `d628bb0d3ba9fef3ca30054f6cfb102252807f12720f8add175e9ac6cc8efeb7` |
| `runs/online-optimal-step-public-20261007/native-public-fences/diameter_argmin-full-v1.json` | `f9589219ef7f67f3d189971c5ad898897a85ae246e1cb1ac128550e3e030d235` |
| `runs/online-optimal-step-public-20261007/native-public-fences/distance_energy_argmin-full-v1.json` | `3095e3dd19392cad0d9b730d0e8e250ec38262ebfbefec6205389c626b8a682d` |
| `runs/online-optimal-step-public-20261007/native-public-fences/gap_identity-full-v1.json` | `b8e3b51fa73bfd9071a9e144fddbb0b58ee5b13e397f9ac97a8436a40b8ee5f8` |
| `runs/online-optimal-step-public-20261007/native-public-fences/lower_bound-full-v1.json` | `5ae031a791da536de4f9074cb675336642f5dc2753b33988097501f98ac75699` |
| `runs/online-optimal-step-public-20261007/native-public-fences/optimal_positive-full-v1.json` | `e8734714cb19e4893afb16b48100f065af0dc8b9f7463ad7c347e7c06ce016b5` |
| `runs/online-optimal-step-public-20261007/native-public-fences/optimal_unique-full-v1.json` | `ea4473ef0980fd5e3e596961d359ba556796912bebc2f5252f7e82c2374fad9e` |
| `runs/online-optimal-step-public-20261007/native-public-fences/optimal_value-full-v1.json` | `6aa7d6c171b977d2411d3c095c927361f58bcaaa5dd57003063b1270e7ef478a` |
| `runs/online-optimal-step-public-20261007/native-public-fences/source_argmin-full-v1.json` | `a8a34df29bea956bf734e33f4590bcba7c5be0fec802eb7b91a5b6301107875a` |
| `runs/online-optimal-step-public-20261007/native-public-fences/zero_coefficients-full-v1.json` | `123310a047283ad967d7749a04394c0b74aba1cd7ad87fe34c54a5e9799b79d4` |
| `runs/online-optimal-step-public-20261007/native-public-fences/zero_distance_decreases-full-v1.json` | `9836496630f0e6153431783dd1f36c7b22b65b0bbce66299e08a6d71d125275b` |
| `runs/online-optimal-step-public-20261007/native-public-fences/zero_energy_decreases-full-v1.json` | `698d2e936fb44f103b457b5fef67d30cf9745c7432b57dee6c443e71afb167ce` |
| `runs/online-optimal-step-public-20261007/proof-obligations-candidate-v1.json` | `bc338aaacaad5814400bd3c80c79f41a159c4d7a7c1ff0f96a2d1c73deb771da` |
| `runs/online-optimal-step-public-20261007/proving-event-v1-exit.json` | `578e75cfa0d33b92ad241d4613b12969f1e2165e22078c6d2bf61bdf90748410` |
| `runs/online-optimal-step-public-20261007/proving-event-v1.log` | `27a207be2c9fb4cc49ed476d4c39524ae5a99029642c2d112a3549877319ac22` |
| `runs/online-optimal-step-public-20261007/public-canary-focused-v1-exit.json` | `2ec9a6aada676234cfc87d36403c51a62d4a380bfe0620fc267357645f3894e0` |
| `runs/online-optimal-step-public-20261007/public-canary-focused-v1.log` | `3c97c3f2b824d2ef9a56b1a7d1840ce27c649d55348b6bd41ab2d097e103c518` |
| `runs/online-optimal-step-public-20261007/public-fence-diameter_argmin-v1-exit.json` | `f3e1a869131679f73af904709f81e832ceab87c2cf6297c5d0d453a5fea48d26` |
| `runs/online-optimal-step-public-20261007/public-fence-diameter_argmin-v1.log` | `f9589219ef7f67f3d189971c5ad898897a85ae246e1cb1ac128550e3e030d235` |
| `runs/online-optimal-step-public-20261007/public-fence-distance_energy_argmin-v1-exit.json` | `33956167174c42556903f4ee74bf7f9bc02af336a209b347206a9e59b6505361` |
| `runs/online-optimal-step-public-20261007/public-fence-distance_energy_argmin-v1.log` | `3095e3dd19392cad0d9b730d0e8e250ec38262ebfbefec6205389c626b8a682d` |
| `runs/online-optimal-step-public-20261007/public-fence-gap_identity-v1-exit.json` | `4096543517bde6e82c3b2cc24d98a7575d30b9d99666f59e45fe27642fc44a80` |
| `runs/online-optimal-step-public-20261007/public-fence-gap_identity-v1.log` | `b8e3b51fa73bfd9071a9e144fddbb0b58ee5b13e397f9ac97a8436a40b8ee5f8` |
| `runs/online-optimal-step-public-20261007/public-fence-lower_bound-v1-exit.json` | `3ae2f4e66b759f7dbad361dc2bc351ca323e750853d83e8498a1a8ab243e26b6` |
| `runs/online-optimal-step-public-20261007/public-fence-lower_bound-v1.log` | `5ae031a791da536de4f9074cb675336642f5dc2753b33988097501f98ac75699` |
| `runs/online-optimal-step-public-20261007/public-fence-optimal_positive-v1-exit.json` | `42a55aafa7afdd7045c670783099dfdd42ee01c2b4d350638bdd3b68cf158202` |
| `runs/online-optimal-step-public-20261007/public-fence-optimal_positive-v1.log` | `e8734714cb19e4893afb16b48100f065af0dc8b9f7463ad7c347e7c06ce016b5` |
| `runs/online-optimal-step-public-20261007/public-fence-optimal_unique-v1-exit.json` | `06dc07e3db5057d4df3f830eca096b052b3c41449caa6ddd996eb51beb38bf68` |
| `runs/online-optimal-step-public-20261007/public-fence-optimal_unique-v1.log` | `ea4473ef0980fd5e3e596961d359ba556796912bebc2f5252f7e82c2374fad9e` |
| `runs/online-optimal-step-public-20261007/public-fence-optimal_value-v1-exit.json` | `1bc71884179da91e3d53fc33f1fe6e111497e4435460ab21699a7c3501356d65` |
| `runs/online-optimal-step-public-20261007/public-fence-optimal_value-v1.log` | `6aa7d6c171b977d2411d3c095c927361f58bcaaa5dd57003063b1270e7ef478a` |
| `runs/online-optimal-step-public-20261007/public-fence-source_argmin-v1-exit.json` | `d9892f30158330729b988d38ce9f6bd789ae7bac0e5ce6038cd61b3a2a8abee2` |
| `runs/online-optimal-step-public-20261007/public-fence-source_argmin-v1.log` | `a8a34df29bea956bf734e33f4590bcba7c5be0fec802eb7b91a5b6301107875a` |
| `runs/online-optimal-step-public-20261007/public-fence-zero_coefficients-v1-exit.json` | `6853c9089d78a004cbcd67d915c47df558014a40e80fa4e8915503c85865f29a` |
| `runs/online-optimal-step-public-20261007/public-fence-zero_coefficients-v1.log` | `123310a047283ad967d7749a04394c0b74aba1cd7ad87fe34c54a5e9799b79d4` |
| `runs/online-optimal-step-public-20261007/public-fence-zero_distance_decreases-v1-exit.json` | `bf31df6f9841919312b3f1eb4c33806c4b998019c11947649a53eab46e487e27` |
| `runs/online-optimal-step-public-20261007/public-fence-zero_distance_decreases-v1.log` | `9836496630f0e6153431783dd1f36c7b22b65b0bbce66299e08a6d71d125275b` |
| `runs/online-optimal-step-public-20261007/public-fence-zero_energy_decreases-v1-exit.json` | `a5d0e4431a30c6cd42af7a9efdcc5b1dc644db8f9776f12075d174133c140ed9` |
| `runs/online-optimal-step-public-20261007/public-fence-zero_energy_decreases-v1.log` | `698d2e936fb44f103b457b5fef67d30cf9745c7432b57dee6c443e71afb167ce` |
| `runs/online-optimal-step-public-20261007/public-named-declarations-v1.json` | `1ead6661856e600ad1366d9d7ac69c1017a6eee55f4969ea9cc3011de22ebb55` |
| `runs/online-optimal-step-public-20261007/public-safe-diameter_argmin-v1-exit.json` | `67b2ebe9eadcf6bdc349fbe20892bd1a9d8f79ca514e090b6b07ce4b6b7dd4c9` |
| `runs/online-optimal-step-public-20261007/public-safe-diameter_argmin-v1.log` | `c74d9bc8b8d1c573e07fe13148b7f7a74122d8a82364b0dee93dd99297eb4e45` |
| `runs/online-optimal-step-public-20261007/public-safe-distance_energy_argmin-v1-exit.json` | `bac132908bcbbf1ea4a64101f26a3bcefff2ce0d320aea6cf65f30f83acf70d9` |
| `runs/online-optimal-step-public-20261007/public-safe-distance_energy_argmin-v1.log` | `33ccc36bd63a808590c27af521777a2dcfd71ed14e05817f33ded28eeab63321` |
| `runs/online-optimal-step-public-20261007/public-safe-gap_identity-v1-exit.json` | `1d5200df6470e58b37c6862ddad7f9e510b3c4841388808865a7ce20381a9ab2` |
| `runs/online-optimal-step-public-20261007/public-safe-gap_identity-v1.log` | `58dd3cbb8557ab1483e0a0fc050a59e3af6638f5d835081d8851ba7774b83922` |
| `runs/online-optimal-step-public-20261007/public-safe-lower_bound-v1-exit.json` | `b940115e2c793ce8957b4f87ea077d3e4d1db5b9207dc459ee4098d252291314` |
| `runs/online-optimal-step-public-20261007/public-safe-lower_bound-v1.log` | `8d17ca311ad42bfbe3bfcdf83369fbe68664e62957e4644d2b207552cd5f8cc8` |
| `runs/online-optimal-step-public-20261007/public-safe-optimal_positive-v1-exit.json` | `7533f99f384e40ebbde8fee76624280448fd4ebb305c3c9971e2294c5261e2ea` |
| `runs/online-optimal-step-public-20261007/public-safe-optimal_positive-v1.log` | `31788d23998a957395a730c957e182369edaffcec4cb36aa653d0caca2bbc02d` |
| `runs/online-optimal-step-public-20261007/public-safe-optimal_unique-v1-exit.json` | `386a8db9cbdcbdb371248ad4291d47f7032053d2f22fbdbc9533015a184ee106` |
| `runs/online-optimal-step-public-20261007/public-safe-optimal_unique-v1.log` | `ae9bc429a9a8ea4584a6048be8a813200c9edc5d88613542ebd90b9a7067e12d` |
| `runs/online-optimal-step-public-20261007/public-safe-optimal_value-v1-exit.json` | `420e6158fa2bc456dd408aaa1ea85f295b3a3923f3fc9c7a44ae83fe9c5d38a5` |
| `runs/online-optimal-step-public-20261007/public-safe-optimal_value-v1.log` | `c4d940e90b25c104239c317429778385015ea3b1fbddf0aae308ad14082e8d0a` |
| `runs/online-optimal-step-public-20261007/public-safe-source_argmin-v1-exit.json` | `0f5e71fd355b628d0e25328286313fc20a20bcd334f3504ca0e92f0561741e48` |
| `runs/online-optimal-step-public-20261007/public-safe-source_argmin-v1.log` | `2bef838b1005d2cec11fa0492a7e1748c317c96d6ce5999250c29eb89b2f5697` |
| `runs/online-optimal-step-public-20261007/public-safe-zero_coefficients-v1-exit.json` | `e8dbe05516c4a3ceaa73f30d3d326f10b653db644a4a13fa7a7c9cc55b065e56` |
| `runs/online-optimal-step-public-20261007/public-safe-zero_coefficients-v1.log` | `a90905e145ef0b9200785f34e9539c3719235c59e9cf61091e4aa1a52ec26b4e` |
| `runs/online-optimal-step-public-20261007/public-safe-zero_distance_decreases-v1-exit.json` | `cfaf5e56490a86a2cf886aa8e29474a1e5a0dc6a88bbb5847b1283dcd87d6c10` |
| `runs/online-optimal-step-public-20261007/public-safe-zero_distance_decreases-v1.log` | `174aa7686cf6b846781beebf8589000278d7431ac8592a93802e051545a7b580` |
| `runs/online-optimal-step-public-20261007/public-safe-zero_energy_decreases-v1-exit.json` | `15a7ab06223909f1a461b63f55791c58145b50f17e08fb5e22bab23d25dd95f1` |
| `runs/online-optimal-step-public-20261007/public-safe-zero_energy_decreases-v1.log` | `7f568f2a8a1f54618107b66d6302a2279b367aac8666389fab97d999e0ad5ae0` |
| `runs/online-optimal-step-public-20261007/source-contract-inputs-v1.json` | `d3e8568d0499c1608e261e232048b612d107409505e3ace7cc7dd1dd52521c81` |
| `runs/online-optimal-step-public-20261007/source-contract-packet-v1.md` | `747b077e5b2375f62a99a03d3ce96eca9ab5d804763e35d3a34dd91c7d897b01` |
| `runs/online-optimal-step-public-20261007/source-contract-receipt-v1.json` | `47e42702a87279e5f2dfd85df21408c739379ad7f5662835a337adec3f212291` |
| `runs/online-optimal-step-public-20261007/source-contract-review-v1.md` | `6221a9a868babc49794b09a0de4248a888d2363c57f953de46494a03fd855581` |
| `runs/online-optimal-step-public-20261007/stabilized-decision-v1.json` | `74754b8b28f1abc6214647b3cd02408aa8f14e60b6580f7ab36d1b58f241b6ab` |
| `runs/online-optimal-step-public-20261007/stabilized-event-v1-exit.json` | `96e7c5f9374d6be49f4fb4e2b583f84ca02c7cbd7cce3bb4aef7a9acd702a7c5` |
| `runs/online-optimal-step-public-20261007/stabilized-event-v1.log` | `62208e14efa9b373116e0ac2dedc207521607a1867d1849026de29512127998a` |
| `runs/online-optimal-step-public-20261007/value-pairs-before-first-export-v1.json` | `a2a6ed8346589779c7ec48fc91d58017fd40db8d6790592af2cd9232cb53a73d` |
| `research-wiki/retrieval-index/online-optimal-step-public-20261007.md` | `e6cb716be7fae0a05dea74c92682aaaf44163efecf971d2f95b5453fc8fe8a98` |
| `runs/online-optimal-step-public-20261007/body-review-inputs-v1.json` | `e6d216b621031dcf1a1660c7b05d5af08f5a1d716925aceba089b1758e54067d` |
| `runs/online-optimal-step-public-20261007/body-review-packet-v1.md` | `9a95ce6d3fb202d26342e356aab2489674152bdc57ffbcfd67011b1c06bac243` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
