# Guessing logarithmic lower bound: CONTRACT review

**Verdict: accepted-with-explicit-delta, stabilization only.** No blocking mathematical or metadata defect found in the16 targets. No target proof/body, source package or chapter is accepted.

Actor /root/source_reviewer has prior staged source-review history, including earlier Chapter1 packages. Requested GPT-6 Astra / medium, runtime unverified; distinct automated role from formalizer and neutral decoder, not blind/human/external attestation.

All153 applicable v2 fixed raw rows independently match before/after. Frozen v10 PDF SHA is cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Actual printed4/PDF16 PNG was viewed; source printed2–3 comparator/mean/causal context checked. The source says logarithmic dependence is unavoidable and explicitly does not prove minimax optimality here. These quantitative constants and the constructive Polya-law route are proposed derived support, not a transcription of a printed quantitative theorem.

## Anti-anchored source and mathematical assessment

The proposed law is policy/seed independent by its definition, not by an assumed conditional independence lemma. A policy takes only newest-first strict past, which can encode time through history length and all exogenous randomness in its seed. For the terminal, v is chosen after fixing mu,A,T but outside the seed integral. That is a fixed oblivious witness for expected regret, not a per-seed/adaptive adversary witness; no separate joint-law independence premise is silently imported. Pointwise bounded measurable seed sections are an explicit admissible randomized-strategy model. No universal measurable-kernel representation theorem is claimed.

The intermediate arbitrary-real deterministic strategy is stronger than the source action constraint; finite histories make its fixed-horizon values finite. The randomized source terminal retains [0,1] to obtain actual seed integrability. Binary labels suffice as legal witnesses inside the original [0,1] adversary class. pathRegret uses the actual shared loss difference and actual same-sequence mean, so the planned feasibility/minimization bridge is essential to interpreting it as best-fixed regret. No generic minimum-existence result follows.

The formulas are internally consistent: at T1 expected minimal learner loss is1/4 and H2/6=1/4. With the proposed moments, expected best comparator loss is (T-1)/6 for positive T. Summing (t+3)/(6(t+2)) over t<T and subtracting that value yields H(T+1)/6. This calculation is a semantic plausibility check, not a Lean proof or acceptance of future recurrence/integral steps. The logarithm bound needs the actual log_add_one_le_harmonic at n=T+1 with exact coercions. T0 must remain excluded from both lower terminals.

## Eight complete definitions

polyaNext has positive denominator length+2 and pseudocount1. pathWeight recursively multiplies the last revealed bit probability on the older tail; branch ordering is newest-first. binaryStream reverses to chronological order and pads false beyond length; binaryValues maps to0/1. causalPredict reverses exactly the t strict-past labels and supplies no current label. pathRegret uses shared comparatorRegret and empiricalMean for this same decoded sequence. pathExpectation is a finite weighted sum, not automatically a probability expectation. prefixMeasure reuses the shared finiteActionMeasure; ofReal clipping cannot replace proof of nonnegativity/normalization. Measurable singleton assumptions appear only where finite measure APIs require them.

Shared empiricalMean_mem/minimizes and finiteActionDistribution/measure/integral definitions and APIs were checked. The latter require a produced distribution, while the seed finite-sum interchange requires actual integrability. The DAG correctly leaves these producers and the actual same-run loss bridge open. It may grow auxiliary leaves without weakening terminal headers. probability_mem alone would not establish unavoidability.

## Per-target seven slots

### N01 probability_mem — accepted-with-explicit-delta
- **objects:** Boolean finite history and smoothed count
- **quantifiers:** all h
- **hypotheses:** none
- **conclusion:** 0<q(h)<1
- **constants_and_indices:** (count_true+1)/(length+2)
- **information_and_probability:** depends only on past
- **boundaries:** empty history q=1/2; strictness even alltrue/allfalse

### N02 branch_mass — accepted-with-explicit-delta
- **objects:** recursive weights at two children
- **quantifiers:** all h
- **hypotheses:** none
- **conclusion:** w(false::h)+w(true::h)=w(h)
- **constants_and_indices:** newest bit prepended
- **information_and_probability:** same parent before current label
- **boundaries:** branch identity alone is not nonnegativity or normalization

### N03 pathWeight_nonneg — accepted-with-explicit-delta
- **objects:** actual recursive list weights
- **quantifiers:** all h
- **hypotheses:** none
- **conclusion:** w(h)>=0
- **constants_and_indices:** w([])=1
- **information_and_probability:** no policy or seed arguments
- **boundaries:** nonnegative not strict lower numerical bound

### N04 prefix_mass_one — accepted-with-explicit-delta
- **objects:** all Boolean vectors length T
- **quantifiers:** all natural T
- **hypotheses:** none
- **conclusion:** sum weights=1
- **constants_and_indices:** fixed-length sum
- **information_and_probability:** actual law to be produced
- **boundaries:** T0 singleton empty vector

### N05 prefix_distribution — accepted-with-explicit-delta
- **objects:** shared FiniteActionDistribution on univ vectors
- **quantifiers:** all T
- **hypotheses:** none
- **conclusion:** nonnegative normalized actual weights
- **constants_and_indices:** unit mass exactly
- **information_and_probability:** reuse shared predicate; not assumed
- **boundaries:** T0 included; no measurable structure needed

### N06 prefixMeasure_probability — accepted-with-explicit-delta
- **objects:** shared finite Dirac measure
- **quantifiers:** all T and measurable structures
- **hypotheses:** MeasurableSpace and MeasurableSingletonClass on vector type
- **conclusion:** IsProbabilityMeasure(prefixMeasure T)
- **constants_and_indices:** actual ofReal weights
- **information_and_probability:** must use produced distribution
- **boundaries:** not probability from definition/name alone; T0 valid

### N07 pathExpectation_integral — accepted-with-explicit-delta
- **objects:** finite atomic measure and real f on lists
- **quantifiers:** all T,f and structures
- **hypotheses:** measurable space/singletons on finite vectors
- **conclusion:** integral equals actual weighted sum
- **constants_and_indices:** only length-T values used
- **information_and_probability:** finite-domain integrability available from actual shared API
- **boundaries:** no infinite-domain integrability claim; T0=f([])

### N08 expected_heads — accepted-with-explicit-delta
- **objects:** true-count moment under actual weights
- **quantifiers:** all T
- **hypotheses:** none
- **conclusion:** E K=T/2
- **constants_and_indices:** first raw count moment
- **information_and_probability:** not IID fair-coin assertion
- **boundaries:** T0=0; moments must be proved

### N09 expected_heads_sq — accepted-with-explicit-delta
- **objects:** squared true-count moment
- **quantifiers:** all T
- **hypotheses:** none
- **conclusion:** E K^2=T(2T+1)/6
- **constants_and_indices:** square inside expectation
- **information_and_probability:** correlated process; not binomial replacement
- **boundaries:** T0=0,T1=1/2

### N10 expected_next_variance — accepted-with-explicit-delta
- **objects:** next-bit conditional variance averaged over past
- **quantifiers:** all T
- **hypotheses:** none
- **conclusion:** E q(1-q)=(T+3)/(6(T+2))
- **constants_and_indices:** strictly positive denominator
- **information_and_probability:** same q from actual counts
- **boundaries:** T0=1/4; no moment premise

### N11 causalPredict_prefix — accepted-with-explicit-delta
- **objects:** same A and two Boolean streams
- **quantifiers:** all A,y,z,t
- **hypotheses:** equal all i<t labels
- **conclusion:** actual causalPredict outputs equal
- **constants_and_indices:** reverse strict prefix, source1=Lean0
- **information_and_probability:** no current/future target argument
- **boundaries:** t0 empty; no computability/externally-selected-A independence claim

### N12 binary_mean_minimizer — accepted-with-explicit-delta
- **objects:** binary chronological labels and shared empiricalMean
- **quantifiers:** all nonempty h and all u in [0,1]
- **hypotheses:** length h>0
- **conclusion:** mean feasible and cumulative square-loss minimal
- **constants_and_indices:** same full-sequence fixed comparator
- **information_and_probability:** hindsight not supplied to policy
- **boundaries:** derive using binary feasibility/shared minimization; not arbitrary-loss argmin existence

### N13 conditional_square_lower — accepted-with-explicit-delta
- **objects:** real x and Boolean history
- **quantifiers:** all h,x
- **hypotheses:** none
- **conclusion:** q(1-q)<= (1-q)x^2+q(x-1)^2
- **constants_and_indices:** difference=(x-q)^2
- **information_and_probability:** numerical conditional loss, no desired certificate
- **boundaries:** unbounded real x allowed; no sequence result alone

### N14 expected_pathRegret_lower — accepted-with-explicit-delta
- **objects:** same deterministic causal A and pathRegret
- **quantifiers:** all A and positive T
- **hypotheses:** T>0 only
- **conclusion:** H(T+1)/6 <= actual finite expected regret
- **constants_and_indices:** cumulative, no half loss factor
- **information_and_probability:** law independent of A; exact same decoded path
- **boundaries:** A need not interval-bound; T0 excluded; average not every sequence

### N15 randomized_harmonic_lower — accepted-with-explicit-delta
- **objects:** probability seed and real bounded history policy
- **quantifiers:** forall seed law,A; forall T>0; exists one vector then integral
- **hypotheses:** probability mu; measurable for every h; pointwise allomega/allh outputs in [0,1]; T>0
- **conclusion:** H(T+1)/6 <= seed expected regret on fixed vector
- **constants_and_indices:** derived coefficient1/6
- **information_and_probability:** fixed v outside integral; no seed-dependent adversary
- **boundaries:** integrability must be produced; no AS/HP/uniformomega or one infinite witness

### N16 randomized_log_lower — accepted-with-explicit-delta
- **objects:** same seeded class and actual source regret
- **quantifiers:** forall mu,A; forall positive T; exists fixed binary vector
- **hypotheses:** same measurable pointwise interval-bounded policy/probability assumptions
- **conclusion:** log(T+2)/6 <= seed expected regret
- **constants_and_indices:** natural log; harmonic index shift exact
- **information_and_probability:** same policy/sequence endpoint; fixed before seed averaging
- **boundaries:** not sharp/printed constant, not average regret; no allhorizon singlepath

## Stable mandatory future reader requirements

R1: Attribute the qualitative logarithmic-unavoidability sentence to printed4/PDF16, explicitly note that no minimax-optimality proof is printed there, and label H(T+1)/6 and log(T+2)/6 as derived support constants, not printed or sharp constants.

R2: Show the actual newest-first recursive path law q=(heads+1)/(length+2), w(empty)=1 and branch multiplication; it depends on neither policy nor seed. Normalization/nonnegativity and the shared finite-action probability/integral construction must be produced, not assumed.

R3: Explain strict-past causalPredict reversal and current-label-after-output order, source1/Lean0 indexing, and the SAME pathRegret/shared comparatorRegret and empirical-mean comparator. Prove actual binary mean feasibility/minimality rather than assuming an argmin or using a different trajectory.

R4: Display the complete randomized quantifier order: every probability seed law and per-history measurable, pointwise all-seed/all-history [0,1]-valued policy; every positive T; exists ONE fixed binary sequence outside the seed integral. Explain integrability production, not Bochner fallback; no seed-dependent witness, almost-sure/high-probability/uniform-seed or one-infinite-sequence guarantee.

R5: Expose the actual count moments, variance, cumulative causal-loss bridge, expected optimum and finite normalized-average bad-sequence producer; no desired-regret/moment/normalization/minimum certificate may stand in as a terminal premise. Distinguish proof dependencies from a teaching plan.

R6: Retain all boundary conditions: T0 law/moments are total, lower terminals require T>=1, q(empty)=1/2, binary adversary labels are legal source labels while learner outputs are real [0,1], deterministic intermediate may be unbounded, cumulative regret is signed and coefficients/index shifts are exact.

R7: Provide meaningful actual validation canaries for causality, small-horizon normalization/moments and nondegenerate regret, deterministic and nontrivial seeded terminal use, and distinguish them from the universal producer. Verify complete rendered formulas, assumptions and actual pixels at FINAL without treating typechecks as theorem proofs.

R8: Reuse the shared Regret/Mean/finite-action probability definitions; preserve old source statements/cards/registry/scanner/pins. Limit acceptance to C1-LOG-UNAVOIDABLE after full proofs and gates; keep all other Chapter1/fullRegret/NoRegret/six main gaps,16sourceitems/nullproof-total, Chapter2, unenumerated3–16 and necessary appendices open with Goal ACTIVE. No main/live/merge or chapter completion.

## Metadata, gates and boundaries

The nested neutral-receipt schema preparation failure is retained. Invalid first input manifest bound one live wrapper log while empty; current v2 was frozen after completion and every row matches. This does not validate the stale original hash. All mathematical headers retain contract version1. Actual planned-type and neutral-type exit0 certify definitions/propositions are well typed, not proofs of16 theorems. The neutral report supplies all16 seven-slot reconstructions and does not supply a source verdict.

Required mathematical repairs: none. Required metadata repairs: none. All actual law/moment/causal loss/minimum/integrability/bad-sequence proofs, meaningful canaries, BODY/combined/rootTests/harness/reader/site/FINAL/native/PR gates remain required. Only future C1-LOG-UNAVOIDABLE may close. Exact PR190 remains an unmerged prior stack; no chapter/Goal/main/live acceptance. Scope16sourceitems/proof-totalnull and all other mandatory work stay open.

## Exact raw inventory

| Path | SHA-256 |
|---|---|
| `docs/contracts/online-guessing-log-lower-v1/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `docs/contracts/online-guessing-log-lower-v1/contract-v1.md` | `0a23cc844787b8a791772a75a620b0a7cc23cfdb9e471c14283db1bf4e3db28e` |
| `docs/contracts/online-guessing-log-lower-v1/dependency-DAG-v1.json` | `132ddc62d6b873ea47515276d43ba218a5266d9bd26b86dcfd67e01e2a3339fd` |
| `docs/contracts/online-guessing-log-lower-v1/planned-definitions-v1.lean.txt` | `5c219f792d87961c27eefee4e5b8f782af2ba64269d0e7cbbe0b74268d233d8f` |
| `docs/contracts/online-guessing-log-lower-v1/planned-public-headers-v1.json` | `71ecce15fe375431ef6a2d4625cbb4bf650a996fe6b3dc9fb366fe76066cc7af` |
| `docs/contracts/online-guessing-log-lower-v1/planned-statement-fingerprints-v1.json` | `e3dbb0e1b07fd1f395a66029b0f9d183588de82260966cfdf3481524158b68ef` |
| `docs/contracts/online-guessing-log-lower-v1/semantic-signature-v1.json` | `22d425631c72598e6bba4afb50fba79c56a360d9cad1c1e17139fb17e4607516` |
| `docs/contracts/online-guessing-log-lower-v1/source-card-v1.json` | `523fac217e3c033e00a70bbcf7648f086b393dc899b7828d49bcca8c0c175046` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/00_context.md` | `f16dfbc895cbaf527e58edf7b9a5d4774cb8696d600f447849a0163317dc9ac9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/10_upper_director.md` | `365defa6f22de3e812efe5c52393f25899287217095d0839e5b9fd82403e2a03` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/20_middle_formalizer.md` | `52ffa12d81864241bf858ab92f1c2fe608d76a1bddc9ac705cea2d59475dd4e7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/30_lower_architect.md` | `d5527c533e797cb655480b555edf5b32c5b92a0625494944915c1015f0d89f17` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/base-PR190-fresh-v1.json` | `0f526d8beff1c97326f6f1552a29e3e57c66bb8d65a0b07d21212d50b1736323` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/blind-binding-audit-v1.json` | `90b49ed300a4dcf4b8d1396b7e8f12e47b0c83ee4b1798c925dcbeec2bb2ba90` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/blind-decoder-receipt-v1.json` | `7e776bdae1d712a05c495b3219afba05645e4181881dc09b69c53738aed38e2c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/blind-decoder-v1.md` | `7da5da4fe209bc8d03fc2d0a60cb79eeaea9aeb585cc2580ef83204448802480` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/canonical-worktree-audit-v1.json` | `e28832f1613443ab34a8d121165e987c008224f73cf4aa4cdddeaf0253806952` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/common_v1.py` | `30514a76aab40ec784ad69729e945cd3ec81a77222e6009e9890b3296d129797` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/current-API-types-v1-exit.json` | `7456b0028a5f7ba05a99300d6ac3ade44f8225a1c12e76f2a31478d8d9033dd8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/current-API-types-v1.log` | `37c49c54ae39dbfb8a4e32bf51b0545bc436cc132a23537f8cc6afb5ba350b72` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/current-lean-version-v1-exit.json` | `6e8e0ba4800053dd0abd5ebac077b875c84a1c0b52e2984180dd829bb1475337` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/current-lean-version-v1.log` | `e77960cdfb8d64df3da4367afc3bd4c528ba980f6bc7e4cea99129226781ba10` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/current-mathlib-pin-v1-exit.json` | `90b922c872951fd3ed458724fd40dcd61a0c3aa06f0651c1936c17169d4f0f6a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/current-mathlib-pin-v1.log` | `884fab88619a3d1adcafe89eecddd2d98f4be5c6fa61262862134dde9e51d225` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/draft-event-v1-exit.json` | `b2fe4b491880ae2881a409f596ec715570f3a302f9a060f228774655c485b197` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/draft-event-v1.log` | `3ee05ac5189421283bbaf6918b607a99b126dd374a62b54610a12e6822b56a66` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/draft-freeze-v1.json` | `f65ba8ba162e972b885130b0d7b31ec51eff38420bcd195d7bfa01371d24ef5d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/existing-shared-distribution-v1-exit.json` | `6f938ff4063c24ed2444144b6bf9fd4dc142741988065b00c126cd14ab41761d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/existing-shared-distribution-v1.log` | `8a43f2f600188fa07f414764697e33dec20202a91952fc1e35b53ff486d6d40d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/existing-shared-mean-v1-exit.json` | `81c12838907ea69b8a15c45a722ed1bbd8874c8eab24125df7897fe7acaa822f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/existing-shared-mean-v1.log` | `d28a2e86b3aab003e639c06fb152abea410d2cacf03132c74151e8ef332e85d5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/existing-shared-regret-v1-exit.json` | `29a57e652c2c0753fcc1441f9f263cae6fbf4f8e86832d0a590a409660fb3c4c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/existing-shared-regret-v1.log` | `01a55234e05ff55ec3c90a70a795b611362b756389cac7436eb6a29bb4d4bd8e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/fresh-fetch-v1-exit.json` | `fae9139d75dcb786cb176d2208f41039ee63d6221ddfeef2e3b156b5a358c20d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/fresh-fetch-v1.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-frontier-refresh-v1-exit.json` | `6cd7cd30e2ad0223b0bba3d694ecf98844ef82d9f3f15cf80524aed0ae0fcedc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-frontier-refresh-v1.log` | `bff73ff554907d7c5dd50b99f2491f5675e93afb29829e402ec383fb52fe3cdc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-frontier-shadow-v1-exit.json` | `74da8f3eb10ace738bb5780c306d2df4d1c7ac74b89507a4c55428ea28c65715` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-frontier-shadow-v1.log` | `ad548f6e24b3214fbf5796c632caa24debbaa21c6622f7dab8abe268f521de7d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-lifecycle-event-v1-exit.json` | `edb92cdef23e05737503788a9dad64cdbab51db475ea8b4fabf4a59315844584` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-lifecycle-event-v1.log` | `b1e8b438a9b725793b9888d206e98a971ace3df200ec90ed9cb63eab26b28507` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-list-lean-decls-v1-exit.json` | `26f441532e701869657195de5433eff92f0321ccb872b3f02dc10906fbd36187` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-list-lean-decls-v1.log` | `258218f16a12b1a530d85ae83e6c2449237af8a0a1153bb35de40245d665b131` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-list-mathlib-v1-exit.json` | `f88b81aa2fe34dae0d5679fc6a6793c8f477ad744196f2513523f59b0dbc7d8d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-list-mathlib-v1.log` | `eedc3e9609fdc7a3bcf76443a33933477de80dcc4ec9906b64a691e29b207e9d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-memory-record-v1-exit.json` | `4e9341031a8fe1d892afe7d6472ca4bf5b34d079a600cad062350cd0177c7ebc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-memory-record-v1.log` | `89e8a7b2bb8d4fd593f0705289ca3c4c63015e48d0e8c9cbe5b71cf2c7cc44f4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-new-task-v1-exit.json` | `4b4fa3596b295c5c7f4c36a6d87c1ce0126e5d0c034e99f7a8a3b9a2b69c4346` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-new-task-v1.log` | `25eb9342c3094bee57187630bd149d2c522fc9f7ac7e65bebe5c198eba60ed99` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-retrieval-record-v1-exit.json` | `7884a447850748fd831d8d1a7ef74956bcea38eebb14f07551a941713c55a21e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-retrieval-record-v1.log` | `73ac93f120215511ff0370d7ce100a9d0e83598ad882bcc5773cd1dc889b5321` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-safe-verify-v1-exit.json` | `9bd7d2930ac9f0faf4388643ced4d028418cbe7535f51c1bf217e75fc266a4f5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-safe-verify-v1.log` | `1773541c625f225e5a9abc61985c3ad19e871cf31aa0cf89cc440b3d8398862c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-statement-fence-v1-exit.json` | `29c9a276e91b1bf3228b16d13be380527822f0478bcc19886893f1b7a1e9baae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-statement-fence-v1.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-trial-log-v1-exit.json` | `50013d7c03df29ff98efe4c0c1870465561d55b1eae50575bd7b81935a6de482` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-trial-log-v1.log` | `ea7bd7e4d64216b46f554a90e02a3d58b4fcbe72766c2f7b316b656b94d19b32` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/initialize-v1.py` | `929eabf22c92b1fa0f01b21939f3e1e2b4bb06174f5124072ddd2bdca5e6d45e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/current-API-types-v1.lean` | `dea443167bdbbf62e5ef80b46f4b966041ede4004310e0e22b857eef3da96eb3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/planned-types-v1.lean` | `da892db4900b09111c196a8a73296e73ead89a46d285374f283cf3c7329d64f2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/memory_digest.md` | `11243e4c33a482cfede7015f744667a20a200b217cd8f9127feed8ddfc59c6b5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/neutral-input-v1.json` | `b552f75a7d0869e20a95329907a9158ecb576abec329fa16537f3804336e5604` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/neutral-packet-v1.lean` | `9e632a51200cec25fffe42fc315c001f1035184a3198fda41d6476aaf83829eb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/neutral-types-v1-exit.json` | `8352dbeb2e241e34d4fcfaf17e78a8264387dd916a6823f25b423706f8c317bc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/neutral-types-v1.log` | `bd3e2f0f20da5b91dc8c4720874efd5f9c43abab339db0ae2eb86dd4083f5cd8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/new-task-v1-exit.json` | `622d0a0d3002fae08f5573e597110fd3db415fc75dd2f33894ea0219e6fbda3f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/new-task-v1.log` | `fe35702b9bc82a45b3a0bee7502dd92662b07e4bfb4ea20719052c44751114bb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/owned-commit-paths-v1.json` | `953d6d35e4fdc08b5270e7cf9f41c93d168c33817ff890d7efddceb3d6e3235f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/paper-boundary-v1.json` | `4b85e7690280863c2a4b3eaab46118453ac1aec397ef8563c47f7567bd57b4f5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/planned-types-v1-exit.json` | `603e456a7cf0a72f8602f7240d5896e544b08f19294eac185a482f200a82aede` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/planned-types-v1.log` | `f9baaa155154964d0bc943e737d745f4f228697ef5fad1918a0252ca5a395098` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/preparation-schema-repair-event-v2-exit.json` | `5a3380762592129b0c1c3054761012ee1c1fb1829dbc02dc21b2c83c50055a66` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/preparation-schema-repair-event-v2.log` | `6b6964034f245bbb3e05a8ccaf75e04fd204609606e4584e265c0ab834a037de` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/preparation-schema-repair-v2.json` | `8d017374ebbcf95b4644af514f4328ef513aa0a83a0bce4e737567ad72e32dc7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/prepare-contract-v1.py` | `0583d2a148c0117b4df45b57be54f4e1937fe6167142d9ec2a4a8c5ffeeef245` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/prepare-source-review-v1.py` | `cad7aba07946e8f52a3ce5ee0326f03997ae232324323e01d421756c71229cc2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/prepare-source-review-v2.log` | `db3044b6eb40f5dea862cc3548b6e9b36a68bb327c295f04f1ee83a1fd70c8d9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/prepare-source-review-v2.py` | `13e70ff91438487763c010d44a2cbf1bc86388fede21c4e5ef34a8039fef2006` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/render-source-v1-exit.json` | `79d760d045846b1beb52168b846f23f5444ed834aa5d8d001c91c9d7f5baa843` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/render-source-v1.log` | `3d3bffa7502670613201c5ad954d0784675f2b142a158dcc60dbcb4ba470ffe4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/render-source-v1.py` | `07881acee8d6890d3590215c36e014186dec1f538cb7764030d90c87e0a46290` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/repair-preparation-v2.py` | `7c182e3b8ce4f5060b6ba5ebd9999dfc62b5a82be6f512200ce43b2345af8273` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/retrieval-initial-v1.json` | `bc0c72a6da5164e8d96140617a3e3afaa28ecb5486df993aff95b0b52f8bb08a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineGuessingComparison.lean.raw` | `0fc28f4459d2cffb5afcf795898dd152508ddb06acb356cb08d1dd72e09f7f14` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineGuessingLower.lean.raw` | `a09390e250f7e55e8e9d282995faedaf186ecf67d8c1aa177e6f8d08ee5428e7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineGuessingOGD.lean.raw` | `12792af1571fde0fe37796686b044f0df0990ca3d808a89431804605d0ee8d00` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineGuessingSubgradient.lean.raw` | `95d206190d443939115037f9bf6d0eeb1e3229f3ae52eb4150927fbe69e89348` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineGuessingSubgradientPolicy.lean.raw` | `ed32d846509d0dc34eb05ce6fad5d3af8aa6dbf92a8c8a78cc8859b0e42e6b0e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningAsymptotic.lean.raw` | `4d704d07b9616ca48a1ee56d47af7f5f8ca9e3797d2a9b47d373038a25d79d59` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningFoundations.lean.raw` | `e23ebdca2f7ce21a16173c93390fd24d16ba36e403c9d084233f7480e75408b8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningFTL.lean.raw` | `8c3574c657f08e0c5291f0689105f9459e92187502f092f4d36d848e52ab4219` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningFTLState.lean.raw` | `fa33c10252eb5cd51b3ea4cdffb10fa95c37416f3098ceb76d9d58f465ff1765` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningHistory.lean.raw` | `3412177ab7dd0ac0e350d8fde7f91e61640d55743d1f17d15c62a65dd4492fc7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningIID.lean.raw` | `92af24e6a2c2b1054503492b2bad97cd17ccea2217439f6d2f8a7bedb0de3d5e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningInformation.lean.raw` | `72bef017a43c293d0d3c449707e4a0e058f4655c2483b54c3120d7b41c98135a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningMean.lean.raw` | `811dcf3741e3d6dee19b2c4a9f43f4b266808b89843a1719e00f239a4687258b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningRegret.lean.raw` | `0bac6b6e454c5d7bd2244fc115bc8df8cbd9b5505302aa81d03baaeeeec204dc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningStochastic.lean.raw` | `0242481022883958afef677654fadd3f6e37b381f3fe463e3605f3eb0542f2bd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof.lean.raw` | `55cfcdaf2b28f0e55ef4326060c861919e9dc3f69fbaac31c6563e4d16135e67` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/CONTRACT-review-conversion-windows--ONLINE-GUESSING-LOG-LOWER-20261008.md.raw` | `8ac3c529d2e0db67496c33287304b664da646d9dad7b322ce790eebb8f27f29f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/CONTRACT-review-proof-blueprints--ONLINE-GUESSING-LOG-LOWER-20261008.md.raw` | `35d1ba3f61ca2c2591fc43f9e48b06f62af79c575df79bca620066806a2c6e85` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/CONTRACT-review-proof-obligations--ONLINE-GUESSING-LOG-LOWER-20261008.md.raw` | `e2500ef474fc22411d9cd2cc1f50e5e6cfdf4994146259d9c2b13c2b21010cae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/CONTRACT-review-research-wiki--retrieval-index--ONLINE-GUESSING-LOG-LOWER-20261008.md.raw` | `35d1ba3f61ca2c2591fc43f9e48b06f62af79c575df79bca620066806a2c6e85` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/CONTRACT-review-tasks--ONLINE-GUESSING-LOG-LOWER-20261008.md.raw` | `85d024f10253eaee51f640ef421f30e9461f77a76e8a2f8d1906cf31f11f98c2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/docs--contracts--online-book-v1--coverage.json.raw` | `fd7580c2d0ec040352317d3c53dc583a6b9b75a68b4026ebf3b38f7010a98f1e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/docs--contracts--online-book-v1--source-inventory.json.raw` | `a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/lake-manifest.json.raw` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/lakefile.lean.raw` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/lean-toolchain.raw` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/MANIFEST.md.raw` | `4a3e05afd265f465fccf76becdf7a749f3dd63f74f1c33fc6339241d57b437fd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/prior-readonly-online-log-lower-api-v1.lean.raw` | `ab3262aa37cc810d80eb1e563a1b5bb87b2bd376c902908eff33338f3f2a15e8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/prior-readonly-online-log-lower-api-v1.log.raw` | `488aa9920f2845ca46d32ca53c4855cbae1d5428357aed91becb1b1614c02dd8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/prior-readonly-online-log-lower-api-v2-exit.json.raw` | `ba0385d9ddf16ad0af1baebf830dd33d38ea9f40965c8a15a9f8e7b966b841ad` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/prior-readonly-online-log-lower-api-v2.log.raw` | `4ef33c0c17b9fcdd99519fe1b852626506a9cd01e320efc9a3a7b3e9a15f7989` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/runs--active_frontier.json.raw` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/runs--lifecycle_memory.jsonl.raw` | `94be3ceb994768191ceb6a7545935c8d16c044511dfe8c4482e2fde493eaa5f8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/runs--lifecycle_sessions.jsonl.raw` | `124dc2affbd0c75ef90455bcc17db55523eb71b3bcaac72fc4e5e18eddfb90a3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/runs--online-regret-domains-20261007--accepted-decision-v1.json.raw` | `99e8ecc2c266d70624085d23f56d4faa16ce9cf15bee9145c34e3dd8744b9a67` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/runs--online-regret-domains-20261007--delivery-obligations-overlay-v1.json.raw` | `c95e61f5bf8bb41819c0795a469c27decaff36ccf1adb84344618ac1986e0dca` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/runs--online-regret-domains-20261007--final-reader-receipt-v1.json.raw` | `abae24c08ec1d21238d5e63b0ffc2305c39ec84c9648416bd7e42a05d1af975a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/runs--trials.jsonl.raw` | `b96cac6f18b967cb8ef8710eac9596c3de8897a80c1f856f3965eca8b8528b08` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/Tests.lean.raw` | `a2e1fc1ff9d41b4c27f443b1865962908ba87291b921476aef681e02bef8eba8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/website--content--chapters.json.raw` | `e471c0acacb9e48f3cfa24849a4cd3d4385317cf1c21c53d7fff8a3959c26300` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/website--content--declaration-boundaries.json.raw` | `6806d5fc69f3ebd42814f502f27afc1295369a80d3c0fbb6f7c59f6c57fdbbe9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/website--content--highlights.json.raw` | `9ea5f8ecf47579a85d72268c44d6c00ece458b60ee57102bc16887456cd45ea3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/website--content--readings.json.raw` | `fbda5ccc1ed0b1e65fe2cf69e8bd984cfb0934ec0970bbe9c41232ae66f4ed7c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/website--scripts--build_site.py.raw` | `4fe18b8b9a543ff5256a278f49d160424b30ba2185c946f3d6081ad5460ccaff` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-contract-review-packet-v1.md` | `1fc97be3ad5fb13fa239ec4a91d8540fc98a9e09552550583296c3cf7185a557` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-pdf14-v1.txt` | `3f9d01aee6e81504b7ca2ef0d9657bc1ee30f36eb54a957b8018c4d0c3e2ac66` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-pdf15-v1.txt` | `037b6d907a868c339b881162333f6e56352cbebf285902eb6ed628ff4f8bd947` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-pdf16-v1.png` | `d2620e7f6c8d60839ae426eddb470eb56f226807ad6b744f73d15267e5252657` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-pdf16-v1.txt` | `b8fe01f6c31bf15cfb67ea948a832f97e2c77f9e1f569a36fd9fa72e831796ee` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-pdf17-v1.txt` | `164b4ca2261475aeadaf633ce67afbf8a221f612b8f4db801c36ea75081263e8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-pdf18-v1.txt` | `bec2bd23e52551c2f353a7dec52c99582185e812f99a24f55983f209007eb484` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-pixel-review-v1.json` | `b059ec6ab119a98390b4c84bb078beae85e797991f5d46a52279a315a31e4ebd` |
| `BanditRLProof/OnlineLearningRegret.lean` | `0bac6b6e454c5d7bd2244fc115bc8df8cbd9b5505302aa81d03baaeeeec204dc` |
| `BanditRLProof/OnlineLearningMean.lean` | `811dcf3741e3d6dee19b2c4a9f43f4b266808b89843a1719e00f239a4687258b` |
| `BanditRLProof/OnlineLearningFTLState.lean` | `fa33c10252eb5cd51b3ea4cdffb10fa95c37416f3098ceb76d9d58f465ff1765` |
| `BanditRLProof/Exp3ConditionalMoments.lean` | `e0d4683319f42d26745fa8f411d50fd2c0abf6f75f19d81177cc9b03814935ba` |
| `BanditRLProof/OnlineGuessingLower.lean` | `a09390e250f7e55e8e9d282995faedaf186ecf67d8c1aa177e6f8d08ee5428e7` |
| `.lake/packages/mathlib/Mathlib/Data/List/Count.lean` | `b0ffe1488d210796008404520d9c99985a98cbc7cf87964686033d115ccf1613` |
| `.lake/packages/mathlib/Mathlib/Data/Fintype/Vector.lean` | `6c08ffb94f10060c874848b7c1fa0059b2a4de12924ef3afcf20df1a15e1a2af` |
| `.lake/packages/mathlib/Mathlib/Data/Vector/Basic.lean` | `27e556fa56f351a80d7a945c21ae50bd3ff116271ffdafe5b01ddde33538989b` |
| `.lake/packages/mathlib/Mathlib/NumberTheory/Harmonic/Bounds.lean` | `92f1c8224c4353a057c306ea1b8f35ff51e02b82462916fcd5820491fce11db5` |
| `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` | `ce6b984f1a4b0ba00688574d9e90785a5d5a7f7c27c3230c501909792d0e2495` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/freeze-source-review-v3.py` | `a1d0d96076bc65d043a0e83404430d04acdb46d06cd777703aa8ce9a93c264b2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/preparation-freeze-repair-event-v3-exit.json` | `ff4c4f1e374c400f1c65d74319dc29bf0a82deb065a9e6392ca457c8f4b01666` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/preparation-freeze-repair-event-v3.log` | `6acecb07e1ccef404f5003c671a2257a0bbaefa3e296558049230b4e15fca788` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/preparation-freeze-repair-v3.json` | `918b01bdbbea27dd5202d646068d82974665b89ca522d23b874c2e624490682f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/prepare-source-review-v2-exit.json` | `ddc67e05cd057ffcd945a68bfdca44fc01b10d4f2bec813cb6b93e66d6c0a354` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-contract-inputs-v1.json` | `a1cb1ec67a2fda334e6c009dfa656ea26d9286d09f2b813e9a31d909ab5bdce7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-contract-review-packet-v2.md` | `005022cef77d5217094b0e1d75846b199455af2c1adcf64ceb8b3f8c62dabaeb` |
| `runs/online-log-lower-20261008/source-contract-inputs-v2.json` | `dacfb20a1fb7d501b310e053efad728abdf2d9225a5da4bf122f24518c4561eb` |
