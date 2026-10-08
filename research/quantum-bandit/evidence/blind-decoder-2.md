# Independent source-blind decoding: packet 2

## Method and status

Only formal declarations, types, proof terms, and needed dependency definitions were used. Lean line comments and nested block comments were stripped before displaying source; no prose comments were used to infer meaning or claim scope. No evidence seals, user specification, author summary, literature, or reviewer feedback was inspected. Procedural messages were not treated as evidence of mathematical intent or certification. The first report was not edited.

No compilation was run by this decoder, no kernel-acceptance verdict is given, and publication is not authorized. Visible theorem bodies contain proofs rather than visible admissions; that is not a transitive proof audit. In particular the Born range theorem remains a source-level declaration here. All hashes refer to original file bytes, including stripped comments.

The five packet-2 files contain 45 explicitly named mathematical declarations; constructors and structure fields are described with their owning type. This report supplies the seven requested slots for each. `None` under cost means the declaration contains no resource-complexity conclusion, not that evaluating the objects is free.

## Formal conventions

**Finite matrix context:** finite index type `ι` with decidable equality where matrices are used; square complex matrices and complex Euclidean vectors on `ι`. `ι` need not be nonempty. Norm is the Euclidean operator norm; matrix order is positive-semidefinite order, not entrywise order. `star U` is the adjoint and equals the inverse under unitary hypotheses. Write `p(U,P,ψ)=Re ⟨Uψ,P(Uψ)⟩`, `q(w)=QuantumQueryWord.queryCount w`, and `E(w,U)=QuantumQueryWord.eval w U`.

**Primitive context:** `n : ℕ`, basis `PrimitiveBasis n = Fin n → Fin 2`, primitive circuits are lists of `X`, `Ry`, `Rz`, and `CX`. Their matrix semantics apply gates in list order. `Aligned δ exact approximate` relates equal-length lists gatewise: a gate is unchanged, or both gates are `Ry` on the same wire with real angle evaluations within `δ`. Primitive angles include arbitrary real numbers and are evaluated noncomputably.

**Arm/measure context:** natural `K,D`; arms `Fin K`; arm values arbitrary real functions. `Δ(i)=realMeanGap mean i=(supremum of mean over Fin K)−mean i`. An actual arm supplies inhabitation; empty block lists need not. `ActionTrace A` is `ℕ→A`; `pullCount action i t` counts occurrences of arm `i` at times `0,…,t−1`. `realMeanRegret mean action t` is `t·sup mean−∑_{s<t}mean(action s)`. It is a deterministic mean-value quantity, with no random reward observations in that definition. `Measure` is arbitrary, not necessarily normalized; evaluation on sets uses outer-measure semantics. `ofReal share` clips negative shares to zero.

Implicit parameters are universally quantified along with explicit ones. Definitions supply functions/types, not existential implementation claims.

## BornStability.lean

The packet-2 Born file is byte-identical to the packet-1 Born file. No changed Born declaration was found. Its declarations are independently described below to make this report self-contained. Namespace: `QuantumBlockEncoding.BornStability`.

| Declaration | Objects | Parameter range | Assumptions | Quantifiers | Output | Costs | Claim scope |
|---|---|---|---|---|---|---|---|
| `probability` | `U,P,ψ` | Finite matrix context | None | Every input triple | Real scalar `p(U,P,ψ)` | None | Noncomputable quadratic-form scalar. Arbitrary inputs need not give a probability in `[0,1]`; no measurement law is defined. |
| `effect_norm_le_one` | `P` | Finite matrix context | `0≤P≤1` | Every such effect | `‖P‖≤1` | None | Norm bound for an effect; projector structure is not required. |
| `unitary_norm_map` | `U,ψ` | Finite matrix context | `U` unitary | Every unitary and every vector | `‖Uψ‖=‖ψ‖` | None | Norm preservation, without a normalization premise. |
| `quadratic_difference_le` | Complex inner-product space `E`, continuous linear `P`, vectors `x,y` | Any normed additive group with complex inner product; no finite-dimension or completeness premise | `‖P‖≤1`, `‖x‖=‖y‖=1` | Every such space/map/vector pair | `abs(Re⟨x,Px⟩−Re⟨y,Py⟩)≤2‖x−y‖` | None | Quadratic-form Lipschitz bound; positivity and self-adjointness are not premises. |
| `probability_difference_le` | `U,V,P,ψ,η` | Finite matrix context, real `η` | Unit vector; unitary `U,V`; `0≤P≤1`; `‖U−V‖≤η` | Every input meeting these premises | `abs(p(U,P,ψ)−p(V,P,ψ))≤2η` | None | Conditional stability with the same vector/effect. Norm premise implies `η≥0`. No approximation is produced. |
| `probability_mem_Icc` | `U,P,ψ` | Finite matrix context | Unit vector; unitary `U`; `0≤P≤1` | Every such triple | `0≤p(U,P,ψ)≤1` | None | Range declaration; acceptance is not independently checked. No distribution, sampler, or measurement implementation is introduced. |

## BasisHellinger.lean

Namespace: `QuantumBlockEncoding.BasisHellinger`. In the first eight rows the index is an arbitrary finite type unless stated otherwise; no decidable-equality instance is requested. Write `b_x(j)=‖x_j‖²` and `H(p,r)=∑_j(√p_j−√r_j)²`. This is the **unhalved** squared square-root distance: there is no factor `1/2` in its definition. `Real.sqrt` is total and is zero on nonpositive inputs, so `H` is defined for arbitrary real functions without certifying that they are probability distributions.

| Declaration | Objects | Parameter range | Assumptions | Quantifiers | Output | Costs | Claim scope |
|---|---|---|---|---|---|---|---|
| `basisProbability` | Vector `x`, index `j` | Finite `ι`, Euclidean complex vector, `j:ι` | None | Every vector/index | `b_x(j)=‖x_j‖²` | None | Noncomputable coordinate weight. Normalization is a separate conditional result. |
| `hellingerSq` | Real functions `p,r` | Finite `ι`; `p,r:ι→ℝ` | None | Every pair | `H(p,r)` | Finite summation only; no complexity bound | Noncomputable unhalved squared square-root distance. No positivity or normalization requirements occur in this definition. |
| `basisProbability_nonneg` | `x,j` | Any `ι`, without `Fintype` requirement in this declaration | None | Every vector/index | `b_x(j)≥0` | None | Coordinate weights are nonnegative, whether or not vector is normalized. |
| `sum_basisProbability` | Vector `x` | Finite `ι` | None | Every vector | `∑_j b_x(j)=‖x‖²` | None | Exact Euclidean norm/coordinate sum identity. |
| `basisProbability_normalized` | Vector `x` | Finite `ι` | `‖x‖=1` | Every unit vector | `∑_j b_x(j)=1` | None | Nonnegative coordinate weights form a finite probability vector together with the previous nonnegativity result; no random sampling law is constructed. |
| `sqrt_basisProbability` | Vector `x`, coordinate `j` | Any `ι`, without `Fintype` requirement here | None | Every vector/index | `√b_x(j)=‖x_j‖` | None | Square-root identity, no normalization needed. |
| `hellingerSq_basis_formula` | Vectors `x,y` | Finite `ι` | None | Every vector pair | `H(b_x,b_y)=∑_j(‖x_j‖−‖y_j‖)²` | None | Coordinate-magnitude expression, valid even for unnormalized vectors. |
| `hellingerSq_nonneg` | Functions `p,r` | Finite `ι`, arbitrary real functions | None | Every pair | `H(p,r)≥0` | None | Sum-of-squares nonnegativity, not a certification that the arguments are distributions or that this totalized function is a metric on arbitrary real functions. |
| `hellingerSq_basis_le` | Vectors `x,y` | Finite `ι` | None | Every vector pair | `H(b_x,b_y)≤‖x−y‖²` | None | Magnitude contraction in squared Euclidean distance. Normalization is unnecessary for this algebraic inequality. |
| `wordOutput` | Quantum query word `w`, matrix `U`, vector `ψ` | Finite matrix context | None; `U` can be nonunitary | Every triple | `Matrix.toEuclideanCLM(E(w,U)) ψ` | None | Noncomputable final vector of straight-line word semantics. |
| `wordOutput_norm` | `w,U,ψ` | Finite matrix context | `U` unitary | Every word/unitary/vector | `‖wordOutput w U ψ‖=‖ψ‖` | None | Norm preservation using word unitarity; input need not be a unit vector. |
| `wordOutput_probability_normalized` | `w,U,ψ` | Finite matrix context | `‖ψ‖=1`; `U` unitary | Every such triple | Coordinate output weights sum to one | None | Normalized basis probability vector for word output; no outcome measure/sampling mechanism is defined. |
| `wordOutput_distance_le` | `w,U,V,ψ,η` | Finite matrix context; real `η` | Unit input vector; unitary `U,V`; `‖U−V‖≤η` | Every fixed word and such data | Output-vector distance is `≤q(w)η` | Linear in syntactic forward-plus-inverse query count | Conditional stability under replacing the same oracle matrix in a fixed word, including identical known gates in both evaluations. |
| `word_hellingerSq_le` | `w,U,V,ψ,η` | Finite matrix context; real `η` | Same premises as previous row | Every fixed word and such data | `H(b_output(U),b_output(V))≤q(w)²η²` | Quadratic in word query count and tolerance | Conditional basis-distribution sensitivity. Zero coordinates are allowed. No likelihood ratios, KL bound, multi-round transcript, or adaptivity occurs in the statement. |
| `bounded_word_hellingerSq_le` | Previous row's objects plus `D` | Finite matrix context; real `η`; natural `D` | Previous premises and `q(w)≤D` | Every such tuple/count certificate | `H(b_output(U),b_output(V))≤D·q(w)·η²` | Replaces one factor of `q(w)` by supplied bound `D` | Single-word bound. `D` bounds query occurrences, not parallel depth or primitive gate count. No summation over rounds or information-theoretic sample-complexity conclusion is present. |

## QueryCircuitCost.lean

Namespace: `QuantumBlockEncoding.QueryCircuitCost`. The word type here differs from the earlier matrix-word type: a known instruction stores a primitive circuit, which can be expanded or erased to a matrix-word instruction. Write `w̄=erase w`, `C(w,c)=expand w c`, and `G(w)=knownGates w`.

| Declaration | Objects | Parameter range | Assumptions | Quantifiers | Output | Costs | Claim scope |
|---|---|---|---|---|---|---|---|
| `Instruction` (constructors `known`, `forward`, `inverse`) | Primitive known circuit or forward/inverse marker | `n:ℕ`; circuit on `n` qubits | None beyond circuit type | Type of every such instruction | Circuit-bearing syntax | Costs supplied by later definitions | Known operations are supplied primitive circuits; oracle implementation is provided to expansion separately. |
| `Word` | List of circuit-bearing instructions | `n:ℕ` | None | Every finite list | Abbreviation of list type | Finite syntax only | No branch, measurement, or adaptive instruction constructor. |
| `Instruction.expand` | Instruction `g`, supplied oracle circuit `c` | Primitive context | None | Every instruction/oracle pair | Known circuit; oracle circuit; or reversed oracle list with each gate daggered | No resource theorem in definition | Substitutes a supplied primitive implementation. Inverse expansion preserves oracle list length and uses exact dagger semantics. No gate synthesis is performed. |
| `Instruction.erase` | Instruction `g` | Primitive context | None | Every instruction | Matrix-word instruction: evaluated known circuit with proof of unitarity, or preserved marker | None | Noncomputable semantic erasure. Known circuit gate details are dropped; its matrix is exact. |
| `Instruction.knownGates` | Instruction | Primitive context | None | Every instruction | Known circuit length, or zero for either marker | Counts all primitive gates in known circuit | Syntax cost measure; different from earlier `knownCount`, which counts known instructions. |
| `expand` | Circuit-bearing word `w`, oracle circuit `c` | Primitive context | None | Every pair | Concatenated instruction expansions `C(w,c)` | No bound in definition | Circuit expansion using one supplied oracle implementation throughout. |
| `erase` | Circuit-bearing word `w` | Primitive context | None | Every word | List map of instruction erasure, `w̄` | None | Noncomputable conversion to a matrix word. |
| `knownGates` | Circuit-bearing word `w` | Primitive context | None | Every word | Sum `G(w)` of known-circuit primitive gate lengths | Primitive known-gate total | Does not count oracle-expanded gates until the later identity. |
| `expanded_length` | `w,c` | Primitive context | None | Every word/oracle circuit pair | `length(C(w,c))=G(w)+q(w̄)·length(c)` | Exact primitive-gate count bridge, including both forward and inverse oracle copies | Counts expanded list length, including redundant/cancelling gates. No parallel-depth, synthesis, bit, or runtime bound is concluded. An empty oracle can make primitive oracle-copy cost zero despite positive marker count. |
| `expanded_semantics` | `w,c` | Primitive context | None | Every word/oracle pair | `evalPrimitiveCircuit(C(w,c))=E(w̄,evalPrimitiveCircuit(c))` | None | Exact semantics bridge for primitive expansion/word erasure, using circuit composition and dagger identities. Does not prove that a supplied oracle circuit approximates a separate target oracle. |

## QuantumQueryAccounting.lean

Namespace: `BanditRLProof.QuantumQueryAccounting`. Compared with the earlier packet, the original seven statement types are unchanged; `expanded_length` has a changed proof body. Three declarations are added. Scope here is read from current types and proof terms, not inferred from a previous verdict.

| Declaration | Objects | Parameter range | Assumptions | Quantifiers | Output | Costs | Claim scope |
|---|---|---|---|---|---|---|---|
| `Block` (fields `arm`, `forward`, `inverse`, `bounded`) | Arm and two counters | Natural `K,D`; arm `Fin K`; counters natural | Stored proof `forward+inverse≤D` | Type of all such records | Bounded counter record | Local forward-plus-inverse cap `D` | Counters can still be arbitrary supplied data. A separate adapter now constructs a particular kind from a word; it does not constrain every block to arise that way. |
| `Block.queries` | Block `b` | Any `K,D` | Well-formed block | Every block | `b.forward+b.inverse` | Unit cost for each counter increment | Definitional total; bounded certificate is not used in computation. |
| `expanded` | Block list | Any `K,D` | Block formation only | Every list | For each block, concatenate `queries` copies of its arm | Total synthetic length from counters | Direction markers are forgotten; this is an accounting arm list. |
| `chargedRegret` | Mean function, block list | Real means; natural `K,D` | Block formation only | Every pair | `∑_blocks Δ(arm)·queries` | Both forward and inverse units charged | Noncomputable deterministic gap accounting. It remains distinct from realized random reward shortfall. |
| `expanded_length` | Block list | Natural `K,D` | None beyond block formation | Every list | Expanded arm-list length equals sum of block query counters | Exact list count identity | Statement unchanged. Current proof's cons case ignores its induction hypothesis and simplifies directly; compilation success is not presumed. |
| `charge_eq_expanded_gap_sum` | Means, block list | Real means; natural `K,D` | None beyond block formation | Every pair | Charge equals sum of gaps over expanded list | Exact gap-charge identity | Synthetic expansion identity. |
| `inverse_only_charge` | Mean function, arm `i`, count `q` | Natural `K,D,q` | `q≤D` | Every mean/arm/count certificate | Inverse-only singleton block charge equals `Δ(i)q` | Explicit inverse cost | Definitional consequence, not a derived environmental regret principle. |
| `expandedAction` | Block list and fallback arm | Natural `K,D`; actual `fallback:Fin K` | None beyond these objects | Every list/fallback | Infinite trace `t↦(expanded blocks).getD t fallback` | None | In-range times reproduce expanded list; out-of-range times use fallback. Provides a total action function, not a probabilistic policy or quantum execution. |
| `chargedRegret_eq_realMeanRegret` | Means, block list, fallback arm | Real means; natural `K,D` | None beyond these objects | Every tuple | Charge equals `realMeanRegret mean (expandedAction blocks fallback) (expanded blocks).length` | Horizon is exactly expanded query total | New formal bridge to the existing deterministic mean-regret definition on the synthetic trace. Fallback does not affect the horizon prefix. No reward process, stochastic expectation, or execution-derived trace is included. |
| `chargedRegret_eq_gap_pullCount` | Same data | Real means; natural `K,D` | None beyond objects | Every tuple | Charge equals `∑_i Δ(i)·pullCount(expandedAction,i,expanded.length)` | Counts pulls in synthetic prefix | New gap-times-pull-count bridge. No cumulative complexity/regret inequality is concluded. |

The local `bounded` field is still unused by these accounting identities. An actual fallback arm is now required to totalize the list, so the added trace identities cannot be instantiated with `K=0`. Empty block lists with a populated arm set give horizon zero. All inverse calls are mapped to repetitions of an arm by this synthetic trace construction.

## QuantumBanditAdapter.lean

Namespace: `BanditRLProof.QuantumBanditAdapter`.

| Declaration | Objects | Parameter range | Assumptions | Quantifiers | Output | Costs | Claim scope |
|---|---|---|---|---|---|---|---|
| `aligned_circuit_confidence_transport` | Exact/approximate circuit, effect `P`, unit vector `ψ`, estimate, angle tolerance `δ`, statistical allowance `s` | Primitive context; real `δ,s,estimate` | `δ≥0`; alignment certificate; `‖ψ‖=1`; `0≤P≤1`; estimate error around approximate-circuit Born scalar `≤s` | Every tuple meeting these conditions | Estimate error around exact-circuit scalar `≤exact.length·δ+s` | Primitive gate count times angle error plus statistical allowance | New circuit-to-confidence composition bridge. Still requires supplied approximate circuit, alignment, and estimate certificate. `s≥0` follows from the estimate bound. No estimator is constructed. |
| `circuit_certified_recommendation_failure_bound` | Finite circuit families `exact,approximate`; tolerances; common effect/vector; outcome-dependent estimates; allowances/shares; measure | Natural `K,n`; nonempty `Fin K`; measurable `Ω`; arbitrary measure `law`; real `ε,δ(i),statistical(i),share(i)` | Nonnegative tolerances; per-arm alignment; unit vector; effect; per-arm `length(exact i)δ(i)+statistical(i)≤ε/2`; per-arm supplied tail-measure bounds for deviations around approximate-circuit Born scalars | Every family and certificates; then all outcomes and arms in failure event | Measure that recommended arm's exact-circuit Born scalar is more than `ε` below some arm's exact-circuit scalar is at most `∑_i ofReal(share i)` | Gate-count bias budget plus statistical budget; sum of tail shares | New specialization of recommendation failure theorem to certified circuit scalar values. Bias is obtained formally from alignment rather than supplied as unrelated real functions. Statistical tails, shares, circuit approximation, and budgets remain assumptions. Common `P,ψ` used for every arm. No probability normalization, estimator/event measurability, concentration result, or sample/query complexity is asserted. |
| `chargedBlock` | Arm `i`, circuit-bearing word `w`, count cap certificate | Natural `K,D,n`; `i:Fin K`; `w:QueryCircuitCost.Word n` | `q(erase w)≤D` | Every arm/word/cap certificate | Block containing word's forward and inverse counts, with bound proved by count identity | Inherits syntactic query count cap | New noncomputable word-to-block construction. Arm label is supplied independently of word/oracle meaning. No oracle circuit, measurement, reward law, or trace is passed to this construction. |
| `chargedBlock_queries` | Same data | Same parameter range | Same count cap certificate | Every such tuple | Constructed block's total queries equal `q(erase w)` | Exact bridge from word queries to block counter total | Resolves a previous count disconnection for blocks produced by `chargedBlock`; it does not claim all blocks originate from words or that their charged arm means have a physical oracle interpretation. |

## Connections now present, and their precise limits

1. **Circuit to confidence:** `aligned_circuit_confidence_transport` supplies deterministic confidence composition, and `circuit_certified_recommendation_failure_bound` instantiates true/perturbed arm values with exact/approximate circuit Born scalars. Thus this packet now contains an explicit circuit-bias-to-recommendation bridge. Alignment and tail bounds remain supplied; no finite-bit approximation procedure or statistical estimator is built.
2. **Word to primitive counts and semantics:** circuit-bearing words expand to primitive lists with exact length `known primitive gates + query markers × oracle primitive length`. Their erased matrix words have exactly the expanded circuit's semantics. Inverse copies count fully. This does not equate query count with total gate count or parallel depth.
3. **Word to accounting:** `chargedBlock` derives the two counters from a word, and `chargedBlock_queries` identifies their total. Combining with accounting identities relates charges to query counts for these constructed blocks. Arm labels remain input data; no theorem connects the word's output probabilities to the arm's `mean` function.
4. **Accounting to regret/pull counts:** the new action trace is obtained by repeating arm labels according to counters. The new equalities identify charge with deterministic mean regret and pull-count sums of that trace at its finite prefix length. This is a real formal bridge to those definitions, while still relying on a synthetic trace rather than a reward-bearing quantum interaction model. No expectation or regret upper bound is present.
5. **Basis output distance:** squared coordinate magnitudes are proved nonnegative and normalized for unitary word output on a unit vector. The unhalved squared Hellinger expression is bounded by vector distance and hence by `q²η²`, or `Dqη²` under `q≤D`. This permits zero probabilities without division. No KL, likelihood, transcript chain rule, multi-round accumulation, adaptive lower bound, or exploration schedule follows from a declaration in this packet.
6. **Constructive and finite-bit limits:** circuit syntax still admits exact arbitrary real angles; erased known gates have exact matrix semantics; recommendation compares exact real scores noncomputably. No rounding, numerical export, gate synthesis, implemented sampler, finite-precision comparison, or bit complexity is proved.
7. **Assumptions and redundant special cases:** no globally unused named premise was found in the new theorem bodies. Normalization is genuinely used to pass matrix error to vector error; unitary conditions are used for the word perturbation theorem. They are unnecessary for special cases such as empty words, but this is not universal redundancy. The proposed new proof of accounting `expanded_length` ignores its induction hypothesis, which is a proof-variable observation rather than an unused mathematical premise or acceptance verdict. The Hellinger vector contraction does not assume normalization. Tolerance nonnegativity in word perturbation follows from the norm certificate. Tail shares remain clipped by `ofReal` with no positive-share or total-δ premise.

## Inspected-file hashes

Packet-2 files were read in full after comment stripping. The changed quantum `CircuitRewardBias` dependency was also read in full. Other dependencies either were previously inspected formally and fingerprinted again, or were inspected through targeted comment-stripped definition excerpts. No unspecified transitive audit is claimed. Hash-only checks are distinguished from content inspection below. The first report itself was not used as statement evidence.

| File | SHA-256 | Inspection |
|---|---|---|
| `C:/qb261009/decoder-packet-2/BasisHellinger.lean` | `7c53ae6d5a845829a2f1e41191d17973215cc1d76d5c1389a64c47eef43d64a5` | Full formal content |
| `C:/qb261009/decoder-packet-2/BornStability.lean` | `df87b7f7f12871ffa5ffd058676e2af9a2d2fe56dfcbf7a9b88cd5c1ee8c62a7` | Full formal content; same bytes as first packet |
| `C:/qb261009/decoder-packet-2/QuantumBanditAdapter.lean` | `0b2753f6d66eba71d96c99fd3de5567f1de1b4ad5ead0671dd08883f85d22dd5` | Full formal content |
| `C:/qb261009/decoder-packet-2/QuantumQueryAccounting.lean` | `d8e5ed5eff0d47dade0ac6fc3598e6e25adebeb7674c5e21e964c11946e93bfe` | Full formal content |
| `C:/qb261009/decoder-packet-2/QueryCircuitCost.lean` | `c025be800fc691cb43d1492485a8232437832f019482e3101991b43bc87f8ab9` | Full formal content |
| `C:/qb261009/quantum/QuantumBlockEncoding/QuantumQueryWord.lean` | `c654b51820c11adf0039003dd76e2502e17f82847b56c8257e9489f21b46333b` | Hash recheck; formal content inspected in first decoding |
| `C:/qb261009/quantum/QuantumBlockEncoding/CircuitRewardBias.lean` | `2bce94952eb200c18b1e0c470b03a849c43399f17d1fb0efa95d09ea35c2981d` | Full current formal content |
| `C:/qb261009/bandit/BanditRLProof/QuantumConfidence.lean` | `1c5dae95090f12b89f732769ba468e8c89dcbe6cd18d28d1ae09b0fe4d0e7a28` | Hash recheck; formal content inspected in first decoding |
| `C:/qb261009/bandit/BanditRLProof/RealMeanRegretPullCount.lean` | `85350988fc9dcf0886f58d50210ad84cc4d0a87533d01218f92bbbf1923c12f7` | Hash recheck; formal content inspected in first decoding |
| `C:/qb261009/bandit/BanditRLProof/MathlibWrappers.lean` | `2e4cd9c436bc956a85a6cea22e2266703bc6729e6dda64ad9ff03d9b6e731dc9` | Targeted imports/pull-count declaration |
| `C:/qb261009/bandit/BanditRLProof/LeafLemmas.lean` | `75a7bff36ad7d596f5efb4890020b72f256174a153175991ab2e53cbe3d1b3e0` | Targeted imports/pull-count excerpts |
| `C:/qb261009/bandit/BanditRLProof/Regret.lean` | `9cdfb07a7acd6fa473b7e1531f877462131540bf9ff47c4b59885edb87eaa889` | Import leading to needed definitions |
| `C:/qb261009/bandit/BanditRLProof/Core.lean` | `a7d3100f1f47ea2938e8ff49bb6d84c2094ce572c5844feeefa715a08f9049cd` | Targeted `ActionTrace` and `pullCount` definitions |
| `C:/qb261009/quantum/.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean` | `ed0c8c0b7a076580699d67aed267443f39d6e10cec30d014af4fd164a6c1feba` | Targeted square-root definition and identities |
| `C:/qb261009/quantum/.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean` | `85e02465e17b84aa75e16c1ff72e1333c7a1744da60d797ac02f946a2ad01c3c` | Targeted squared Euclidean norm identity |

Earlier formally inspected definitions of `PrimitiveCircuit`, `PrimitiveSemantics`, `PrimitiveCircuitPerturbation`, matrix operator norm/order, finite real argmax, and measure/`ofReal` conventions were reused from this decoder's first formal reading; their inspected-byte hashes remain recorded in the first report. They were not treated as author prose or certification. No build was used to establish resolved dependency versions across the separate checkouts. File-name search for `norm_sq_eq_of_L2` showed additional mathlib paths but only the listed `PiLp.lean` content was inspected. Attempted `BanditRLProof/Basic.lean` lookup was absent, so no content was read at that path.

Reused-definition byte fingerprints rechecked during packet-2 decoding:

| File | SHA-256 |
|---|---|
| `C:/qb261009/quantum/QuantumBlockEncoding/PrimitiveCircuit.lean` | `853ea17d56ffc5ba75d94c4f4197f26ca23db4c1ebd9fa613107230311d48458` |
| `C:/qb261009/quantum/QuantumBlockEncoding/PrimitiveSemantics.lean` | `3cb00be8b8fb982b772fcbf6c20efb6195f6fdfe49402dba49602a8867b8ca74` |
| `C:/qb261009/quantum/QuantumBlockEncoding/PrimitiveCircuitPerturbation.lean` | `92c3259a8a2a13ed46f84bc502e7156002e766fcd9d57c8604aa8f828e0eaac4` |
| `C:/qb261009/bandit/BanditRLProof/FiniteRealArgmax.lean` | `f599122d4a0a720d5ff8f7a86ac88dcde18f67ad7db684cfc0b2e6c7e9309a95` |
| `C:/qb261009/bandit/BanditRLProof/ProbabilityUnionBound.lean` | `b470c5c1c0a9db57d6bfb47c72e3fcc71a93b501d546f28a476dc11f8046e444` |
| `C:/qb261009/quantum/.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Matrix.lean` | `9a33f2ac6ab021ef61ee5c2178af394a805d9a4dd899254c7599c37c850cbf7a` |
| `C:/qb261009/quantum/.lake/packages/mathlib/Mathlib/Analysis/Matrix/Order.lean` | `18b0d5524ec8bae533b2893d326ad39796d0074ce51897f5e3e08ce81958e518` |
| `C:/qb261009/quantum/.lake/packages/mathlib/Mathlib/Data/ENNReal/Basic.lean` | `f4903d0f1646a4d6bef15badf2fed979bd81ef3c839456cb299d21911331f800` |
| `C:/qb261009/quantum/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean` | `fc598927771d9ee3f907c28f8a324fa0018a764335e5102c29c3c4cb8b15aaf1` |
