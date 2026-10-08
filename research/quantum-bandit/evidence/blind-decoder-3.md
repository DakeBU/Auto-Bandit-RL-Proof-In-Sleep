# Independent source-blind decoding: packet 3

## Method, restriction, and status

This report reconstructs the formal declarations and canary meanings in `decoder-packet-3`. Lean line comments and nested block comments were removed before source content was displayed. Only types, definitions, proof terms, and needed dependency definitions were used. No prose comments, evidence seals, user specification, author summaries, literature, or reviewer feedback supplied evidence of intended meaning. Procedural requests were not treated as a mathematical specification or certification.

No compilation was run by this decoder; no kernel acceptance or publication verdict is given. The canary's commands are recorded as commands in source, not as observed successful executions. The first two reports were not edited or used as author evidence. Previously inspected formal dependency definitions were reused after matching their hashes.

The process file contains 11 explicitly named public mathematical declarations. The canary contains seven private named declarations and five anonymous examples, all described below. Automatically generated structure projections are included with `Plan` rather than listed separately.

## Dependency meanings needed for this packet

An index type `ι` is finite with decidable equality. Vectors are in complex Euclidean space on `ι`, and matrices use Euclidean operator norm. A quantum query word is a finite list of known exact unitary matrices, forward oracle markers, and inverse markers. A known matrix has query cost zero; forward and inverse each have query cost one. Evaluation gives the known matrix, the supplied oracle matrix, or its adjoint, respectively, composed in list order. Under unitary oracle assumptions the adjoint is the inverse. Syntactic query count includes redundant and cancelling occurrences.

`BasisHellinger.basisProbability x j` is `‖x_j‖²`. These values are nonnegative, and their finite sum equals `‖x‖²`. A unit vector therefore supplies normalized weights. `BasisHellinger.wordOutput w U ψ` is the vector obtained by applying the evaluated word to `ψ`, and unitary word evaluation preserves its norm.

The inspected mathlib definitions specify:

- `PMF α` is a function `α → ℝ≥0∞` together with a proof its sum is one.
- `PMF.ofFintype f h` uses the supplied finite weights `f` and finite-sum normalization certificate `h`; its value at an index is exactly `f` there.
- `p.support` is the set where `p` is nonzero, equivalently where its mass is positive. This is positive-mass support, not topological support or a general measurability predicate.
- `PMF.pure a` places mass one at `a` and zero elsewhere.
- `p.bind f` has mass at `b` equal to `∑' a, p(a) · f(a)(b)`. A point is in its support exactly when it is supported by `f(a)` for some supported `a`.

Thus the use of `PMF` adds normalized discrete probability laws to the previously scalar basis weights. It does not implement a numerical sampler. No measurable-space instance or external arbitrary `Measure` is required for these discrete PMF declarations.

Write `q(w)` for word query count, `B_x(j)=ofReal(‖x_j‖²)`, and `L_n` for `historyLaw ... n`. Natural parameters are universally quantified along with all explicit arguments and certificates. An actual plan contains `arm : Fin K`; a policy defined on all lists consequently requires an inhabited arm set even though no explicit nonempty instance is listed. A unit vector excludes an empty basis in any feasible instantiation.

## Seven-slot reconstruction: ResetBlockProcess.lean

Namespace: `QuantumBlockEncoding.ResetBlockProcess`. All rows inherit finite `ι` and decidable equality. `None` in the cost slot means no resource bound appears in that declaration, not that implementation is free.

| Declaration | Objects | Parameter range | Assumptions | Quantifiers | Output | Costs | Claim scope |
|---|---|---|---|---|---|---|---|
| `basisPMF` | Euclidean vector `x`, normalization certificate `hx` | Finite `ι`; `x : EuclideanSpace ℂ ι` | `‖x‖=1` | Every unit vector and certificate | A `PMF ι` with coordinate weights `B_x(j)` | None | Noncomputable normalized finite basis-outcome law. Nonnegativity means `ofReal` does not alter the weights. No sampler or physical measurement implementation is constructed. |
| `basisPMF_apply` | `x,hx,j` | Same vector context, `j:ι` | `‖x‖=1` | Every unit vector, certificate, coordinate | `basisPMF x hx j = ofReal(‖x_j‖²)` | None | Exact pointwise mass identity, proved by definitional equality. |
| `Plan` (fields `arm`, `word`, `bounded`) | Arm label, matrix query word, count certificate | Natural `K,D`; `arm:Fin K`; word on `ι` | Stored `q(word)≤D` | Type of all such records | Bounded arm/word plan | Per-plan cap `D` on forward-plus-inverse markers | Plan now pairs arm and word in the same record. Known matrices remain arbitrary supplied exact unitaries and are free under query cost. No parallel-depth, primitive-gate, or bit bound is stored. |
| `blockPMF` | Plan, family of unitary oracles, common input vector/certificate | Natural `K,D`; `oracle:Fin K→Matrix.unitaryGroup ι ℂ` | Unit vector; plan's stored count bound; oracle unitarity encoded in oracle type | Every plan/oracle family/unit vector | Basis PMF of `wordOutput plan.word (oracle plan.arm) ψ` | No cost theorem here; count cap remains in plan | New direct arm-to-oracle connection: the record's arm chooses the matrix used in every forward/inverse slot of its word. The same supplied `ψ` is used for the block. No reward mean or scalar estimator is assigned to the outcome. |
| `blockPMF_apply` | Previous objects plus outcome `j` | Same ranges | Same type/certificate requirements | Every plan/oracle/input/outcome | Point mass is `ofReal(‖(wordOutput plan.word (oracle plan.arm) ψ)_j‖²)` | None | Literal probability of that basis outcome, not just an upper bound or symbolic event name. |
| `historyLaw` | Deterministic classical policy, oracle family, fixed input vector/certificate, round count | Natural `K,D,n`; `policy:List ι→Plan K D ι` | Unit input; unitary oracle family; bounded plans supplied by policy | Every such policy/family/input and every finite `n` | PMF on outcome lists, with `L_0=pure []`; `L_{n+1}` mixes supported histories `h`, samples from `blockPMF(policy h)`, and appends outcome `j` | No total count conclusion inside definition | Noncomputable adaptive classical history law. Policy can change arm and entire word based on the full prior outcome list. Every new block starts again at the same fixed `ψ`; previous quantum output vectors are not carried forward. Only classical outcomes are stored. No randomized policy constructor, coherent cross-block state, stopping-time rule, or sampler is supplied. |
| `historyLaw_length_support` | Policy, oracle family, fixed input, round `n`, history `h` | Same context; `n:ℕ`; arbitrary list `h` | `h ∈ L_n.support`, plus input/type conditions | For every process, every `n`, and every supported history | `h.length=n` | Round/history-length identity | All positive-mass histories have exactly one appended outcome per round. It does not assert that every length-`n` list has positive mass. Proof follows support of bind and pure, not a computation of all path probabilities. |
| `historyQueryCost` | Policy, arbitrary history list `h` | Natural `K,D`; any `h:List ι` | No probability/support condition | Every policy/history | `∑_{t<h.length} q((policy (h.take t)).word)` | Prefix plan query counts summed once per recorded outcome | Deterministic query charge on a history. Uses each prior prefix, including empty prefix at round zero. Forward/inverse both cost one; known gates, preparation/reset, measurement, policy computation, and classical memory costs are omitted. Defined even for zero-probability histories. |
| `historyQueryCost_le` | Policy, arbitrary history | Natural `K,D`, finite list `h` | Only each plan's stored cap | Every policy and every list | `historyQueryCost policy h ≤ h.length · D` | Worst-case per-round-cap accumulation | Pathwise arithmetic bound, without oracle or state inputs. Support membership is unnecessary here. |
| `historyLaw_queryCost_le` | Process, round `n`, supported history `h` | Same process context; natural `n` | Unit input and oracle/plan type conditions; `h∈L_n.support` | Every process/round and every supported history | Query charge is at most `nD` | Total query budget for `n` blocks | Combines support length with prefix-cost bound. It is a pointwise statement on positive-mass histories; no expectation or concentration theorem is required or given. |
| `historyLaw_queryCost_le_budget` | Previous objects plus target budget `T` | Natural `n,T,K,D` | Previous type/support conditions; supplied `nD≤T` | Every such process, rounds, budget certificate, supported history | Query charge is at most `T` | Supplied total cap `T` | Sufficient deterministic budget implication. Does not derive a stopping rule, maximize number of rounds, or prove every feasible process must satisfy `nD≤T`. |

## Literal probability/history behavior

Expanding the inspected `bind` definitions gives the following semantic identity, stated here as a reading of definitions rather than an extra theorem proved by the packet:

`L_{n+1}(z) = ∑'_h L_n(h) · ∑'_j blockPMF(policy h)(j) · 1[z = h ++ [j]]`.

Consequently, a generated list is in chronological order. The next block's plan depends on the existing list before the new outcome is appended. Each block uses the same oracle family and freshly supplied input vector; the policy can choose a new arm and word, but cannot recover or retain the previous quantum state through this type. Positive-probability histories use exactly the prefix plans appearing in `historyQueryCost`. A particular list's recursively generated weight is determined by its sequence of conditional block masses; arbitrary plans on unreachable histories do not change supported path masses, though `historyQueryCost` still assigns those histories a charge.

This is a classical adaptive reset-block model with a unitary circuit within each block and a basis outcome at block end. Outcomes need not be independent, because the policy can depend on prior outcomes. A constant policy fixes the same conditional outcome PMF each round in this construction. The definitions do not model entanglement across blocks, coherent adaptive measurements within a word, arbitrary POVM measurements, mixed-state initialization, changing input states, randomized internal policy state, or reward observations separate from basis labels.

## Seven-slot reconstruction: ResetBlockProcessCanary.lean

These are source statements, not observed execution results. Private definitions and lemmas are included because their literal meanings determine the examples. The basis is `Fin 2`; arms are `Fin 1`; the plan cap is three. `e₀` and `e₁` denote the two coordinate unit vectors.

| Declaration / example | Objects | Parameter range | Assumptions | Quantifiers | Output | Costs | Actual meaning |
|---|---|---|---|---|---|---|---|
| private `xOracle` | Explicit matrix | Two-dimensional complex space | Stored proof that `!![0,1;1,0]` is unitary | One fixed object | Unit swap matrix `X` | None | Exact bit-swap oracle, not an arbitrary or perturbed unitary family. |
| private `oneQubitPlan` | Fixed plan | `K=1`, `D=3`, basis `Fin 2` | Stored boundedness proof | One fixed object | Arm zero and word `[forward,forward,inverse]` | Three query markers | All calls use the only arm. No known gates; two forward and one inverse occurrence. |
| private `zeroState` | Fixed vector | Complex Euclidean `Fin 2` | None in definition | One fixed object | `PiLp.single 2 0 1 = e₀` | None | Exact coordinate input state. |
| private `zeroState_norm` | `zeroState` | Same | None | One fixed statement | `‖e₀‖=1` | None | Normalization certificate for constructing PMFs. |
| first anonymous `example` | Fixed plan word | Same fixed plan | None | One fixed identity | `q(word)=3` | Exact syntactic count three | Confirms inverse marker is included even though the word later simplifies semantically. |
| private `eval_plan` | Fixed word and `xOracle` | Same fixed objects | Unitarity carried by oracle | One fixed identity | `E(word,X)=X` | No revised cost | The product is `X* · X · X`, simplifying by unitarity to `X`. Equivalent action does not reduce the syntactic count from three. The printed theorem specializes to `X`; the algebraic cancellation in its proof does not need `X`'s special entries. |
| private `output_plan` | Word, swap oracle, zero input | Same fixed objects | None beyond stored definitions | One fixed identity | Word output is `e₁` | None | Literal vector result from swapping `e₀`. |
| private `block_plan` | Block PMF of fixed plan/oracle/input | Same fixed objects | Unit-input certificate | One fixed identity | `blockPMF = PMF.pure 1` | Three-marker plan | Outcome one has mass one; outcome zero has mass zero. This is a deterministic block outcome, not a noisy statistical test. |
| second anonymous `example` | Constant policy/oracle family, zero input, two rounds | Fixed process, `n=2` | Unit-input certificate | One fixed law identity | `historyLaw ... 2 = PMF.pure [1,1]` | Cost proved separately | Both blocks restart from `e₀` and output one. It does not pass `e₁` into the second block; retaining the output state would produce different behavior for this oracle. |
| third anonymous `example (n)` | Fixed constant-policy process | Arbitrary natural `n` | Supported history | Every `n`, every history in its law's support | `length(h)=n` | Number of blocks | Applies general support-length theorem to this process. It does not establish an additional generic theorem about adaptive policies. |
| fourth anonymous `example` | Fixed constant policy and list `[1,1]` | Two-outcome list | None; support membership not required | One fixed identity | `historyQueryCost ... [1,1]=6` | Three queries per block, six total | Confirms raw forward-plus-inverse occurrence charging despite semantic cancellation. |
| fifth anonymous `example (n T) (hT)` | Fixed process, arbitrary round/budget parameters | Natural `n,T` | `3n≤T`; supported history | Every such `n,T`, certificate, supported history | Query charge `≤T` | Supplied cap on three-marker rounds | Instantiates general budget theorem. Does not derive an optimized or stopping-time budget. |

The canary therefore checks statement-level examples of normalization, oracle-word cancellation, deterministic basis outcome, two successive resets, support length, and syntactic cost. It does not exercise a policy that changes arm or word in response to history, nontrivial outcome randomness, differing oracle environments, zero-probability path estimates, or a statistical recommendation/regret bound. This describes the actual chosen example's coverage, not an inferred intended test requirement.

## Canary introspection commands

The source includes `#check` for `basisPMF`, `blockPMF`, `historyLaw`, `historyLaw_length_support`, and `historyLaw_queryCost_le_budget`. These request Lean's inferred declaration types if executed successfully.

It includes `#print axioms` for `basisPMF`, `blockPMF`, `historyLaw`, `historyLaw_length_support`, `historyLaw_queryCost_le`, and `historyLaw_queryCost_le_budget`. These request dependency-axiom information if executed successfully. No outputs of those commands were supplied or observed here. Their presence does not establish compile acceptance, an axiom list, absence of admissions, or certification.

## Connections and remaining boundaries

1. A normalized basis PMF and a history law now exist formally, rather than only normalized real weights. Arm labels directly select the oracle used in block evaluation. Policy selection can depend on full classical outcome history.
2. The process has an explicit reset boundary: the same `ψ` initializes every block; only basis labels are retained. This is not a quantum state carried between blocks. The constant-plan canary's law `pure [1,1]` distinguishes these two models in its literal result.
3. Query cost is based on the same policy-prefix words that define the transition law, and it is bounded on every supported length-`n` history. Thus a process-to-query-budget connection now exists. Its budget omits known-gate work, state preparation/reset, measurement, and classical control, and `D` is a query cap rather than a proved depth bound.
4. The imported Hellinger file supplies single-word basis-distance bounds, but this packet contains no theorem comparing two `blockPMF`s or two `historyLaw`s, no transcript Hellinger chain bound, no KL/likelihood theorem, and no adaptive information or sample-complexity conclusion.
5. This packet supplies no scalar reward map from outcomes, arm mean model, estimator, statistical tail theorem, recommendation algorithm, regret bound, accounting-block conversion, or finite-bit sampling implementation. Those cannot be inferred from a normalized PMF or a resource cap alone.
6. Boundedness is stored in each plan and used in query-budget proofs; it is not needed by the PMF formulas or support-length proof. Oracle unitarity and unit-input normalization make the block PMF construction valid. No explicit measurability assumptions are missing from the discrete PMF construction. Special cases can require fewer assumptions, but no globally unused new named theorem premise was identified.

## Exact inspected files and SHA-256 hashes

Packet files were inspected in full after comment stripping. New mathlib dependency definitions were inspected through targeted, comment-stripped excerpts. The two project dependency files listed as reused matched the already inspected formal content from earlier decoding. Imported dependencies were not exhaustively audited. No build was run to establish resolved dependency versions.

| File | SHA-256 | Inspection |
|---|---|---|
| `C:/qb261009/decoder-packet-3/ResetBlockProcess.lean` | `04c3f4fe802b250b6b8ca6f6aca63c002e723c3746e2b20ffbd71af20b16cde8` | Full formal source |
| `C:/qb261009/decoder-packet-3/ResetBlockProcessCanary.lean` | `ef6942b13e1a1981f7e1972e292b17dcd72b729fb9f03a8561deb541735ea21a` | Full formal source, including command text |
| `C:/qb261009/quantum/QuantumBlockEncoding/BasisHellinger.lean` | `7c53ae6d5a845829a2f1e41191d17973215cc1d76d5c1389a64c47eef43d64a5` | Byte fingerprint recheck; previously inspected formal content reused |
| `C:/qb261009/quantum/QuantumBlockEncoding/QuantumQueryWord.lean` | `c654b51820c11adf0039003dd76e2502e17f82847b56c8257e9489f21b46333b` | Byte fingerprint recheck; previously inspected formal content reused |
| `C:/qb261009/quantum/.lake/packages/mathlib/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean` | `67de8d28ee88f071053223e165c642a5067d5e073614e061b5b0df002baffeaf` | Targeted `ofFintype` definition/mass/support declarations |
| `C:/qb261009/quantum/.lake/packages/mathlib/Mathlib/Probability/ProbabilityMassFunction/Basic.lean` | `e31b47f86384cc969eaeed5405bfedec048e46d9b298f43f5505a9051291b4bc` | Targeted `PMF` and support definitions |
| `C:/qb261009/quantum/.lake/packages/mathlib/Mathlib/Probability/ProbabilityMassFunction/Monad.lean` | `0a0b2ae80a64b4b7960d95c722dc0589cce598b75c97fcb6cee8ac470779516b` | Targeted pure/bind definitions and mass/support identities |

Cost boundary cases from the definitions: `n=0` gives only the empty history and zero charged queries. A cap `D=0` permits words containing known gates only; repeated state preparation and basis outcomes can therefore occur with zero charged oracle queries. The budget statements count oracle markers, not total work.
