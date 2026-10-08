# Single-block coherent query-word handoff

Objective / frontier node: implement the frozen `QueryWordSeal.md` v1 contract,
at quantum HEAD `305952f4291d7be530c76f51f7e98d77faf1cf45`, Lean 4.29.1.
Applied repository `qbe-substantive-worker`; read AGENTS/HARNESS and the three
publication, proof-digestion, and evidence-memory protocols before coding.

Mathematical delta / root effect: a chronological word of individually certified
known unitary gates and forward/inverse calls to one fixed oracle now has derived
unitary evaluation, exact forward-plus-inverse query count, telescoping operator
error at most `q * η`, and normalized pure-state effect probability error at most
`2 * q * η`. A supplied actual query budget `q ≤ D` yields `D * η` and `2 * D * η`.
These are substantive single-block circuit semantics, not estimator or lower-bound
closure and not a cross-block reset/stochastic-process producer.

Named Lean evidence (namespace `QuantumBlockEncoding.QuantumQueryWord`):

- `queryCount_eq`: `queryCount = forwardCount + inverseCount`.
- `length_eq_costs`: instruction length = known count + query count.
- `eval_unitary`, `eval_append`: product certificate and chronological composition.
- `Instruction.eval_distance_le`: known gates cost zero; adjoint differences use
  Mathlib `norm_star` and `star_sub`.
- `eval_distance_le`, `bounded_eval_distance_le`.
- `probability_difference_le`, `bounded_probability_difference_le`: consume parent
  `BornStability.probability_difference_le` and internally derived word certificates.

Assumptions/conventions / binder audit: finite complex Euclidean basis `ι`
(TYPING), U/V unitary and operator-distance bound (SOURCE), each known gate is an
actual member of `Matrix.unitaryGroup` (SOURCE contract embedded in instruction
typing), normalized fresh ψ and Loewner effect `0 ≤ P ≤ 1` (SOURCE), and actual
query-budget premise for bounded corollaries (SOURCE). No EXCESS binder. No extra
nonnegativity assumption on η; it follows from the distance premise. Definitions
are literal. Lists run earliest instruction first: `eval (g::rest) U = eval rest U *
g.eval U`; inverse instructions denote `star U`, hence the inverse for unitary U.
Both oracle directions are charged even if their actions cancel. Known gates are
the same actual list for the two evaluations. Norm is L2 operator norm throughout.

Source / Lean expansion nodes: instructions → chronological products → product
unitarity; forward/adjoint norm difference → chronological telescoping; exact
query counts → budget transport; normalized input/effect + BornStability → bias.
All nodes of the scoped seal are covered. Initialization, end measurement/discard,
only classical inter-block history, estimator suppliers, and compiled finite-bit
resources remain outside this theorem's certified boundary.

Files changed:

- `C:\qb261009\quantum\QuantumBlockEncoding\QuantumQueryWord.lean`
  SHA256 `C654B51820C11ADF0039003DD76E2502E17F82847B56C8257E9489F21B46333B`.
- `C:\qb261009\quantum\ABEISTests\QuantumQueryWordCanary.lean`
  SHA256 `7E6EEFB0B6400D9FD226C25F3E135C4BAD6675D5F92CA88DAE282E7C3BC4048F`.
- This handoff. No roots/global metadata, original D-drive repository, or parent
  BornStability source modified; no push.

Exact focused commands, cwd `C:\qb261009\quantum`:

1. `lake env lean QuantumBlockEncoding\QuantumQueryWord.lean`: PASS exit 0 for
   the initial core without Born import.
2. `lake env lean -o .lake\build\lib\lean\QuantumBlockEncoding\QuantumQueryWord.olean QuantumBlockEncoding\QuantumQueryWord.lean`:
   first attempt ENV_BLOCKED exit 1 because `BornStability.olean` did not yet exist;
   retry after parent's dependency proof compiled PASS exit 0 for the final module.
3. `lake env lean ABEISTests\QuantumQueryWordCanary.lean`: first attempt
   IMPLEMENTATION_FAILED exit 1, because simp left `2*2*η` rather than `4*η`;
   replaced numeral normalization with `norm_num`; final retry PASS exit 0.
   Canary confirms two charged queries through heterogeneous interleaving,
   chronological matrix order, and actual `4*η` probability consumer.
4. Canary `#print axioms` for `eval_unitary`, `eval_distance_le`,
   `probability_difference_le`, `bounded_probability_difference_le`: only
   `[propext, Classical.choice, Quot.sound]`; no sorryAx/new axioms. Text audit
   found no sorry/admit/axiom declarations in either owned Lean file.
5. `lake build QuantumBlockEncoding.QuantumQueryWord ABEISTests.QuantumQueryWordCanary`:
   PASS exit 0, 3400 jobs; BornStability rebuilt (18s), QuantumQueryWord (17s),
   canary (23s). Same four standard-axiom-only reports emitted by canary.

Failure class: NONE for final focused kernel checks; full integration gates pending
Frontier Master. Salvage: all intended final nodes compiled; no discarded residue.
Reusable insight: CStarRing unitary multiplication preserves norms even for the
empty basis, avoiding an unnecessary nonempty-dimension binder or `‖U‖=1` premise.
Local reuse audit: prior `PrimitiveCircuitPerturbation` has the same chronological
telescoping mechanism but its RY-alignment carrier/count differs; reuse Mathlib's
unitary norm identities directly rather than misrepresenting a syntactic oracle
call as an approximate primitive RY instruction.

Process-memory IDs consulted: `QBE-PM-LOW-TOKEN-CONTROL-PLANE`,
`QBE-PM-VERIFIER-SEMANTIC-LEVEL`. Direction fingerprint:
`literal-list-word / chronological-product / fixed-U-and-star-U / true-query-cost`.
Expected information gain: close previously missing coherent-block semantics,
independently of estimator/supplier questions. Parent explicitly admitted this
worker for distinct uncertainty. Only one query-word route survives; no route
comparator or multi-route common-blind-spot audit applies here.

Purification / Exposition-Seal state: PROVED_LOCAL; independent source-blind
round trip, full repository `lake build` / `lake build Tests`, publication binding,
site gate and final purification remain with integration owner. No reader-facing
completion claim. Recommended merge: retain this literal exact-query word API,
run aggregate gates, and connect a genuinely initialized measured/discarded block
producer and classical-history protocol only when those obligations are proved.
Confidence: high for the kernel-checked single-block theorem; no confidence claim
is transferred to the explicitly open stochastic/estimator/lower-bound nodes.
