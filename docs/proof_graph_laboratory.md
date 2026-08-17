# Proof Graph Laboratory

## Evidence status

This laboratory has five deliberately separate status words:

- **compiled**: a declaration was loaded from the checked Lean environment used by the exporter;
- **prototype**: executable analysis code and focused tests exist, but the model is not a theorem of
  Lean or a validated scientific instrument;
- **partial**: some target obligations are discharged, but the declared target is not complete;
- **planned**: a contract or evaluation is specified without an implementation/result;
- **blocked**: a named obligation and blocking reason have been recorded.

The environment exporter and the three benchmark roots are compiled observations.  The proof-cost,
ZDD, hypergraph/MIP, and proof-structural novelty layers are prototypes.  CNG is now **partial**:
route-independent finite tangent, weighted min-shift, and signal–noise algebra compiles, but no
route-replacement, Pareto-shift, held-out-transfer, new CNG bandit theorem, or complete calculus is
claimed here.

## Audit result: the old website graph is not kernel extracted

At the frozen `origin/main` baseline, `website/scripts/build_site.py` scans Lean source with regular
expressions, reads manually maintained `depends_on` and teaching `dependencies`, and parses textual
imports.  `tools/bandit.py` has a separate source scanner.  The lifecycle DAG records task status and
fingerprints, not constant dependencies.  The static Mermaid diagram is explanatory.  None of those
is the direct dependency graph of compiled declaration types and values.

`tools/ProofGraphExport.lean` instead loads `BanditRLProof.olean` and traverses Lean's environment.
For every project-owned constant it exports:

- declaration name, namespace, kind, owning module, source path/range, and `compiled` status;
- direct constants in the type/signature;
- direct constants used only by the value/proof term;
- a type edge with `also_in_value = true` when the same target occurs in both places;
- shared-object counts for type and value expressions as representation-size proxies;
- direct module imports and their modifiers.

Project ownership comes from the environment's module index, not a name-prefix guess.
The analyzer preserves `type`, `value`, and derived `type+value` roles, so a dependency moving from
signature-only use into a proof term is not silently collapsed.
`ModuleData.constNames` can repeat generated equation/simp declarations, so names are canonicalized
through a set before serialization.  Arrays and edges are sorted, and no timestamp is emitted.

The closure is explicitly `project-direct-with-external-boundary`: every project source has its exact
direct constant occurrences, while directly referenced library constants are boundary nodes.  The
export does not unfold declarations, expand the transitive Mathlib graph, record elaborator tactic
states, or prove target faithfulness.  “Environment extracted” is the accurate phrase; “kernel trace”
would overstate the result.

## Running the exporter

Build the checked root library, then run the Lean source through the interpreter:

```text
lake build BanditRLProof
lake env lean --run tools/ProofGraphExport.lean --compact proof-graph.json
python tools/proof_graph_lab.py validate-export --graph proof-graph.json
python tools/proof_graph_lab.py benchmark --graph proof-graph.json \
  --config research-wiki/proof-graph/benchmark_roots.json \
  --measurements research-wiki/proof-graph/benchmark_measurements.json \
  --output benchmark-report.json
python tools/proof_graph_lab.py candidate-audit --frozen frozen.json \
  --candidate candidate-a.json --candidate-rerun candidate-b.json \
  --benchmark-config research-wiki/proof-graph/benchmark_roots.json \
  --candidate-config research-wiki/proof-graph/cng_candidate_roots.json \
  --output cng-candidate-evaluation.json
```

`lake exe proof_graph_export OUTPUT.json` is also configured.  The executable dynamically loads the
compiled `BanditRLProof` environment instead of statically linking the full project dependency
closure; `lean --run` remains the focused development path.  On Windows with long paths disabled,
use a genuinely short isolated checkout or a temporary short package build directory.  Changing a
drive letter alone may not help because Lake normalizes workspace paths.  Never reuse a different
dirty worktree's project `.olean` as evidence.

The repository/CI check also runs `lake env lean tools/ProofGraphExport.lean`, which elaborates the
exporter without executing the roughly 155 MB export.

The full JSON is intentionally a local artifact.  The versioned
`research-wiki/proof-graph/benchmark_report.json` contains its hash and compact results.

## External tool and license review

The implementation was designed after a read-only review of:

- [Lean Atlas](https://github.com/NyxFoundation/lean-atlas), commit
  `3a81e194db0e6c41a2a8c5286f9e1b4962c3866a` (MIT): it demonstrates environment traversal and a
  useful type/value dependency distinction.  Its “relevant constant” filtering is unsuitable for
  the exact project audit because it can omit generated/private declarations.  No Lean Atlas source
  was copied and no dependency was added.
- [import-graph](https://github.com/leanprover-community/import-graph) (Apache-2.0): already present
  through Mathlib and appropriate for module import graphs, but it does not supply the required
  declaration type/value graph.

A small native exporter keeps the interface replaceable and avoids introducing a heavy framework.
If a maintained upstream format later satisfies the exact contract, the deterministic JSON schema
and black-box tests should remain the compatibility boundary.

## Library-aware proof cost

Correctness and target faithfulness are hard constraints, not cost dimensions that can be traded
away.  Among faithful checked candidates, the cost stays a vector/Pareto record:

- nonnegative new-declaration count;
- nonnegative shared-lemma fixed charges, charged once in a route union;
- reuse coverage reported separately, never subtracted as an unbounded negative reward;
- semantic graph nodes, edges, SCC condensation, and depth;
- proof-term shared-object proxy;
- separately measured Lean check time and command/environment;
- typed open obligations and their statuses.

The JSON Schema is `research-wiki/proof-graph/proof_cost.schema.json`.  The fixed benchmark uses one
existing compiled terminal each from EXP3 realized all-time regret, half-Tsallis finite-arm IID
logarithmic regret, and OFUL all-time confidence.  It does not edit the theorems or imply that the
entire algorithm family has been formalized.

`benchmark_measurements.json` records one warm-dependency local wall-clock check per terminal module,
including the command, Lean/OS/processor context, repetition count, and short temporary build root.
These seconds are diagnostic observations on one machine, not a machine-independent proof-cost
constant; comparisons must keep the protocol fixed and disclose cache and repetition policy.

## ZDD boundary and ordering experiment

The prototype ZDD stores only a finite family of minimal support sets over a fixed declaration
universe.  Dependent proof state, metavariables, unification constraints, tactics, and open goals stay
outside it.  An explicit-set representation is the correctness baseline.  The implementation has a
replaceable `ZDD` interface, zero suppression, a unique table, exact family counting, small-family
round-trip tests, and lexical/frequency/first-seen ordering experiments.  Reported memory is local
Python `tracemalloc` peak plus deterministic serialized-size proxies, not a universal memory model.

## Hypergraph relaxation and safe lower bounds

An obligation owns one or more alternative support hyperedges; vertices are library declarations
with nonnegative fixed charges.  A concrete completion selects at least one alternative for every
obligation and pays for the union.  It maps to the relaxation by setting selected alternative
variables and union vertex variables to one.  Focused tests enumerate a small model and check this
mapping.

The current admissible bound is `max_o min_e cost(e)`, optionally summed over a set of obligations
whose complete alternative universes are pairwise disjoint.  Every completion contains a selected
edge for every obligation, so these nonnegative-cost bounds cannot exceed the remaining optimum.
Only a bound with an established `LB(s) <= OPT_remaining(s)` contract may be used for safe pruning.
The MIP schema is a library planner/scheduler; it is not and must not be described as a Lean
elaborator.

## Proof-structural novelty audit

Formal coverage alone does not establish a proof-technical contribution.  The versioned
`research-wiki/proof-graph/novelty_audit.json` freezes the library at a graph hash and separates:

1. conditional residual signatures for lemma motifs, hyperedges, obligation types, and composition
   constraints, with irreducibility requiring separate evidence;
2. backward compression of already existing routes;
3. non-scalar proof-cost Pareto-frontier changes;
4. transfer to theorem families held out from abstraction design;
5. target novelty from proof novelty.

Raw new-node count is excluded from novelty because naming, helper lemmas, and splitting can
manipulate it.  A target-faithful statement/assumption fence, fixed canonicalization/compression,
retrospective landmark-versus-incremental cases, held-out transfer, ordering/compression ablations,
and blind human interpretability review are mandatory.  The proposed neutral labels are `coverage
extension`, `library consolidation`, `new proof route`, `reusable abstraction`, and `cross-family
conceptual compression`.

CNG is a falsifiable candidate abstraction.  Restating a Tsallis-INF derivation is insufficient.  It
can become structural-discovery evidence only after a compiled, target-faithful interface replaces
multiple audited route-specific subgraphs, improves the declared cost vector with a reported Pareto
relation, and helps a held-out theorem family or unlocks a blocked obligation.  Until those tests are
run, its structural-novelty result fields remain `prototype-no-candidate-result` or `planned`.

## Partial CNG algebra layer

`BanditRLProof/CurvatureNoiseGapGeometry.lean` is deliberately independent of Tsallis-specific and
bandit-specific definitions.  It compiles constant-shift invariance on finite zero-sum tangent
directions, the weighted-center residual and completed-square characterization, minimum and
uniqueness under explicit total-weight assumptions, and exact/bounded signal–noise decompositions.
Its focused external canary is `Tests/CurvatureNoiseGapGeometry.lean`.

These leaves are evidence of a target-faithful algebraic interface only.  The versioned candidate
audit compares the post-CNG graph with the frozen graph.  A two-round name-independent
Weisfeiler--Lehman-style proxy sees 9 color signatures and 5 direct-support signatures absent from
the frozen library, but those signatures do not prove semantic irreducibility.  All three frozen
benchmark closures remain byte-identical as support sets, no existing declaration depends on a new
CNG declaration, and held-out OFUL contains zero CNG declarations.  Thus current backward
compression and held-out transfer are **not demonstrated**, the full cost-vector Pareto relation is
**not assessed**, and structural discovery is **not established**.
The constrained-cometric target and actual route replacement remain planned.

## Non-overlap boundary

This laboratory does not edit or advance Lattimore–Szepesvári Chapters 13–17, finite-arm lower
bounds, Bernoulli-KL/change-of-measure/minimax/asymptotic lower-bound declarations, their
task/blueprint/retrieval cards, Textbook Spine pages, or the other task's active frontier.  Existing
modules may be loaded by the root library, but they are not benchmark roots or mutation targets.
