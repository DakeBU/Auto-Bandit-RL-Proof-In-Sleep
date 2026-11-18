# First reproducible expansion proposal

Six **draft, public-dev** task packages extend the four legacy cores. They are
reviewable development and opt-in training material, not an admitted benchmark
release. No model performance or Harbor execution is claimed.

| Family | Knowledge / understanding | Reasoning | Agentic Lean target |
| --- | --- | --- | --- |
| `iw-variance-v1` | `BRB-IW-K`: support, sampling law, predictability | `BRB-IW-R`: variance derivation and a false bounded-estimator argument | `BRB-IW-L`: normalized signed-weight centered moment |
| `bellman-evaluation-v1` | `BRB-BE-K`: terminal data and fixed-policy semantics | `BRB-BE-R`: backward uniqueness and a false contraction argument | `BRB-BE-L`: uniqueness of the library's finite-horizon evaluation |

The schema abilities remain `knowledge`, `reasoning`, and `agentic-lean`.
`factual-accuracy` and `understanding` are distinct rubric axes, not new schema
ability labels. Every criterion scores 0/1/2 with a reason. Accept equivalent
notation, other valid proofs and counterexamples. The reference-control pass
requires all NL criteria to be complete; it is not a reported system score.

## Sources, reuse and seals

Library/source snapshot: `abc2959ff7c866c47e8bee5714d43a336a857353`.
Lean: `leanprover/lean4:v4.29.1`; dependencies: that snapshot's `lake-manifest.json`.
Each task records exact source hashes, declaration IDs, source links and graph
navigation links. Files are original MIT benchmark material using the MIT
repository. No book or paper text is redistributed.

The statement and binder audit is in [PLAN.md](PLAN.md); exact formal statements
are in each Lean package's `environment/workspace/target.json`. Intake seals
bind the four required contract files; the environment manifest additionally
binds the target, proof, rubric, controls and executable entry points. LF line
endings are pinned for portable artifact hashes. The runner checks these extra
bindings before replay. These seals detect changed artifacts; they are not a
security boundary or semantic certificate.

The permitted IW corpus already includes
`BanditRLProof.Exp3.sum_prob_mul_sq_comparatorEstimatorDeviation_eq`, a
near-complete solution with the stronger `FiniteActionDistribution` premise.
Its proof uses only normalization. It is recorded as a family solution alias;
IW-L is retrieval/adaptation, with unmeasured difficulty. Its signed-weight
identity is not by itself a probability/conditional expectation guarantee.
BE-L reuses the library's chronological recursion and terminal API through
backward induction, without a supplied solution lemma. No production theorem,
chapter status, or library root is changed. Source correspondence is an overlay;
only replay-exported type/value constants are compiler-backed dependency evidence.

## Reproduce

Use Python 3.11+, Git, and the committed Lean toolchain/lock. On Windows set
`PYTHONUTF8=1`; the tested interpreter reports Python 3.13.5. Existing declaration-boundary
file hashes also require the repository's Git/LF source bytes. Use an LF checkout
(`git -c core.autocrlf=false clone ...`) rather than rehashing those boundaries.
Use a fresh output directory for each command. The final evidence records exact
commands, runtimes, results and artifact hashes.

```bash
python tools/bench_task_contract.py validate-all
python -m unittest tools.test_bench_expansion tools.test_bench_task_contract
python tools/bandit.py check
for task in BRB-IW-K BRB-IW-R BRB-IW-L BRB-BE-K BRB-BE-R BRB-BE-L; do
  python tools/bench_expansion.py controls --task "$task" --library . --output "_out/expansion/$task" --trusted-local
done
python tools/check_process_memory.py check
python tools/check_contributor_contract.py --base abc2959ff7c866c47e8bee5714d43a336a857353
python website/scripts/build_site.py --lean-verified
python website/scripts/check_site.py
git diff --check
```

Lean control `pass` means only the fixed target passed the kernel and allowed
axiom audit. Agentic rubric criterion c2 (authentic exploration and construction)
is separately reviewed; compilation alone never grants it. Local mutation,
axiom, tampering, spoofing, tiny-deadline and visible-file leakage controls test
specific code paths. They do not establish adversarial isolation. The timeout
probe deliberately forces a 1 ms startup deadline; it does not certify a full
process-tree kill. Untrusted Lean must not be executed on a credentialed host.

The reference and verifier entry points live in `solution/solve.py` and
`tests/verify.py`, outside `instruction.md` and `environment/workspace/`.
For trusted local proof development:

```bash
python benchmarks/banditrlbench/tasks/BRB-BE-L/solution/solve.py --output _out/reference-answer.txt
python tools/bench_expansion.py verify --task BRB-BE-L --answer _out/reference-answer.txt --library . --output _out/submission-check --trusted-local
python tools/bench_reference_trajectory.py --task BRB-BE-L --output _out/reference-trajectory
```

The trajectory command captures actual searches, Lean API queries and replay of
the preauthored reference. Its scope receipt explicitly excludes earlier author
construction history and independent agent evaluation; it does not close c2.

For NL submissions, supply `--review REVIEW.json` from a distinct reviewer,
using the `tests/review.json` schema with a `submission` key and hashes of the
actual answer/rubric. This validates review bindings and arithmetic; it does
not authenticate an expert, establish correctness automatically or calibrate
a judge. The bundled fixture reviews are independent **agent** reviews.

## Training, access and reporting

```bash
python tools/bench_expansion.py export --output _out/prompt-only
python tools/bench_expansion.py export --include-solutions --output _out/opt-in-training
```

Prompt-only output contains only instructions and agent-visible files. Training
solutions require the explicit flag and produce a differently named file. All
variants, NL/Lean views and solution aliases stay with their family in dev.
Existing public near-solutions exclude these families from future unseen-test
claims. The runner rejects non-dev export; no protected prompt or answer exists
in this PR. A future held-out family requires access enforcement before exposure.

No pilot model trials are bundled. Future authorized trials must record model
and agent versions, exact settings/seeds, budgets, trajectory and artifact hashes,
resource use, mathematical failure types, repetitions and denominators. Report
knowledge/factual, understanding, reasoning and agentic outcomes separately,
and separate closed-book, text-retrieval, graph-retrieval and Lean-assisted
conditions. These drafts declare closed-book NL and Lean-assisted Lean only;
they do not provide measurements in the other conditions. Human rubric agreement
and judge calibration must precede any automatic-judge score publication.

## Admission

See [gates.json](gates.json) for individual gates and evidence. Distinct author,
blind decoder and source reviewer reports are in [reviews](reviews). Agent
semantic review cannot substitute for independent human expert gold admission.
Keep the packages draft. Maintainers may promote only after all protocol gates
are met and admit only through a separately versioned, reviewed suite manifest.
`families.json` is a draft inventory, not that release manifest. Corrections must
retain prior versions, record appeals and create explicit successors for changed
questions. This PR does not merge or deploy the public site.
