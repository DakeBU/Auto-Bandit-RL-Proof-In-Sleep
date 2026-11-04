# BanditRLBench

Source-bound QA for training and evaluating bandit and reinforcement-learning knowledge and mathematical reasoning.

**0.0.1 development seed:** four mathematical cores, four natural-language views and two authored, compiler-checked Lean subtargets. This is a starting point, not an independently admitted gold dataset, full-library benchmark or measured model evaluation. RL question coverage is future work.

- [Read the benchmark](https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/banditrlbench/)
- [Without Lean](https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/banditrlbench/non-lean/) · [track guide](tracks/non-lean/README.md)
- [Lean companion](https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/banditrlbench/lean/) · [track guide](tracks/lean/README.md)
- [Core registry](cores.json) · [shared contract](CONTRACT.md) · [dataset card](DATASET_CARD.md) · [verification](VERIFICATION.md)

The original overview and QA readers are published. This increment adds run/training and expert-review routes, graph node links, fixed-target submissions and trusted-local proof replay.

From repository root:

```sh
python website/scripts/banditrlbench.py validate
python website/scripts/banditrlbench.py export --track non-lean --output _out/brb-nl-prompts.jsonl
python website/scripts/banditrlbench.py export --track lean --output _out/brb-lean-prompts.jsonl
lake env lean benchmarks/banditrlbench/lean/Reference.lean
```

Exports omit solutions and rubrics by default. Use `--include-solutions` only for intentionally released training/development material. Public solutions are folded in the reader, not secret. No paid model call, training run or model score is included.


## Run and review

- [Run and train](https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/banditrlbench/run/)
- [Expert review and graph locations](https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/banditrlbench/review/)
- [Environment and isolation boundary](ENVIRONMENT.md) · [Contribute a family](CONTRIBUTING.md)

```sh
python tools/banditrlbench.py prepare --track non-lean --mode closed-book --model YOUR_MODEL --agent YOUR_AGENT --output _out/nl-run
python tools/banditrlbench.py review-pack --predictions _out/nl-run/predictions.jsonl --output _out/review
# Expert fills review.jsonl; keep reviewer gold outside agent inputs.
python tools/banditrlbench.py assess --predictions _out/nl-run/predictions.jsonl --review _out/review/review.jsonl --output _out/nl-results
python tools/banditrlbench.py prepare --track lean --mode lean-assisted --model YOUR_MODEL --agent YOUR_AGENT --output _out/lean-run
# Fill proof expressions in predictions.jsonl after building the pinned library.
python tools/banditrlbench.py replay --trusted-local --library . --mode lean-assisted --model YOUR_MODEL --agent YOUR_AGENT --predictions _out/lean-run/predictions.jsonl --output _out/lean-results
python tools/banditrlbench.py canary --trusted-local --library . --output _out/canary
```

Outputs bind question, exact formal signature, prediction and environment identities.
Replay logs axioms and actual direct type/proof constants. It executes trusted Lean
code and is **not a sandbox**. The local access mode is an operator declaration;
no closed-book policy is mechanically enforced. See the environment document before
using any generated proof. Current dev training exports require explicit solution
opt-in and never create a held-out test set.
