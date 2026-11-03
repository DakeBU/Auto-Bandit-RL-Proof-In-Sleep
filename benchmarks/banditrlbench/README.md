# BanditRLBench

Source-bound QA for training and evaluating bandit and reinforcement-learning knowledge and mathematical reasoning.

**0.0.1 development seed:** four mathematical cores, four natural-language views and two authored, compiler-checked Lean subtargets. This is a starting point, not an independently admitted gold dataset, full-library benchmark or measured model evaluation. RL question coverage is future work.

- [Read the benchmark](https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/banditrlbench/)
- [Without Lean](https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/banditrlbench/non-lean/) · [track guide](tracks/non-lean/README.md)
- [Lean companion](https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/banditrlbench/lean/) · [track guide](tracks/lean/README.md)
- [Core registry](cores.json) · [shared contract](CONTRACT.md) · [dataset card](DATASET_CARD.md) · [verification](VERIFICATION.md)

The website routes are introduced by this branch; they are not claimed live before merge and deployment.

From repository root:

```sh
python website/scripts/banditrlbench.py validate
python website/scripts/banditrlbench.py export --track non-lean --output _out/brb-nl-prompts.jsonl
python website/scripts/banditrlbench.py export --track lean --output _out/brb-lean-prompts.jsonl
lake env lean benchmarks/banditrlbench/lean/Reference.lean
```

Exports omit solutions and rubrics by default. Use `--include-solutions` only for intentionally released training/development material. Public solutions are folded in the reader, not secret. No paid model call, training run or model score is included.
