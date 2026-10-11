# BanditRLlib: human understanding in Math 2.0

BanditRLlib connects sequential-learning mathematics, source-aligned explanations
and Lean evidence. Its central purpose is to help readers understand why a
guarantee holds, reuse its proof ideas, and see where its assumptions stop applying.
ABRL is the proof/review harness; BanditRLlib is the maintained mathematical library
and reader interface.

This position responds to Terence Tao's [*Math 2.0* report, October 2026](https://teorth.github.io/tao-web/slides/math-2-0-caltech-2026.pdf),
especially pp. 21–22 and 25–26. The nine directions on the
[public positioning page](https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/math-2-0/)
are our organization of his examples, not an official nine-goal program or an
endorsement of these libraries.

## Priority and library roles

1. **Foundations (2, 3):** a living, source-linked knowledge network and a
   high-quality reusable Lean library.
2. **Human value (1, 8):** clearer explanations and interactive teaching, using
   compressed proof spines and conceptual maps with drill-down to exact evidence.
3. **Research agenda (4, 5, 6, 7, 9):** cross-pollination of proof methods,
   controlled ablation, verified theorem neighborhoods, inspectable material for
   specialized models, and analysis of mathematical/model boundaries.

Samplinglib contributes sampling and analytic mechanisms; QuantumComputinglib
contributes quantum semantics and oracle interfaces; BanditRLlib contributes
feedback models, sequential decisions and regret/sample-complexity guarantees.
Cross-library links express a research agenda until compatible imports or compiled
adapters prove the transport. The three libraries share a purpose, not a claim of
identical maturity or interchangeable foundations.

## Public claims and evidence

The canonical positioning data lives in `website/content/math_2_0.json`. Every
direction keeps **current foundation** separate from **next contribution**, with
links to existing evidence. Update the data before revising public copy.

- Say “explains”, “organizes” or “supports” when describing an existing interface;
  say “aims”, “planned” or “next” for unfinished mathematical/research outcomes.
- Keep local Lean compilation, source-fidelity review, route completion and
  conceptual transport independent. A graph view is not a source-fidelity audit.
- An ablation freezes the conclusion and source assumptions, classifies proof
  ingredients, removes a theory/input, and checks a replacement proof route.
  Encoder–denoiser review helps preserve meaning but is not an ablation by itself.
- A theorem-neighborhood experiment changes a hypothesis contract explicitly and
  records a new proof, a checked counterexample, or an unresolved target. Failure
  of proof search alone is not a negative mathematical result.
- A compressed graph and natural-language/Lean pair are proposed research and
  model resources. Do not claim a trained model, a validated data set, faithful
  internal chain-of-thought access, or guaranteed interpretability/safety without
  corresponding evidence. Tao's slides do not make a white-box chain-of-thought
  requirement.
- Use only our own or appropriately licensed source/proof/exposition pairs for
  model work. External-reference libraries are not automatically training data;
  preserve their attribution and use restrictions, including ATLAS v1's CC BY-NC
  rider where applicable to cross-library references.
- Proof structure may reveal reusable mechanisms and help assess contributions;
  graph size or compression is not an automatic novelty or scientific-value score.
- Formal proofs and counterexamples examine the specified mathematical model.
  Whether a real environment satisfies the model requires external evidence.

This communication protocol supplements the theorem-publication and
proof-digestion protocols; it does not change theorem acceptance gates.
