# Terminal point in Be-The-Regularized-Leader

[Orabona v10, Algorithm 15.9 and Theorem 15.31](https://arxiv.org/pdf/1912.13213v10#page=278) select a feasible minimizer after the current loss is revealed. The printed movement sum refers to one point beyond the last round. The corrected theorem keeps every played point and repeats the last one for that extra index. The movements and the regularizer drift then range over actual transitions only. The proof also gives the final negative quadratic term at the comparator. A second theorem supplies a unique feasible minimizer at each actual round.

The [source contract](source-contract.json) gives the original and repaired readings, frozen statements, dependencies and four concrete test contracts. The [candidate evidence](candidate-evidence.json) records the focused declaration fingerprints, axioms, actual parent applications and original comparison failures. These results are used by the Chapter 2 dependency map; they do not close either chapter.

The implementation is in [OnlineBTRLTerminal](../../../BanditRLProof/OnlineBTRLTerminal.lean) and the examples in [OnlineBTRLTerminalCanary](../../../Tests/OnlineBTRLTerminalCanary.lean). From the shared Lake project:

```sh
lake build BanditRLProof.OnlineBTRLTerminal Tests.OnlineBTRLTerminalCanary
python tools/bandit.py check
```
