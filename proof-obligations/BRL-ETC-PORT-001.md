# Proof Obligations: BRL-ETC-PORT-001

| Node | Target | Dependencies | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `ETC-CORE` | verify exploration-arm finite selector | ABRL core | reviewer | `ETC.exploreArm_val` | check | compiled |
| `ETC-COUNT` | prove round-robin pull-count arithmetic | `ETC.exploreArm` | lower Lean | TBD | build | planned |
| `ETC-COMMIT` | define empirical-mean argmax commit | finite history | middle/lower | TBD | build | planned |
| `ETC-CONC` | wrong-commit probability bound | sub-Gaussian cards | retrieval | TBD | memory/build | obligation |
| `ETC-FINAL` | local theorem compatible with `Bandits.ETC.regret_le` | all above | lower Lean | TBD | build | blocked |
