# Proof Obligations: BRL-UCB-PORT-001

| Node | Target | Dependencies | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `UCB-ROUTE` | choose card-only, port, or dependency route | task packet | upper | no Lean declaration | memory | planned |
| `UCB-CORE` | verify ABRL finite trace and pseudo-regret surfaces | `BanditRLProof.Core`, `Regret` | reviewer | `pseudoRegret_succ` | `python3 tools/bandit.py check` | compiled |
| `UCB-INDEX` | replace placeholder score with UCB width when dependency layer is selected | route decision | lower Lean | TBD | build | blocked |
| `UCB-CONC` | record or prove sub-Gaussian tail lemmas | concentration cards | lower retrieval | TBD | memory/build | obligation |
| `UCB-FINAL` | local theorem compatible with `Bandits.UCB.regret_le` | all above | lower Lean | TBD | build | blocked |

## Current Reviewer Note

The upstream LML theorem is a theorem card only.  Do not export it as an ABRL
local proof until the route is imported or ported.
