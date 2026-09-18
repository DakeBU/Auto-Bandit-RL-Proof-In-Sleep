# BanditRLlib collaborator contribution bootstrap

Use this as the common Codex/ChatGPT bootstrap for every collaborator.

Before planning or editing, pull the current target branch and read:

1. `AGENTS.md`
2. `CONTRIBUTING.md`
3. `docs/contributor-codex-contract.md`
4. `docs/theorem-publication-protocol.md`
5. `.agents/skills/bandit-substantive-advance/SKILL.md`
6. `.agents/skills/bandit-semantic-roundtrip/SKILL.md`
7. the relevant bandit/RL skill and exact source-route files.

Do not rely on an old prompt copied from chat when it conflicts with the repository.

Before writing Lean, return a compact plan naming:

- exact source theorem/version/anchor;
- target Lean declarations and owning module;
- route/frontier target;
- BanditRLlib, Mathlib, LML, and compatible upstream declarations searched;
- reuse/adapt/new-shared decision;
- reader-page update;
- source-blind semantic review plan;
- results/progress/roadmap update;
- Lean Graph delta;
- Functor Hypergraph audit.

For every substantive PR, create/update a manifest under
`research-wiki/contribution-contracts/`.

Do not claim completion until the current-base contributor contract, Lean gate, site build/check, graph publication review, and source-fidelity review pass. Generated `website/_site/` is never committed.
