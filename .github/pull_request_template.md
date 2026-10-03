## Contribution scope

- Type: `theorem-edge | reusable-interface | integration-node | source-correction | strict-obstruction | documentation/tooling`
- Route / frontier cell:
- Exact source paper/book/version/anchor, or `internal-design`:
- Exact theorem-sized target:
- Contribution manifest: `research-wiki/contribution-contracts/...`

## Reuse / shared-floor audit

- BanditRLlib searched:
- Mathlib searched:
- LML / other compatible upstreams searched when relevant:
- Classification: `reuse | adapt | missing | out_of_scope`
- Decision: `reuse_existing | adapt_existing | new_route_local | new_shared | out_of_scope`
- Exact declarations actually reused:
- New shared declaration(s), if any:
- Existing and planned consumers:
- Why this boundary avoids duplicate/wrapper-only lemmas:

If a missing lower-level lemma has at least two real consumers, prefer one
canonical shared declaration plus explicit source/setting adapters.

## Reader and encoder–denoiser contract

For source-facing mathematics:

- [ ] Exact source version/anchor and faithful attributed statement are visible.
- [ ] Natural-language proof uses mathematical formulas, not only tactic prose.
- [ ] Hidden assumptions and source-vs-Lean assumption deltas are visible.
- [ ] Exact Lean statement/proof is folded beside the mathematics where the renderer supports it.
- [ ] BanditRLlib parents and Mathlib/LML/external dependencies are distinguished.
- [ ] The remaining red boundary is visible.
- [ ] A fresh source-blind decoder reconstructed the Lean statement.
- [ ] A distinct anti-anchored source reviewer checked the reconstruction against the source.
- [ ] Any source repair is stored/reviewed separately and does not silently mutate the faithful target.

Formalizer / blind decoder / source reviewer:
Semantic verdict and remaining delta:

## Route, progress, and website delta

For each surface, state the update or `no-change-with-reason`:

- Teaching/book route:
- Source Chapter 13–17 spine:
- BanditRLwiki setting/case/frontier history:
- `website/content/results.json`:
- Roadmap/frontier:
- Reader/publication page(s):
- Contributor/provenance surfaces:

Do not hand-edit generated completion badges or `website/_site/`.

## Graph contribution

- Lean Graph: `new-node | reuse-only | integration-node | no-change-with-reason`
- Overview/route graph: `updated | no-change-with-reason`
- Functor Hypergraph: `none-found-with-reason | candidate-published | stabilized`
- Conceptual family/transport IDs, if any:
- Graph focus target(s):
- Visual review performed:
- Remaining graph boundary:

Truth contract:

- compiler-backed formal structure/reviewed dependency = **solid**;
- source/planned/semantic/scan/conceptual overlay = **dashed**;
- evidence-status and library/domain grouping remain separate;
- conceptual similarity is never a formal Lean edge or certified functor without a separate proof certificate.

## Mathematical and status boundary

- Result/correction:
- Owning Lean module/declaration(s):
- Important assumptions/constants/conventions:
- Local Lean status:
- Source-fidelity status:
- Route/chapter status:
- Remaining mathematical obligations:
- If blocked: exact obstruction and strictly smaller next target:

## Provenance and collaboration safety

- Adapted code/source, license, authorship, and modifications:
- Source-to-Lean drift risks:
- Shared registries rebased/merged semantically rather than overwritten from a stale branch:
- Contributor credit:

## Verification

- [ ] Read `AGENTS.md`, `docs/contributor-codex-contract.md`, and `docs/theorem-publication-protocol.md`.
- [ ] `python3 tools/check_contributor_contract.py --base BASE_COMMIT`
- [ ] Relevant focused Lean checks exercise the named declarations.
- [ ] `python3 tools/bandit.py check`
- [ ] `python3 website/scripts/build_site.py --lean-verified`
- [ ] `python3 website/scripts/check_site.py`
- [ ] `git diff --check`
- [ ] Source-facing work has independent encoder–denoiser review.
- [ ] Status matches compiler, source-review, route, and integration evidence.
- [ ] No `sorry`, `admit`, hidden axiom/interface closure, fake completion, or committed generated `website/_site/`.
- [ ] I have the right to submit the material and license my intentional contribution under MIT.
- [ ] No credentials, private review material, or sensitive information is included.

## Reviewer notes

Call out statement drift, hidden assumptions, shared-foundation collisions,
incorrect graph edge semantics, stale website/progress state, source ambiguity,
or follow-up work that must remain visibly open.
