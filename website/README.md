# ABRL literate formalization website

This directory contains the source for the Blueprint-style documentation site.
It is deliberately generated from the current Lean tree rather than from a
hand-maintained declaration list:

- every public `def`, `abbrev`, `structure`, `class`, `inductive`, `theorem`,
  and `lemma` under `BanditRLProof/` is indexed;
- namespace-relative dotted names and declarations whose keyword/name span
  separate lines are resolved without collapsing distinct Lean declarations;
- module imports become the implementation dependency map;
- selected declarations receive longer teaching notes from
  `content/highlights.json`;
- theorem-route milestones and honest incomplete/blocked states live in
  `content/results.json`;
- Mermaid sources in `diagrams/` remain editable alongside the prose.
- the Research IDE page adds live MathJax rendering, reviewed LaTeX-to-Lean
  mappings, dependency-tree navigation, an optional local Lean compiler, and a
  versioned community lemma-packet export;
- the community page separates learning, lemma discovery, public proposal,
  Lean checking, and upstream integration instead of collapsing them into one
  completion badge;
- `community/contribution.schema.json` is the stable handoff contract for the
  browser prototype and a future authenticated LaTeX↔Lean compiler;
- `public-repo/` contains the issue form, contribution guide, governance,
  packet validator, and public Pages workflow copied into a public snapshot.

The generator uses only the Python standard library.  The published site loads
MathJax and Mermaid from jsDelivr in the browser.

## Build locally

Run the Lean gate before marking declarations as compiled:

```text
python3 tools/bandit.py check
python3 website/scripts/build_site.py --lean-verified
python3 website/scripts/check_site.py
python3 website/scripts/ide_server.py
```

Then open `http://localhost:8000/`; the IDE is at
`http://localhost:8000/ide/`.  Omitting `--lean-verified` builds a preview whose
status banner explicitly says that the Lean gate was not run.

## Research IDE execution model

The browser always supports formula rendering, editing, source navigation,
reviewed mappings, the visual dependency tree, and lemma-packet export.
`scripts/ide_server.py`
adds `POST /api/compile` on loopback and invokes `lake env lean` on a temporary
file.  It serializes compilations, imposes source-size and time limits, deletes
the temporary directory after each request, and never writes into
`BanditRLProof/`.

This is deliberately a prototype, not a claimed Lean language server.  It
does not yet provide cursor-level proof states, semantic synthesis for
arbitrary LaTeX, collaborative persistence, or an elaborated environment
graph.  The “safe draft scaffold” is visibly marked as a placeholder and does
not claim that its `True` proposition translates the user's mathematics.
Packet export is local and unauthenticated: it neither uploads code nor marks a
draft integrated.  The public contribution guide supplies the review step.

## Community contribution contract

The public unit of contribution is one JSON lemma packet.  It records the
mathematical source, plain-English and LaTeX statements, Lean imports and code,
named dependencies, compiler evidence, contributor credit, and MIT license
agreement.  The public validator rejects missing provenance or credit,
unaccepted license terms, and `lean-checked`/`integrated` statuses without
compiler evidence.  Only maintainers assign `integrated` after the result has
entered the indexed ABRL tree and passed the full Lean and website gate.

The public repository uses `scripts/build_community_registry.py` to validate
`community/entries/*.json` and regenerate `community/registry.json` before
Pages deployment.  Large formalizations should begin with the public lemma
proposal issue so statement, assumptions, and module ownership are agreed
before substantial proof work.

For a static-only preview without any execution endpoint:

```text
python3 -m http.server 8000 --directory website/_site
```

## Temporary private sharing

`scripts/serve_private.py` serves the generated site on loopback with HTTP
Basic Authentication. Keep credentials in environment variables rather than
in the repository:

```powershell
$env:ABRL_SHARE_USER = 'reviewer'
$env:ABRL_SHARE_PASSWORD = '<random strong password>'
python3 website/scripts/serve_private.py --port 8001 --directory website/_site
```

In another terminal, a temporary HTTPS tunnel can forward to that protected
loopback server:

```powershell
cloudflared tunnel --url http://127.0.0.1:8001 --no-autoupdate
```

Anyone without the username and password receives HTTP 401. The temporary
address stops working when either process exits; Quick Tunnels have no uptime
guarantee and should not be treated as a production deployment.

Only tunnel `serve_private.py`, which serves static files.  Never tunnel
`ide_server.py`: its compile API intentionally trusts the local researcher and
is restricted to loopback rather than designed as a multi-user sandbox.

## Maintain the mapping

1. Add or edit Lean declarations normally.
2. Put detailed student-facing notes only for major declarations in
   `content/highlights.json`.
3. Update route-level completion and missing steps in `content/results.json`.
4. Keep chapter scope and recommended reading order in
   `content/chapters.json`.
5. Rebuild and run `check_site.py`.  The build fails if a highlighted or
   milestone declaration does not exist in the current Lean sources.
6. Use the IDE's reviewed mapping selector for major declarations. Arbitrary
   LaTeX edits become “review required” until a human confirms the statement
   and the exact Lean declaration compiles.

This separation keeps the exhaustive declaration catalog automatic while
making mathematical explanations reviewable as ordinary data.

For the independent public snapshot, replace private source-line links with the
explicit access-boundary page during generation:

```text
python3 website/scripts/build_site.py --lean-verified --public-base-url https://jicheng9617.github.io/Auto-Bandit-RL-Proof-In-Sleep-site
python3 website/scripts/check_site.py
```

## Deployment

`.github/workflows/documentation.yml` builds Lean and tests, generates the
site, checks internal links and mapping integrity, and uploads
`website/_site/` to GitHub Pages.  Pages is intentionally static: it publishes
the IDE interface and reviewed mappings but no code-execution endpoint.
Repository maintainers must select
**GitHub Actions** as the Pages source once in the repository settings.  No
untrusted Lean code is executed by either Pages workflow.  The independent
public site is deployed at
<https://jicheng9617.github.io/Auto-Bandit-RL-Proof-In-Sleep-site/>.

## Attribution

The site's organization is inspired by
[Sho Sonoda's Lean-Ridgelet project](https://github.com/shosonoda/lean-ridgelet)
and its
[Blueprint website](https://shosonoda.github.io/lean-ridgelet/), particularly
the implementation-map idea.  Lean-Ridgelet is Apache-2.0 licensed.  This site
uses an independent generator and original templates, styles, diagrams, and
text; no Lean-Ridgelet source file is copied.  The reference does not imply
that Sho Sonoda participates in, endorses, or maintains ABRL.

The learning/browsing/contribution organization also takes inspiration from
[StatsMLlib](https://statsmllib.github.io/) and its
[public repository](https://github.com/Lean-MoDS/StatsMLlib), which is
Apache-2.0 licensed.  ABRL independently implements its generator, community
contract, prose, HTML, CSS, JavaScript, diagrams, and governance.  No
StatsMLlib source file or template is copied, and the reference does not imply
participation, endorsement, review, or maintenance by StatsMLlib or Lean-MoDS.
