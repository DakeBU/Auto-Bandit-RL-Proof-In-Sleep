# Review and validation refinements

After the first successful full gate, desktop inspection exposed a legacy renderer
assumption: every teaching chapter's breadcrumb and list belonged to Bandit Book.
The OGD registry correctly belonged only to Online Learning Book, so the renderer
was repaired to follow membership, filter the Bandit Book list, and use shared-route
labels outside a particular Book. A regression assertion checks the OGD breadcrumb
and preserves shared RL breadcrumbs. The final rendered HTML and canonical registry
are checked by check-rendered-book.py, including 16 OGD source nodes and 10 original
Bandit Book teaching cards. Full gate rerun follows this renderer/test change.

The desktop screenshot was used to find this issue. The attempted mobile-size
Chrome capture was rejected by automatic tool approval with `blocked by policy`
and no detailed reason. It was not retried through another helper. No mobile visual
verification is claimed; deterministic site checks cover links, anchors, mappings,
formulas and source consistency. This optional screenshot does not replace a Lean gate.

The first complete harness run failed solely because the new Lean files were not
in Git's index and the anonymous inventory test rejects untracked allowlisted source.
Staging these files resolved that test. The anonymous submission snapshot itself
was not changed or published; these are ordinary isolated builder tests.
