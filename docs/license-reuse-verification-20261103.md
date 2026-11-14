# Apache 2.0 and reuse entry: documentation verification

Base: `ee8c0b805c785220ee31799012325f4179dad875`. Branch: `docs/apache-reuse-20261103`. No Lean source or mathematical status changes are included.

- LICENSE is the unchanged Apache Software Foundation LICENSE-2.0.txt, downloaded from https://www.apache.org/licenses/LICENSE-2.0.txt. SHA-256: `cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30` (11,358 bytes).
- LICENSE-MIT retains the previous root license. NOTICE, NOTICE.md, LICENSE_SCOPE.md, contributor policy, README and the attribution route explain the scope and earlier/third-party rights.
- Python renderer compilation passed. Focused source/text checks verified the standard license digest, retained MIT text, every scope paragraph and actual attribution-section rendering. Three contributor-contract unit tests passed.
- `python website/scripts/build_site.py` passed as an explicitly unverified preview. The initial raw-hash boundary failure was caused by Windows checkout line endings in OnlinePrescientBregman.lean. The isolated file was temporarily restored to identical Git-blob bytes for the site gate, then restored to its original checkout representation; no Lean diff is included.
- `python website/scripts/check_site.py --allow-unverified` passed, including local links and license downloads. No `--lean-verified` status was supplied.
- Actual generated attribution page inspected in headless Edge at 1440 and 390 pixel widths. The license section, download links and scope are readable; no document horizontal overflow was detected.
- `git diff --check` passed. The contributor contract is checked against the committed diff before pushing.

The full current-checkout `tools/bandit.py check` / Lean gate was not rerun for this documentation-only increment. It remains a pre-merge gate; earlier research compilation is not substituted. No main merge or deployment is claimed. The previous frontier announcement PR #207 is still draft/open and is not incorporated by this licensing branch.
