# Causal review evidence correction, 2026-09-20

An independent Claude Code audit identified three invalid sampling-file hashes
and five foundations without completed semantic-review bindings. These are real
evidence gaps. They are corrected by a fresh source-blind/source round trip at
commit `132a8340f097b5e05bd17669980830b1f9c3d7e3`, without changing Lean proofs.
The topic and the all-ten program remain incomplete.

## Historical findings and preservation

Both `runs/extended-topics-20260919/causal-sampling-review.json` and
`causal-sampling-validation.json` bind CausalSampling, CausalTuning and
CausalRecommendation to hashes that match neither LF nor CRLF bytes at the
validation's stated code commit. Testing zero through four terminal newlines
does not recover those three hashes. Other entries use mixed line endings.
The reproducible values and file histories are preserved in
`runs/extended-topics-20260920/causal-historical-binding-audit.json`.

Git history does not establish the original reviewed bytes or why the hashes
became invalid. Do not infer a particular pre-commit edit from this discrepancy.
The old receipts, their verdicts and their historical build logs are unchanged;
their invalid source bindings are not silently repaired or retroactively signed.
The original descriptive case and its graph counts remain historical artifacts;
this correction supersedes their reliance on the old sampling semantic binding,
not their independently reproduced graph counts.

The OrderedLaw, MarginalLaw, Importance and Allocation foundation checkpoints
recorded semantic review as pending. OptimalAllocation had no completed
standalone review receipt. Compiled downstream consumers did not discharge that
missing source review. Those historical checkpoints remain preserved.

The sampling reader's Lean code bodies already match current source, allowing
for the Markdown closing-fence newline. Its stale SHA256 labels and current
review narrative are corrected. There was no divergent Lean proof body to fix.

## Fresh review and exact scope

`runs/extended-topics-20260920/causal-review-rebinding.json` binds thirteen files:

- Five foundations: CausalOrderedLaw, CausalMarginalLaw, CausalImportance,
  CausalAllocation and CausalOptimalAllocation.
- Seven sampling/performance modules: CausalSampling, CausalSampleMGF,
  CausalTuning, CausalConfidence, CausalRecommendation, CausalExpectedRegret
  and CausalAllocationRegret.
- Tests/CausalNoisyGraphCanary.lean, including the actual noisy graph, derived
  means and instantiated uniform expected-regret endpoint.

Two fresh actors reconstructed the foundation and sampling/canary packets from
Lean with source-identifying comments removed. A third actor independently read
the pinned primary model, Algorithm 2, Theorem 3 and complete proof, Proposition 4
and convex-design discussion, then compared both reconstructions with the actual
source files and proofs. Both groups received `accepted-with-explicit-delta`.
The formalizer did not act as decoder or source reviewer.

The review retains finite common-alphabet scope, explicit support coverage and
totalized-division boundaries, the corrected coefficient `2 sqrt(2)+7` and
failure-event direction, exact design cost in tuning, and fixed-order ties.
The optimal covered allocation is constructed by compactness and continuity;
it is a noncomputable choice, not a verified numerical optimizer. Convexity is
a separately reviewed geometry result, not a dependency of the existence proof
or the final performance consumer. No ordering of actual regrets follows from
minimizing the design cost. No new source repair or mathematical strengthening
is introduced by this evidence correction.

## Executable identity gate

```text
python tools/check_causal_review_bindings.py
python -m unittest discover -s tools -p test_causal_review_bindings.py
```

Production and historical-receipt hashes use UTF-8 bytes with CRLF and bare CR
converted to LF only: no trimming or other whitespace normalization. Production
hashes must match both the immutable Git **commit** and current working tree.
Every bound file must have declared distinct formalizer/decoder/reviewer roles,
an accepted verdict, and distinct hash-bound blind/source reports. The live test
pins the thirteen-file inventory independently, preventing removal of an
obligation from both the hash map and review metadata. `bandit.py check` discovers
and runs this regression through its existing unittest gate.

The private reports can additionally be checked with `--review-dir`; their
hashes cover raw report bytes. Without that argument the output explicitly says
private reports were not verified. Identity and coverage checks do not themselves
certify mathematical correctness, review quality, or actual actor independence.

Regression tests reject stale commit hashes, modified working files, a forged
current hash concealing commit drift, Git tree objects used as commits, malformed
report digests, whitespace role aliases, missing coverage and changed reports.
CRLF checkout differences alone are accepted. Independent tooling review found
and prompted fixes for the tree-object, report-digest and role-alias cases.

The separate `causal-review-rebinding-validation.json` records checks actually
run for this correction. Claude Code's reported 9052-job build and 53 axiom
reports remain attributed external evidence, not a fresh run by this author.
Full-topic evaluation, manuscript integration and final acceptance remain open;
there is no main merge, deployment or anonymous snapshot refresh.
