# Chapter 17 corrected terminal: local validation

Task: `TEXTBOOK-PART-IV-CHAPTER-17-HIGH-PROBABILITY-LOWER-BOUNDS-SPINE`.

## Mathematical contract

For the same arbitrary randomized history policy, `k=m+1>=2`, `N=n+1>=1`,
`0<delta<=1/32`, and `64*k*log(1/(2*delta))<=N`, the terminal
`adversarialRandomRegret_ge_theorem17_4` produces a deterministic reward table
with all entries in `[0,1]`, such that

```text
delta <= 1 - F_table((1/160)*sqrt(N*k*log(1/(2*delta)))).
```

`F_table(u)` is the probability of actual random regret `<=u` under the
original policy interacting with that fixed table. Its complement is the
strict `>u` event, not a non-strict pseudo-regret event. The separate expected
regret is the Bochner integral of this measurable, integrable random variable.

The user approved two explicit source corrections:

- Claim 17.6 uses `T_i<=N/2`. A balanced two-arm/two-round schedule refutes the
  printed strict event; this non-strict version still suffices for Eq. (17.8).
- Theorem 17.4 is restricted to the domain above. At `delta=3/4`, the printed
  logarithm is negative; Lean's real square root gives zero, and the uniform
  one-round two-arm policy has positive regret with probability at most `1/2`.
  The canary records both arithmetic counterexample components.

## Proof audit

- The reward construction uses one shared Gaussian coordinate per round and
  the exact full-family shifts; independence is only across rounds.
- All-round history marginal equality connects the noise/table construction
  to the clipped feedback law for the same policy.
- Claim 17.6 supplies a `2*delta` non-strict pull-small event.
- Claim 17.7 controls the literal full-family boundary clipping count by the
  Gaussian noise envelope and bounded-variable concentration, including the
  base environment; its source constants are not assumptions of a substitute
  concentration theorem.
- Eq. (17.8) is proved for actual finite-comparator random regret.
- Event subtraction yields mass `delta` above `Delta*N/4`; a measurable
  kernel-section first-moment argument extracts a deterministic table.
- Logarithm/horizon calibration proves the displayed threshold is strictly
  smaller than `Delta*N/4`, giving the source CDF-complement notation.
- Fixed-table random regret takes only finitely many action-path values;
  this supplies a finite norm bound and integrability of its expectation.

## Validation status

Focused module build passed (3588 jobs), including the CDF terminal and
integrability lemma. The full root build passed (8852 jobs) on the initial
short-path snapshot. Full Tests (8894 jobs), exporter, and placeholder scan
also passed. The first Python run had two Git-metadata errors (374 tests,
7 skips); both used Git commands before the snapshot had a `.git` reference.
With that reference present, the final full gate passed: root 8852 jobs,
Tests 8894 jobs, exporter, placeholder scan, and 400 Python tests in 204.764s
with 7 expected skips. The final typed canary and both source-obstruction
examples compile. Endpoint audits contain only `propext`, `Classical.choice`,
and `Quot.sound`. Final gate log: `E:/Temp/ch17-final-gate-20260905.log`.
No independent-agent review,
commit, merge, or deployment is asserted.

The local verified website build and checker pass (604 modules, 8365
declarations, 658 HTML pages, zero placeholders, 9132 valid Lean source links).
The old blanket post-Chapter-13 promotion fence now admits only Chapter 17
when all eleven required body interfaces are indexed; Chapters 14--16 remain
fenced. Three focused tests cover successful closure, each missing interface,
and preservation of the other chapter fences. This is not a browser visual
review or a deployment.

After the website-validator change, the full Python suite was rerun in the
original workspace: 403 tests passed in 189.924s, with 7 expected skips.
Log: `E:/Temp/ch17-postsite-python-20260905.log`. The unchanged Lean source
and canary still match the final full-gate hashes below. The regression
command's unrelated CSV-summary schema regeneration was restored to its
pre-turn content; no unrelated source change is included.

## Windows path workaround

The native workspace full gate failed creating an unrelated RL module's
very long `.olean` output. A junction-only checkout did not shorten Lake's
canonical output paths. Validation therefore uses a physical source snapshot
at `E:/af/ch17-validation`, excluding `.git` and `.lake` from the bulk source copy.
Its `.lake/packages` and `.lake/build` are junctions to the existing dependency
cache and build artifacts. Source files are not moved; system settings and
unrelated RL source are not modified. The formerly failing RL module then
built successfully. The original `.git` reference was then copied separately
so read-only history/index regression checks can access the actual repository.
No Git history or source commit was fabricated for the snapshot.

Final-revision source hashes match between the workspace and validation copy:

- `HighProbability.lean`: `7DC4D2AFC6B139DCCD6C295E87A06C8E2C57C68EE8D832067BF2EBF011267CFA`.
- `TextbookPartIVChapter17Canary.lean`: `DC6A991ADD87FF51BB5A835D48AE559FAE1ED730B39C22D0D292EFA78F435F9C`.
