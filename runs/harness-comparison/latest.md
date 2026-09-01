# ABRL Harness Comparison

## Evidence boundary

- Eligible structured rows: 0
- Matched experiments: none
- Minimum matched experiments for a recommendation: 2
- Decision status: **insufficient-evidence**
- Recommended default: **retain-current-default**
- Next matched arm to collect: **master-worker**

Historical trials without an explicit harness mode, experiment id, frozen target
fingerprint, reviewed progress class, and verifier evidence are excluded from the
causal comparison.  A successful agent command is not a compiled Lean result.

## Matched evidence

| Harness | Runs | Attempts | Reviewed | Substantive | Score | Obligations closed | Critical seconds | Prompt chars |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| hierarchical | 0 | 0 | 0 | 0 | 0 | 0 | 0.0 | 0 |
| master-worker | 0 | 0 | 0 | 0 | 0 | 0 | 0.0 | 0 |

The score weights reviewer-validated mathematical progress: diagnostics and
statement repairs count, compiled leaves count more, and a closed frontier or
terminal counts most.  Raw worker/node count is not a success metric.

## Excluded or unmatched experiments

- none

## Deterministic conclusion

need at least 2 matched experiments; found 0.  GPT review may explain the pattern and propose the next
matched experiment, but it cannot promote an unreviewed attempt or silently
change the frozen theorem target.
