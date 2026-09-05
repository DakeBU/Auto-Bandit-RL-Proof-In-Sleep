# Arithmetic code identity: retained interval invariant

The final source audit found a semantic interface gap. Although
exists_arithmeticPrefixCode constructs addresses inside each message interval,
exists_zeroSafe_arithmeticCode discarded that conjunct. Its consumer
exists_arithmeticBlockSupport consequently characterized only lengths and
expected cost. Classical.choose in arithmeticBlockCode could select a different
prefix code satisfying that weaker specification. The rate proof is valid,
but the named-family arithmetic-identity claim needs stronger evidence.

Repair route: preserve the existing interval containment conjunct through both
existence theorems; leave the constructor and rate proof unchanged except for
conjunction projections. Expose containment for the positive-support payload
of the actual named arithmeticBlockCode after removing its leading support tag.
Use existing extendZeroMass/supportTaggedWord definitions and choose_spec; no
new Mathlib API, assumptions, concentration, or external theorem is required.
This is a project-local specification strengthening, not a new coding route.
Add a typed canary for the actual named code's payload interval containment.

Until this strengthened interface compiles and is gated, the prior full gate
certifies rates and prefix freedom but not the full arithmetic-identity claim.

The strengthened ArithmeticZeroExtension and ArithmeticBlockCoding modules
now build successfully (2686 jobs). The retained conjunct is used by
arithmeticBlockCode_payload_interval for the actual selected positive payload;
the expected-length proof uses the unchanged bound at its new projection.
Both focused ArithmeticBlock and ArithmeticZero canaries pass. The new named
payload theorem and unchanged rate conclusions report only propext,
Classical.choice and Quot.sound. The subsequent full gate remains pending.
The Markdown/LaTeX export records this audit; its previous visual QA is stale
after the added audit paragraph and must be rerun.

Export QA rerun: the b5e21b8 LaTeX fragment compiled successfully with the
existing article wrapper using TeX Live; three pages, no overfull boxes or
LaTeX errors. All three pages were rendered with Poppler at 1300 pixels and
visually inspected: equations, identifiers and the new arithmetic-identity
paragraph are readable without clipping or overlap. This replaces the stale
visual QA for this export snapshot only. Full Lean gate still runs separately.
