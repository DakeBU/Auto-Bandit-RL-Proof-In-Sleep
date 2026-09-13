# Metadata repair, not a mathematical target revision

The first native safe-verify call rejected `source_assumptions_preserved` while
confirming equal expected/actual statement hashes. The original fence invocation
incorrectly supplied the source-card path to --source-assumption. Inspection of
abrl_lifecycle.safe_verify establishes that this field expects literal Lean header
substrings, not provenance paths. Preserve the original fences and failure report;
write corrected-schema fences in fences/. Require their statement/hash to equal
the original captures. The source-card provenance remains in contract.md.
No header, definition, quantifier, or assumption changed. This repair is confined
to validation metadata; it does not reopen the terminal proof scope.
