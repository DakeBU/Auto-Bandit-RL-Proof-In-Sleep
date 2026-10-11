# Independent capture-helper V3 delta review

Verdict: accepted-prepared-capture-helper-v3; blockers empty. Actor /root/adaptive_decoder, requested GPT-6 Astra / medium, runtime not attested.

Exact old and new SHA pins match. Mechanical reconstruction proves the entire new source differs only by three intended replacements: Git helper argv adds -c core.longpaths=true; active-tree enumeration adds .github/workflows; ZIP selection adds precisely the .github/workflows/ prefix. This covers tracked workflow files plus new or ignored files found inside that active tree, and makes their same RAW bytes eligible for the selected ZIP.

Clean committed candidate requirement, namespace safety, file ordinary/repository checks, create-only evidence, snapshot hash checks, exact argv execution, actual exit recording, full pre/post path-and-byte comparison, HEAD/branch/status equality, capture failure exit125 and ordinary process-exit propagation are byte-unchanged. The direct check-ignore invocation is unchanged; the new longpath setting applies to Git helper commands rather than asserting every possible shell command was rewritten. Historical runs remain excluded except active process memory. No production exemption or new ignore rule is introduced.

Independent compile() syntax check succeeded in memory. Definitions were loaded with a non-main module name solely to test six pure selected_for_zip predicates: both repaired workflows and an added workflow select; historical runs and unrelated .github paths do not; process memory still selects. main(), inventory(), subprocess gates and Lean/build were not called. No pycache or tracked edit was made.

This is prepared-tool eligibility only. Current untracked candidate source is not a clean gate snapshot; the unchanged clean-state check must reject it until parent commits the final integrated source. Future receipts must pin this new helper SHA and new enumerated workflow rows rather than reusing old recorder/inventory hashes. Remote CI progress mentioned by parent is not independently reverified here.
