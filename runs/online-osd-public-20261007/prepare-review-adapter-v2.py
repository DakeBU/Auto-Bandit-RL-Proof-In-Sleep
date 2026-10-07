"""Version the review adapter; preserve rejected contract v1 and prior receipt names."""
from common_v2 import *
fixed();passed('repair-neutral-comparison-v3-01')
text=(RUN/'prepare-review-v1.py').read_text(encoding='utf-8')
text=text.replace("blind-receipt-v1.json","blind-receipt-v2.json").replace("blind-packet-v1.md","blind-packet-v2.md").replace("blind-reconstruction-v1.md","blind-reconstruction-v2.md")
text=text.replace("mode.lower()+'-v1-reviewed-'","mode.lower()+'-v2-reviewed-'")
for s in ['-native-snapshot-bindings-v1.json','-inputs-v1.json','-packet-v1.md','-review-v1.md','-receipt-v1.json']:
 text=text.replace("stem+'"+s,"stem+'"+s.replace('v1','v2')).replace('{stem}'+s,'{stem}'+s.replace('v1','v2'))
text=text.replace("effective_raw_metadata_version=2,existing_bodies", "effective_raw_metadata_version=2,neutral_context_version=2,compiled_comparison_version=3,existing_bodies")
insert='''
Metadata M3 (separate repair review REQUIRED): original CONTRACT v1 was REJECTED because neutral P02/P03 lost the actual public FiniteDimensional real E binder. Original successful neutral elaboration did not establish faithful scoped types; original all15_exact_actual_types_preserved claim was false for two rows and is retained as refuted history. Explicit FD binders on all15 neutral propositions now elaborate. Fresh neutral-only decoder v2 must reconstruct these complete types; do not reuse its v1 result as repaired evidence. No PUBLIC/CANARY/header/source target change.
Metadata M4 (separate repair review REQUIRED): first complete-type comparison v2 passed first3 then failed at iterate_mem because independently named recursive definitions are not literally definitionally equal. Actual v3 compares compiled type AND value of all6 neutral dependencies under an explicit six-name map, then checks all15 complete proposition types under exactly that audited map. Inspect actual Lean Meta probe and output; this is equality under an audited dependency renaming, not direct equality of separately named recursive constants or a proof of the source theorem. All original v2 failure/probe/output preserved. Require repair_verdict.M3 and M4 separately satisfied before stabilization. M1 raw/native header fix and M2 renderer failure remain separately assessed.
'''
needle='Current mathematical bounded scope is canonical OSD chain only.';assert needle in text;text=text.replace(needle,insert+'\n'+needle)
text=text.replace('CONTRACT only: exact current types/context/semantic targets and separate M1 repair.', 'CONTRACT only: exact current types/context/semantic targets and separate M1/M3/M4 repairs. Read effective neutral-to-actual-map-v3.json and full-context-comparison-v3-01.log; older v1 mapping is refuted, v2 failed comparison remains historical. Fresh blind v2 mandatory.')
write(RUN/'prepare-review-v2.py',text)
write(RUN/'review-adapter-before-first-use-v2.json',dict(script_sha256=sha(RUN/'prepare-review-v2.py'),original_v1_generator_and_rejected_receipt_preserved=True,neutral_context_version=2,compiled_comparison_version=3,prior_dependency_receipt_filenames_unchanged=True,source_CONTRACT_BODY_FINAL_output_version=2,separate_repairs=['M1','M3','M4']))
print('Version2 bounded review adapter prepared; original rejected source review preserved.')
