from common_body_v2 import *

fixed_integrated()
prior = ROOT / 'runs/online-ae-causal-20261008'
source = (prior / 'record-acceptance-v2.py').read_text(encoding='utf8')
for old, new in [
    ('from common_accepted_v2 import *', 'from common_accepted_v1 import *'),
    ('-v2', '-v1'), ('basePR=197', 'basePR=198'),
    ('Three derived AE causal proofs only: one bounded all-time history version, actual original current-target independence, exact original IID expected-fixed excess and nonnegativity for every natural horizon.',
     'Four derived ambient-completion proofs only: actual real measurable-version producer, one same-process all-time bounded history family, original current-target independence and exact original IID expected-fixed excess for every natural horizon.'),
    ('Original16 Chapter1 source objects/null proof total, ambient completed-information bridge, general causal stochastic-kernel realization, remaining Chapter1/2, unenumerated Chapters3-16 and necessary appendices remain REQUIRED; whole Goal ACTIVE, main/live unchanged.',
     'Original16 Chapter1 source objects/null unknown proof total, general causal stochastic-kernel realization, other source-required information/completion constructions, remaining Chapter1/2, unenumerated Chapters3-16 and necessary appendices remain REQUIRED; whole Goal ACTIVE, main/live unchanged.'),
    ('derived_obligations_before=3', 'derived_obligations_before=4'),
    ('accepted_production_proofs=3', 'accepted_production_proofs=4'),
    ('presentation_repair_version=2', 'presentation_version=1'),
    ('current_AE_leaf_overlay', 'current_completed_leaf_overlay'),
    ('registry-v4.json', 'registry-v1.json'),
    ('AE-CAUSAL-FINAL-V2', 'COMPLETED-CAUSAL-FINAL-V1'),
    ("'--obligations-before','3'", "'--obligations-before','4'"),
    ('Persistent Orabona Chapters1-16; three derived AE causal proofs only',
     'Persistent Orabona Chapters1-16; four derived ambient-completion proofs only'),
    ('source-reviewed-compiled-AE-causal-producer', 'source-reviewed-compiled-completed-causal-producer'),
    ('AE versions causal history, original current independence and IID expected fixed excess',
     'Actual completed-information real versions, original causal history/current independence/IID expected fixed excess'),
    ("'--candidate',targets[2]['name'],", "'--candidate',targets[2]['name'],'--candidate',targets[3]['name'],"),
    ('canary-focused-build-v1-exit.json', 'canary-focused-v1-exit.json'),
    ('Three derived AE causal obligations accepted; draft delivery pending',
     'Four derived completed-information obligations accepted; draft delivery pending'),
    ('Three derived AE causal obligations accepted by actual scoped native commands;',
     'Four derived completed-information obligations accepted by actual scoped native commands;')]:
    assert old in source, old
    source = source.replace(old, new)
lines = source.splitlines()
for i, line in enumerate(lines):
    if line.startswith('digest='):
        lines[i] = "digest='Task: `'+TASK+'`\\n\\n'+scope+' '+remaining+' Four focused public proofs and11actual canary proofs;56 standard axiom records;52selected compiled nodes2614coalesced TYPE_VALUE edges18required directVALUEpairs. Actual root9101/Tests9262/fullharness passed (exact test/skip counts in raw log), both contributor bases and own shadow passed. Applicable clean local site preserves10938COMPLETE old nodes plus4actual declarations;10original current images separately viewed by formalizer/source reviewer. CONTRACT175/BODY285/FINAL current receipt, exactR1-R7; proof/type-printer/receipt-schema failures retained. Distinct reused staged automated actors, no absolute blind/human/external/runtime attestation. Native/post-native/draft delivery separately recorded.'"
start = next(i for i, line in enumerate(lines) if line.startswith('updates={'))
end = next(i for i in range(start, len(lines)) if lines[i].startswith('assert ['))
lines[start:end] = [
    "updates={('semantic_roundtrip','remaining_semantic_delta'):'Actual FINAL accepted; exactR1-R7 satisfied. '+scope+' '+remaining,",
    "    ('graph_contribution','visual_review'):'56standard-only axiom outputs;52selected nodes2614coalesced TYPE_VALUE edges18required directVALUEpairs;10938COMPLETE old registry nodes preserved plus4new Online Learning declarations;10original formalizer/distinctFINAL pixel inspections.',",
    "    ('verification','independent_review'):'Distinct CONTRACT175/BODY285/FINAL exact current fixed inputs;R1-R7 satisfied. Reused automated actors, no human/external/absolute blind/runtime attestation. Receipt '+sha(RUN/'final-reader-receipt-v1.json'),",
    "    ('verification','bandit_check'):'Actual four focused/whole-type VALUE/56axiom/fences/root9101/Tests9262/fullharness; both contributor bases/ownshadow passed. Closes4derived completion obligations only; exact tests/skips in raw evidence.',",
    "    ('verification','site_build'):'Actual applicable clean local source '+load(RUN/'registry-v1.json')['source_commit']+'; combined gate passed, dirtyfalse, production/canary/pins immutable; no deployment.',",
    "    ('verification','site_check'):'10938COMPLETE old shared registry nodes preserved plus4actual Online Learning declarations, full four headers and10original formalizer/distinctFINAL pixels reviewed; genuine v1 browser/DOM/capture evidence.'}"]
write(RUN / 'record-acceptance-v1.py', '\n'.join(lines))
source = (prior / 'prepare-post-native-review-v2.py').read_text(encoding='utf8')
source = source.replace('common_accepted_v2', 'common_accepted_v1').replace('-v2', '-v1')
source = source.replace('derived_obligations_before=3', 'derived_obligations_before=4')
source = source.replace('FINAL475', 'FINAL current exact input count').replace('3derivedAEproof obligations3->0', '4derivedcompletionproof obligations4->0')
source = source.replace('required completion/kernel/remainingchapters/appendices', 'required general kernel/other information constructions/remainingchapters/appendices')
source = source.replace('selected PR title/body v2', 'selected PR title/body v1')
write(RUN / 'prepare-post-native-review-v1.py', source)
write(RUN / 'native-helper-adaptation-v1.json', dict(
    original_helpers_retained=True, future_native_commands_not_yet_executed=True,
    own_closed_derived_obligations=4, original_source16_and_null_proof_total_retained=True,
    actual_guard='common_accepted_v1.py', uses_current_FINAL_dynamic_count=True))
