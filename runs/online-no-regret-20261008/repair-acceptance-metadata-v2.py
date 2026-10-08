from common_accepted_v1 import *
accepted_fixed()
assert not (RUN/'native-acceptance-overlay-v1.json').exists()
for label in ['accepted-reviewer-trial-v1','accepted-lifecycle-v1','accepted-frontier-refresh-v1','accepted-frontier-shadow-v1','accepted-memory-record-v1','accepted-retrieval-record-v1']:
    assert load(RUN/(label+'-exit.json'))['exit_code']==0
write(RUN/'acceptance-metadata-repair-v2.json',dict(
    failure='record-acceptance-v1.py exited1 after six successful native commands; KeyError delta at source-card summary lookup.',
    actual_source_card_keys=list(load(CONTRACT/'source-card-v1.json')),
    repair='Resume only the unexecuted manifest/owned metadata overlay tail. Preserve the current reviewed explicit delta prose, replace only its FINAL pending phrase, and append actual acceptance evidence. No native replay, receipt rewrite or target change.',
    original_script_sha256=sha(RUN/'record-acceptance-v1.py'),
    native_six_commands_successfully_completed=True, source_or_statement_change=False))
source=(RUN/'record-acceptance-v1.py').read_text(encoding='utf8')
tail=source[source.index('manifest = load(MANIFEST)'):]
old="load(CONTRACT/'source-card-v1.json')['delta']"
assert old in tail
tail=tail.replace(old,"manifest['semantic_roundtrip']['remaining_semantic_delta'].replace('CONTRACT/separate proposed repair/BODY accepted; FINAL pending.', 'CONTRACT/separate proposed repair/BODY/FINAL accepted with explicit delta; original R1-R8 satisfied.')")
prefix="""from common_accepted_v1 import *
accepted_fixed()
decision=load(RUN/'accepted-decision-v1.json')
scope=decision['scope'];remaining=decision['remaining_required']
digest=(RUN/'memory-digest-accepted-v1.md').read_text(encoding='utf8').strip()
boundary={k:decision[k] for k in ['source_package_accepted','chapter_complete','goal_complete','merged','live','new_public_proofs','new_public_definitions','reused_public_proofs','new_source_subobligation_closures','new_public_registry_nodes','new_named_validation_proofs']}
"""
write(RUN/'resume-acceptance-metadata-v2.py',prefix+tail)
print('Six actual successful native commands retained; bounded metadata-only tail prepared.')
