from common_accepted_v1 import *
accepted_fixed()
decision=load(RUN/'accepted-decision-v1.json')
scope=decision['scope'];remaining=decision['remaining_required']
digest=(RUN/'memory-digest-accepted-v1.md').read_text(encoding='utf8').strip()
boundary={k:decision[k] for k in ['source_package_accepted','chapter_complete','goal_complete','merged','live','new_public_proofs','new_public_definitions','reused_public_proofs','new_source_subobligation_closures','new_public_registry_nodes','new_named_validation_proofs']}
manifest = load(MANIFEST)
manifest['semantic_roundtrip']['remaining_semantic_delta'] = manifest['semantic_roundtrip']['remaining_semantic_delta'].replace('CONTRACT/separate proposed repair/BODY accepted; FINAL pending.', 'CONTRACT/separate proposed repair/BODY/FINAL accepted with explicit delta; original R1-R8 satisfied.')+' Actual distinct CONTRACT/BODY/FINAL accepted-with-explicit-delta; exact R1-R8 satisfied. Decoder reconstructs only; no human/external/runtime attestation.'
manifest['verification']['independent_review'] = 'Actual distinct source CONTRACT/BODY/FINAL accepted with explicit delta. FINAL receipt '+sha(RUN/'final-reader-receipt-v1.json')+'; exact R1-R8 satisfied. Package only; chapter and total Goal remain open.'
manifest['verification']['bandit_check'] = 'Actual combined-root-v2 9095 jobs, combined-Tests-v2 9249 jobs, full-harness-v2 472 tests/7 skips; after separately reviewed source-comment append.'
manifest['verification']['site_build'] = 'Actual clean41a225 source with lean_verified=true and applicable combined gates; local site-build-v2/site-check-v2 only, not deployed.'
manifest['verification']['site_check'] = 'Actual10894old IDs/URLs/statementhashes preserved,12new public registry nodes,12current images root individually viewed and separately FINAL reviewed.'
manifest['graph_contribution']['visual_review'] = 'Actual34compiled scoped nodes/27proofs/7definitions and19VALUEpairs;12new shared registry nodes; current reader DOM/pixels and separate FINAL accepted.'
MANIFEST.write_bytes((json.dumps(manifest,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
write(RUN/'native-acceptance-overlay-v1.json',dict(status='passed',one_accepted_reviewer_trial=True,progress_class='terminal',obligations_before=9,obligations_after=0,obligation_count_scope='Only fixed nine derived reconciliation terminals, never whole chapter/program',globalSGB_unchanged=True,PR_delivery_pending=True,**boundary))
for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']:
    path=Path(folder)/(TASK+'.md')
    path.write_bytes(path.read_bytes()+('\n\n## Actual no-regret reconciliation accepted; delivery pending\n\n'+digest+'\n').encode('utf8'))
write(RUN/'40_reviewer_decision-v1.md','Actual distinct staged source/FINAL reviewer accepted-with-explicit-delta, separately bound by raw receipt; formalizer validates exact bindings/R1-R8 discharge and records native acceptance. '+digest)
accepted_fixed()
print('Only C1-NOREGRET source package/native acceptance recorded. PR delivery pending; total Goal ACTIVE.')
