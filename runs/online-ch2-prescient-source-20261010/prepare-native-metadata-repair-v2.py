from publication_guard_v1 import *
fixed()
final=RUN/'FINAL-review-v1.json';r=load(final)
assert r['package_verdict']=='accepted-with-explicit-delta' and not r['required_repairs']
for row in load(RUN/'FINAL-inputs-v1.json')['rows']:assert sha(row['path'])==row['sha256']
s=(RUN/'record-native-acceptance-v1.py').read_text(encoding='utf8')
old="allowed=[('semantic_roundtrip','remaining_semantic_delta'),('verification','independent_review'),('graph_contribution','visual_review')]"
assert s.count(old)==1
s=s.replace(old,old[:-1]+",('verification','site_check')]")
needle="CONTRIBUTION.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\\n').encode('utf8'))"
assert s.count(needle)==1
replacement="c['verification']['site_check']='Actual site check and complete11020oldregistryobjects unchanged+6canonicalproduction=11026;12sourcecards. Actualfile desktop15sourceguideformulas/zeroerrors/foldedLean/wrap/14originals personally viewed byroot and distinct bounded FINAL '+sha(final)+'. Local-only, notHTTP/live/mobile/allviewports; postnative/delivery pending.'\n"+needle
s=s.replace(needle,replacement)
write(RUN/'record-native-acceptance-v2.py',s)
compile(s,str(RUN/'record-native-acceptance-v2.py'),'exec')
write(RUN/'native-metadata-repair-v2.json',dict(reason='verification.site_check would retain misleading FINAL/pixels pending text after accepted FINAL. V1 and all364FINAL inputs preserved; only prospective metadata helper versioned.',
    old_helper_sha256=sha(RUN/'record-native-acceptance-v1.py'),new_helper_sha256=sha(RUN/'record-native-acceptance-v2.py'),
    added_allowed_field=['verification','site_check'],exact_added_assignment=replacement.split('\n')[0],
    unchanged_semantics='Six actual source proofs/two full canaries/root/readers/contracts and native trial/event/state/suffix logic unchanged. No additional verification.site_build permission.',
    native_executed=False,distinct_addendum_pending=True))
write(RUN/'native-metadata-repair-inputs-v2.json',dict(rows=rows([RUN/'record-native-acceptance-v1.py',RUN/'record-native-acceptance-v2.py',RUN/'native-metadata-repair-v2.json',final,RUN/'FINAL-review-v1.md',RUN/'FINAL-inputs-v1.json',CONTRIBUTION])))
fixed()
print('Exact prospective helper-only metadata repair prepared; native not executed, all FINAL inputs unchanged.')
