from publication_guard_v4 import *
fixed()
assert (RUN/'root-reader-pixel-review-v2.json').is_file()
assert load(RUN/'integrated-candidate-native-v1.json')['actual_exit']==0
assert not (RUN/'FINAL-inputs-v1.json').exists()
write(RUN/'FINAL-preparation-failure-v1.json',dict(
    command=['python','-B','-X','utf8','runs/online-ch2-prescient-cumulative-20261009/prepare-FINAL-v1.py'],
    actual_tool_process_exit=1,
    observed_failure='Resolver did not index the existing before_raw_base64 field in OWN-whitespace-exact-before-v1.json; it stopped at the historical publication-director-v1.md SHA e060a6258e995d30eca03adc19d4695ea3c65cd5590ce46e6e02f1d0888077a8.',
    completed_before_failure=['Root12pixel receipt','Exact contemporaneous OWN pre-FINAL metadata snapshot','Approved OWN candidate metadata updates','Actual OWN candidate lifecycle event'],
    repair='Continuation-only helper indexes the existing exact before_raw_base64 field, then completes historical resolution and FINAL staging/packet. Does not repeat metadata updates/candidate event or overwrite receipts.',
    production_or_reader_change=False, whole_Goal_status='ACTIVE'))
s=(RUN/'prepare-FINAL-v1.py').read_text(encoding='utf8')
start=s.index('indices=')
s='from publication_guard_v4 import *\nfixed()\nb=load(RUN/\'formula-render-v2-browser.json\')\nr=load(RUN/\'registry-inspected-v2.json\')\ndocs=[ROOT/d/(TASK+\'.md\') for d in [\'tasks\',\'proof-obligations\',\'research-wiki/retrieval-index\']]\n'+s[start:]
assert s.count("['raw_base64','historical_raw_base64']")==1
s=s.replace("['raw_base64','historical_raw_base64']","['raw_base64','historical_raw_base64','before_raw_base64']")
write(RUN/'prepare-FINAL-v2.py',s)
print('Preserved actual partial preparation failure; continuation-only exact resolver repair ready.')
