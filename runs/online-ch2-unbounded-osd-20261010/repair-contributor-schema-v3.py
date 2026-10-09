from publication_guard_v2 import *
fixed()
for label in ['candidate-final-stage-v1','candidate-final-diff-v1','candidate-commit-v1','contributor-stack-v1']:
    p=ROOT/'tmp'/(TASK+'-'+label+'.json');assert p.is_file()
    write(RUN/('pre-site-failed-v2-'+label+'.json'),p.read_bytes())
assert load(RUN/'pre-site-failed-v2-contributor-stack-v1.json')['actual_exit']==1
old=CONTRIBUTION.read_bytes();c=load(CONTRIBUTION)
text=c['verification']['focused_checks'];assert isinstance(text,str) and text
write(RUN/'contributor-schema-before-v3.json',dict(path=CONTRIBUTION.as_posix(),before_sha256=sha(CONTRIBUTION),before_raw_base64=base64.b64encode(old).decode('ascii'),production_Test=rows([PUBLIC,TEST]),candidate_commit=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()))
c['verification']['focused_checks']=[text]
new=(json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8')
reset=json.loads(new.decode('utf8'));reset['verification']['focused_checks']=reset['verification']['focused_checks'][0]
assert reset==json.loads(old.decode('utf8'))
ps=[RUN/n for n in ['lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md']]
write(RUN/'contributor-schema-native-before-v3.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),before_raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in ps]))
event('contributor-schema-repair-v3','repair',dict(task=TASK,failure='Actual nonempty contributor gate requires focused_checks string-list',change='Wrap exact existing string in singleton list; no prose/source/statement/definition/body/reader/pin change',statement_changed=False,proof_changed=False))
CONTRIBUTION.write_bytes(new)
write(RUN/'contributor-schema-repair-v3.json',dict(before_sha256=hashlib.sha256(old).hexdigest(),after_sha256=sha(CONTRIBUTION),only_change='verification.focused_checks: exact text -> singleton list of same text',all_words_preserved=True,root_Tests_full_harness_reuse='Actual source/root/Tests/pins unchanged; not a Lean failure',distinct_FINAL_review='pending',source_Test=rows([PUBLIC,TEST]),chapter_complete=False,whole_Goal='ACTIVE'))
s=(RUN/'commit-and-build-site-v2.py').read_text(encoding='utf8')
for label in ['candidate-stage-v2','candidate-full-package-diff-v2','exact-RAW-line-ending-snapshots-candidate-v2','candidate-diff-audit-v2','candidate-final-stage-v1','candidate-final-diff-v1','candidate-commit-v1','contributor-stack-v1','contributor-main-v1']:
    s=s.replace(label,label[:-2]+'v3')
s=s.replace('Prove causal unbounded OSD lower bound and source coefficient','Fix OSD contribution verification schema and retain gate evidence')
compile(s,'commit-and-build-site-v3.py','exec');write(RUN/'commit-and-build-site-v3.py',s)
fixed()
print('Only OWN contributor schema type repaired; exact existing text preserved; resumed gate v3 ready.',flush=True)
