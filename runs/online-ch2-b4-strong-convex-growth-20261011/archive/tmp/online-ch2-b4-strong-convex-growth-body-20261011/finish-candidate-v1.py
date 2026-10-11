from pathlib import Path
import json,hashlib,subprocess
out=Path('tmp/online-ch2-b4-strong-convex-growth-body-20261011')
def bind(p):
 p=Path(p);b=p.read_bytes();return dict(path=p.as_posix(),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
raw=(out/'dependency-probe-v2.stdout.raw').read_text(encoding='utf-8'); marker='ACTUAL_DEPENDENCIES_JSON='
d=json.loads(raw.split(marker,1)[1]);d['TYPE']=sorted(d['TYPE']);d['VALUE']=sorted(d['VALUE'])
d['semantics']='Direct syntactic constant occurrences in actual theorem TYPE and VALUE; not necessity or a transitive graph.'
d['source_receipt']=bind(out/'dependency-probe-v2.json')
d['candidate_sha256']='55b37c648437e231f1b967cdc9cfa4102ce1bea6efde3ed81b23884604f89317'
d['axioms']=['propext','Classical.choice','Quot.sound'];assert 'sorryAx' not in d['VALUE']
d['counts']={k:len(d[k]) for k in ['TYPE','VALUE']}
d['selected_value_dependencies']=[x for x in d['VALUE'] if x.startswith('EReal.') or x in ['norm_sub_rev','div_pos','div_lt_one','mul_pos','mul_nonneg','div_nonneg','sq_nonneg']]
(out/'actual-dependencies-v1.json').write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
(out/'dependency-probe-v2-console-failure.json').write_text(json.dumps(dict(classification='ENV_BLOCKED',scope='Python console rendering after completed Lean subprocess and saved raw/receipt',actual_lean_exit=0,wrapper_exit=1,error='GBK console UnicodeEncodeError on subscript in dependency name',evidence='dependency-probe-v2.json saved before print; stdout raw includes complete JSON and axioms',mathematical_failure=False,repair='Parse saved UTF8 raw via Python -X utf8; no unnecessary Lean replay'),indent=2)+'\n')
# Probe is exact candidate plus diagnostic commands; no changed theorem BODY.
c=(out/'Candidate-v1.lean').read_bytes();pr=(out/'DependencyProbe-v2.lean').read_bytes();assert pr.startswith(c)
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();status=subprocess.check_output(['git','status','--porcelain=v1'],text=True).strip()
report=dict(status='FOCUSED_CANDIDATE_COMPILED_AWAITING_INDEPENDENT_BODY_REVIEW',candidate=bind(out/'Candidate-v1.lean'),focused=bind(out/'candidate-v1.json'),fence=bind(out/'statement-fence-v1.json'),probe=bind(out/'dependency-probe-v2.json'),actual_dependencies=bind(out/'actual-dependencies-v1.json'),probe_exact_candidate_prefix=True,axioms=d['axioms'],current_head=head,current_status=status,first_proof_attempt_actual_exit=0,diagnostic_failures_retained=['dependency-probe-v1-failure.json','dependency-probe-v2-console-failure.json'],production_changed=False,canaries='not authored; separate header freeze required',remaining='Independent BODY/source review, production authorization, fresh combined root/Tests/harness/axioms, reader/site/canary/purification/Exposition/contribution/PR; C2 partial false/null,7+6/fullB4/parents OPEN')
(out/'candidate-delivery-v1.json').write_text(json.dumps(report,indent=2)+'\n')
files=[bind(p) for p in sorted(out.iterdir()) if p.is_file() and p.name!='artifact-manifest-v1.json']
(out/'artifact-manifest-v1.json').write_text(json.dumps(files,indent=2)+'\n')
print(json.dumps({'counts':d['counts'],'selected':d['selected_value_dependencies'],'delivery':bind(out/'candidate-delivery-v1.json'),'deps':bind(out/'actual-dependencies-v1.json'),'manifest':bind(out/'artifact-manifest-v1.json')},ensure_ascii=True,indent=2))
