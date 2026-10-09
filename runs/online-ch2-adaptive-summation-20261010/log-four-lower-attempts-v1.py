from common import *
fixed()
assert not (RUN/'trials.jsonl').exists()
capture('trial-log-help-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--help')
for label,receipt,lean,before,note in [
    ('production-body-v1','production-focused-build-v1','BanditRLProof/OnlineAdaptiveSummation.lean',1,'Production frozen BODY focused build0; production BODY semantics separately reviewed; canary/package acceptance pending.'),
    ('canary-body-v1','canary-focused-build-v1','Tests/OnlineAdaptiveSummationCanary.lean',2,'Retained failure: integral_sub rewrite inferred id instead of target identity lambda. Route/type unchanged.'),
    ('canary-body-v2','canary-focused-build-v2','Tests/OnlineAdaptiveSummationCanary.lean',2,'Retained failure: actual global integral_id wrongly qualified intervalIntegral.integral_id. Exact pinned API audit repaired qualification.'),
    ('canary-body-v3','canary-focused-build-v3','Tests/OnlineAdaptiveSummationCanary.lean',2,'Both full frozen canary BODYs compiled after two recorded API repairs; semantic BODY/package gates pending.')]:
    r=load(RUN/(receipt+'.json'));status='compiled' if r['actual_exit']==0 else 'failed'
    capture('native-trial-'+label,sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status',status,'--notes','Retrospective append from immutable actual execution receipt; native log time is append time. '+note+' Bounded unaccepted obligations retained; not chapter counts.','--lean',lean,'--source','ORABONA-V10-L4.13','--run-id',RUN.name,'--attempt-id',label,'--worker-id','/root','--progress-class','unreviewed','--obligations-before',before,'--obligations-after',before,'--verifier-evidence',(RUN/(receipt+'.json')).relative_to(ROOT),'--lean-check-seconds',r['seconds'])
trial=RUN/'trials.jsonl';raw=trial.read_bytes();assert len(raw.splitlines())==4
attrs=RUN/'.gitattributes';old=attrs.read_bytes()
rule=b'trials.jsonl whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol\n'
assert b'trials.jsonl' not in old
if b'\r\n' in raw:
    attrs.write_bytes(old+rule)
write(RUN/'native-attempts-and-attributes-inspected-v1.json',dict(native_trial_count=4,compiled=2,failed=2,trials=rows([trial]),ordinary_whitespace_checks_retained=True,attribute_delta=dict(path=attrs.as_posix(),before_sha256=hashlib.sha256(old).hexdigest(),before_raw_base64=base64.b64encode(old).decode('ascii'),after_sha256=sha(attrs),literal_rule_added=rule.decode('ascii') if b'\r\n' in raw else None),reviewer_validated=False,accepted=False,chapter_complete=False,whole_Goal='active'))
fixed()
