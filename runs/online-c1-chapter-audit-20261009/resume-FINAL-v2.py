from common_reader_v6 import *
import ast,base64

fixed()
write(RUN/'FINAL-preparation-failure-v1.md','The first cumulative-audit wrapper halted on candidate-full-diff-check-v2.log, a RAW diagnostic produced after the earlier11-file audit. No FINAL packet/index was issued. Actual cumulative output names12 files; its own new RAW diagnostic adds one further preserved log on staging. The new v2 check captures stdout as base64 in JSON, preserving exact output without recursively adding another whitespace-bearing diagnostic log. Existing11-file audit/digest remains historical, not current cumulative truth. Exactly13 current RAW exceptions require distinct FINAL adjudication; no code/reader/Test/contract exception is permitted.')
old=load(RUN/'candidate-diff-audit-v2.json')['retained_exact_RAW_exceptions']
extras=[RUN/'candidate-full-diff-check-v2.log',RUN/'FINAL-cumulative-full-diff-v1.log']
exceptions=rows([Path(x['path']) for x in old]+extras)
for x in old: assert sha(x['path'])==x['sha256']
assert len(exceptions)==13
gate('FINAL-stage-evidence-v2','git','add',RUN.relative_to(ROOT).as_posix())
def diff(label,args):
    command=['git','diff','--cached',BASE,'--check']+args
    p=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    write(RUN/(label+'.json'),dict(command=command,cwd=ROOT.as_posix(),actual_exit=p.returncode,
        stdout_base64=base64.b64encode(p.stdout).decode('ascii'),stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),
        encoding_note='Exact RAW bytes encoded as base64 to avoid recursive whitespace diagnostics'))
    return p
full=diff('FINAL-cumulative-full-diff-v2',[])
observed={s.split(':',1)[0] for s in full.stdout.decode('utf8').splitlines() if ': trailing whitespace.' in s or ': new blank line at EOF.' in s}
allowed={Path(x['path']).relative_to(ROOT).as_posix() for x in exceptions}
assert observed==allowed and full.returncode==2,(observed-allowed,allowed-observed)
scoped=diff('FINAL-cumulative-scoped-diff-v2',['--','.',*[':(exclude)'+p for p in sorted(allowed)]])
assert scoped.returncode==0
write(RUN/'FINAL-cumulative-diff-audit-v2.json',dict(base=BASE,
    actual_full_exit=2,exact_RAW_exceptions=exceptions,exception_count=13,exact_log_count=11,
    frozen_decoder_report_count=2,scoped_actual_exit=0,full_unexcluded_gate_zero=False,
    code_reader_contract_Test_exceptions=False,distinct_FINAL_adjudication_required=True))
write(RUN/'memory-digest-candidate-v4.md',(RUN/'memory-digest-candidate-v3.md').read_text('utf8').replace(
    'exactly11 old SHA-bound RAW exceptions (9 logs and2 frozen decoder reports)',
    'exactly13 current SHA-bound RAW exceptions (11 logs and2 frozen decoder reports), including diagnostics produced after the older11-file audit'))
write(RUN/'FINAL-delivery-state-v2.json',dict(
    actual_HEAD=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip(),
    canonical_main=subprocess.check_output(['git','-C','E:/ABRL/research','rev-parse','HEAD'],encoding='utf8').strip(),
    fetched_origin_main=subprocess.check_output(['git','rev-parse','origin/main'],encoding='utf8').strip(),
    canonical_status=subprocess.check_output(['git','-C','E:/ABRL/research','status','--porcelain'],encoding='utf8'),
    PR202=json.loads(subprocess.check_output(['gh','pr','view','202','--json','number,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt,url'],encoding='utf8')),
    worktree_kept_active=True,new_PR_pending=True,merge_deploy_authorized=False))
tree=ast.parse((RUN/'prepare-FINAL-v1.py').read_text('utf8'))
packet=next(n.value.args[1].s for n in tree.body if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call)
    and getattr(n.value.func,'id','')=='write' and isinstance(n.value.args[1],ast.Str)
    and n.value.args[1].s.startswith('# Distinct Chapter1 FINAL'))
packet=packet.replace('FINAL-inputs-v1.json','FINAL-inputs-v2.json').replace('exactly11 preserved oldRAW exceptions:9logs','exactly13 preserved currentRAW exceptions:11logs')
packet+='\nThe v1 FINAL-preparation script stopped before dispatch on an additional preserved diagnostic log. V2 current cumulative audit binds13 exceptions explicitly; two prior raw diagnostic logs were added since the historical11-file audit. New diagnostics store exact stdout base64 in JSON to prevent recursive whitespace logs. Inspect FINAL-preparation-failure-v1.md and FINAL-cumulative-diff-audit-v2.json. Current memory-digest-candidate-v4 supersedes v3 count only.\n'
write(RUN/'FINAL-review-packet-v2.md',packet)
historical=load(RUN/'chapter-canary-BODY-inputs-v2.json')
paths={Path(x['path']) for x in historical['rows']}
paths.update(p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
paths.update([PUBLIC,CANARY,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',CONTRIBUTION])
paths.update(Path(r['path']) for r in load(RUN/'reader-integration-bindings-v3.json')['rows'])
paths.update(ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows'])
paths.update([SITE/'chapters/online-foundations/index.html',SITE/'books/registry.json',SITE/'site-manifest.json'])
paths.update(SITE/p for p in load(RUN/'registry-v3.json')['module_HTML_sha256'])
assert all(p.is_file() for p in paths),[p.as_posix() for p in paths if not p.is_file()]
write(RUN/'FINAL-inputs-v2.json',dict(phase='distinct full Chapter1 integration FINAL; postnative/delivery pending',
    rows=rows(paths),whole_Goal_active=True,source_objects=17,generic_contracts=54,canaries=27,proof_total=None))
fixed()
print('FINAL packet v2 ready',len(paths),'current RAW inputs; exactly13 SHA-bound evidence exceptions.')
