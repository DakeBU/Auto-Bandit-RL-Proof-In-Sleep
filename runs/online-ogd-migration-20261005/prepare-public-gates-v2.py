"""Freeze actual public exports, valid assumption fences and the named axiom probe."""
from pathlib import Path
import hashlib, json, re, subprocess, sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header, _strip_lean_comments
run=Path(__file__).parent
module=Path('BanditRLProof/OnlineGradientDescentSource.lean')
canary=Path('Tests/OnlineGradientDescentSourceCanary.lean')
contract=Path('docs/contracts/online-ogd-migration-v2')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,obj):
    with Path(p).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(obj,str):f.write(obj)
        else:json.dump(obj,f,indent=2);f.write('\n')
def gate(label,*args):
    subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
prefix=module.read_text(encoding='utf-8').split('theorem source_to_feasible',1)[0]
context=(contract/'context.lean.txt').read_text(encoding='utf-8').rsplit('end BanditRL.OnlineGradientDescentSource',1)[0]
assert tokens(prefix)==tokens(context)
for path in ['BanditRLProof/OnlineGradientDescent.lean','BanditRLProof/OnlineGradientDescentVariable.lean']:
    snapshot=run/'leaves'/('pre-integration-'+path.replace('/','--')+'.txt')
    assert tokens(snapshot.read_text(encoding='utf-8'))==tokens(Path(path).read_text(encoding='utf-8'))
freeze=load(run/'freeze-review-v2.json')
(run/'public-fences').mkdir(exist_ok=True)
headers={}
for name,hh in freeze['headers'].items():
    header=lean_declaration_header(module,name)
    assert hashlib.sha256(header.encode()).hexdigest()==hh,name
    headers[name]=dict(statement=header,statement_hash=hh)
    # The native safe verifier checks header substrings, not paths to source cards.
    # Retain the old draft capture unchanged; make valid public fences separately.
    assumptions=[];start=None;depth=0
    for i,ch in enumerate(header):
        if ch=='(':
            if depth==0:start=i
            depth+=1
        elif ch==')':
            depth-=1
            if depth==0 and header[start:start+2]=='(h':assumptions.append(header[start:i+1])
    fence=run/'public-fences'/(name+'.json')
    cmd=[sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration',
        'BanditRL.OnlineGradientDescentSource.'+name,'--file',str(module),'--output',str(fence)]
    for a in assumptions:cmd+=['--source-assumption',a]
    gate('public-fence-v2-'+name,*cmd)
    assert load(fence)['statement_hash']==hh
    gate('safe-public-v2-'+name,sys.executable,'-X','utf8','tools/bandit.py','safe-verify',
         '--fence',str(fence),'--lean-file',str(module),'--lean-file',str(canary))
new_names=['BanditRL.OnlineGradientDescentSource.'+n for n in
    ['FeasibleRegularLoss','SourceRegularLoss']+list(freeze['headers'])]
canary_names=['Tests.OnlineGradientDescentSource.'+n for _,n in
    re.findall(r'(?m)^(?:@\[simp\] )?(theorem|def|abbrev)\s+(\w+)',canary.read_text(encoding='utf-8'))]
old_names=['BanditRL.OnlineGradientDescent.'+n for n in
    ['Domain','project','RegularLoss','step','iterate','regret','iterateVariable','regretVariable']+
    list(load(Path('docs/contracts/online-ogd-migration-v1/native-headers-v1.json')))]
assert len(new_names)==14 and len(canary_names)==37 and len(old_names)==24
names=new_names+canary_names+old_names;assert len(names)==75 and len(set(names))==75
probe='import BanditRLProof\nimport Tests.OnlineGradientDescentSourceCanary\n\n'
for n in names:probe+='#check @'+n+'\n#print axioms '+n+'\n'
write(run/'leaves/public-axioms-v2.lean',probe)
write(run/'public-named-declarations-v2.json',dict(new_public=new_names,canary=canary_names,
    old_reused=old_names,axiom_probe=names,expected_actual_names=75))
write(run/'public-fence-audit-v2.json',dict(status='passed',headers=headers,
    frozen_headers=12,context_semantic_tokens_unchanged=True,old_lean_code_tokens_unchanged=True,
    native_public_safe_verifications=12,
    draft_capture_caveat='Original draft fences used source-intent paths as source_assumption metadata. '
        'Creation captured headers only; such paths are not header substrings required by safe-verify. '
        'Original captures/receipts remain unchanged. These separate public fences preserve actual '
        'Lean hypothesis fragments; source-card/PDF fingerprints remain separate raw evidence.',
    public_module_sha256=sha(module),public_canary_sha256=sha(canary),
    body_review='pending',package_accepted=False))
gate('public-declaration-retrieval-v2',sys.executable,'-X','utf8','tools/bandit.py','list-lean-decls',
     '--include-tests','--statement','OnlineGradientDescentSource')
print('Twelve actual public fences/safe guards passed;75 named axiom/check targets prepared.')
