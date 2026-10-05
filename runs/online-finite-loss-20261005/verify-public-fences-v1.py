"""Bind public statements to the immutable draft headers; guards are not compilation."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;public='BanditRLProof/OnlineConstraintFiniteLoss.lean'
freeze=json.loads((run/'draft-freeze-v1.json').read_text(encoding='utf-8'))
def gate(label,args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
for n,h in freeze['headers'].items():
    assert hashlib.sha256(lean_declaration_header(Path(public),n).encode()).hexdigest()==h
    output=run/('native-public-fences/'+n+'.json')
    args=[sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineConvex.'+n,'--file',public,'--output',str(output)]
    if n=='effectiveDomain_add_indicator':args+=['--source-assumption','(hbot : ∀ x, f x ≠ ⊥)']
    gate('public-fence-'+n+'-v1',args)
    assert json.loads(output.read_text(encoding='utf-8'))['statement_hash']==h
    gate('public-safe-'+n+'-v1',[sys.executable,'-X','utf8','tools/bandit.py','safe-verify','--fence',str(output),'--lean-file',public])
print('Both public headers unchanged; actual native safe guards passed.')
