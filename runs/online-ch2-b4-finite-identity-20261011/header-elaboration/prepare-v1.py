from pathlib import Path
import subprocess, hashlib, json, datetime
root=Path('E:/ABRL/worktrees/research-online-book')
out=root/'tmp/online-ch2-b4-finite-identity-formalizer-20261011'
out.mkdir(exist_ok=True)
def put(name,data):
    if isinstance(data,str): data=data.encode('utf-8')
    with (out/name).open('xb') as f: f.write(data)
def run(name,argv):
    start=datetime.datetime.now(datetime.timezone.utc).isoformat()
    p=subprocess.run(argv,cwd=str(root),stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    end=datetime.datetime.now(datetime.timezone.utc).isoformat()
    put(name+'.stdout.raw',p.stdout); put(name+'.stderr.raw',p.stderr)
    rec=dict(argv=argv,cwd=str(root),startUTC=start,endUTC=end,actual_exit=p.returncode,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stderr_sha256=hashlib.sha256(p.stderr).hexdigest())
    put(name+'.json',json.dumps(rec,indent=2)+'\n')
    print(name,p.returncode,p.stdout.decode('utf-8',errors='replace'),p.stderr.decode('utf-8',errors='replace'))
h=root/'tmp/online-ch2-b4-finite-identity-proposal-20261011/neutral-proposed-header-v1.txt'
b=h.read_bytes(); assert hashlib.sha256(b).hexdigest()=='92e0dcfac53595e35b68bfd8083c09640d06da809355ab02ec4eb4b007b0bd67'
s=b.decode('utf-8'); assert '\r' not in s
probe=s.replace('theorem finite_regret_identity','def finite_regret_identity_typeprobe',1).replace('(hT : 0 < T) :','(hT : 0 < T) : Prop :=',1)
probe=probe.replace('\nend BanditRL.OnlineCumulativePotential','\n#check finite_regret_identity_typeprobe\n#print finite_regret_identity_typeprobe\n\nend BanditRL.OnlineCumulativePotential')
put('HeaderOriginalContextProbe.lean',probe)
run('header-original-context-elaboration-v1',['lake','env','lean','tmp/online-ch2-b4-finite-identity-formalizer-20261011/HeaderOriginalContextProbe.lean'])
minimal=probe.replace('import Mathlib.Algebra.BigOperators.Module\nimport Mathlib.Tactic','import Mathlib.Algebra.BigOperators.Group.Finset.Basic\nimport Mathlib.Data.Real.Basic')
put('HeaderMinimalContextProbe.lean',minimal)
run('header-minimal-context-elaboration-v1',['lake','env','lean','tmp/online-ch2-b4-finite-identity-formalizer-20261011/HeaderMinimalContextProbe.lean'])
run('retrieval-telescope-names-v1',['rg','-n','sum_range_sub|sum_range_sub\x27|sum_range_succ',' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean'.strip()])