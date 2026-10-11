from pathlib import Path
import subprocess,json,datetime,hashlib
root=Path('E:/ABRL/worktrees/research-online-book');out=root/'tmp/online-ch2-b4-next-strong-convex-header-20261011'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(n,s):
 with (out/n).open('xb') as f:f.write(s.encode('utf-8') if isinstance(s,str) else s)
def dump(n,x):put(n,json.dumps(x,indent=2)+'\n')
def run(n,argv):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat();r=subprocess.run(argv,cwd=str(root),stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 put(n+'.stdout.raw',r.stdout);put(n+'.stderr.raw',r.stderr);dump(n+'.json',dict(argv=argv,cwd=str(root),startUTC=t,endUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),actual_exit=r.returncode,stdout_sha256=hashlib.sha256(r.stdout).hexdigest(),stderr_sha256=hashlib.sha256(r.stderr).hexdigest()));print(n,r.returncode);return r
inputs=['tmp/online-ch2-b4-next-strong-convex-source-interface-20261011/source-interface-v1.json','tmp/online-ch2-b4-next-mathematical-readiness-20261011/v1.json','.lake/packages/mathlib/Mathlib/Analysis/Convex/Strong.lean','BanditRLProof/OnlineClosedProper.lean','BanditRLProof/OnlineConvexExtended.lean','lean-toolchain','lakefile.lean','lake-manifest.json']
def context():return dict(UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),HEAD=subprocess.check_output(['git','rev-parse','HEAD'],cwd=str(root)).decode().strip(),status=subprocess.check_output(['git','status','--short'],cwd=str(root)).decode(),hashes={p:sha(root/p) for p in inputs})
before=context();dump('context-before-v1.json',before)
assert before['hashes'][inputs[0]]=='39aff6e1805f55be87f4cf2cfe0f03c54f07effc3a6246beb6da50de79d34aea'
header=(out/'neutral-complete-header-v1.txt').read_text(encoding='utf-8');old='theorem stronglyConvex_minimum_growth';new='def stronglyConvex_minimum_growth_typeprobe'
probe=header.replace(old,new,1).replace('(hq : q ∈ V) :\n','(hq : q ∈ V) : Prop :=\n',1)
commands='\n#check stronglyConvex_minimum_growth_typeprobe\n#print stronglyConvex_minimum_growth_typeprobe\n#check SourceProper\n#print SourceProper\n#print effectiveDomain\n#print StrongConvexOn\n#print UniformConvexOn\n#check IsMinOn\n#check EReal.coe_toReal\n#check EReal.toReal_le_toReal\n'
end='\nend BanditRL.OnlineConvex\n';probe=probe.replace(end,commands+end)
undo=probe.replace(commands+end,end).replace(new,old,1).replace('(hq : q ∈ V) : Prop :=\n','(hq : q ∈ V) :\n',1);assert undo==header
put('HeaderTypeProbe.lean',probe)
run('bounded-retrieval-v1',['rg','-n','def UniformConvexOn|def StrongConvexOn|theorem coe_toReal|theorem toReal_le_toReal|def SourceProper|def effectiveDomain','.lake/packages/mathlib/Mathlib/Analysis/Convex/Strong.lean','.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean','BanditRLProof/OnlineClosedProper.lean','BanditRLProof/OnlineConvexExtended.lean'])
r=run('header-elaboration-v1',['lake','env','lean','tmp/online-ch2-b4-next-strong-convex-header-20261011/HeaderTypeProbe.lean'])
after=context();dump('context-after-v1.json',after);assert before['hashes']==after['hashes']
dump('elaboration-receipt-v1.json',dict(actual_exit=r.returncode,complete_header_sha256=sha(out/'neutral-complete-header-v1.txt'),probe_sha256=sha(out/'HeaderTypeProbe.lean'),reverse_transform_exact=True,canonical_status_before=before['status'],canonical_status_after=after['status'],HEAD_before=before['HEAD'],HEAD_after=after['HEAD'],readiness_only=True,proof_BODY=False))