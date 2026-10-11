from pathlib import Path
import hashlib,json,subprocess,datetime,sys
root=Path('E:/ABRL/worktrees/research-online-book'); out=root/'tmp/online-ch2-b4-finite-identity-core-20261011'
def sha(b):return hashlib.sha256(b).hexdigest()
def put(n,b):
 if isinstance(b,str):b=b.encode()
 with (out/n).open('xb') as f:f.write(b)
v=sys.argv[1]
h=(root/'docs/contracts/online-ch2-b4-finite-identity-v1/neutral-frozen-header-v1.txt').read_bytes(); assert sha(h)=='92e0dcfac53595e35b68bfd8083c09640d06da809355ab02ec4eb4b007b0bd67'
marker=b'\n\nend BanditRL.OnlineCumulativePotential\n'; prefix,suffix=h.split(marker)
body=(out/('body-'+v+'.txt')).read_bytes()
candidate=prefix+b' := by\n'+body+marker
assert candidate.split(b' := by\n',1)[0]+marker==h
core=root/'BanditRLProof/OnlineCumulativePotential.lean'
core.write_bytes(candidate);put('candidate-'+v+'.lean',candidate)
start=datetime.datetime.now(datetime.timezone.utc).isoformat()
argv=['lake','env','lean','BanditRLProof/OnlineCumulativePotential.lean']
p=subprocess.run(argv,cwd=str(root),stdout=subprocess.PIPE,stderr=subprocess.PIPE)
put('focused-'+v+'.stdout.raw',p.stdout);put('focused-'+v+'.stderr.raw',p.stderr)
put('focused-'+v+'.json',json.dumps(dict(argv=argv,cwd=str(root),startUTC=start,endUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),actual_exit=p.returncode,candidate_sha256=sha(candidate),stdout_sha256=sha(p.stdout),stderr_sha256=sha(p.stderr),failure_class='NONE' if p.returncode==0 else 'IMPLEMENTATION_FAILED',HEAD=subprocess.check_output(['git','rev-parse','HEAD'],cwd=str(root)).decode().strip(),header_erasure_exact=True),indent=2)+'\n')
print('actual_exit',p.returncode)