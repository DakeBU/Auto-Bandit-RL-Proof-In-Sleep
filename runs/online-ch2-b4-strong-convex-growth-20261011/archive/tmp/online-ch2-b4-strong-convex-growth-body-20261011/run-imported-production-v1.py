from pathlib import Path
import json,hashlib,subprocess,datetime,sys
out=Path('tmp/online-ch2-b4-strong-convex-growth-body-20261011');p=out/'ImportedProductionProbe-v1.lean'
def bind(p):
 p=Path(p);b=p.read_bytes();return dict(path=p.as_posix(),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def git(*args):return subprocess.check_output(['git',*args])
r={'argv':['lake','env','lean',str(p)],'utc_start':datetime.datetime.now(datetime.timezone.utc).isoformat(),'probe':bind(p),'head_before':git('rev-parse','HEAD').decode().strip(),'dirty_before_hex':git('status','--porcelain=v1','-z').hex(),'module_before':bind('BanditRLProof/OnlineStrongConvexMinimum.lean'),'public_root_before':bind('BanditRLProof.lean')}
x=subprocess.run(r['argv'],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
(out/'imported-production-v1.stdout.raw').write_bytes(x.stdout);(out/'imported-production-v1.stderr.raw').write_bytes(x.stderr)
r.update(actual_exit=x.returncode,utc_end=datetime.datetime.now(datetime.timezone.utc).isoformat(),head_after=git('rev-parse','HEAD').decode().strip(),dirty_after_hex=git('status','--porcelain=v1','-z').hex(),module_after=bind('BanditRLProof/OnlineStrongConvexMinimum.lean'),public_root_after=bind('BanditRLProof.lean'),stdout=bind(out/'imported-production-v1.stdout.raw'),stderr=bind(out/'imported-production-v1.stderr.raw'))
(out/'imported-production-v1.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
print('actual_exit',x.returncode)
if x.returncode:print(x.stdout.decode('utf-8',errors='replace'))
