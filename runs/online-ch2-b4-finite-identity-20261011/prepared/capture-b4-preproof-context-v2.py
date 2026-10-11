import hashlib,json,subprocess,zipfile
from pathlib import Path
from datetime import datetime,timezone

ROOT=Path.cwd();DOC=Path('docs/contracts/online-ch2-b4-finite-identity-v1');RUN=Path('runs/online-ch2-b4-finite-identity-20261011')
OUT=Path('tmp/online-ch2-b4-finite-identity-preproof-20261011/capture-v2')
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.now(timezone.utc).isoformat()
def write(p,b):
 p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists(),str(p);p.write_bytes(b)
def js(p,o):write(p,(json.dumps(o,ensure_ascii=False,indent=2)+'\n').encode())
def command(tag,args,cwd=ROOT):
 start=now();r=subprocess.run(args,cwd=str(cwd),stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 write(OUT/(tag+'.stdout.raw'),r.stdout);write(OUT/(tag+'.stderr.raw'),r.stderr)
 js(OUT/(tag+'.receipt.json'),{'argv':args,'cwd':str(cwd),'startUTC':start,'endUTC':now(),'actual_exit':r.returncode,'stdout_sha256':sha(r.stdout),'stderr_sha256':sha(r.stderr)})
 assert r.returncode==0,(tag,r.returncode)
 return r.stdout
def git(*a):return subprocess.check_output(['git',*a],cwd=str(ROOT)).decode().strip()
def selection():
 names=set()
 for directory in [Path('BanditRLProof'),Path('Tests'),DOC,RUN]:
  for p in directory.rglob('*'):
   if p.is_file() and (directory in [DOC,RUN] or p.suffix=='.lean'):names.add(p.as_posix())
 tracked=git('ls-files','-z').split('\0')
 for x in tracked:
  if not x:continue
  if (x.startswith('BanditRLProof/') or x.startswith('Tests/')) and x.endswith('.lean'):names.add(x)
  if x.startswith(DOC.as_posix()+'/') or x.startswith(RUN.as_posix()+'/'):names.add(x)
 names.update(['BanditRLProof.lean','Tests.lean','lean-toolchain','lakefile.lean','lake-manifest.json','MANIFEST.md','AGENTS.md','CONTRIBUTING.md','docs/contributor-codex-contract.md','docs/theorem-publication-protocol.md','docs/proof-digestion-protocol.md','docs/evidence-routed-memory-protocol.md','docs/openai-math-assimilation-protocol.md','research-wiki/openai-math-2026-intake.json','runs/process_memory.json','docs/contracts/online-ch2-complete-target-freeze-v1/effective-targets-frozen-v3.2.json','tools/bandit.py','tools/check_contributor_contract.py','tools/check_process_memory.py','.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Module.lean','.lake/packages/mathlib/Mathlib/Tactic.lean'])
 return sorted(names)
def rows():return [{'path':x,'sha256':sha(Path(x).read_bytes()),'bytes':Path(x).stat().st_size} for x in selection()]
assert not OUT.exists()
before_HEAD=command('HEAD-before',['git','rev-parse','HEAD']).decode().strip()
before_branch=command('branch-before',['git','branch','--show-current']).decode().strip()
assert before_branch=='codex/research-online-ch2-b4-finite-identity'
assert command('status-before',['git','status','--porcelain'])==b''
assert not Path('BanditRLProof/OnlineCumulativePotential.lean').exists()
assert not Path('Tests/OnlineCumulativePotentialCanary.lean').exists()
before=rows();js(OUT/'source-RAW-before.json',before)
version=command('lean-version',['lake','env','lean','--version']).decode().strip()
mathlib=Path('.lake/packages/mathlib')
mathlib_HEAD=command('mathlib-HEAD-before',['git','rev-parse','HEAD'],mathlib).decode().strip()
assert mathlib_HEAD=='5e932f97dd25535344f80f9dd8da3aab83df0fe6'
assert command('mathlib-tracked-status-before',['git','status','--porcelain','--untracked-files=no'],mathlib)==b''
zip_path=OUT/'selected-preproof-source.zip'
with zipfile.ZipFile(zip_path,'x',compression=zipfile.ZIP_DEFLATED) as z:
 for r in before:z.writestr(r['path'],Path(r['path']).read_bytes())
with zipfile.ZipFile(zip_path) as z:
 assert sorted(z.namelist())==[r['path'] for r in before]
 assert all(sha(z.read(r['path']))==r['sha256'] for r in before)
after=rows();js(OUT/'source-RAW-after.json',after)
assert before==after
assert not Path('BanditRLProof/OnlineCumulativePotential.lean').exists()
assert not Path('Tests/OnlineCumulativePotentialCanary.lean').exists()
assert command('mathlib-HEAD-after',['git','rev-parse','HEAD'],mathlib).decode().strip()==mathlib_HEAD
assert command('mathlib-tracked-status-after',['git','status','--porcelain','--untracked-files=no'],mathlib)==b''
assert command('status-after',['git','status','--porcelain'])==b''
assert command('HEAD-after',['git','rev-parse','HEAD']).decode().strip()==before_HEAD
assert command('branch-after',['git','branch','--show-current']).decode().strip()==before_branch
seal=json.loads((DOC/'leaf-freeze-receipt-v1.json').read_bytes())
assert all(sha(Path(r['path']).read_bytes())==r['sha256'] for r in seal['frozen_inputs'])
js(OUT/'receipt.json',{'UTC':now(),'task':'ONLINE-CH2-B4-FINITE-IDENTITY-20261011','HEAD':before_HEAD,'branch':before_branch,'clean_before_after':True,'core_and_canary_absent_before_after':True,'seal_sha256':sha((DOC/'leaf-freeze-receipt-v1.json').read_bytes()),'helper_sha256':sha(Path(__file__).read_bytes()),'frozen_inputs_unchanged':True,'source_RAW_before':{'path':str(OUT/'source-RAW-before.json'),'sha256':sha((OUT/'source-RAW-before.json').read_bytes()),'rows':len(before)},'source_RAW_after':{'path':str(OUT/'source-RAW-after.json'),'sha256':sha((OUT/'source-RAW-after.json').read_bytes()),'rows':len(after)},'selection':'All actual on-disk BanditRLProof/Tests .lean including ignored/untracked; all actual current bounded DOC/RUN including ignored/untracked; roots/pins/current governance/inventory/checker files and two exact Mathlib import sources. Does not claim whole Git historical RUN snapshot. Selection recomputed before/after; all rows identical and actual ZIP verified.','selected_zip_sha256':sha(zip_path.read_bytes()),'selected_zip_entries':len(before),'lean_version':version,'Mathlib_clean_HEAD_before_after':mathlib_HEAD,'authorization':'Context evidence only. Independent verification and explicit parent BODY authorization still required.'})
print('preproof-captured',before_HEAD,'rows',len(before),'receiptSHA',sha((OUT/'receipt.json').read_bytes()))
