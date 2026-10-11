from pathlib import Path
import hashlib,json,subprocess,sys,datetime
r=Path.cwd();d=r/'tmp/online-main-latest-sync-20261011';py='C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
cmds=json.loads((d/'gate-commands-v5.json').read_bytes());rec=r/'runs/online-ch2-b4-finite-identity-20261011/prepared/capture-gate-v2.py'
assert hashlib.sha256(rec.read_bytes()).hexdigest()=='bafe784fad8810f866105ffd19e3504f70ebf1e28949611549d584630a5b7ce8'
assert subprocess.check_output(['git','status','--porcelain=v1','-z'],cwd=r)==b''
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r).decode().strip();assert head==sys.argv[1]
prefix=[py,'-B','-X','utf8',str(rec),'--root',str(r),'--run','tmp/online-main-reconciliation-gates-20261011','--leaf-contract','docs/contracts/online-book-v1','--leaf-contract','docs/contracts/online-main-reconciliation-v1']
for source in ['AGENTS.md','CONTRIBUTING.md','docs/contributor-codex-contract.md','docs/theorem-publication-protocol.md','docs/proof-digestion-protocol.md','docs/evidence-routed-memory-protocol.md','docs/openai-math-assimilation-protocol.md','research-wiki/openai-math-2026-intake.json','website/static/site.css']:
 prefix+=['--owned-source',source]
results=[]
for row in cmds:
 label=row['role']+'-v5';argv=prefix+['--label',label,'--',*row['argv']]
 print('START '+label,flush=True)
 with (d/(label+'.runner2.recorder.stdout.raw')).open('xb') as o,(d/(label+'.runner2.recorder.stderr.raw')).open('xb') as e:p=subprocess.run(argv,cwd=r,stdout=o,stderr=e)
 result={'role':row['role'],'argv':argv,'recorder_exit':p.returncode};results.append(result)
 print('END '+label+' actual recorder exit '+str(p.returncode),flush=True)
 if p.returncode!=0:break
out=d/'gate-runner-execution-v5.json';out.write_bytes((json.dumps({'head':head,'results':results,'scope':'Actual recorder child calls; inspect every nested receipt before any gate acceptance.'},indent=2)+'\n').encode());sys.exit(0 if len(results)==9 and all(x['recorder_exit']==0 for x in results) else 1)
