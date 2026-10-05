"""Audit the existing Huber source package and create bounded, hash-bound probes."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
run=Path(__file__).parent;task='ONLINE-HUBER-MIGRATION-20261006'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip()=='codex/research-online-huber-migration'
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip()=='52f628a7ae699887069c5a621d301901718ed772'
assert subprocess.check_output(['git','rev-parse','origin/main'],encoding='utf-8').strip()=='6847b678a73db68dee5101d6f05c2453c1405afc'
assert not subprocess.check_output(['git','-C','E:/ABRL/research','status','--porcelain'],encoding='utf-8')
common=subprocess.check_output(['git','rev-parse','--git-common-dir'],encoding='utf-8').strip();assert common=='E:/ABRL/research/.git'
write(run/'workspace-audit-v1.json',dict(branch='codex/research-online-huber-migration',stacked_base_PR=164,stacked_base='52f628a7ae699887069c5a621d301901718ed772',origin_main='6847b678a73db68dee5101d6f05c2453c1405afc',canonical_clean=True,common_git=common,worktrees_porcelain=subprocess.check_output(['git','worktree','list','--porcelain'],encoding='utf-8'),reused_checkout='E:/ABRL/worktrees/research-online-book',other_checkouts_ignored_files_stores_junctions_preserved=True,merged=False,live=False))
write(run/'00_context.md','Persistent real Orabona Chapters1–16 Goal ACTIVE/unbudgeted. Canonical E:/ABRL/research clean/main6847b678a73db68dee5101d6f05c2453c1405afc freshly fetched, shared Git E:/ABRL/research/.git. Reused isolated research-online-book on new codex/research-online-huber-migration, exact OPENdraftPR164 delivered52f628a7ae699887069c5a621d301901718ed772 stacked base, notmain. Other activeworktrees/stores/junctions/ignored/private/anonymous/generated_site preserved. Requested GPT-6 Astra/medium allroles/no upgrades/runtime attestation. Only Example2.15 Huber:19retainedproofs3definitions/whole14canaryproofs0defs, no new mathematical proof-count gain. Current source/contract/body/reader/gates revalidation pending; Chapter1migration/Chapter2totalnull/wholeGoal incomplete, legacy11beforefutureonly10afterOnlineHuberacceptance. No merge/deploy/retirement/Chapter3proofwriting. Earlier actual19proof source roundtrip accepted in old run, historical receipts cannot substitute for this current gate. Three distinct required automated actors, current restricted packets do not erase actor history. Guessed nonexistent bandit-paper-theorem-migration skill and Jensen bootstrap filename were read-only retrieval errors; actual rg skill catalog used, required local docs/domain skills read. Native command gates and role/file conventions distinguished.')
helper=run/'run-command.py';assert not helper.exists();helper.write_bytes(Path('runs/online-guessing-migration-20261006/run-command.py').read_bytes())
public=Path('BanditRLProof/OnlineHuber.lean');canary=Path('Tests/OnlineHuberCanary.lean')
text=public.read_text(encoding='utf-8');names=re.findall(r'(?m)^theorem\s+(\w+)',text);defs=re.findall(r'(?m)^(?:noncomputable\s+)?def\s+(\w+)',text)
assert len(names)==19 and defs==['huber','fullSpace','linearLoss']
scope=[];canary_names=[]
for line in canary.read_text(encoding='utf-8').splitlines():
 m=re.match(r'^namespace\s+(\S+)',line)
 if m:scope.append(m.group(1));continue
 if re.match(r'^end\b',line):scope.pop();continue
 m=re.match(r'^(?:theorem|lemma)\s+(\w+)',line)
 if m:canary_names.append('.'.join(scope+[m.group(1)]))
assert len(canary_names)==14 and len(set(canary_names))==14
for p in [public,canary,Path('BanditRLProof.lean'),Path('Tests.lean')]:
 (run/('original-'+p.name+'.txt')).write_bytes(p.read_bytes())
write(run/'public-named-declarations-v1.json',dict(public_proofs=['BanditRL.OnlineHuber.'+n for n in names],public_definitions=['BanditRL.OnlineHuber.'+n for n in defs],canary_proofs=canary_names,canary_definitions=[],new_proofs=0,axiom_probe=['BanditRL.OnlineHuber.'+n for n in names+defs]+canary_names))
probe='import BanditRLProof\nimport Tests.OnlineHuberCanary\nset_option pp.universes true\nset_option pp.explicit true\n'
probe+='\n'.join('#check @BanditRL.OnlineHuber.'+n for n in names+defs)+'\n'
probe+='\n'.join('#check @'+n for n in canary_names)+'\n'
write(run/'leaves/actual-types-v1.lean',probe)
write(run/'bootstrap-generated-before-use-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [helper,run/'leaves/actual-types-v1.lean']],before_first_use=True))
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(helper),label,*args],check=True)
gate('CLI-help-v1-01',sys.executable,'-X','utf8','tools/bandit.py','--help')
gate('lifecycle-help-v1-01',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--help')
gate('fence-help-v1-01',sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--help')
gate('local-retrieval-help-v1-01',sys.executable,'-X','utf8','tools/bandit.py','list-lean-decls','--help')
print('Current bounded Huber setup/probe hash-bound;19retainedproofs3defs/14wholecanaryproofs, source review and real elaboration still pending.')
