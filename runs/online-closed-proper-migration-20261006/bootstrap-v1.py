"""Audit the existing closed/proper source package and bind actual declaration probes."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
run=Path(__file__).parent;task='ONLINE-CLOSED-PROPER-MIGRATION-20261006'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip()=='codex/research-online-closed-proper-migration'
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip()=='f989706461cb466bc290261f4845f113621e807d'
assert subprocess.check_output(['git','rev-parse','origin/main'],encoding='utf-8').strip()=='6847b678a73db68dee5101d6f05c2453c1405afc'
assert not subprocess.check_output(['git','-C','E:/ABRL/research','status','--porcelain'],encoding='utf-8')
common=subprocess.check_output(['git','rev-parse','--git-common-dir'],encoding='utf-8').strip();assert common=='E:/ABRL/research/.git'
write(run/'workspace-audit-v1.json',dict(branch='codex/research-online-closed-proper-migration',stacked_base_PR=165,stacked_base='f989706461cb466bc290261f4845f113621e807d',origin_main='6847b678a73db68dee5101d6f05c2453c1405afc',canonical_clean=True,common_git=common,worktrees_porcelain=subprocess.check_output(['git','worktree','list','--porcelain'],encoding='utf-8'),reused_checkout='E:/ABRL/worktrees/research-online-book',other_checkouts_ignored_files_stores_junctions_preserved=True,merged=False,live=False))
write(run/'00_context.md','''Persistent real Orabona Chapters1–16 Goal ACTIVE/unbudgeted. Canonical E:/ABRL/research clean/main6847b678a73db68dee5101d6f05c2453c1405afc freshly fetched; shared Git E:/ABRL/research/.git. Reused isolated research-online-book on codex/research-online-closed-proper-migration, exact OPENdraftPR165 final f989706461cb466bc290261f4845f113621e807d stacked base, not main. Direct delivery checks matched local/remote/REST heads, clean checkout and all407current Huber raw Git blobs. An initial read-only inline-Python final-check command used literal newline escapes and failed to parse; corrected direct check passed, no mathematical/production change. Subsequent read-only next-package rg wildcard mistake resolved using --glob and actual file listing. Other active worktrees (including independently advanced extended-topics), shared stores/junctions, ignored/private/anonymous/generated_site preserved.

Requested GPT-6 Astra/medium all roles, no upgrades or runtime-model attestation. Only Definition2.16/Example2.17/Definition2.18/Example2.19 and associated unnumbered lower-semicontinuity equivalence, printed16/PDF28:3retained proofs/2full definitions/whole6canaryproofs, zero new mathematical code/nodes expected. Current source/contract/body/reader/gates revalidation pending. Legacy10beforepackage, only9after OnlineClosedProper passes; Chapter1migration/Chapter2 mandatorytotalnull/incomplete/wholeGoal active, Chapters3–16 mandatory unenumerated. Old20261003 accepted artifacts remain historical, not current review evidence. No merge/deploy/retirement/competing Chapter3 proof writing.

Source closedness uses real finite thresholds; actual equivalence must include mathlib EReal thresholds including both infinities and bottom-valued losses, without adding properness/no-bottom/convexity/Hausdorff premises. Source properness means nowhere bottom plus one finite-real value; source excludes identically top even on an empty ambient type. Shared zero-on-V/top-outside extendedIndicator stays canonical. Actual topological generality/actual @types (unused TopologicalSpace may disappear from properness) must be compiled and reviewed; no guessing from namespace variables. Genuine nonconstant interval indicator, bottom closed/lsc but improper and empty indicator improper canaries, complete11namedaxes/3nativeguards planned. Source4numbered anchors plus unnumbered equivalence, not3newprintedproofresults. Single lower retained route; three distinct required automated roles with restricted current packet and honest prior-history limits, no human/external review claim. Native command gates and role/prompt/file convention stages remain separate.

Current authoritative private harness.tex SHA31370babc09de16f536d2f975902b035fe02ba3c290deb3380501efd24a848e6 was freshly rechecked/read for lifecycle/role/conversion-window gates against actual docs/CLI. Historical hardening doc reports absence of root AGENTS at its old baseline; current AGENTS exists and was read. Current contributor/publication/domain/semantic rules retain shared library/registry, exact contracts, distinct actors and combined acceptance gates. No private manuscript content copied into this public run.''')
helper=run/'run-command.py';assert not helper.exists();helper.write_bytes(Path('runs/online-huber-migration-20261006/run-command.py').read_bytes())
public=Path('BanditRLProof/OnlineClosedProper.lean');canary=Path('Tests/OnlineClosedProperCanary.lean')
text=public.read_text(encoding='utf-8');names=re.findall(r'(?m)^theorem\s+(\w+)',text);defs=re.findall(r'(?m)^(?:noncomputable\s+)?def\s+(\w+)',text)
assert names==['sourceClosed_iff_lowerSemicontinuous','sourceClosed_indicator_iff','sourceProper_indicator_iff'] and defs==['SourceClosed','SourceProper']
scope=[];canary_names=[]
for line in canary.read_text(encoding='utf-8').splitlines():
 m=re.match(r'^namespace\s+(\S+)',line)
 if m:scope.append(m.group(1));continue
 if re.match(r'^end\b',line):scope.pop();continue
 m=re.match(r'^(?:theorem|lemma)\s+(\w+)',line)
 if m:canary_names.append('.'.join(scope+[m.group(1)]))
assert len(canary_names)==len(set(canary_names))==6
for p in [public,canary,Path('BanditRLProof.lean'),Path('Tests.lean')]:
 dest=run/('original-'+p.name+'.txt');assert not dest.exists();dest.write_bytes(p.read_bytes())
full=['BanditRL.OnlineConvex.'+n for n in names+defs];allnames=full+canary_names
write(run/'public-named-declarations-v1.json',dict(public_proofs=full[:3],public_definitions=full[3:],canary_proofs=canary_names,canary_definitions=[],new_proofs=0,axiom_probe=allnames))
write(run/'leaves/actual-types-v1.lean','import BanditRLProof\nimport Tests.OnlineClosedProperCanary\nset_option pp.universes true\nset_option pp.explicit true\n'+''.join('#check @'+n+'\n' for n in allnames))
write(run/'leaves/actual-types-readable-v2.lean','import BanditRLProof\nimport Tests.OnlineClosedProperCanary\n'+''.join('#check @'+n+'\n' for n in allnames))
write(run/'bootstrap-generated-before-use-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [helper,run/'leaves/actual-types-v1.lean',run/'leaves/actual-types-readable-v2.lean']],before_first_use=True))
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(helper),label,*args],check=True)
gate('CLI-help-v1-01',sys.executable,'-X','utf8','tools/bandit.py','--help')
gate('lifecycle-help-v1-01',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--help')
gate('fence-help-v1-01',sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--help')
gate('local-retrieval-help-v1-01',sys.executable,'-X','utf8','tools/bandit.py','list-lean-decls','--help')
print('Bounded closed/proper setup and11actual type probes bound before use;3retainedproofs2defs6canaryproofs, no source acceptance yet.')
