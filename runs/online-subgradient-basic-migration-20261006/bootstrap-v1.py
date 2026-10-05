"""Freeze retained next source scope and bind exact public declaration probes."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
from pypdf import PdfReader
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-BASIC-MIGRATION-20261006'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
base='283e359e2b85740ad557574d337d6f4a1d55fe8f';main='6847b678a73db68dee5101d6f05c2453c1405afc'
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip()=='codex/research-online-subgradient-basic-migration'
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip()==base
assert subprocess.check_output(['git','rev-parse','origin/main'],encoding='utf-8').strip()==main
assert not subprocess.check_output(['git','-C','E:/ABRL/research','status','--porcelain'],encoding='utf-8')
common=subprocess.check_output(['git','rev-parse','--git-common-dir'],encoding='utf-8').strip();assert common=='E:/ABRL/research/.git'
pr=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/166']))
assert pr['state']=='open' and pr['draft'] and not pr['merged'] and pr['head']['sha']==base
assert subprocess.check_output(['git','ls-remote','origin','refs/heads/codex/research-online-closed-proper-migration'],encoding='utf-8').split()[0]==base
write(run/'workspace-audit-v1.json',dict(branch='codex/research-online-subgradient-basic-migration',stacked_base_PR=166,stacked_base=base,origin_main=main,canonical_clean=True,common_git=common,worktrees_porcelain=subprocess.check_output(['git','worktree','list','--porcelain'],encoding='utf-8'),reused_checkout='E:/ABRL/worktrees/research-online-book',prior_PR_OPEN_draft_unmerged=True,prior_current_run_all_raw_Git_blobs_verified=315,other_checkouts_stores_junctions_ignored_files_preserved=True,merged=False,live=False))
write(run/'00_context.md','''Persistent real Orabona Chapters1–16 Goal ACTIVE/unbudgeted. Canonical E:/ABRL/research clean/main6847b678a73db68dee5101d6f05c2453c1405afc freshly fetched, shared Git E:/ABRL/research/.git; other active worktrees/stores/.lake/runtime junctions/ignored/private/anonymous/generated_site preserved. Reused isolated checkout on codex/research-online-subgradient-basic-migration after prior finalclean/localremoteRESTexacthead/315rawfile equality. Exact OPENdraftPR166283e359e2b85740ad557574d337d6f4a1d55fe8f stackedbase, notmain. Local/remote branch absence checked before create; show-ref absent returned diagnostic as expected, no override/reset.

Only Definition2.20, adjacent necessary global-support/domain observation and Theorem2.21, printed16–17/PDF28–29. Two retained proofs/one COMPLETE definition/whole3canaryproofs, zero new mathcode/nodes expected. Source actual definition-global supports, proper+convex outside-domain observation versus actual proper-only point-finiteness, and actual real-valued convex-on-convex-V theorem must be frozen/reviewed after actual type/retrieval/compiled graph. Both∞/globalfinitewitness/properness, global not merely local support, arbitrary real innerproduct generality versus finiteEuclidean source, no CompleteSpace/differentiability or supplied desired-convexity oracle. Domain inclusion/empty-outside follows quantified point-membership theorem; audit exact semantic equivalence rather than adding duplicate wrappers. Source properness/convexity is not part of generic subgradient definition. T2.21 genuinely assumes support-existence at each Vpoint, does not prove existence from convexity; later interior/relative-interior, singleton/differentiability and sum-rule statements remain REQUIRED separate obligations.

Current package CONTRACT/BODY/reader/rootTests/fullharness/axioms/registry/site/PR pending. Six namedaxes planned=2publicproof+1complete definition+3canaryproof,2nativeguards; zero new nodes/all10809oldIDsURLs expected preserved. Wholecanary actual square support2x and squareconvex onrealuniv; everyg excluded outside real[0,1] indicatorat2 using produced sourceproperness. Read-only future source and module audit occurred before next branch, no competing chapter writing. Legacy9beforepackage->8ONLYOnlineSubgradientBasic after allgates/PR; Chapter1migration/Chapter2mandatorytotalnull/incomplete/Chapters3–16mandatoryunenumerated/wholeGoalACTIVE. Old source receipts history only, not current review acceptance. Requested allroles GPT-6 Astra/medium, no upgrades/runtime-modelattestation; distinct formalizer/blind/source actors required by current semantic skill, restricted packet does not erase history/nohumanexternalreview. Native command gates versus role/prompt/file conventions distinct. Same authoritative ABRL paper workflow, no private manuscript copied/edited, no merge/deploy/retirement.

Prior closed/proper fullharnessv1 lexicalcomment hit and exactcontributorv1 metadata-prefix failure retained with actualrepair/fullv2/exactv2success; mathematical code/tests not weakened. Current package does not inherit those gates as fresh acceptance. Avoid bare axiom token in new Lean source comments because actual unchanged placeholder scanner scans comments too. Globalreference-index rewrite not planned for bounded retained reuse; current scoped declarations/pinned API retrieval required.''')
helper=run/'run-command.py';assert not helper.exists();helper.write_bytes(Path('runs/online-closed-proper-migration-20261006/run-command.py').read_bytes())
public=Path('BanditRLProof/OnlineSubgradientBasic.lean');canary=Path('Tests/OnlineSubgradientBasicCanary.lean');text=public.read_text(encoding='utf-8')
names=re.findall(r'(?m)^theorem\s+(\w+)',text);defs=re.findall(r'(?m)^(?:noncomputable\s+)?def\s+(\w+)',text)
assert names==['subgradient_point_finite','theorem_2_21'] and defs==['SourceSubdifferential']
scope=[];canary_names=[]
for line in canary.read_text(encoding='utf-8').splitlines():
 m=re.match(r'^namespace\s+(\S+)',line)
 if m:scope.append(m.group(1));continue
 if re.match(r'^end\b',line):scope.pop();continue
 m=re.match(r'^(?:theorem|lemma)\s+(\w+)',line)
 if m:canary_names.append('.'.join(scope+[m.group(1)]))
assert canary_names==['SubgradientProbe.square_support','SubgradientProbe.square_convex','SubgradientProbe.interval_outside_no_support']
for p in [public,canary,Path('BanditRLProof.lean'),Path('Tests.lean')]:
 dest=run/('original-'+p.name+'.txt');assert not dest.exists();dest.write_bytes(p.read_bytes())
full=['BanditRL.OnlineConvex.'+n for n in names+defs];allnames=full+canary_names
write(run/'public-named-declarations-v1.json',dict(public_proofs=full[:2],public_definitions=full[2:],canary_proofs=canary_names,canary_definitions=[],new_proofs=0,axiom_probe=allnames))
write(run/'leaves/actual-types-v1.lean','import BanditRLProof\nimport Tests.OnlineSubgradientBasicCanary\nset_option pp.universes true\nset_option pp.explicit true\n'+''.join('#check @'+n+'\n' for n in allnames))
write(run/'leaves/actual-types-readable-v2.lean','import BanditRLProof\nimport Tests.OnlineSubgradientBasicCanary\n'+''.join('#check @'+n+'\n' for n in allnames))
pdf=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(pdf)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
reader=PdfReader(str(pdf))
for index in [27,28]:
 p=run/('source-printed'+str(index-11)+'-pdf'+str(index+1)+'.txt');assert not p.exists();p.write_bytes(reader.pages[index].extract_text().encode('utf-8'))
write(run/'bootstrap-generated-before-use-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [helper,run/'leaves/actual-types-v1.lean',run/'leaves/actual-types-readable-v2.lean']],before_first_use=True))
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(helper),label,*args],check=True)
for label,args in [('CLI-help-v1-01',['--help']),('lifecycle-help-v1-01',['lifecycle-event','--help']),('fence-help-v1-01',['statement-fence','--help']),('local-retrieval-help-v1-01',['list-lean-decls','--help'])]:gate(label,sys.executable,'-X','utf8','tools/bandit.py',*args)
print('Subgradient basic retained scope actual6typeprobes and exactsource pages bound; source review pending.')
