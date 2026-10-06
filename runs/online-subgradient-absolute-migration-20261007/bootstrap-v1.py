"""Freeze actual source, retained public headers, bodies, and borrowed support context."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
from pypdf import PdfReader
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;contract=Path('docs/contracts/online-subgradient-absolute-migration-v1')
task='ONLINE-SUBGRADIENT-ABSOLUTE-MIGRATION-20261007';prefix='BanditRL.OnlineConvex.'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(x if isinstance(x,bytes) else (x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def git(*args):return subprocess.check_output(['git',*args],encoding='utf-8').strip()
base='c9bc29000c6b72d26d5d90899f26a5d1bc0c2998';main='6847b678a73db68dee5101d6f05c2453c1405afc'
assert git('branch','--show-current')=='codex/research-online-subgradient-absolute-migration'
assert git('rev-parse','HEAD')==base and git('rev-parse','origin/main')==main
assert not git('-C','E:/ABRL/research','status','--porcelain')
assert git('rev-parse','--git-common-dir')=='E:/ABRL/research/.git'
pr=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/170']))
assert pr['state']=='open' and pr['draft'] and not pr['merged'] and pr['head']['sha']==base
assert git('ls-remote','origin','refs/heads/codex/research-online-subgradient-sum-migration').split()[0]==base
prior=Path('runs/online-subgradient-sum-migration-20261007');raw=[]
for p in sorted(prior.rglob('*')):
 if p.is_file():
  blob=subprocess.check_output(['git','show',base+':'+p.as_posix()]);assert blob==p.read_bytes(),p
  raw.append(dict(path=p.as_posix(),sha256=sha(p)))
assert len(raw)==419,len(raw)
write(run/'prior-delivery-raw-binding-v1.json',dict(base=base,prior_PR=170,status='passed',rows=raw))
write(run/'.gitattributes','* -text')
write(run/'run-command.py',(prior/'run-command.py').read_bytes())
write(run/'workspace-audit-v1.json',dict(branch=git('branch','--show-current'),base=base,base_PR=170,base_OPEN_draft_unmerged=True,origin_main=main,canonical_clean=True,shared_git=git('rev-parse','--git-common-dir'),worktrees=git('worktree','list','--porcelain'),prior_raw_files_verified=419,checkout='E:/ABRL/worktrees/research-online-book',merged=False,live=False))
public=Path('BanditRLProof/OnlineSubgradientAbsolute.lean');canary=Path('Tests/OnlineSubgradientAbsoluteCanary.lean')
text=public.read_text(encoding='utf-8');names=re.findall(r'^theorem (\w+)',text,re.M)
assert names==['abs_subgradient_zero','abs_subgradient_positive','abs_subgradient_negative','example_2_24']
assert not re.findall(r'^def ',text,re.M)
ct=canary.read_text(encoding='utf-8');ns='';cn=[]
for line in ct.splitlines():
 if line.startswith('namespace '):ns=line.split()[1]
 if line.startswith('theorem '):cn.append(ns+'.'+line.split()[1])
assert len(cn)==3 and not re.findall(r'^def ',ct,re.M)
q=[prefix+n for n in names];write(run/'public-named-declarations-v1.json',dict(public_proofs=q,public_definitions=[],whole_canary_proofs=cn,whole_canary_definitions=[],axiom_probe=q+cn,new_production_proofs=0,new_test_proofs=0))
fixed=['BanditRLProof/OnlineSubgradientBasic.lean','BanditRLProof/OnlineSubgradientSum.lean','BanditRLProof.lean','Tests.lean','lean-toolchain','lakefile.lean','lake-manifest.json','runs/active_frontier.json']
snap=[]
for p in [public.as_posix(),canary.as_posix()]+fixed+['website/content/readings.json','website/content/chapters.json','website/content/highlights.json','MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/trials.jsonl']:
 dest=run/('snapshots/'+p.replace('/','--')+'.txt');write(dest,Path(p).read_bytes())
 snap.append(dict(path=p,raw_sha256=sha(p),snapshot=dest.as_posix(),snapshot_sha256=sha(dest),authorized_delta='Only current Absolute leading ordinary source comment, route subtree and task-native append after distinct review; all mathematical bytes/pins/roots/shared modules fixed.'))
write(run/'historical-raw-supersession-v1.json',dict(rows=snap,old_receipts_unmodified=True))
basic=Path(fixed[0]).read_text(encoding='utf-8');a=basic.index('def SourceSubdifferential');b=basic.index('\ntheorem ',a);sdef=basic[a:b].strip()
write(contract/'borrowed-definition.txt',sdef)
context=dict(imports=text[:text.index('noncomputable section')],scope='noncomputable section; open Set; namespace BanditRL.OnlineConvex',space='ALL four public proofs specialize to scalar ℝ; no E/FiniteDimensional/CompleteSpace explicit binder',borrowed_definition=sdef,borrowed_definition_tokens=re.findall(r'\S+',sdef),borrowed_not_owned_definition=True,generic_scope_delta='S permits all EReal functions, broader than printed proper-function definition; fixed real-valued absolute function is finite/proper at every x so this source instance is legitimate.',public_definitions=0,new_production_proofs=0)
write(contract/'scoped-contexts.json',context)
headers={n:dict(statement=lean_declaration_header(public,n),file=public.as_posix()) for n in names}
for row in headers.values():row['statement_hash']=hashlib.sha256(row['statement'].encode()).hexdigest();row['context_hash']=sha(contract/'scoped-contexts.json')
write(contract/'headers.json',headers)
write(run/'draft-freeze-v1.json',dict(stage='draft',headers={n:r['statement_hash'] for n,r in headers.items()},original_module_sha256=sha(public),whole_old_canary={canary.as_posix():sha(canary)},fixed_shared_files={p:sha(p) for p in fixed},borrowed_definition_sha256=sha(contract/'borrowed-definition.txt'),retained_proofs=4,whole_canary_proofs=3,new_production_proofs=0,new_test_proofs=0,source_package_accepted=False,chapter_complete=False,goal_complete=False))
pdf=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(pdf)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
page=PdfReader(str(pdf)).pages[29].extract_text();assert 'Example 2.24' in page and 'Example 2.25' in page
write(run/'source-printed18-pdf30.txt',page)
write(contract/'source-card.json',dict(url='https://arxiv.org/pdf/1912.13213v10',version_date='2026-06-21',sha256=sha(pdf),printed_pages=[18],pdf_pages=[30],anchor='Example 2.24',source_result_count=1,mandatory_cases=['x>0: {1}','x=0: [-1,1]','x<0: {-1}'],page_extraction_sha256=sha(run/'source-printed18-pdf30.txt'),cache=pdf.as_posix(),adjacent_results_separate_required=True))
private=Path('E:/ABRL/papers/long/main/harness.tex');assert sha(private)=='31370babc09de16f536d2f975902b035fe02ba3c290deb3380501efd24a848e6'
write(run/'authoritative-private-workflow-binding-v1.json',dict(path=private.as_posix(),sha256=sha(private),content_not_copied_or_edited=True,title='ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory.'))
intent='''Orabona v10 Example 2.24, printed18/PDF30, ONE mandatory body example and THREE exhaustive sign cases. For f:REAL->REAL, f(y)=|y|, characterize the FULL GLOBAL subdifferential at EVERY scalar x: {1} if x>0; closed interval [-1,1] at zero; {-1} if x<0. Every scalar g is tested against ALL ambient real y with |x|+g(y-x)<=|y|. Inclusive endpoints -1 and 1 at zero, every interior slope and exclusion outside the interval must remain. No chosen-gradient/existence-only substitute, no relative-domain support and no differentiability assumption at zero. The allx terminal dispatches three actual retained equalities, not an assumed support inequality consumer.

Actual producer route: at zero, test y=1,-1 for necessity; for arbitrary g in the interval, split y>=0 versus y<0 and multiply the upper/lower bound by a correctly signed y. At positive and negative x, test y=0,2*x, derive x*(g-1)=0 or x*(g+1)=0; sign supplies x!=0 for cancellation. Sufficiency uses y<=|y| or -y<=|y| at EVERY y. EReal real coe_add/coercion order converts the globally finite function without mixed-infinity arithmetic. The generic shared S definition is broader than printed proper-function definition; here fixed absolute value is finite/proper on ALL REAL, so there is no improper-function extension in the actual source instance. Full borrowed S tokens/context retained, not a new/local owned definition. ALL four actual proofs scalarREAL, no extra space parameter/classes beyond intrinsic real inner product; actual @types separately checked. No high-dimensional norm characterization, probability, feedback, causal algorithm, regret, numerical-selection procedure or Chapter2 completion.

Retain exactly four old production proof bodies, zero definitions; whole old canary has three proof declarations, zero definitions. Zero-boundary canary uses both endpoints and 1/2, rejects2; separate proof excludes ANY singleton; whole allpoints canary invokes full source terminal at2,-2,0. Seven unique named kernel checks, four native frozen header guards, selected compiled dependency graph/actual support and source-terminal value edges, focused/body/wholecanary/root/Tests/fullharness/site/registry/FINAL/PR all required. No new production math or TESTs planned. Prior20261003 reviews/contracts/logs remain historical, not this run's acceptance. Source-blind decoder and anti-anchored reviewer distinct from formalizer, requested Astra/medium with honest prioractor context and no human/external/runtime model attestation. Same lower route; root may stage director/architect/worker roles. Native command gates and prompt/file conventions remain distinct; task-only shadow/globalSGB fixed.

Allowed after distinct CONTRACT/BODY: ordinary leading source/scope comment retaining every original RAW module byte as suffix, only online-subgradient-absolute subtrees in readings/highlights/chapters, scoped manifest/current evidence. Frozen headers, original mathematical bodies, borrowed S, shared modules, pins, public roots and whole oldcanary remain fixed. Preserve original curatedroute count<=4 and EXACT THREE notation-primer entries, allfour canonical module links and all10811 prior shared registry IDs/URLs with0newnodes. No perBook library, wrappers, toolchain upgrade, external Optlib rebuild claim, generated_site/private/anonymous changes.

OPENdraftPR170 exact c9bc29000c6b72d26d5d90899f26a5d1bc0c2998 stacked base; main6847b678a73db68dee5101d6f05c2453c1405afc clean/unchanged. Legacy5->4 ONLY OnlineSubgradientAbsolute after fresh source acceptance/gates/real PR delivery. Nine OTHER Chapter1 main-relative contract gaps and all remaining maintext/necessaryappendix obligations stay REQUIRED; Chapter2 mandatorytotal null/incomplete, Chapters3-16 unenumerated, whole Goal ACTIVE/unbudgeted. Adjacent Example2.25 normal cone is next mandatory package, then T2.26 etc. No Chapter3 competitive writing, merge/deploy/main/live/retirement/Goalcomplete.
'''
write(contract/'source-intent.md',intent)
dag=[['example_2_24','abs_subgradient_positive/abs_subgradient_zero/abs_subgradient_negative'],['all three branch proofs','SourceSubdifferential/EReal.coe_add/EReal.coe_le_coe_iff and scalar abs/order APIs']]
write(contract/'dependency-DAG-v1.json',dict(stage='draft',terminal='example_2_24',DAG=dag,actual_compiled_edges_pending=True,single_lower_route=True))
for folder in ['tasks','conversion-windows','proof-obligations']:write(Path(folder)/(task+'.md'),'# '+task+'\n\n'+intent)
write(run/'00_context.md',intent)
write(run/'10_upper_director-v1.md','Bounded integration-node: ONE printed example, complete allx three-case terminal; existing proofs reused, not new mathematical growth. Source contract/signature/DAG and distinct semantic review before actual retained body revalidation. Book Goal remains ACTIVE.')
write(run/'20_architect-v1.md',intent+'\n\nProof review: sign-correct allambient-y inequalities and nonzero-x cancellation; inclusive full zero interval, allx final dispatch. No support/decomposition oracle added.')
write(run/'proof-obligations-draft-v1.json',dict(stage='draft',required=[dict(name=n,statement_hash=r['statement_hash'],state='distinct-contract-review-pending') for n,r in headers.items()],source_result_count=1,mandatory_cases=3,retained_proofs=4,new_production_proofs=0,whole_canary_proofs=3,new_canary_proofs=0,chapter_total=None,source_package_accepted=False,chapter_complete=False,goal_complete=False))
write(run/'leaves/actual-types-v1.lean','import BanditRLProof\nimport Tests.OnlineSubgradientAbsoluteCanary\n'+''.join('#check @'+n+'\n' for n in q+cn)+'#print BanditRL.OnlineConvex.SourceSubdifferential\n')
write(run/'leaves/pinned-APIs-v1.lean','import BanditRLProof.OnlineSubgradientAbsolute\n'+''.join('#check @'+n+'\n' for n in ['EReal.coe_add','EReal.coe_le_coe','EReal.coe_le_coe_iff','abs_of_pos','abs_of_neg','abs_of_nonneg','le_abs_self','neg_le_abs','mul_le_mul_of_nonneg_left','mul_le_mul_of_nonpos_left','mul_eq_zero']))
export=(prior/'leaves/export-scoped-dependencies-v1.lean').read_text(encoding='utf-8');a=export.index('def targets');b=export.index('\ndef moduleName',a)
export=export[:a]+'def targets : Array Name := #[\n '+',\n '.join('`'+n for n in q)+']\n'+export[b:]
export=export.replace('nine retained sum-rule proofs and one complete Minkowski-witness definition; direct type/value boundary only; canary graph not exported','four retained scalar absolute-value proof bodies; direct type/value occurrence only; canary not yet exported')
write(run/'leaves/export-ready-dependencies-v1.lean',export)
export=export.replace('`BanditRLProof }]','`BanditRLProof }, { module := `Tests.OnlineSubgradientAbsoluteCanary }]')
a=export.index('def targets');b=export.index('\ndef moduleName',a)
export=export[:a]+'def targets : Array Name := #[\n '+',\n '.join('`'+n for n in q+cn)+']\n'+export[b:]
export=export.replace('four retained scalar absolute-value proof bodies; direct type/value occurrence only; canary not yet exported','four retained producer proofs and three whole canary proofs; direct type/value occurrence only; not full registry graph')
write(run/'leaves/export-public-dependencies-v1.lean',export)
write(run/'leaves/public-all-axioms-v1.lean','import BanditRLProof\nimport Tests.OnlineSubgradientAbsoluteCanary\n'+''.join('#print axioms '+n+'\n' for n in q+cn))
write(run/'preparation-diagnostics-v1.md','Read-only attempted sum migration contract-manifest.json and manifest without date did not exist. No gate/production mutation. Actual rg listing corrected these paths before use; preserve conversation tool outputs.\n')
write(run/'bootstrap-generated-before-use-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [run/'run-command.py']+sorted((run/'leaves').glob('*.lean'))],before_first_use=True))
print('Exact PR170/base and ALL419 raw files bound; sourcePDF30/exact4headers/fullborrowedS/whole3canary proofs frozen; fresh compilation/reviews pending.')
