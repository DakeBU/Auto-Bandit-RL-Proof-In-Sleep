"""Audit the exact delivered base/source and inventory actual retained sum-rule APIs."""
from pathlib import Path
import hashlib,json,re,subprocess
from pypdf import PdfReader
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-SUM-MIGRATION-20261007'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(x if isinstance(x,bytes) else (x if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def git(*args):return subprocess.check_output(['git',*args],encoding='utf-8').strip()
base='52c24a9971a5d7953a129227b61384061ea3493e';main='6847b678a73db68dee5101d6f05c2453c1405afc'
branch='codex/research-online-subgradient-sum-migration'
assert git('branch','--show-current')==branch and git('rev-parse','HEAD')==base
assert git('rev-parse','origin/main')==main and not git('-C','E:/ABRL/research','status','--porcelain')
assert git('rev-parse','--git-common-dir')=='E:/ABRL/research/.git'
pr=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/169']))
assert pr['state']=='open' and pr['draft'] and not pr['merged'] and pr['head']['sha']==base
assert git('ls-remote','origin','refs/heads/codex/research-online-subgradient-differentiability-migration').split()[0]==base
write(run/'workspace-audit-v1.json',dict(branch=branch,stacked_base_PR=169,stacked_base=base,origin_main=main,canonical_clean=True,common_git='E:/ABRL/research/.git',worktrees_porcelain=git('worktree','list','--porcelain'),reused_checkout='E:/ABRL/worktrees/research-online-book',prior_PR_OPEN_draft_unmerged=True,prior_run_ALL_raw_Git_blobs_verified=452,other_checkouts_stores_junctions_ignored_files_preserved=True,merged=False,live=False))
write(run/'00_context.md','''Persistent Orabona Chapters1-16 Goal ACTIVE/unbudgeted; requested GPT-6 Astra/medium. Exact OPENdraftPR16952c24a9971a5d7953a129227b61384061ea3493e base after final direct clean/localremoteREST/ALL452 currentrun rawblob checks. Fresh main6847...clean, shared Git and worktrees freshly inspected (ExtendedTopics independently advanced to b249622..., preserve it). Prior T2.22 acceptance is only its exact package, no chapter/Goal completion. Current legacy6; decrement ONLY OnlineSubgradientSum after actual source acceptance, combined gates and real scopedPR delivery. Canonical main/live unchanged; no merge/deploy/retirement.

Theorem2.23 printed17-18/PDF29-30: arbitrary proper finite components, ordinary sum F, unconditional global Minkowski support inclusion at EVERY x, even nonconvex components and empty right handside. Equality additionally proper convex CLOSED components and exact common point in the LAST effective domain and all OTHER ambient domain interiors. The point of qualification is not the queried x; no all-interiors or supplied queryfinite premise. Positive family equality Fin(n+1), singleton other-interior condition vacuous. Existing inclusion generalizes to empty Fintype; empty-family extension must be separately described, not a printed source claim.

Retain nine public proof declarations and one complete Minkowski-witness definition. Actual inclusion adds genuine individual inequalities/finite sums. Actual reverse binary producer constructs a separating functional over the IMAGE of two real epigraphs, proves its HEIGHT COEFFICIENT strictlynegative using the mixed qualification, then produces actual component supports via Riesz. Finite family induction derives aggregate properness, query finiteness and each finite component from actual aggregate support; invokes binary decomposition and constructs Fin.snoc actual vector family. No assumed decomposition, dual attainment, gradient oracle, all-domain interior or algorithm existence. Closedness is kept in the full printed terminal; helper stronger without closedness, unused source hypothesis not removed silently.

Shared generic SourceSubdifferential is a wider global inequality predicate than the printed proper-function definition. Each component SourceProper excludes bottom and supplies real finite witness; ordinary EReal addition agrees with source on proper components. Aggregate may lack a common finite point in unqualified inclusion, so identicallytop formal support behavior must be reviewed explicitly; equality's mixed qualification derives aggregate properness. Full SourceSubgradientSum uses actual vector witnesses and their finite sum, not mere membership in a supplied set. Convex REALheight epigraph, original effective domains and AMBIENT interiors, not closure/relative interior. Actual @types will determine which intermediate/inclusion APIs omit global unused finiteD/inner classes; do not infer types from module variables. Zero dimension, zero slope, empty-component/singleton/outside-domain cases stay explicit.

Single lower route, source contract and actual signature review before proof revalidation. Prior20261003 contracts/verdicts/compilation are historical, not inherited fresh source acceptance. Three distinct semantic actors required by repository semantic-roundtrip skill; no human/external/runtime model attestation. Global SGB frontier untouched; task-onlyshadow. Native command gates distinct from prompt/file conventions. All Chapter1/2 mandatory source branches/necessaryappendix remain required; Chapter2totalnull/incomplete/3-16unenumerated/wholeGoalACTIVE. Do not compete by writing Chapter3. Only owned current package paths editable after distinct contract/body review; no shared-pins/project duplication/private/anonymous/generated_site changes.
''')
write(run/'preparation-read-diagnostics-v1.md','Read-only CLI preparation: lifecycle-guard --help failed with invalid subcommand (the actual CLI exposes statement-fence and safe-verify). This was not an executed guard or mutation; preserve the tool transcript, use actual root/help commands. No gate weakening or mathematical acceptance.\n')
helper=run/'run-command.py';write(helper,Path('runs/online-subgradient-differentiability-migration-20261007/run-command.py').read_bytes())
for n in ['BanditRLProof/OnlineSubgradientSum.lean','Tests/OnlineSubgradientSumCanary.lean','BanditRLProof/OnlineSubgradientDifferentiability.lean','BanditRLProof/OnlineConvexSums.lean','BanditRLProof/OnlineSubgradientBasic.lean','BanditRLProof/OnlineConvexBarycenter.lean','BanditRLProof.lean','Tests.lean']:
 write(run/('original-'+Path(n).name+'.txt'),Path(n).read_bytes())
public=Path('BanditRLProof/OnlineSubgradientSum.lean');text=public.read_text(encoding='utf-8')
names=re.findall(r'^theorem (\w+)',text,re.M);defs=re.findall(r'^def (\w+)',text,re.M)
assert len(names)==9 and defs==['SourceSubgradientSum']
can=Path('Tests/OnlineSubgradientSumCanary.lean').read_text(encoding='utf-8');ns='';cn=[];cd=[]
for line in can.splitlines():
 if line.startswith('namespace '):ns=line.split()[1]
 if line.startswith('theorem '):cn.append(ns+'.'+line.split()[1])
 if line.startswith('def '):cd.append(ns+'.'+line.split()[1])
assert len(cn)==19 and len(cd)==3
q=['BanditRL.OnlineConvex.'+n for n in names+defs]
write(run/'public-named-declarations-v1.json',dict(public_proofs=q[:9],public_definitions=q[9:],whole_canary_proofs=cn,whole_canary_definitions=cd,retained_proofs=9,new_public_proofs=0,axiom_probe=q[:9]+cn))
write(run/'leaves/actual-types-v1.lean','import BanditRLProof\nimport Tests.OnlineSubgradientSumCanary\n'+''.join('#check @'+n+'\n' for n in q+cn+cd)+'#print BanditRL.OnlineConvex.SourceSubgradientSum\n')
pdf=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(pdf)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
pages=PdfReader(str(pdf));source17=pages.pages[28].extract_text();source18=pages.pages[29].extract_text()
assert 'Theorem 2.23' in source17 and 'proper functions' in source17 and 'closed' in source17
assert 'Corollary 16.50' in source18
write(run/'source-printed17-pdf29.txt',source17);write(run/'source-printed18-pdf30.txt',source18)
private=Path('E:/ABRL/papers/long/main/harness.tex');assert sha(private)=='31370babc09de16f536d2f975902b035fe02ba3c290deb3380501efd24a848e6'
write(run/'authoritative-private-workflow-binding-v1.json',dict(path=private.as_posix(),sha256=sha(private),content_not_copied_or_edited=True,title='ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory.'))
write(run/'bootstrap-generated-before-use-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [helper,run/'leaves/actual-types-v1.lean']],before_first_use=True))
print('ExactPR169/sourcePDF29-30/9retainedproofs1definition/19oldcanaries3definitions audited. Contract/signature/fresh source review pending.')
