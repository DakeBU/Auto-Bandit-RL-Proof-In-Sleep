"""Audit the delivered stack and the exact source before reviewing retained endpoints."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
from pypdf import PdfReader
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-DIFFERENTIABILITY-MIGRATION-20261007'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes((x if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def git(*args):return subprocess.check_output(['git',*args],encoding='utf-8').strip()
base='4cf116c2ee42caa37e5a956ebbbfddfb0bc046f2';main='6847b678a73db68dee5101d6f05c2453c1405afc'
branch='codex/research-online-subgradient-differentiability-migration'
assert git('branch','--show-current')==branch and git('rev-parse','HEAD')==base
assert git('rev-parse','origin/main')==main and not git('-C','E:/ABRL/research','status','--porcelain')
assert git('rev-parse','--git-common-dir')=='E:/ABRL/research/.git'
pr=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/168']))
assert pr['state']=='open' and pr['draft'] and not pr['merged'] and pr['head']['sha']==base
assert git('ls-remote','origin','refs/heads/codex/research-online-subgradient-interior-migration').split()[0]==base
write(run/'workspace-audit-v1.json',dict(branch=branch,stacked_base_PR=168,stacked_base=base,origin_main=main,canonical_clean=True,common_git='E:/ABRL/research/.git',worktrees_porcelain=git('worktree','list','--porcelain'),reused_checkout='E:/ABRL/worktrees/research-online-book',prior_PR_OPEN_draft_unmerged=True,prior_run_ALL_raw_Git_blobs_verified=369,other_checkouts_stores_junctions_ignored_files_preserved=True,merged=False,live=False))
write(run/'00_context.md','''Persistent real Chapters1-16 Goal ACTIVE/unbudgeted; requested GPT-6 Astra/medium. Exact OPENdraftPR1684cf116c2ee42caa37e5a956ebbbfddfb0bc046f2 base after final direct clean/localremoteREST/ALL369 currentrun rawblob checks. Fresh main6847...clean; shared Git, all other checkouts, junctions, private manuscript, anonymous snapshots and runtime links preserved. Current legacy7; decrement ONLY OnlineSubgradientDifferentiability after actual acceptance and PR delivery. Two new relative-interior proofs belong to the prior accepted package, never recounted as current growth. Chapter1migration/Chapter2mandatorytotalnull/incomplete/Chapters3-16unenumerated/wholeGoalACTIVE. Mandatory T2.23 and later Chapter2 branches remain separate.

Theorem2.22 Orabona v10 printed17/PDF29, convex EReal f FINITE AT THE POINT, differentiability iff singleton global subdifferential, with its element the gradient. Existing public module already contains11proofs and one complete local-real-representative definition. Fresh source matching/migration is required, old20261003 verdicts/contracts do not give current acceptance. Retain all existing proofs, statements and definition tokens. No extra properness/interior/closedness/boundedness premise allowed in the FULL equivalence. Review genuine local finite representative differentiability, not naive DifferentiableAt of toReal: singleton indicator toReal is constantlyzero despite infinite values off its onepoint domain. New meaningful canaries planned to prove this distinction and invoke regularity/full endpoints, frozen before bodies.

Readiness builds/type retrieval/contract review are separate; no new mathematical proof claimed by retained module compilation. Freeze all11headers/complete SourceDifferentiableAt/scoped contexts/initialDAG/source fingerprints before proof revalidation. Single lower route; bounded mathlib/local retrieval. Distinct actors required by semantic-roundtrip skill; formalizer cannot serve decoder/reviewer, restricted current packets do not erase history, no human/external/runtime-model attestation claim. Preserve failure logs/immutable versions/raw-byte receipts. Global SGB frontier unchanged; only task-specific shadow. Native command gates versus prompt/file conventions distinct. Main/live unchanged; no merge/deployment/retirement.
''')
write(run/'preparation-read-diagnostics-v1.md','''Readonly preparation diagnostics retained: literal PowerShell rg *overlay* filename was invalid123; use -g filters/actual listings. Guessed docs/ONLINE-LEARNING-PROGRAM.md was absent2; actual memory pointer and local document show E:/ABRL/maintenance/ogd-session-20260913/ONLINE-LEARNING-PROGRAM.md. Repository maintenance directory absent in a multi-directory rg; authoritative hub maintenance read with absolute paths. No failed mutation, theorem/gate weakening or automatic acceptance from these reads. Prior raw preparation outputs are tool transcript evidence.
''')
helper=run/'run-command.py';helper.write_bytes(Path('runs/online-subgradient-interior-migration-20261006/run-command.py').read_bytes())
for name in ['BanditRLProof/OnlineSubgradientDifferentiability.lean','Tests/OnlineSubgradientDifferentiabilityCanary.lean','BanditRLProof/OnlineSubgradientInterior.lean','BanditRLProof/OnlineConvexFirstOrder.lean','BanditRLProof/OnlineSubgradientBasic.lean','BanditRLProof.lean','Tests.lean']:
 write(run/('original-'+Path(name).name+'.txt'),Path(name).read_bytes().decode('utf-8'))
public=Path('BanditRLProof/OnlineSubgradientDifferentiability.lean')
text=public.read_text(encoding='utf-8');names=re.findall(r'^theorem (\w+)',text,re.M);defs=re.findall(r'^def (\w+)',text,re.M)
assert len(names)==11 and defs==['SourceDifferentiableAt']
can=Path('Tests/OnlineSubgradientDifferentiabilityCanary.lean').read_text(encoding='utf-8')
ns='';cn=[]
for line in can.splitlines():
 if line.startswith('namespace '):ns=line.split()[1]
 if line.startswith('theorem '):cn.append(ns+'.'+line.split()[1])
assert len(cn)==6
q=['BanditRL.OnlineConvex.'+n for n in names+defs]
write(run/'public-named-declarations-v1.json',dict(public_proofs=q[:11],public_definitions=q[11:],whole_canary_proofs=cn,retained_proofs=11,new_public_proofs=0,axiom_probe=q[:11]+cn))
write(run/'leaves/actual-types-v1.lean','import BanditRLProof\nimport Tests.OnlineSubgradientDifferentiabilityCanary\n'+''.join('#check @'+n+'\n' for n in q+cn)+'#print BanditRL.OnlineConvex.SourceDifferentiableAt\n')
pdf=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')
assert sha(pdf)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
pages=PdfReader(str(pdf));source=pages.pages[28].extract_text()
assert 'Theorem 2.22' in source and 'finite inx' in source and 'single' in source
write(run/'source-printed17-pdf29.txt',source)
private=Path('E:/ABRL/papers/long/main/harness.tex')
assert sha(private)=='31370babc09de16f536d2f975902b035fe02ba3c290deb3380501efd24a848e6'
write(run/'authoritative-private-workflow-binding-v1.json',dict(path=private.as_posix(),sha256=sha(private),content_not_copied_or_edited=True,title='ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory.'))
write(run/'bootstrap-generated-before-use-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [helper,run/'leaves/actual-types-v1.lean']],before_first_use=True))
print('ExactPR168/sourcePDF29/11retainedproofs1definition/6oldcanaries audited. Contract/source review and fresh gates pending.')
