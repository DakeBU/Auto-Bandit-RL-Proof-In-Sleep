"""Freeze anti-anchored FTL contract review inputs before reuse-proving starts."""
from pathlib import Path
import hashlib,json,subprocess
run=Path(__file__).parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
    with (run/n).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
blind=load(run/'blind-receipt-v1.json')
for k in ['input','report']:assert sha(blind[k]['path'])==blind[k]['sha256_raw_bytes']
assert blind['scope']['target_count']==7 and blind['scope']['semantic_slots_per_target']==7
assert blind['scope']['source_maps_proofs_logs_judgments_other_files_read_this_pass'] is False
module=Path('BanditRLProof/OnlineFTLFailure.lean');freeze=load(run/'draft-freeze-v1.json')
assert sha(module)==freeze['original_public_module_sha256']==sha(run/'original-public-module.lean.txt')
assert sha('Tests/OnlineFTLFailureCanary.lean')==freeze['original_public_canary_sha256']
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
worktree=subprocess.check_output(['git','worktree','list','--porcelain'],encoding='utf-8')
write('workspace-workflow-audit-v1.json',dict(branch=subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip(),
    base_head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip(),
    canonical_main=subprocess.check_output(['git','-C','E:/ABRL/research','rev-parse','main'],encoding='utf-8').strip(),
    origin_main=subprocess.check_output(['git','rev-parse','origin/main'],encoding='utf-8').strip(),
    canonical_dirty=subprocess.check_output(['git','-C','E:/ABRL/research','status','--porcelain'],encoding='utf-8').strip(),
    common_git=subprocess.check_output(['git','rev-parse','--git-common-dir'],encoding='utf-8').strip(),worktrees=worktree,
    paper_title='ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory.',
    long_paper_sha256=sha('E:/ABRL/papers/long/main/harness.tex'),shared_registry=True,
    native_gates_vs_conventions='CLI-specific typed/fence/build/lifecycle gates and file/prompt semantic roles are separately recorded; no single-runtime enforcement claim.',
    other_worktrees_touched=False,whole_goal='active',chapter_complete=False))
packet='''Required distinct source contract review, requested GPT-6 Astra / medium. Audit frozen retained Example2.10 signatures and context against exact Orabona v10 printed12/PDF24 and fresh restricted-input decoder. Seek mismatch rather than confirming root; old same-model acceptance is historical, not independently recertified. Source-contract verdict only now:existing bodies are supplied so you may detect contradictions, but fresh actual body/canary/current package gates will follow stabilization and must be separately accepted.

Seven targets plus three actual definitions:recursive prefixCoefficient, actual sign-selected linearFTLPredict, specified failureCoefficient. Verify outputbeforecurrent feedback, strict-prefix dependence, feasible initial/output, actual historical minimization (not assumed desired regret), exact witness prefix/parity/played loss and regretT-1-x0/2 >=T-3/2, comparator0, arbitrary feasible initial x0 and everyT>=1. Generic helpers take arbitrary coefficient streams; failure source alone fixes [-1/2,+1,-1,...]. Tie rule at later zero prefix is a concrete permitted selection; failure prefixes are never zero. Historical minimization helper does not require feasible x0 because at0 sums vanish; algorithm feasibility and source endpoint separately require x0 in[-1,1]. T0 deliberately not in source endpoint; no universal all-algorithm lower bound/stochastic/measurable randomized-law/unknown-future algorithm-existence claim. The full coefficient stream is the mathematical representation; actual recursive prefix and public prefix identity establish causality with fixed initial x0.

Native7 statement captures bind existing public headers and actual hypothesis fragments; they are NOT yet safe-verify build acceptance. Fresh declaration retrieval finds exact current public terminal. Existing two canaries are meaningful initial1/3, predictions1/3,1,-1 and six-round loss29/6; these must be rebuilt and audited later. No public Lean edit occurred; source/module/canary exact raw snapshots are preserved. The prepare-draft01 administrative failure added an EOF to a proposed raw snapshot; failed snapshot retained, authoritative snapshot02 uses exact write_bytes and matches live module. It was not a mathematical or compiler gate.

Chapter2 navigation draft freshly finds32 numbered entries/two algorithm boxes, but remains source-navigation only with unnumbered precise signatures/counts not frozen. Problems2.1/2.2 are separate exercises; formal main-text results with exercise proofs remain required. Whole Chapters1-16 Goal active; selected one old production path only, no seven-new-proofs count, no chapter or main/live update. Same shared Lean/Lake/registry; other tasks and global SGB untouched.

Read contract-source-inputs-v1.json and independently rehash exact raw rows. Write ONLY source-contract-review-v1.md and source-contract-receipt-v1.json here, with seven-slot comparison/per-target verdicts, required repairs, remaining body/package gates, exact reviewed_files raw SHA inventory and report path/SHA. No input edits; distinct automated actor, no human/external-model review; requested medium not independently attested.'''
write('source-review-packet-v1.md',packet)
paths={p.as_posix() for p in run.rglob('*') if p.is_file()}
paths.update(p.as_posix() for p in Path('docs/contracts/online-ftl-migration-v1').rglob('*') if p.is_file())
paths.update(['../research-online-ogd/tmp/pdfs/orabona-v10.pdf','.agents/skills/bandit-semantic-roundtrip/SKILL.md',
    'BanditRLProof/OnlineFTLFailure.lean','Tests/OnlineFTLFailureCanary.lean','BanditRLProof/OnlineLearningFTL.lean',
    'BanditRLProof/OnlineLearningFoundations.lean','BanditRLProof/OnlineLearningMean.lean','BanditRLProof/OnlineLearningRegret.lean',
    'BanditRLProof.lean','Tests.lean','lean-toolchain','lakefile.lean',
    'docs/contracts/online-book-v1/source-inventory.json','docs/contracts/online-book-v1/coverage.json',
    'docs/hierarchical_harness.md','docs/lifecycle_and_proof_frontier_hardening.md','runs/active_frontier.json',
    'tasks/ONLINE-FTL-MIGRATION-20261005.md','conversion-windows/ONLINE-FTL-MIGRATION-20261005.md',
    'proof-obligations/ONLINE-FTL-MIGRATION-20261005.md',
    'runs/online-ftl-failure-20260914/acceptance-decision.md','runs/online-ftl-failure-20260914/source-audit.json',
    'runs/online-ch2-enumeration-20261005/source-navigation-draft-v1.json',
    'tmp/online-ch2-enumeration-source20-35.txt'])
paths.discard((run/'contract-source-inputs-v1.json').as_posix())
for p in paths:assert Path(p).is_file(),p
write('contract-source-inputs-v1.json',dict(scope='retained causal FTL7 headers/3definitions source contract only',
    public_body_accepted=False,rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('FTL source contract review frozen:',len(paths),'exact raw inputs; reuse proving not yet begun.')
