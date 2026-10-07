from common_v1 import *
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()==BASE
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/research-online-guessing-osd-policy'
assert not subprocess.check_output(['git','-C','E:/ABRL/research','status','--porcelain'],text=True).strip()
main=subprocess.check_output(['git','rev-parse','origin/main'],text=True).strip()
assert main==subprocess.check_output(['git','-C','E:/ABRL/research','rev-parse','HEAD'],text=True).strip()
pr=subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/181']);write(RUN/'base-PR181-fresh-v1.json',pr)
parent=json.loads(pr);assert parent['head']['sha']==BASE and parent['state']=='open' and parent['draft'] and not parent['merged']
assert not PUBLIC.exists() and not CANARY.exists()
fixed_paths=['BanditRLProof/OnlineGuessingSubgradient.lean','Tests/OnlineGuessingSubgradientCanary.lean','BanditRLProof/OnlineSubgradientPolicy.lean','Tests/OnlineSubgradientPolicyCanary.lean','BanditRLProof/OnlineSubgradientDescent.lean','BanditRLProof/OnlineGradientDescent.lean','BanditRLProof/OnlineSubgradientBasic.lean','BanditRLProof/OnlineSubgradientAbsolute.lean','lean-toolchain','lakefile.lean','lake-manifest.json','runs/active_frontier.json','docs/contracts/online-book-v1/source-inventory.json','research-wiki/contribution-contracts/ONLINE-GUESSING-OSD-20261004.json','research-wiki/contribution-contracts/online-osd-policy-public-20261007.json','runs/online-osd-policy-public-20261007/accepted-decision-v1.json','runs/online-osd-policy-public-20261007/delivery-obligations-overlay-v1.json']
frozen={p:sha(p) for p in fixed_paths}
before=['BanditRLProof.lean','Tests.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl','runs/trials.jsonl']
for p in before:write(RUN/'snapshots'/p.replace('/','--'),Path(p).read_bytes())
old=Path('BanditRLProof/OnlineGuessingSubgradient.lean').read_text(encoding='utf-8')
old_headers={m.group(1):m.group(0).strip() for m in re.finditer(r'(?m)^theorem (\w+)\b[\s\S]*?(?= := by)',old)};assert len(old_headers)==12
write(RUN/'existing-canonical-headers-v1.json',old_headers)
pdf=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')
assert sha(pdf)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
from pypdf import PdfReader
reader=PdfReader(pdf)
for page in [13,14,15,27,28,31,32]:write(RUN/f'source-pdf{page}-v1.txt',reader.pages[page-1].extract_text())
write(CONTRACT/'source-card-v1.json',dict(title='Online Learning: A Modern Introduction Using Convex Optimization',version='arXiv1912.13213v10,2026-06-21',PDF_url='https://arxiv.org/pdf/1912.13213v10',cached_PDF=pdf.as_posix(),SHA256=sha(pdf),anchors=['Example2.32 printed20/PDF32','Guessing game printed1-3/PDF13-15','Eq2.1 printed15/PDF27','Definition2.18/2.20 printed16/PDF28','Lemma2.31/Algorithm2.2 transfer printed19-20/PDF31-32'],boundary='Generic played-legal deterministic finite-history OSD for absolute-loss guessing; horizon-prescribed eta=1/sqrtT, not an anytime/signed-convergence or randomized-law theorem. Existing12 canonical declarations byte-frozen dependencies.'))
write(RUN/'draft-freeze-v1.json',dict(stage='draft',fixed_files=frozen,canonical_main=main,exact_stacked_base=BASE,base_PR=181,new_proofs_planned=4,new_definitions_planned=0,source_package_accepted=False,chapter_complete=False,goal_complete=False))
write(RUN/'worktree-audit-v1.json',dict(canonical='E:/ABRL/research',canonical_main=main,canonical_clean=True,worktree=ROOT.as_posix(),branch='codex/research-online-guessing-osd-policy',stacked_PR=181,stacked_head=BASE,base_state='OPEN-DRAFT-unmerged',prior_DIRECT_actual_raw_files=539,shared_git=subprocess.check_output(['git','rev-parse','--path-format=absolute','--git-common-dir'],text=True).strip(),worktrees=subprocess.check_output(['git','worktree','list','--porcelain'],text=True),shared_packages_junction_preserved=True,other_worktrees_untouched=True,private_harness_SHA256=sha('E:/ABRL/papers/long/main/harness.tex'),main_live_unchanged=True))
write(RUN/'00_context.md',f'''# Example2.32 arbitrary played-legal history-policy extension
Whole Chapters1-16 Goal ACTIVE/unbudgeted. Requested GPT6Astra/medium, runtime model/effort not independently attested. Exact OPEN draft PR181 base {BASE}; actual DIRECT clean/localremoteREST/every539OWN raw files verified before branch. Canonical main/origin {main} freshly fetched/clean; shared Git/packages junction and other worktrees preserved. No merge/deploy/retirement.
New theorem-sized delta is actual same-run sqrtT regret for any fixed finite-history policy having true global support membership only at played queries. Existing canonical12 proofs/one loss definition and shared OSD21/recursion definitions remain byte-frozen; no duplication. Planned new4 proofs/no definitions. Chapter1/2 incomplete;3-16 unenumerated, no guessed totals/percentages.
Source/contract/neutral typed targets first; mandatory distinct decoder/source reviewer, roles and file conventions separately recorded. Native command-specific checks do not enforce the whole paper protocol. One lower route. No actual proof body before stabilization. Future integration limited to new module/test, additive imports/task/run/contract/manifest/native journals and this existing reader route only.
Read retrieval correction: conversion windows are .md, not the missing .json path queried during initial read. No write followed that missing-path read.
''')
native('native-new-task-v1-01','new-task',TASK,'--kind','theorem','--title','Example2.32 arbitrary played-legal finite-history OSD policy guarantee','--target-lean','BanditRL.OnlineGuessingSubgradientPolicy.example_2_32')
native('draft-event-v1-01','lifecycle-event','--session',TASK,'--event','draft','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,chapter_complete=False,goal_complete=False,exact_stacked_base=BASE)))
fixed();print('Actual draft/source/base frozen; new target bodies not yet authored.')
