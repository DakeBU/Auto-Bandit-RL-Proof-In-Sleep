from common_v1 import *
fixed(integrated=True);assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed'
a=load(RUN/'accepted-decision-v1.json');assert a['new_public_math']==0 and a['new_source_subobligation_closures']==1 and not a['goal_complete']
body='''The shared Regret API can represent predictions in W and comparators in V⊆W, provided losses are defined on W. This package audits that source modelling boundary (Orabona v10 printed p2/PDF14 Footnote1), preserves every existing public mathematical statement/body, adds only public module documentation, eight typed validation proofs/eight fixtures, one source card and two proof notes. It adds zero production mathematical results, definitions or registry nodes.

The tests include a genuine strict inclusion V=[0,1], W=[0,2], output2, loss=-x and same-prediction T2 regrets -4/-2. The illustrative no-regret bound is derived from that concrete game. Per-comparator eventual positive-epsilon upper control remains an explicit interpretation of the source limit inequality; no ordinary limit existence, nonnegative regret, uniform threshold, causal producer or generic W algorithm performance is claimed.

Validation:20 named standard-only kernel checks,10 exact proposition and10 definition identities,10 native theorem fences,3 prespecified VALUE pairs; combined root9093/Tests9245; full harness472 tests/7 existing skips; nonvacuous exact-base contributor gate; clean Lean-verified site/build/check; all10835 existing shared registry IDsURLs/hashesequal;8 current panels individually viewed. Required distinct automated decoder/CONTRACT/BODY/FINAL reviews accepted with explicit deltas and R1–R8 discharged; reused role history disclosed. All failures and versioned repairs retained under runs/online-regret-domains-20261007.

Stacked on OPEN unmerged draft PR#189 at exact3e473465298ea1ea10b7771608497d34e558fbeb, base branch codex/research-online-ftl-state. Only C1-REGRET-DIFFERENT-ACTION-COMPARATOR-SETS is discharged. Full Chapter1 regret/minimum/no-regret, logarithmic lower/source claim and other required audits remain open;16 source entries/unknown mandatory proof total; Chapter2 incomplete;3–16 unenumerated/necessary appendices required; total Goal ACTIVE. Six other main-relative contributor gaps remain FAILUNWAIVED. No merge, main/live update, deployment or worktree retirement.
'''
write(RUN/'pr-body-v1.md',body)
write(RUN/'pr-payload-v1.json',dict(title='Audit typed action and comparator domains in shared Regret API',head=BRANCH,base=BASE_BRANCH,draft=True,body=body))
write(RUN/'pr-payload-before-API-v1.json',dict(path=(RUN/'pr-payload-v1.json').as_posix(),sha256=sha(RUN/'pr-payload-v1.json'),exact_stacked_base=BASE,goal_complete=False))
# Acceptance changed task status/journals, so exercise the full packing/runtime gate once.
native('full-harness-final-v1','check')
raw=(RUN/'full-harness-final-v1.log').read_text(encoding='utf-8');assert 'Ran 472 tests' in raw and 'OK (skipped=7)' in raw and 'check passed' in raw
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v2.py'),'Accept bounded Regret domain mapping after distinct FINAL'],check=True)
gate('contributor-final-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-final-v1',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','final-v1')
gate('source-scope-final-v1',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','final-v1')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v2.py'),'Bind final Regret domain source and contributor gates'],check=True)
temporary=Path('tmp/online-regret-domains-raw-audit-v1.log');start=time.time();cmd=[sys.executable,'-B','-X','utf8',str(RUN/'audit-committed-raw-v1.py')]
with temporary.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'committed-raw-audit-v1.log',temporary.read_bytes());write(RUN/'committed-raw-audit-v1-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'committed-raw-audit-v1.log'),stdout_ignored_until_completion=True));assert child.returncode==0
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v2.py'),'Preserve raw Regret domain evidence before draft publication'],check=True)
gate('push-creation-v1','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','-u','origin',BRANCH)
gate('create-pr-v1',sys.executable,'-B','-X','utf8',RUN/'create-pr-v1.py')
fixed(integrated=True)
