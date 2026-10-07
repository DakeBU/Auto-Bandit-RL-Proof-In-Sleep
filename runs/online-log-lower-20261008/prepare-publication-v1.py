from common_accepted_v1 import *
accepted_fixed();a=load(RUN/'accepted-decision-v1.json');assert a['source_package_accepted'] and not a['goal_complete']
body='''Orabona v10 Chapter1 states that logarithmic guessing regret is unavoidable, without printing a minimax proof there. This package proves a concrete causal lower producer: a policy-independent normalized binary history law gives actual count moments and variance; actual strict-past predictions and the shared empirical-mean comparator yield expected signed cumulative regret at least H(T+1)/6. For every probability seed law with per-history measurable, pointwise interval-bounded causal policies, it produces ONE fixed length-T binary sequence outside the seed integral with regret at least log(T+2)/6. T≥1; the coefficients are derived support, not printed or claimed sharp.

The new shared module has48public proofs/10definitions and16named nondegenerate canaries. It reuses the existing regret, mean and finite-action probability APIs. The public/Test roots and source-qualified Book route share the same Lean graph; all10835old registry IDs/URLs/statement hashes are preserved, with58public new nodes plus1explicit private source identity. Original8cards/four curated IDs remain intact.

Validation: public/canary focused builds;76named standard-only axiom checks;64actual closed proposition and12definition identities (including recursive/nominal bridges);64native statement guards;30specified compiled VALUE pairs; root9094jobs, Tests9247jobs; full harness472tests/7existing skips; own frontier/shadow; nonvacuous exact-base contributor gate; clean Leanverified site/registry and13individually inspected current panels. Distinct required automated blind decoder and anti-anchored CONTRACT/BODY/FINAL reviewer accepted with explicit source delta; allR1–R8 satisfied. These roles reuse staged history and are not human/external/runtime-attested review. Failed attempts and versioned repairs remain in runs/online-log-lower-20261008; exact terminals were not weakened.

Stacked on OPEN unmerged PR#190 exact head9425fecb38be60b1acb7a918cb149f72117133ad (codex/research-online-regret-domains). This PR closes only C1-LOG-UNAVOIDABLE. Chapter1 still has16source inventory items and an unknown mandatory proof total; full regret/minimum, NoRegret and six other main-relative contributor gaps remain required and unwaived. Chapter2 is incomplete; Chapters3–16 and necessary appendix dependencies remain outstanding. The whole-book Goal stays active. No merge, deployment or main/live update is claimed.

Review entry points: BanditRLProof/OnlineGuessingLogLower.lean; Tests/OnlineGuessingLogLowerCanary.lean; docs/contracts/online-guessing-log-lower-v1; runs/online-log-lower-20261008/accepted-decision-v1.json, accepted-binding-audit-v1.json, accepted-reader-discharge-v1.json and final-reader-review-v1.md. Kernel/source review and each engineering gate are separate evidence; native safe-verify is a header/source scan, not a Lean compiler.
'''
write(RUN/'PR-body-v1.md',body)
write(RUN/'pr-payload-v1.json',dict(title='Prove causal logarithmic guessing regret lower bound',base=BASE_BRANCH,head=BRANCH,draft=True,body_file=(RUN/'PR-body-v1.md').as_posix(),exact_stacked_base=BASE,source_package_accepted=True,chapter_complete=False,goal_complete=False,merge_deploy_authorized=False))
gate('scope-before-publication-commit-v1',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','before-publication-commit-v1')
owned=load(RUN/'owned-commit-paths-v1.json')
for cmd in [['git','add','--',*owned],['git','commit','-m','Accept source-reviewed lower package and record integrated evidence']]:
 child=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 print('\n'.join(child.stdout.decode('utf8',errors='replace').splitlines()[-5:]),flush=True);assert child.returncode==0,cmd
gate('contributor-final-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
assert 'affected production paths: 5' in (RUN/'contributor-final-v1.log').read_text(encoding='utf8')
gate('scoped-diff-final-v1',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','final-v1')
gate('source-scope-final-v1',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','final-v1')
gate('committed-raw-audit-v1',sys.executable,'-B','-X','utf8',RUN/'audit-committed-raw-v1.py')
native('full-harness-final-v1','check')
accepted_fixed();print('Post-acceptance publication gates completed; authorized push/draft PR remains required.')
