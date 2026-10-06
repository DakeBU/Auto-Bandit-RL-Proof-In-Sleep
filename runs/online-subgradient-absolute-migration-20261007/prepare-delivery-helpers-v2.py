from common import *
prior=Path('runs/online-subgradient-sum-migration-20261007')
t=(RUN/'preserve-native-prefix-v1.py').read_text(encoding='utf-8').replace("'body':'public-body-receipt-v1.json'", "'body':'public-body-receipt-v1.json','final':'final-reader-receipt-v1.json'")
write(RUN/'preserve-native-prefix-v2.py',t)
t=(prior/'create-pr-v1.py').read_text(encoding='utf-8')
t=t.replace('PR169','PR170').replace('/pulls/169','/pulls/170').replace('52c24a9971a5d7953a129227b61384061ea3493e',BASE)
t=t.replace('online-subgradient-sum-migration','online-subgradient-absolute-migration').replace('online-subgradient-differentiability-migration','online-subgradient-sum-migration')
t=t.replace('online-subgradient-sum-migration\'\n','online-subgradient-sum-migration\'\n')
# URI head still uses URL encoding; update its exact encoded name separately.
t=t.replace('online-subgradient-sum-migration\')','online-subgradient-sum-migration\')')
write(RUN/'create-pr-v1.py',t)
write(RUN/'prepare-pr-payload-v1.py',"""from common import *
a=load(RUN/'accepted-decision-v1.json');assert a['source_package_accepted'] is True and a['goal_complete'] is False
gate='Current postcomment sequential root '+str(a['root_Tests_jobs']['root-v1-01'])+', Tests '+str(a['root_Tests_jobs']['Tests-v1-01'])+' and full harness '+str(a['full_tests'])+' tests / '+str(a['existing_skips'])+' existing skips PASS. Four native frozen headers; seven unique named kernel checks standard foundations; focused3288/wholecanary3289 jobs. Actual selected seven proof nodes/1024 direct type-value occurrences/9 required producer-canary pairs, separate readiness4nodes666refs. Exact-base contributor, scoped CRLF-aware whitespace, historical raw-binding audit, clean local leanverified sitebuild/sitecheck/shared registry preservation and actual firstviewport review PASS.'
body='''Example 2.24 now has a current source-qualified acceptance packet for its complete scalar subdifferential: {1} for x>0, the FULL CLOSED [-1,1] at zero, and {-1} for x<0. The actual retained proofs establish necessity and global sufficiency at every real test point; the all-x terminal invokes all three branches. Four retained proof refinements represent ONE body example/THREE cases, with zero new mathematical or TEST declarations.

This PR stacks on OPEN draft #170 at exact c9bc29000c6b72d26d5d90899f26a5d1bc0c2998. It adds only a leading source/scope comment retaining the original raw Lean code, scoped reader corrections, contract/evidence and a contributor manifest. Frozen headers, whole threecanary proofs, full borrowed shared support definition, dependencies, roots and pins are preserved. The generic EReal supporting predicate is wider than the book's proper-function definition; fixed scalar absolute value is globally finite/proper, so this source instance has no improper-function gap. No multidimensional norm, algorithm, probability, regret or selection guarantee is added.

Distinct formalizer, restricted blind decoder and anti-anchored source reviewer completed CONTRACT/BODY/FINAL under requested GPT-6 Astra/medium. These are automated roles with disclosed prior history, not human/external review or attested runtime model provenance. Reader page preserves all four original curated links, exactly three notation entries, folded exact Lean and actual proof/dependency explanations. All10811 shared registry IDs/URLs remain; zero new per-Book nodes or library projects. Lean graph reuse-only; route overlay updated; no separately certified conceptual functor proposed.

'''+gate+'''

The separate origin/main-relative contributor diagnostic still finds nine OTHER mandatory Chapter1 contract gaps. This scoped PR passes against its exact stacked base; those gaps are retained, not waived. Raw command logs/source snapshots/PDF extraction have explicit whitespace exceptions; ignored initial Python runtime cache is preserved locally and excluded from source evidence/Git delivery. Native log appends preserve their reviewed raw prefixes by exact SHA, not reserialization. Unexecuted helper adapter versions and read-only preparation diagnostics are retained; no mathematical statement weakening or unreported proof failure.

Evidence: runs/online-subgradient-absolute-migration-20261007/accepted-decision-v1.json, accepted-binding-audit-v1.json, integrated-gates-overlay-v1.json, final-reader-review-v1.md, history-binding-audit-v1.json, registry-v1.json; source/contract: docs/contracts/online-subgradient-absolute-migration-v1. Frozen v10 PDF SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17, printed18/PDF30.

Only this bounded Example2.24 package is accepted/compiled-local/PR-ready. Legacy5→4 applies ONLY OnlineSubgradientAbsolute after actual PR delivery. Example2.25 and all remaining Chapter1/2/necessary appendix results remain REQUIRED; Chapter2 totalnull/incomplete, Chapters3–16 unenumerated, total Goal ACTIVE. Canonical main/live and generated _site/private/anonymous materials are unchanged. No merge, deployment or worktree retirement.
'''
write(RUN/'pr-body-v1.md',body)
payload=dict(title='Qualify Orabona Example2.24 complete scalar support equality',head='codex/research-online-subgradient-absolute-migration',base='codex/research-online-subgradient-sum-migration',draft=True,body=body)
write(RUN/'pr-payload-v1.json',payload);write(RUN/'pr-payload-before-API-v1.json',dict(path=(RUN/'pr-payload-v1.json').as_posix(),sha256=sha(RUN/'pr-payload-v1.json'),before_first_API_use=True))
print('Current exact scoped acceptance payload prepared; push/freshparent/duplicate checks precede POST.')
""")
generated('delivery-helpers-before-use-v1.json',[RUN/'preserve-native-prefix-v2.py',RUN/'create-pr-v1.py',RUN/'prepare-pr-payload-v1.py'])
print('Versioned final-prefix and scoped draft-PR helpers prepared before use; not yet executed.')
