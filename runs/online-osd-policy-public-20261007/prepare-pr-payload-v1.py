"""Concrete authorized scoped draft payload after real source/native acceptance."""
from common_v1 import *
a=load(RUN/'accepted-decision-v1.json');assert a['source_package_accepted'] and not a['chapter_complete'] and not a['goal_complete']
assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed'
body=f'''The finite-history OSD reader relied on historical receipts and described Lemma2.31's single-step loss gap as a horizon sum. This change corrects that field and revalidates the existing source/public mapping against frozen Orabona v10 Algorithm2.2, Lemma2.31 and the explicit Theorem2.13/eq2.1 transfer. Actual projected recursion, played-only legality, finite-loss conversion and sharp same-run fixed/variable/tuned/coarse bounds remain unchanged. Four performance cards and21 library notes retain the source-versus-structural distinction.

Stacks on OPEN unmerged #179 at exact {BASE}. Historical #149 already accepted the byte-identical21 public proofs/7 definitions/2 abbreviations and whole74 canary proofs/11 definitions/7 abbreviations. Zero new proofs, definitions, registry nodes or mathematical obligation closures. Fixed exogenous deterministic policies may depend on finite history; randomized/measurable laws, external-parameter independence, executable oracles and anytime tuning remain outside this contract.

Validation: focused{a['focused_jobs']} jobs,122 standard-only kernel audits,21 unchanged statement guards and32 pre-specified actual VALUE pairs; combined root/Tests{json.dumps(a['root_Tests_jobs'])} jobs (caches included), full harness{a['full_tests']} tests/{a['existing_skips']} existing skips. Exact-base contributor/scope/shadow and clean local Lean-verified site checks pass, with10817 previous shared IDs/URLs preserved and five current images reviewed. Distinct automated decoder and source CONTRACT/BODY/FINAL reviews discharge R1-R8; requested Astra/medium, no human or runtime attestation. The origin/main diagnostic still fails for nine OTHER required Chapter1 gaps, UNWAIVED.

Evidence: docs/contracts/online-osd-policy-public-v1; runs/online-osd-policy-public-20261007/accepted-decision-v1.json, accepted-binding-audit-v1.json, final-reader-review-v1.md and integrated-gates-overlay-v1.json. PDF SHA256 cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17; printed16/19-21, PDF28/31-33. Remaining Example2.32/linearization/unitanalysis/maintext/appendix obligations are required; Chapter2 incomplete, Chapters3-16 unenumerated, whole Goal ACTIVE. No merge/deployment/main/live update or retirement.
'''
write(RUN/'pr-body-v1.md',body)
write(RUN/'pr-payload-v1.json',dict(title='Revalidate finite-history OSD policies and shared Book mapping',head='codex/research-online-osd-policy-migration',base='codex/research-online-osd-migration',draft=True,body=body))
write(RUN/'pr-payload-before-API-v1.json',dict(path=(RUN/'pr-payload-v1.json').as_posix(),sha256=sha(RUN/'pr-payload-v1.json'),before_first_API_use=True))
print('Concrete authorized scoped policy draft prepared; fresh parent/push/duplicate checks remain.')
