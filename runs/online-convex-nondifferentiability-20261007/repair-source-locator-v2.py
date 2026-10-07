"""Separate source-locator repair proposal; preserve rejected v1 and every target byte."""
from common_v3 import *
fixed();r=load(RUN/'source-contract-receipt-v1.json');assert r['verdict']=='rejected'
assert not r.get('required_mathematical_repairs',[]) and not r.get('mathematical_repairs',[])
old=CONTRACT;new=Path('docs/contracts/online-convex-nondifferentiability-v2');assert not new.exists()
for p in sorted(old.rglob('*')):
 if not p.is_file():continue
 dest=new/p.relative_to(old)
 if p.name=='source-card.json':
  d=load(p);assert '2.3' in d['anchor'];d['anchor']='Final convex-analysis paragraph before Section 2.2.2 Analysis with Subgradients';write(dest,d)
 elif p.name=='contract.md':
  t=p.read_text(encoding='utf-8');assert 'before section2.3' in t;t=t.replace('observation, v1','observation, v2').replace('before section2.3','before Section2.2.2 Analysis with Subgradients')
  t+='\nVersion2 repairs source locator M1 ONLY after actual rejectedv1 metadata review. All complete-definition/three target headers/raw and native fingerprints unchanged. Rejectedv1 sourcecard/contract/receipt remain preserved, not rewritten. Task/conversion/obligationv1 sourceheading text is historical; this v2 effective contract supersedes the mistaken locator explicitly. Preceding countability consequence remains required separate terminal.\n';write(dest,t)
 else:write(dest,p.read_bytes())
for name in ['headers.json','complete-definition.lean','native-statement-fingerprints-v1.json','initial-dependency-DAG.json']:assert sha(old/name)==sha(new/name),name
write(RUN/'source-locator-repair-v2.json',dict(repair_id='M1',kind='metadata-only-source-locator',original_rejected_receipt=(RUN/'source-contract-receipt-v1.json').as_posix(),original_receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),old_contract=old.as_posix(),effective_proposed_contract=new.as_posix(),incorrect_locator='before section2.3',actual_source_heading='2.2.2 Analysis with Subgradients',source_PDF_unchanged=True,all_definition_headers_fingerprints_exactly_unchanged=True,mathematical_repairs=[],rejected_v1_all_original_bytes_preserved=True,review_pending=True,proof_compiled=False))
event('repair',dict(repair=(RUN/'source-locator-repair-v2.json').as_posix(),reason='Independent CONTRACTreview rejected M1 sourceheading metadata; newversion onlylocator, no statement/definition mutation.'))
packet=(RUN/'source-contract-packet-v1.md').read_text(encoding='utf-8')
packet=packet.replace('source-contract-review-v1.md','source-contract-review-v2.md').replace('source-contract-receipt-v1.json','source-contract-receipt-v2.json')
packet+='\nREPAIR CONTRACT v2: original actual reviewerrejectedv1 for M1metadataONLY incorrectsourceheading before2.3. New docs/contracts/online-convex-nondifferentiability-v2/source-card.json and contract.md correctlybeforeSection2.2.2 AnalysiswithSubgradients. Review this repair separately and verifyallcopiedheaders/definition/raw/nativefingerprints identical; oldv1/sourcecontractreceipt/task/conversion/obligation prose preservedhistorical, effectivev2supersedes mistakenlocator. No proofbody/provingyet. Independentlyhashallnewfixedinputs/ACTUALLY view originalpage again. Explicit repair_verdict forM1; no silentmath or sourcechange.\n'
write(RUN/'source-contract-packet-v2.md',packet)
paths={p.as_posix() for d in [RUN,old,new] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
source=load(new/'source-card.json');paths.update([source['cached_PDF'],source['image'],'runs/lifecycle_sessions.jsonl','runs/trials.jsonl','docs/contributor-codex-contract.md','docs/theorem-publication-protocol.md','.agents/skills/bandit-semantic-roundtrip/SKILL.md','docs/contracts/online-book-v1/source-inventory.json']);paths.update(load(RUN/'draft-freeze-v1.json')['fixed_files'])
for d in ['tasks','conversion-windows','proof-obligations']:paths.add(d+'/'+TASK+'.md')
write(RUN/'source-contract-inputs-v2.json',dict(stage='REPAIR-CONTRACT-v2',effective_contract=new.as_posix(),proof_compiled=False,source_package_accepted=False,chapter_complete=False,goal_complete=False,rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Newmetadata-onlyM1repair proposal andfixedinputs ready; independent reviewpending/no proving.')
