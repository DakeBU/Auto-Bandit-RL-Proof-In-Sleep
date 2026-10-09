from common import *
fixed()
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle
leaf=load(CONTRACT/'stabilized-v1.json')['targets'][0]
frozen=load(CONTRACT/'frozen-currentSubgradient_affine-v1.json')
assert sha(PUBLIC)==sha(RUN/'selector-attempt-source-v1.lean')
assert load(RUN/'selector-focused-build-v1.json')['actual_exit']==1
assert lifecycle.statement_hash(lifecycle.lean_declaration_header(PUBLIC,leaf['name']))==frozen['statement_hash']
ps=[RUN/n for n in ['lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md','trials.jsonl']]
write(RUN/'native-selector-repair-exact-before-v2.json',dict(rows=[dict(path=p.as_posix(),exists=p.exists(),sha256=sha(p) if p.exists() else None,before_raw_base64=base64.b64encode(p.read_bytes()).decode('ascii') if p.exists() else None) for p in ps]))
event('native-selector-repair-v2','repair',dict(task=TASK,leaf=leaf['name'],failure='dependent rewrite at Classical.choose membership has an ill-typed motive',change='Transport generic set membership through the singleton equality before applying to the chosen point',statement_changed=False,definitions_changed=False,prior_attempt=rows([RUN/'selector-attempt-source-v1.lean',RUN/'selector-focused-build-v1.json'])))
text=PUBLIC.read_text(encoding='utf8')
before='''  have hc := Classical.choose_spec hs
  rw [BanditRL.OnlineConvex.affine_subdifferential a b x] at hc
  exact Set.mem_singleton_iff.mp hc
'''
after='''  have hc := Classical.choose_spec hs
  have hsub : BanditRL.OnlineConvex.SourceSubdifferential
      (fun z => ((inner ℝ a z + b : ℝ) : EReal)) x ⊆ {a} := by
    intro z hz
    rwa [BanditRL.OnlineConvex.affine_subdifferential a b x] at hz
  exact Set.mem_singleton_iff.mp (hsub hc)
'''
assert text.count(before)==1
PUBLIC.write_bytes(text.replace(before,after).encode('utf8'))
assert lifecycle.statement_hash(lifecycle.lean_declaration_header(PUBLIC,leaf['name']))==frozen['statement_hash']
assert PUBLIC.read_bytes().startswith((CONTRACT/'definitions-draft-v1.lean').read_bytes())
write(RUN/'selector-attempt-source-v2.lean',PUBLIC.read_bytes())
code,out=capture('selector-focused-build-v2','lake','build','BanditRLProof.OnlineUnboundedOSD',required=False)
write(RUN/'selector-focused-inspected-v2.json',dict(actual_exit=code,actual_stdout=out,build_completed_marker='Build completed successfully' in out,source=rows([PUBLIC]),leaf=leaf['name'],status='focused compiled leaf only' if code==0 and 'Build completed successfully' in out else 'failed/unconfirmed',body_only_repair=True,statement_and_definitions_unchanged=True,other_frozen_terminals_open=10,source_lower_bound_closed=False,chapter_complete=False))
assert code==0 and 'Build completed successfully' in out
capture('selector-native-fence-v2',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','statement-fence','--declaration',leaf['name'],'--file',PUBLIC.relative_to(ROOT),'--output',CONTRACT.relative_to(ROOT)/'selector-native-extracted-v2.json')
actual=load(CONTRACT/'selector-native-extracted-v2.json')
assert actual['statement_hash']==frozen['statement_hash']
write(RUN/'selector-fence-compared-v2.json',dict(actual_native_hash=actual['statement_hash'],frozen_hash=frozen['statement_hash'],unchanged=True,definitions_prefix_exact=True,other_frozen_terminals_open=10))
write(RUN/'SelectorPublicAuditV1.lean','''import BanditRLProof.OnlineUnboundedOSD
#check BanditRL.OnlineUnboundedOSD.currentSubgradient_affine
#check (BanditRL.OnlineUnboundedOSD.currentSubgradient_affine (3 : ℝ) 2 7)
#print axioms BanditRL.OnlineUnboundedOSD.currentSubgradient_affine
''')
code,out=capture('selector-public-axiom-v1','lake','env','lean',RUN/'SelectorPublicAuditV1.lean')
assert 'sorryAx' not in out
write(RUN/'selector-public-inspected-v1.json',dict(actual_exit=code,raw_stdout=out,leaf=leaf['name'],nonzero_instance='Real slope3/point2/intercept7 #check applied proof expression',scope='Public instantiation and first leaf axioms only; no Test/source terminal/canary acceptance.'))
write(RUN/'memory-digest-selector-compiled-v2.md','Frozen11targets/4defs. First actual affine selector proof compiled after body-only dependent-motive rewrite repair; firstfailedsource/log retained. Nativefence unchanged, namedpublic/nonzero appliedproof/axiomauditactual. Fullstep/strictprefix/phi range+limit/actualregretidentity/lowerbound/unitlift/existence10otherterminals open; BODY/sourcepackage/combinedproject/readers/Tests remainpending. Chapter2sourcecontainer requiredopen/totalnull; whole16GoalACTIVE.\n')
fixed()
print('First actual selector leaf compiled after recorded body-only repair; ten frozen source dependencies remain open.')
