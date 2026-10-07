"""Repair CLI discovery only; preserve failed guessed lifecycle-start and exact targets."""
from common_v2 import *
failed=load(RUN/'help-lifecycle-start-v1-exit.json');assert failed['exit_code']==2
fixed()
write(RUN/'readiness-CLI-repair-v2.json',dict(actual_failed_attempt='prepare-readiness-v1-01',actual_nested_failure='help-lifecycle-start-v1',cause='Guessed lifecycle-start is absent from actual current CLI; parser lists lifecycle-event only.',resolution='Use actual listed lifecycle-event help; reuse only actually passed preceding help commands; no target/definition or proof body mutation.',mathematical_repairs=[],failed_logs_preserved=True))
commands=['list-lean-decls','search-memory','reference-index','list-mathlib','list-papers','list-weapons','statement-fence','safe-verify','lifecycle-event','trial-log','frontier-refresh','frontier-shadow']
for c in commands:
 if (RUN/('help-'+c+'-v1-exit.json')).exists():passed('help-'+c+'-v1')
 else:native('help-'+c+'-v2',c,'--help')
for i,q in enumerate(['coordinateAbsolute','nondifferentiable','absolute'],1):
 native('project-declarations-'+str(i)+'-v1','list-lean-decls',q,'--statement')
 native('memory-search-'+str(i)+'-v1','search-memory',q)
gate('reference-index-v1-01',sys.executable,'-B','-X','utf8',RUN/'scoped-reference-index-v1.py')
for c in ['list-mathlib','list-papers','list-weapons']:native(c+'-v1',c)
gate('target-types-v1-01','lake','env','lean',RUN/'leaves/target-types-v1.lean')
gate('pinned-APIs-v1-01','lake','env','lean',RUN/'leaves/pinned-APIs-v1.lean')
fixed()
write(RUN/'source-visual-read-v1.json',dict(path=load(CONTRACT/'source-card.json')['image'],sha256=load(CONTRACT/'source-card.json')['image_sha256'],actual_view_image_original=True,actor='/root',finding='Actual printed19/PDF31 lastparagraph explicitly realR2/absfirstcoordinate/convex/notdifferentiableentire(0,0)-(0,1)segment. Readsourceagainafternewpackageinitialization; no EReal or restricted-verticalderivative claim.'))
write(RUN/'readiness-v1.json',dict(status='target-types-and-retrieval-checked',proof_compiled=False,source_package_accepted=False,definition_actual='coordinateAbsolute : EuclideanSpace real Fin2 -> real, firstindex0',target_type_checks=3,pinned_API_checks=15,reuse_decision='adapt_existing',route='Pinned convexrealnorm through actual PiLp projection; horizontal derivative restriction contradicts pinned scalar abs at0; trueclosedsegmentmembership firstcoordinate0.',external_imports_added=False,new_generic_mathlib_leaf=False,initial_DAG='docs/contracts/online-convex-nondifferentiability-v1/initial-dependency-DAG.json',chapter_complete=False,goal_complete=False))
print('3actual target propositions/complete definition and15pinnedAPItypes elaborated; theorem bodies NOTcompiled, CONTRACT review pending.')
