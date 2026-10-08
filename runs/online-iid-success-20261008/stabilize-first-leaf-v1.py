from common_reviewed_v1 import *
r=reviewed_fixed()
rows=load(CONTRACT/'targets-v1.json')['targets']
write(RUN/'stabilized-contract-v1.json',dict(state='stabilized',version=1,
    source_sha256=PDF_SHA,targets_sha256=sha(CONTRACT/'targets-v1.json'),
    context_sha256=sha(CONTRACT/'public-context-v1.lean'),review_receipt_sha256=REVIEW_SHA,
    reader_requirements=r['reader_requirements'],terminal_headers=rows,first_ready_leaf='S001',
    theorem_bodies_compiled=False,package_accepted=False,chapter_complete=False,goal_complete=False))
for p in APPEND_METADATA:
    write(RUN/'snapshots'/('CONTRACT-before-proving--'+p.as_posix().replace('/','--')+'.raw'),p.read_bytes())
    p.write_bytes(p.read_bytes()+('\n\n## Stabilized v1: first ready leaf S001\n\n'
        'Distinct CONTRACT accepted-with-explicit-delta, four complete headers unchanged. '
        'R1–R8 exact future reader requirements retained in stabilized-contract-v1.json. '
        'S001 first proving leaf; no BODY/package/chapter/Goal acceptance.\n').encode('utf8'))
native('stabilized-event-v1','lifecycle-event','--session',TASK,'--event','stabilized',
    '--payload-json',json.dumps(dict(contract_version=1,contract=(RUN/'stabilized-contract-v1.json').as_posix(),
        source_review_receipt_sha256=REVIEW_SHA)))
native('proving-event-v1','lifecycle-event','--session',TASK,'--event','proving',
    '--payload-json',json.dumps(dict(leaf=rows[0]['name'],edit_scope=PUBLIC.as_posix(),
        frozen_header_sha256=load(CONTRACT/'source-statement-fingerprint-v1.json')['headers']['S001'],
        single_lower_route=True)))
for command in ['trial-log','statement-fence','safe-verify']:
    native(command+'-help-v1',command,'--help')
native('S001-running-v1','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','running',
    '--run-id',RUN.name,'--lean',PUBLIC,'--attempt-id','SUCCESS-S001-V1','--harness','hierarchical',
    '--target-fingerprint',sha(CONTRACT/'targets-v1.json'),'--notes',
    'First frozen generic centered-total normalization adapter; existing Mathlib little-o/quotient and eventual positive natural horizons. No convergence assumed.')
context=(CONTRACT/'public-context-v1.lean').read_text(encoding='utf8')
context=context[:context.index('def S001')]
body=''' := by
  have hz : ∀ᶠ T : ℕ in atTop,
      (T : ℝ) = 0 → total T - (T : ℝ) * c = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    intro hzero
    exact False.elim ((ne_of_gt (Nat.cast_pos.mpr hT)) hzero)
  have he : (fun T => total T / (T : ℝ) - c) =ᶠ[atTop]
      (fun T => (total T - (T : ℝ) * c) / (T : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    exact normalized_excess (total T) c T hT
  rw [isLittleO_iff_tendsto' hz]
  exact (tendsto_congr' he).symm

'''
write(PUBLIC,context+'/-- Signed centered-total sublinearity is exactly vanishing average excess; eventual positive horizons only. -/\n'+
    rows[0]['header']+body+'end BanditRL.OnlineLearning\n')
write(RUN/'leaves'/'S001-body-v1.lean',PUBLIC.read_bytes())
headers_fixed(1)
gate('S001-focused-build-v1','lake','build','BanditRLProof.OnlineGuessingIIDSuccess')
native('S001-fence-v1','statement-fence','--declaration',rows[0]['name'],'--file',PUBLIC,
    '--output',RUN/'S001-fence-v1.json')
native('S001-safe-verify-v1','safe-verify','--fence',RUN/'S001-fence-v1.json','--lean-file',PUBLIC)
write(RUN/'S001-kernel-v1.lean','import BanditRLProof.OnlineGuessingIIDSuccess\n#check '+rows[0]['name']+
    '\n#print axioms '+rows[0]['name']+'\n')
gate('S001-kernel-v1','lake','env','lean',RUN/'S001-kernel-v1.lean')
native('S001-compiled-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled',
    '--run-id',RUN.name,'--lean',PUBLIC,'--attempt-id','SUCCESS-S001-V1','--harness','hierarchical',
    '--target-fingerprint',sha(CONTRACT/'targets-v1.json'),'--new-declaration',rows[0]['name'],
    '--verifier-evidence',RUN/'S001-focused-build-v1-exit.json','--progress-class','compiled-leaf',
    '--obligations-before','4','--obligations-after','3','--notes',
    'Actual generic frozen S001 body build/kernel, no zero-horizon strengthening. Three bounded terminals plus canaries/BODY/root/Tests/harness/readers/site/FINAL/PR remain; whole Goal active.')
write(RUN/'30_worker-S001-v1.md','Actual frozen S001 body builds, exact name/kernel audit and native header fence/safe scan separately pass. Mathlib little-oiffdivision uses eventual denominator nonzero; existing normalized_excess gives eventual arithmetic identity. NoA0/c restriction or convergence assumption. Four→three own bounded terminals only; not chapter coverage. BODY/source acceptance pending.')
write(RUN/'leaf-progress-S001-v1.json',dict(contract_version=1,total_bounded_terminals=4,
    compiled=[rows[0]['name']],remaining=[t['name'] for t in rows[1:]],
    public_sha256=sha(PUBLIC),package_accepted=False,chapter_complete=False,goal_complete=False))
headers_fixed(1)
