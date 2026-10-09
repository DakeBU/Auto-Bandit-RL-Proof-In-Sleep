from lower_common_v1 import *
d=reviewed();current=headers(1)
b=load(RUN/'absolute-focused-build-v1.json');out=base64.b64decode(b['stdout_base64']).decode('utf8')
assert b['actual_exit']==0 and 'Build completed successfully' in out and 'error:' not in out
write(RUN/'absolute-public-value-v1.lean','''import BanditRLProof.OnlineNonsmoothExamples
open scoped InnerProductSpace
example (c : ℝ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => |x - c|) ∧
      ∀ x : ℝ, DifferentiableAt ℝ (fun w : ℝ => |w - c|) x ↔ x ≠ c :=
  BanditRL.OnlineConvex.shifted_absolute_convex_differentiable_iff c
#print axioms BanditRL.OnlineConvex.shifted_absolute_convex_differentiable_iff
''')
code,stdout=capture('absolute-public-value-v1','lake','env','lean',RUN/'absolute-public-value-v1.lean')
assert 'depends on axioms: [propext, Classical.choice, Quot.sound]' in stdout
write(RUN/'leaf-NS001-compiled-v1.json',dict(phase='candidate compiled finite terminal; distinct BODY/source final acceptance pending',
 declaration=current[0],complete_production_file_sha256=sha(PRODUCTION),attempt_snapshot_sha256=sha(RUN/'leaf-NS001-attempt-v1.lean'),
 focused_build_sha256=sha(RUN/'absolute-focused-build-v1.json'),actual_build_success_marker=out.rstrip().splitlines()[-1],
 actual_public_value_and_axiom_sha256=sha(RUN/'absolute-public-value-v1.json'),axioms=['propext','Classical.choice','Quot.sound'],
 new_production_proof_count=1,source_family='shifted absolute intro',chapter_complete=False,whole_Goal_status='ACTIVE'))
event('absolute-candidate-event-v1','candidate',dict(leaf='NS001',terminal_hash=d['targets'][0]['statement_hash'],
 actual_current_kernel='compiled',body_review_pending=True,proof_receipt=sha(RUN/'leaf-NS001-compiled-v1.json'),chapter_complete=False,goal_complete=False))
event('hinge-proving-event-v1','proving',dict(leaf='NS002',terminal_hash=d['targets'][1]['statement_hash'],
 approved_scope=sha(CONTRACT/'nonsmooth-stabilized-v1.json'),
 ready_dependencies='Actual prior affine convexity/real-epigraph bridge, full hinge support set, singleton differentiability iff and finite real-germ producer; all complete current dependency files match prior scoped review.',
 chapter_complete=False,goal_complete=False))
reviewed();print('NS001 actual focused/public-value/standard-axiom evidence inspected; NS002 proving event recorded before body.')
