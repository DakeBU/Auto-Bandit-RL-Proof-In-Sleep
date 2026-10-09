from lower_common_v1 import *

reviewed(); headers(3)
c=load(CONTRACT/'nonsmooth-canary-contracts-v2.json')
receipt=load(RUN/'nonsmooth-canary-blind-receipt-v2.json')
assert receipt['inputs_unchanged'] and receipt['target_count']==5
assert receipt['report_sha256']==sha(RUN/'nonsmooth-canary-blind-reconstruction-v2.md')
assert load(RUN/'nonsmooth-canary-type-probe-v2.json')['actual_exit']==0
test=ROOT/'Tests/OnlineNonsmoothExamplesCanary.lean'
assert not test.exists()
event('nonsmooth-canaries-proving-event-v1','begin-proving',dict(
    leaf='five complementary public canaries for the three finite production terminals',
    frozen_contract_sha256=sha(CONTRACT/'nonsmooth-canary-contracts-v2.json'),
    neutral_reconstruction_sha256=sha(RUN/'nonsmooth-canary-blind-receipt-v2.json'),
    allowed_new_file=test.relative_to(ROOT).as_posix(), old_Test_root_pins_immutable=True,
    chapter_complete=False, goal_complete=False))
bodies=[
'''  have h := BanditRL.OnlineConvex.shifted_absolute_convex_differentiable_iff (10 : ℝ)
  refine ⟨h.1, ?_, (h.2 9).mpr (by norm_num), (h.2 11).mpr (by norm_num)⟩
  intro hd
  exact ((h.2 10).mp hd) rfl''',
'''  have hp := BanditRL.OnlineConvex.labelled_hinge_convex_differentiable_iff (2 : ℝ) (3 : ℝ)
  have hn := BanditRL.OnlineConvex.labelled_hinge_convex_differentiable_iff (-2 : ℝ) (3 : ℝ)
  refine ⟨hp.1, hn.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hd
    have h := (hp.2.1 (1 / 6)).mp hd
    norm_num [RCLike.inner_apply] at h
  · intro hd
    have h := (hn.2.1 (-1 / 6)).mp hd
    norm_num [RCLike.inner_apply] at h
  · exact (hp.2.1 0).mpr (by norm_num)
  · exact (hn.2.1 0).mpr (by norm_num)
  · intro hd
    have h := hp.2.2.mp hd
    norm_num at h
  · intro hd
    have h := hn.2.2.mp hd
    norm_num at h''',
'''  refine ⟨?_, ?_, ?_⟩
  · exact (BanditRL.OnlineConvex.labelled_hinge_convex_differentiable_iff (0 : ℝ) z).2.2.mpr
      (by simp)
  · exact (BanditRL.OnlineConvex.labelled_hinge_convex_differentiable_iff y (0 : ℝ)).2.2.mpr
      (by simp)
  · intro w
    simp''',
'''  have h := BanditRL.OnlineConvex.hinge_convex_differentiable_iff e0
  refine ⟨?_, (h.2 e1).mpr (by simp), ?_⟩
  · intro hd
    have hm := (h.2 (e0 + (3 : ℝ) • e1)).mp hd
    simp [inner_add_right, real_inner_smul_right] at hm
  · have hc : (fun t : ℝ => max (1 - inner ℝ e0 (e0 + (3 + t) • e1)) 0) =
        (fun _ : ℝ => (0 : ℝ)) := by
      funext t
      simp [inner_add_right, real_inner_smul_right]
    rw [hc]
    exact differentiableAt_const 0''',
'''  refine ⟨?_, ?_⟩
  · exact (BanditRL.OnlineConvex.labelled_hinge_convex_differentiable_iff y z).2.2.mpr
      (Subsingleton.elim _ _)
  · intro w
    have hz : z = 0 := Subsingleton.elim _ _
    simp [hz]''']
text='''/-
Five public concrete tests of the frozen nonsmooth terminals. C004 compares
ambient and tangential differentiability at the same plane point (1,3).
Zero-normal and dimension-zero cases are explicit boundary tests, not
substitutes for the nondegenerate shifted/positive/negative/plane cases.
These canaries do not establish chapter or whole-book acceptance.
-/
import BanditRLProof.OnlineNonsmoothExamples
import Tests.OnlineGradientDescentSourceCanary

noncomputable section
open scoped InnerProductSpace
open Tests.OnlineGradientDescentSource
namespace Tests.OnlineNonsmoothExamples

'''
for t,body in zip(c['targets'],bodies): text+=t['exact_header']+' := by\n'+body+'\n\n'
text+='end Tests.OnlineNonsmoothExamples\n'
write(test,text)
for t in c['targets']:
    assert statement_hash(lean_declaration_header(test,t['declaration']))==t['statement_hash']
write(RUN/'nonsmooth-canaries-attempt-v1.lean',test.read_bytes())
capture('nonsmooth-canaries-focused-build-v1','lake','build','Tests.OnlineNonsmoothExamplesCanary',required=False)
reviewed(); headers(3)
print('Actual five canary bodies authored at the frozen v2 types; inspect the actual focused-build receipt.')
