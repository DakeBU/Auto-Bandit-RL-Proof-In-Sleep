from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash

frozen = load(CONTRACT/'potential-stabilized-v2.json')
assert statement_hash(lean_declaration_header(PUBLIC, 'weighted_potential_sum')) == frozen['statement_hash']
probe = '''import BanditRLProof.OnlineAdaptivePotential
open Finset

example (a w : ℕ → ℝ) (C : ℝ) (T : ℕ) (hT : 0 < T)
    (hw : ∀ t < T, 0 ≤ w t)
    (hmono : ∀ t, t + 1 < T → w t ≤ w (t + 1))
    (hbound : ∀ t < T, a t ≤ C) :
    (∑ t ∈ range T, (a t - a (t + 1)) * w t) ≤
      C * w (T - 1) - a T * w (T - 1) :=
  BanditRL.OnlineAdaptivePotential.weighted_potential_sum a w C T hT hw hmono hbound

#check BanditRL.OnlineAdaptivePotential.weighted_potential_sum
#print BanditRL.OnlineAdaptivePotential.weighted_potential_sum
#print axioms BanditRL.OnlineAdaptivePotential.weighted_potential_sum
'''
write(RUN/'PotentialPublicProbeV1.lean', probe)
capture('potential-public-probe-v1', 'lake', 'env', 'lean', RUN/'PotentialPublicProbeV1.lean')
name = 'BanditRL.OnlineAdaptivePotential.weighted_potential_sum'
args = [sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py', 'statement-fence',
    '--declaration', 'weighted_potential_sum', '--file', PUBLIC,
    '--output', RUN/'potential-fence-native-v1.json']
for token in ['hT : 0 < T', 'hw : ∀ t < T, 0 ≤ w t',
    'hmono : ∀ t, t + 1 < T → w t ≤ w (t + 1)', 'hbound : ∀ t < T, a t ≤ C']:
    args += ['--source-assumption', token]
capture('potential-fence-v1', *args)
capture('potential-safe-verify-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'safe-verify', '--fence', RUN/'potential-fence-native-v1.json', '--lean-file', PUBLIC)
capture('potential-named-declaration-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'list-lean-decls', 'OnlineAdaptivePotential.weighted_potential_sum', '--statement')
capture('potential-compiled-trial-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'compiled',
    '--attempt-id', 'potential-body-v1', '--harness', 'hierarchical',
    '--progress-class', 'compiled-leaf', '--statement-hash', frozen['statement_hash'],
    '--lean', name, '--changed-file', PUBLIC.relative_to(ROOT),
    '--obligations-before', '1', '--obligations-after', '1',
    '--new-declaration', name, '--reused-declaration', 'Finset.sum_range_by_parts',
    '--verifier-evidence', RUN/'potential-focused-build-v1.json',
    '--verifier-evidence', RUN/'potential-public-probe-v1.json',
    '--notes', 'Actual focused BODY and full generic public application compile. Acceptance pending BODY/canary/combined gates; parent OSD remains open.')

context = '''import BanditRLProof.OnlineAdaptivePotential

noncomputable section
open Finset
namespace Tests.OnlineAdaptivePotentialCanary

def a : ℕ → ℝ
  | 0 => 3
  | 1 => 1
  | 2 => 3
  | 3 => 2
  | _ => 1

def w : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | _ => 2

def signed : ℕ → ℝ
  | 0 => -3
  | 1 => -2
  | 2 => -4
  | _ => 7

def terminal : ℕ → ℝ
  | 0 => 0
  | _ => 5
'''
first = '''theorem leading_zero_and_stall :
    (∑ t ∈ range 4, (a t - a (t + 1)) * w t) ≤ 4 * w 3 - a 4 * w 3 ∧
    (∑ t ∈ range 4, (a t - a (t + 1)) * w t) = 1 ∧
    a 4 * w 3 = 2 ∧
    (∑ t ∈ range 4, (a t - a (t + 1)) * w t) < 4 * w 3 - a 4 * w 3 ∧
    w 0 = 0 ∧ w 1 = w 2 ∧ a 1 < a 2 := by
'''
second = '''theorem signed_zero_and_free_terminal :
    (∑ t ∈ range 3, (signed t - signed (t + 1)) * (0 : ℝ)) ≤
      (-2 : ℝ) * 0 - signed 3 * 0 ∧
    (∑ t ∈ range 1, (terminal t - terminal (t + 1)) * (2 : ℝ)) ≤
      (1 : ℝ) * 2 - terminal 1 * 2 ∧
    (∑ t ∈ range 1, (terminal t - terminal (t + 1)) * (2 : ℝ)) = -10 ∧
    (1 : ℝ) * 2 - terminal 1 * 2 = -8 := by
'''
write(CONTRACT/'potential-canary-context-draft-v1.lean.txt', context)
write(CONTRACT/'potential-canary-header-1-draft-v1.lean.txt', first)
write(CONTRACT/'potential-canary-header-2-draft-v1.lean.txt', second)
neutral = (context.replace('import BanditRLProof.OnlineAdaptivePotential', 'import Mathlib')
    .replace('Tests.OnlineAdaptivePotentialCanary', 'Neutral')
    .replace('def a :', 'def P :').replace('def w :', 'def W :')
    .replace('def signed :', 'def Q :').replace('def terminal :', 'def Z :'))
import re
neutral_headers = first.replace('leading_zero_and_stall', 'certificate_one') + '\n' + second.replace('signed_zero_and_free_terminal', 'certificate_two')
for old, new in [('a','P'), ('w','W'), ('signed','Q'), ('terminal','Z')]:
    neutral_headers = re.sub(r'\b'+old+r'\b', new, neutral_headers)
neutral_headers = neutral_headers.replace(' := by', '')
write(CONTRACT/'potential-canary-neutral-v1.lean.txt', neutral+'\n'+neutral_headers+'\nend Neutral\n')
write(CONTRACT/'potential-canary-contract-draft-v1.md', '''# Complete potential validation contract

Two entire conjunctions are frozen in separate headers. First: played potentials [3,1,3,2], terminal1, weights[0,1,1,2], C4, sum1, negative terminal contribution2, strict gap1<6, leading zero, stalled weight, interior potential increase. BODY must visibly use public weighted_potential_sum at C4 for the bound and C3 for the strict bound (sum<=4<6). Second: signed played potentials[-3,-2,-4], terminal7, allzero weights and C=-2; plus T1 potential0->5 with weight2,C1, exact sum-10 and RHS-8. BODY must visibly use the public lemma in both boundary bounds. Four selected public calls expected in compiled canary VALUEs, not import-only evidence. T0 is outside this lemma and remains a separate parent OSD obligation. No regret or algorithm claim. Exact definitions/context and both FULL conjunctions require neutral decoding and distinct source/BODY+canary-CONTRACT review before creating Tests/OnlineAdaptivePotentialCanary.lean. Test root untouched. All parent/source-repair/combined/registry/publication/Goal gates stay open.
''')
write(RUN/'potential-canary-draft-inputs-v1.json', rows([
    CONTRACT/'potential-canary-context-draft-v1.lean.txt',
    CONTRACT/'potential-canary-header-1-draft-v1.lean.txt',
    CONTRACT/'potential-canary-header-2-draft-v1.lean.txt',
    CONTRACT/'potential-canary-neutral-v1.lean.txt',
    CONTRACT/'potential-canary-contract-draft-v1.md']))
print('Actual potential compiler/public/fence evidence recorded; canary contract only, no Test BODY.', flush=True)
