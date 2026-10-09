from common import *
from fractions import Fraction as Q
def psi(z): return z**4/4+z**2/2
def d(a,b): return psi(a)-psi(b)-(b**3+b)*(a-b)
zero,half=Q(0),Q(1,2)
movement=[d(zero,half),d(half,zero)]
fixed_eta=[Q(1),Q(1)]
variable_eta=[Q(1),half]
def case(u,coeff,eta):
    a=[d(u,half),d(u,zero)]
    terminal=d(u,half)
    actual=-abs(u)+coeff*(half-u)
    return dict(u=str(u),paid_loss_difference=str(actual),previous_divergences=list(map(str,a)),initial=str(a[0]),terminal=str(terminal),previous_max=str(max(a)),weighted_movements=str(sum((m/e for m,e in zip(movement,eta)),Q(0))),variable_sharp_rhs=str(max(a)/eta[-1]-terminal/eta[-1]-sum((m/e for m,e in zip(movement,eta)),Q(0))),printed_max_rhs=str(max(a)/eta[-1]-sum((m/e for m,e in zip(movement,eta)),Q(0))))
data=dict(diagnostic_only=True, compiled_Lean=False,actual_argmin_or_run_proof=False,statement_frozen=False,movements=list(map(str,movement)),fixed=[case(u,Q(-5,8),fixed_eta) for u in [-half,half]],variable=[case(u,Q(-5,4),variable_eta) for u in [-half,half]],whole_Goal_status='ACTIVE')
assert movement == [Q(11,64),Q(9,64)]
assert data['variable'][0]['paid_loss_difference']=='-7/4' and data['variable'][0]['variable_sharp_rhs']=='-29/64'
assert data['variable'][1]['previous_max']=='9/64' and data['variable'][1]['initial']=='0' and data['variable'][1]['printed_max_rhs']=='-11/64'
write(RUN/'canary-arithmetic-diagnostic-v1.json',data)
print('Exact rational draft arithmetic checked; no actual-run/minimum or Lean evidence.')
