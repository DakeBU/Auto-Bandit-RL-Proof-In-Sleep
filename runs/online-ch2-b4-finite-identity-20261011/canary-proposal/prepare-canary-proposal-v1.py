from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,datetime,subprocess
root=Path('E:/ABRL/worktrees/research-online-book')
out=root/'tmp/online-ch2-b4-finite-identity-canary-proposal-20261011'
out.mkdir(exist_ok=True)
def put(n,s):
    b=s.encode('utf-8') if isinstance(s,str) else s
    assert b'\r' not in b
    with (out/n).open('xb') as f: f.write(b)
def calc(T,psi,loss,x,u,z):
    y=lambda t:z if t==T else x(t)
    G=lambda t,v:psi(t,v)+sum((loss(i,v) for i in range(t+1)),Q(0))
    R=sum((loss(t,y(t))-loss(t,u) for t in range(T)),Q(0))
    A=psi(T-1,u)-psi(0,y(0))
    W=sum((G(t,y(t))-G(t,y(t+1)) for t in range(T)),Q(0))
    D=sum((psi(t,y(t+1))-psi(t+1,y(t+1)) for t in range(T-1)),Q(0))
    H=G(T-1,z)-G(T-1,u)
    return dict(R=str(R),initial=str(A),within=str(W),drift=str(D),terminal_gap=str(H),identity_numeric_check=R==A+W+D+H,drop_gap_bound=R<=A+W+D,original_terminal=str(x(T)),spliced_terminal=str(y(T)))
a=calc(1,lambda t,v:v*v/2,lambda t,v:(v-1)**2/2,lambda t:Q(1,2),Q(1,2),Q(2,3))
b=calc(2,lambda t,v:(t+1)*v*v/2,lambda t,v:v if t==0 else -2*v+1 if t==1 else Q(0),lambda t:Q(0) if t==0 else Q(1) if t==1 else Q(100),Q(3),Q(2))
put('arithmetic-v1.json',json.dumps(dict(UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),method='Python fractions.Fraction exact rational arithmetic; not Lean proof',case1=a,case2=b),indent=2)+'\n')
context='import BanditRLProof.OnlineCumulativePotential\nimport Mathlib.Algebra.BigOperators.Module\nimport Mathlib.Tactic\n\nnoncomputable section\nopen Finset\nnamespace BanditRL.OnlineCumulativePotentialCanary\n\n'
r='(∑ t ∈ range T, (loss t (y t) - loss t u))'
aexpr='(psi (T - 1) u - psi 0 (y 0))'
w='(∑ t ∈ range T, (G t (y t) - G t (y (t + 1))))'
d='(∑ t ∈ range (T - 1),\n        (psi t (y (t + 1)) - psi (t + 1) (y (t + 1))))'
g='(G (T - 1) z - G (T - 1) u)'
common='    let y : ℕ → ℝ := fun t => if t = T then z else x t\n    let G : ℕ → ℝ → ℝ := fun t v => psi t v + ∑ i ∈ range (t + 1), loss i v\n'
identity='    ('+r+' =\n      psi (T - 1) u - psi 0 (y 0) +\n      '+w+' +\n      '+d+' +\n      G (T - 1) z - G (T - 1) u)'
first='theorem finite_identity_one_round_positive_gap :\n    let psi : ℕ → ℝ → ℝ := fun _ v => v ^ 2 / 2\n    let loss : ℕ → ℝ → ℝ := fun _ v => (v - 1) ^ 2 / 2\n    let x : ℕ → ℝ := fun _ => 1 / 2\n    let u : ℝ := 1 / 2\n    let z : ℝ := 2 / 3\n    let T : ℕ := 1\n'+common+identity+' ∧\n    '+r+' = 0 ∧\n    '+aexpr+' = 0 ∧\n    '+w+' = -(1 / 36 : ℝ) ∧\n    '+d+' = 0 ∧\n    '+g+' = (1 / 36 : ℝ) ∧\n    ¬ ('+r+' ≤\n      '+aexpr+' + '+w+' +\n      '+d+')\n'
second='theorem finite_identity_two_round_terminal_splice :\n    let psi : ℕ → ℝ → ℝ := fun t v => ((t : ℝ) + 1) * v ^ 2 / 2\n    let loss : ℕ → ℝ → ℝ := fun t v =>\n      if t = 0 then v else if t = 1 then -2 * v + 1 else 0\n    let x : ℕ → ℝ := fun t => if t = 0 then 0 else if t = 1 then 1 else 100\n    let u : ℝ := 3\n    let z : ℝ := 2\n    let T : ℕ := 2\n'+common+identity+' ∧\n    '+r+' = 1 ∧\n    '+aexpr+' = 9 ∧\n    '+w+' = -(7 / 2 : ℝ) ∧\n    '+d+' = -(1 / 2 : ℝ) ∧\n    '+g+' = -4 ∧\n    x 2 = 100 ∧ y 2 = 2 ∧ y 2 ≠ x 2\n'
for name,statement in [('one-round',first),('two-round',second)]:
    put('neutral-'+name+'-complete-header-v1.txt',context+statement+'\nend BanditRL.OnlineCumulativePotentialCanary\n')
proposal=dict(status='HEADER PROPOSAL ONLY; not frozen, elaborated, or proved',actor='/root/b4_finite_identity_formalizer',UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_scope='Finite real-valued identity at positive horizons only. Case 1 witnesses necessity of retaining a positive terminal gap; case 2 witnesses independent terminal splice and nonzero regularizer drift. Neither is an actual optimistic-FTRL trajectory theorem or full B4 closure.',public_canary_count=2,new_named_helper_definitions=0,production_theorem='BanditRL.OnlineCumulativePotential.finite_regret_identity',required_future_dependency='First conjunct of EACH canary must directly specialize the new production theorem with the displayed psi/loss/x/u/z/T and positivity, preserving full identity. Numeric automation may discharge remaining conjuncts only; an unused consumer or independently numeric-proved first conjunct is insufficient.',parent_arithmetic='Both cases confirmed exactly by Fraction; all proposed values match.',scope_limits=['No T=0 claim','No EReal or infinity adapter','No algorithm/optimizer/convexity claim','No BODY constructed or compiled','Imports reference planned production module; no claim it currently exists','Fresh blind reconstruction and independent source/canary review required before freeze'],case1=a,case2=b,headers={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in out.glob('neutral-*.txt')},head_observed=subprocess.check_output(['git','rev-parse','HEAD'],cwd=str(root)).decode().strip())
put('canary-header-proposal-v1.json',json.dumps(proposal,indent=2)+'\n')
put('manifest-v1.json',json.dumps({f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in out.iterdir() if f.is_file()},indent=2)+'\n')
print(json.dumps(proposal['headers'],indent=2))
print('proposal',hashlib.sha256((out/'canary-header-proposal-v1.json').read_bytes()).hexdigest())