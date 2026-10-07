from common_v1 import *
fixed()
assert load(RUN/'public-canary-build-v3-exit.json')['exit_code']==0
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,normalize_statement
pubtext=PUBLIC.read_text(encoding='utf-8');testtext=CANARY.read_text(encoding='utf-8')
public_names=re.findall(r'(?m)^theorem (\w+)\b',pubtext)
test_names=re.findall(r'(?m)^theorem (\w+)\b',testtext)
actual=[]
for path,prefix,names in [(PUBLIC,PRE,public_names),(CANARY,'GuessingLogLowerProbe.',test_names)]:
    for n in names:
        actual.append(dict(name=prefix+n,path=path.as_posix(),header=lean_declaration_header(path,n)))
assert len(public_names)==48 and len(test_names)==16
for n,h in load(CONTRACT/'planned-public-headers-v1.json').items():
    assert lean_declaration_header(PUBLIC,n)==normalize_statement(h),n
for n,h in load(RUN/'planned-canary-headers-v1.json').items():
    assert lean_declaration_header(CANARY,n)==normalize_statement(h),n
write(RUN/'actual-public-canary-headers-v1.json',actual)
write(RUN/'actual-public-canary-header-fingerprints-v1.json',
      {x['name']:hashlib.sha256(x['header'].encode()).hexdigest() for x in actual})
old=(RUN/'neutral-packet-v1.lean').read_text(encoding='utf-8')
context=old[:old.index('def N01')]
context+='''noncomputable def f9 (A : List Bool → ℝ) (h : List Bool) : ℝ :=
  ∑ t ∈ range h.length, (f5 A (f3 h) t - f4 h t)^2
noncomputable def f10 (h : List Bool) : ℝ :=
  ∑ t ∈ range h.length, (m (f4 h) h.length - f4 h t)^2
noncomputable def f11 : Measure Bool := law univ (fun _ => (1 : ℝ)/2)
def f12 (b : Bool) (_h : List Bool) : ℝ := if b then 1 else 0
'''
replacement={'BanditRLProof.Exp3.FiniteActionDistribution':'P',
 'BanditRLProof.Exp3.finiteActionMeasure':'law','polyaNext':'f1','pathWeight':'f2',
 'binaryStream':'f3','binaryValues':'f4','causalPredict':'f5','pathRegret':'f6',
 'pathExpectation':'f7','prefixMeasure':'f8','pathLearnerLoss':'f9','pathBestLoss':'f10',
 'coinMeasure':'f11','seededPolicy':'f12','empiricalMean':'m','comparatorRegret':'r'}
def neutral(s):
    for a,b in sorted(replacement.items(),key=lambda x:-len(x[0])):s=s.replace(a,b)
    return s
packet=context+'\nuniverse u\n'
index=[]
for i,row in enumerate(actual,1):
    h=row['header'];local=row['name'].rsplit('.',1)[1]
    start='theorem '+local
    assert h.startswith(start)
    binders,prop=h[len(start):].split(' : ',1)
    binders=neutral(binders.strip()).replace('Type*','Type u')
    prop=neutral(prop)
    closed=('∀ '+binders+', '+prop) if binders else prop
    ident='B'+str(i).zfill(3)
    packet+='def '+ident+' : Prop :=\n  '+closed+'\n\n'
    index.append(dict(id=ident,name=row['name'],polymorphic='Type u' in binders))
packet+='end NeutralContext\n'
write(RUN/'full-neutral-packet-v1.lean',packet)
write(RUN/'full-neutral-map-v1.json',index)
gate('full-neutral-types-v1','lake','env','lean',RUN/'full-neutral-packet-v1.lean')
write(RUN/'full-neutral-input-v1.json',dict(path=(RUN/'full-neutral-packet-v1.lean').as_posix(),
    sha256=sha(RUN/'full-neutral-packet-v1.lean'),number_of_targets=64,
    definitions_context_only=True,proofs_absent=True,source_identity_not_supplied_in_packet=True,
    reused_actor_history_must_be_disclosed=True,actual_closed_types=True))
fixed()
print('All64 actual public/test closed propositions typechecked; mandatory full neutral reconstruction pending.')
