from common_reviewed_v2 import *
import re

headers_fixed(7)
bindings=load(RUN/'actual-compiled-kind-bindings-v2.json')
names=bindings['compiled_names']
assert len(names)==55 and bindings['named_canary_proofs']==29
actual=load(RUN/'actual-public-canary-headers-v2.json')
TEST='Tests.OnlineGuessingRandomizedIID.'
text=CANARY.read_text(encoding='utf8')
write(RUN/'leaves'/'all-selected-axioms-v2.lean','import Tests.OnlineGuessingRandomizedIIDCanary\n'+
    '\n'.join('#check '+n+'\n#print axioms '+n for n in names))
gate('all-selected-axioms-v2','lake','env','lean',RUN/'leaves/all-selected-axioms-v2.lean')
log=(RUN/'all-selected-axioms-v2.log').read_text(encoding='utf8')
assert 'sorryAx' not in log
matched=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
assert len(matched)==len(names)
axioms={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matched}
assert set(axioms)==set(names)
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
write(RUN/'all-selected-axiom-bindings-v2.json',dict(names=names,axioms=axioms,count=len(names),
    actual_kinds=bindings['kinds'],public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY)))

def closed_type(raw):
    short=raw.split()[1]
    tail=raw[len('theorem '+short):].strip()
    depth=0
    for pos,char in enumerate(tail):
        if char in '([{': depth+=1
        elif char in ')]}': depth-=1
        elif char==':' and depth==0:
            params,result=tail[:pos].strip(),tail[pos+1:].strip()
            return ('∀ '+params+',\n' if params else '')+result
    raise AssertionError(raw)

s='''import Tests.OnlineGuessingRandomizedIIDCanary

noncomputable section
open MeasureTheory ProbabilityTheory BanditRL.OnlineLearning
open Tests.OnlineGuessingIIDBenchmark Tests.OnlineGuessingRandomizedIID
open scoped ENNReal

namespace ExactSeedCanary
def propositionOf {P : Prop} (_ : P) : Prop := P
local instance : MeasurableSpace (Fin 4) :=
  Tests.OnlineGuessingRandomizedIID.instMeasurableSpaceFinOfNatNat_tests
local instance : MeasurableSingletonClass (Fin 4) :=
  Tests.OnlineGuessingRandomizedIID.instMeasurableSingletonClassFinOfNatNat_tests
'''
for i,row in enumerate(actual[7:],1):
    s+='\ndef C%03d : Prop := %s\nexample : C%03d = propositionOf (@%s) := rfl\n' % (i,closed_type(row['raw_header']),i,row['name'])
fixture_shorts=re.findall(r'(?m)^def (\w+)\b',text)
for short in fixture_shorts:
    start=text.index('def '+short+' ')
    raw=text[start:text.index('\n\n',start)].replace('def '+short+' ','def '+short+'Fixture ',1)
    s+='\n'+raw+'\nexample : @'+short+'Fixture = @'+TEST+short+' := rfl\n'
s+='\nexample : propositionOf (@seededLaw_probability) = IsProbabilityMeasure seededLaw := rfl\n'
s+='example : propositionOf (@fourLaw_probability) = IsProbabilityMeasure fourLaw := rfl\n'
s+='example : @Tests.OnlineGuessingRandomizedIID.instMeasurableSpaceFinOfNatNat_tests = (⊤ : MeasurableSpace (Fin 4)) := rfl\n'
s+='example : propositionOf (@Tests.OnlineGuessingRandomizedIID.instMeasurableSingletonClassFinOfNatNat_tests) = @MeasurableSingletonClass (Fin 4) (⊤ : MeasurableSpace (Fin 4)) := rfl\n'
s+='end ExactSeedCanary\n'
write(RUN/'leaves'/'actual-canary-types-fixtures-v2.lean',s)
gate('actual-canary-types-fixtures-v2','lake','env','lean',RUN/'leaves/actual-canary-types-fixtures-v2.lean')

graph=load(RUN/'compiled-body-value-graph-v2.json')
edges={(e['source'],e['target']) for e in graph['edges'] if e['kind']=='value' or e['also_in_value']}
required=[(PRE+a,b) for a,b in [
    ('independent_private_seed_pair','ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map'),
    ('independent_private_seed_pair','MeasurableEquiv.prodAssoc'),
    ('independent_private_seed_pair','MeasureTheory.Measure.prodAssoc_prod'),
    ('private_seed_past_independent',PRE+'independent_private_seed_pair'),
    ('private_seed_past_independent','ProbabilityTheory.iIndepFun.indepFun_finset'),
    ('private_seed_past_independent','ProbabilityTheory.IndepFun.comp'),
    ('predictable_private_seed_independent',PRE+'private_seed_past_independent'),
    ('predictable_private_seed_independent','ProbabilityTheory.indep_of_indep_of_le_left'),
    ('randomized_history_policy_independent',PRE+'private_seed_past_independent'),
    ('predictable_private_seed_expectedFixed_excess',PRE+'predictable_private_seed_independent'),
    ('predictable_private_seed_expectedFixed_excess',PRE+'expectedFixedMinimum_eq_variance'),
    ('predictable_private_seed_expectedFixed_excess',PRE+'iid_cumulative_prediction_decomposition'),
    ('randomized_history_policy_expectedFixed_excess',PRE+'predictable_private_seed_expectedFixed_excess')]]
required += [(TEST+a,b) for a,b in [
    ('target_independent','ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map'),
    ('seed_independent_whole_process','ProbabilityTheory.indepFun_prod'),
    ('actual_information_monotone',PRE+'privateSeedPastInformation_monotone'),
    ('actual_seed_history_independent',PRE+'private_seed_past_independent'),
    ('actual_policy_current_independent',PRE+'randomized_history_policy_independent'),
    ('actual_randomized_excess_nonnegative',PRE+'randomized_history_policy_expectedFixed_excess'),
    ('actual_general_information_excess_nonnegative',PRE+'predictable_private_seed_expectedFixed_excess'),
    ('actual_empty_excess',PRE+'randomized_history_policy_expectedFixed_excess'),
    ('actual_two_round_excess',PRE+'randomized_history_policy_expectedFixed_excess'),
    ('current_target_not_private_information',PRE+'predictable_private_seed_independent'),
    ('xor_seed_not_independent_whole_pair',PRE+'independent_private_seed_pair'),
    ('xor_seed_not_independent_whole_pair',TEST+'xor_seed_past_not_independent_current'),
    ('pairwise_seed_independence_is_insufficient',TEST+'xor_seed_past_not_independent_current')]]
for pair in required: assert pair in edges,pair
write(RUN/'required-direct-VALUE-pairs-v2.json',dict(required_pairs=required,count=len(required),
    extraction='Actual compiled proof VALUE constant occurrence, separate from type and registry mappings.',
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY)))
fences=[]
for row in actual:
    short=row['name'].rsplit('.',1)[1]
    label=('public-' if Path(row['path'])==PUBLIC else 'canary-')+short
    fence=RUN/'full-header-fences-v2'/(label+'.json')
    native('full-fence-'+label+'-v2','statement-fence','--declaration',row['name'],'--file',row['path'],
        '--source-assumption',row['header'],'--output',fence)
    native('full-safe-'+label+'-v2','safe-verify','--fence',fence,'--lean-file',row['path'])
    assert load(fence)['statement']==row['header']
    fences.append(dict(name=row['name'],path=fence.as_posix(),sha256=sha(fence),statement_hash=load(fence)['statement_hash']))
write(RUN/'full-fence-bindings-v2.json',fences)
native('actual-public-lookup-v2','list-lean-decls','--statement',PRE+'private_seed')
native('actual-canary-lookup-v2','list-lean-decls','--include-tests','--statement',TEST)
write(RUN/'body-bindings-v2.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),contract_version=2,
    frozen_targets=7,new_public_proofs=7,new_public_definitions=1,named_canary_proofs=29,test_definitions=9,
    named_probability_instances=2,actual_anonymous_measurable_instances=2,named_kernel_checks=55,
    actual_compiler_kinds=bindings['kinds'],axioms=axioms,actual_public_universal_type_gate='actual-public-types-kernel-v2-exit.json',
    canary_Prop_identities=29,canary_whole_definition_identities=9,probability_Prop_identities=2,
    actual_anonymous_class_definition_and_Prop_identities=2,required_direct_VALUE_pairs=required,
    full_native_header_guards=len(fences),safe_verify_scope='Header/token scan only; actual kernel builds recorded separately.',
    BODY='pending',combined_reader_FINAL_native_PR='pending',package_accepted=False,chapter_complete=False,goal_complete=False))
headers_fixed(7)
print('Actual 55 kernel checks, 29 exact canary Props, 9 whole fixtures, 2 probability types, 2 actual class identities, 26 VALUE pairs, 36 native fences passed; BODY pending.')
