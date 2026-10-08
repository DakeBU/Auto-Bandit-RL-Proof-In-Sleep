from common_v1 import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash

baseline_fixed()
assert not PUBLIC.exists()
text = (CONTRACT/'targets-v1.lean.txt').read_text(encoding='utf8')
parts = text.split('\ntheorem ')[1:]
targets = []
for i, part in enumerate(parts):
    if i == len(parts)-1:
        part = part.split('\n\nend BanditRL.OnlineLearning')[0]
    header = 'theorem ' + part.strip()
    name = header.split()[1]
    targets.append(dict(id='L'+str(i+1), name='BanditRL.OnlineLearning.'+name,
        owning_file='BanditRLProof/OnlineGuessingAECausal.lean', header=header,
        statement_hash=statement_hash(header), raw_header_sha256=hashlib.sha256(header.encode('utf8')).hexdigest(),
        phase='draft', compiled=False))
assert len(targets) == 3
write(CONTRACT/'targets-v1.json', dict(version=1, targets=targets, mathematical_terminals_compiled=0))
write(CONTRACT/'dependency-DAG-v1.json', dict(nodes=[
    dict(id='L1', prerequisites=['AEStronglyMeasurable.measurable_mk','Measurable.exists_eq_measurable_comp','continuous_projIcc','Set.projIcc_of_mem','ae_all_iff'], ready=True, terminal='AE all-time bounded history representation'),
    dict(id='L2', prerequisites=['AEStronglyMeasurable.measurable_mk','predictable_private_seed_independent','IndepFun.congr'], ready=True, terminal='actual current-target independence'),
    dict(id='L3', prerequisites=['L2','AEStronglyMeasurable.mono','memLp_of_bounded','expectedFixedMinimum_eq_variance','iid_cumulative_prediction_decomposition'], ready=False, terminal='same original prediction expected fixed-comparator excess identity and nonnegativity')],
    route='single lower route', types_frozen_after_source_contract_review=True, original_source_objects=16, unknown_proof_total=None))
write(CONTRACT/'semantic-signature-v1.json', dict(source_version='1912.13213v10,2026-06-21',
    source_sha256=PDF_SHA, source_pages=[dict(printed=1,pdf=13),dict(printed=3,pdf=15)],
    source_claim='IID guessing lower variance benchmark and pre-reveal information',
    derived_targets=[t['name'] for t in targets], prediction='one infinite original process, before all horizons',
    seed='measurable private tape independent of entire infinite target stream',
    information='F_t subordinate to seed+strict past, AE strongly measurable for ambient measure',
    equality='L1 one AE event all natural times, not off-null pointwise; L3 exact original process',
    comparator='minimum of expected losses of fixed unit comparators, outside expectation',
    initial_time='zero=printed round1, seed and empty history', zero_horizon='empty integral/sum and fixed minimum0',
    conclusions=['bounded measurable policy representation','derived current independence','exact finite expected excess identity and nonnegativity'],
    completion_and_kernel_universality='REQUIRED separately; not equivalent to AE hypothesis without proof',
    chapter_complete=False, goal_complete=False))
proto=text.split('\ntheorem ')[0]+'\n'
for t in targets:
    rest=t['header'].split(t['name'].split('.')[-1],1)[1].strip()
    rest=rest.replace(' :\n', ',\n', 1)
    proto += '#check (∀ '+rest+')\n\n'
proto += 'end BanditRL.OnlineLearning\n'
write(RUN/'draft-typecheck-v1.lean',proto)
gate('draft-typecheck-v1','lake','env','lean',RUN/'draft-typecheck-v1.lean')
native('draft-new-task-v1','new-task',TASK,'--kind','ae-causal-producer',
    '--title','AE strict-past representation and same-prediction IID excess','--target-lean','BanditRLProof/OnlineGuessingAECausal.lean')
for directory in ['tasks','proof-obligations','conversion-windows']:
    p=ROOT/directory/(TASK+'.md')
    raw=p.read_bytes()
    suffix=('\n\n## Frozen draft contract\n\n'+(CONTRACT/'source-intent-v1.md').read_text(encoding='utf8')+
        '\nExact targets: docs/contracts/online-ae-causal-v1/targets-v1.json. DAG: dependency-DAG-v1.json. L1/L2 dependency-ready, L3 awaits L2. Draft type syntax checked; zero theorem bodies/terminals compiled. Contract semantic round trip and review pending.\n').encode('utf8')
    write(RUN/('native-'+directory+'-template-v1.raw'),raw)
    p.write_bytes(raw+suffix)
native('draft-blueprint-v1','blueprint-refresh',TASK)
native('draft-lifecycle-v1','lifecycle-event','--session',TASK,'--event','draft','--payload-json',
    json.dumps(dict(run_id=RUN.name,contract_version=1,target_statement_hashes=[t['statement_hash'] for t in targets],
        source_sha256=PDF_SHA,obligations=3,compiled=0,chapter_complete=False,goal_complete=False)))
for name in ['bandit_paper_cards','bandit_scenario_cards','bandit_textbook_cards','proof_weapon_cards','local_leaf_cards','local_lean_declarations']:
    p=ROOT/'research-wiki/retrieval-index'/(name+'.json')
    write(RUN/'baseline'/('retrieval-'+name+'.raw'),p.read_bytes())
native('draft-reference-index-v1','reference-index')
for label, command in [('search-memory-ae','search-memory'),('list-declarations-ae','list-lean-decls')]:
    native('draft-'+label+'-v1',command,'AEStronglyMeasurable')
native('draft-list-predictable-types-v1','list-lean-decls','predictable_private_seed','--statement')
native('draft-list-mathlib-v1','list-mathlib')
native('draft-list-papers-v1','list-papers')
native('draft-list-weapons-v1','list-weapons')
write(RUN/'draft-retrieval-v1.json', dict(decision='adapt_existing',
    actual_API_lean_exit=load(RUN/'online-ae-causal-api-probe-v4-exit.json')['actual_exit'],
    wrapper_exit_not_Lean_failure='Initial v4 driver failed printing Unicode under GBK after writing actual Lean exit0/log; retain record. No mathematical theorem was proved by #check.',
    source_card='source-qualified Orabona v10 C1 IID guessing / online-foundations',
    scenario='IID unit squared guessing with private independent seed and strict past',
    mathlib_card='MLIB-MEASURE-INTEGRAL plus actual pinned Doob-Dynkin/projIcc API',
    local_candidates=['predictable_private_seed_independent','expectedFixedMinimum_eq_variance','iid_cumulative_prediction_decomposition'],
    generic_reuse=['Measurable.exists_eq_measurable_comp','AEStronglyMeasurable.measurable_mk','AEStronglyMeasurable.ae_eq_mk','IndepFun.congr','continuous_projIcc','Set.projIcc_of_mem','ae_all_iff','memLp_of_bounded'],
    no_duplicate_clipping_definition=True,no_toolchain_or_dependencies_changed=True, proof_weapon='none; not a theorem dependency',
    mathematical_terminals_compiled=0, source_contract_review_pending=True))
context='''Scoped context only. Finset.range t is{0,...,t-1}; its subtype is the finite-history coordinate type. Measure mu is on the ambient measurable space. AEStronglyMeasurable[F] P mu means existence of an F-strongly-measurable real function equal to P mu-almost everywhere, using ambient mu (not an asserted completion identity). iIndepFun is joint independence of the infinite family; IndepFun S(fun omega t=>Y t omega) is seed independence from the entire infinite stream. IdentDistrib is identical distribution under the two displayed measures. These terms are used exactly as the pinned Lean APIs define them.

def privateSeedPastInformation(S:Omega->Seed)(Y:Nat->Omega->Real)(t:Nat) := comap (fun omega => (S omega, fun i:range(t) => Y i omega)) productMeasurableSpace
expectedFixedMinimum(mu,Y,T) := sInf ((fun u:Real => integral mu (fun omega => sum(t<T) (u-Y_t omega)^2)) '' Icc(0,1))
expectedFixedRegret(mu,Y,P,T) := integral mu (fun omega => sum(t<T) (P_t omega-Y_t omega)^2) - expectedFixedMinimum(mu,Y,T)

Reconstruct only the following exact Lean headers in natural language and LaTeX, seven semantic slots each. No source identity, proof body, prior reviewer verdict or production acceptance is supplied. Requested Astra/medium is unverified runtime configuration. This actor has prior staged history; disclose it and do not claim absolute blindness.
'''
write(RUN/'blind-packet-v1.md',context+'\n```lean\n'+text+'```\n')
write(RUN/'blind-inputs-v1.json',dict(rows=raw_index([RUN/'blind-packet-v1.md',CONTRACT/'targets-v1.lean.txt']),
    phase='source identity withheld from this packet; reused prior actor history disclosed',compiled_proof=False))
baseline_fixed(mutable=['MANIFEST.md','runs/lifecycle_sessions.jsonl'])
print('Draft three exact types checked; blind packet ready; production proofs absent')
