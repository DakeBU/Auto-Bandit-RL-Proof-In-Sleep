from leaf_driver import *
guard()
versions={'currentSubgradient_affine':('selector',2),'step_affine_fullSpace':('step_affine_fullSpace',1),'iterate_affine_prefix':('iterate_affine_prefix',1),'powerSteps_pos':('powerSteps_pos',1),'switching_loss_regular':('switching_loss_regular',2),'switching_scalar_regret_identity':('switching_scalar_regret_identity',2),'phi_range':('phi_range',3),'phi_limit':('phi_limit',2),'switching_scalar_lower_bound':('switching_scalar_lower_bound',2),'switching_vector_lower_bound':('switching_vector_lower_bound',1),'theorem_5_4':('theorem_5_4',1)}
assert set(versions)==set(targets)
for n,(tag,v) in versions.items():
    assert load(RUN/(tag+'-focused-build-v'+str(v)+'.json'))['actual_exit']==0
    assert load(RUN/(tag+'-fence-compared-v'+str(v)+'.json'))['unchanged']
write(RUN/'FullPublicAuditV1.lean','import BanditRLProof.OnlineUnboundedOSD\n'+''.join('#check '+row['name']+'\n#print axioms '+row['name']+'\n' for row in targets.values())+'''#check (BanditRL.OnlineUnboundedOSD.theorem_5_4 (E := EuclideanSpace ℝ (Fin 2)) (1/2 : ℝ) (by norm_num) (by norm_num) 64)
''')
code,out=capture('full-public-axiom-v1','lake','env','lean',RUN/'FullPublicAuditV1.lean')
lines=[line for line in out.splitlines() if 'depends on axioms:' in line]
assert len(lines)==11 and all(line.endswith('[propext, Classical.choice, Quot.sound]') for line in lines)
assert 'sorryAx' not in out
write(RUN/'full-public-inspected-v1.json',dict(actual_exit=code,raw_stdout=out,axiom_lines=lines,all11_named=True,actual_horizon_64_instance=False,note='Public full source theorem partially applied to64; its numeric horizon proof is REQUIRED in exact canary. No supplied trajectory or regret bound.'))
write(RUN/'full-body-source-v1.lean',PUBLIC.read_bytes())
prefix='''import BanditRLProof.OnlineUnboundedOSD
noncomputable section
open Set Finset Filter Topology
open scoped InnerProductSpace
set_option autoImplicit false
namespace BanditRL.OnlineUnboundedOSDCanary
open BanditRL.OnlineUnboundedOSD
abbrev scalarRun (T t : ℕ) : ℝ :=
  BanditRL.OnlineSubgradientDescent.iterate BanditRL.OnlineHuber.fullSpace (powerSteps (1/2))
    (fun s z => (switchLoss T (1 : ℝ) s z : EReal)) 0 t
abbrev scalarRegret (T : ℕ) : ℝ :=
  BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps (1/2))
    (fun s z => (switchLoss T (1 : ℝ) s z : EReal)) 0 0 T
abbrev direction : EuclideanSpace ℝ (Fin 2) := PiLp.single 0 1
abbrev vectorRun (T t : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  BanditRL.OnlineSubgradientDescent.iterate BanditRL.OnlineHuber.fullSpace (powerSteps (1/2))
    (fun s z => (switchLoss T direction s z : EReal)) 0 t
abbrev vectorRegret (T : ℕ) : ℝ :=
  BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps (1/2))
    (fun s z => (switchLoss T direction s z : EReal)) 0 0 T
'''
headers=[('scalar_actual_two_rounds','''theorem scalar_actual_two_rounds :
    powerSteps (1/2) 0 = 1 ∧
    0 < powerSteps (1/2) 1 ∧
    powerSteps (1/2) 1 < powerSteps (1/2) 0 ∧
    scalarRun 2 0 = 0 ∧ scalarRun 2 1 = 1 ∧
    scalarRun 2 2 = 1 - (2 : ℝ) ^ (-(1/2 : ℝ)) ∧
    scalarRegret 2 = 1'''),('finiteDim_source_lower_bound','''theorem finiteDim_source_lower_bound :
    ‖direction‖ = 1 ∧ vectorRun 64 1 = direction ∧
    (∀ t < 64, ConvexOn ℝ univ (switchLoss 64 direction t) ∧
      LipschitzWith 1 (switchLoss 64 direction t)) ∧
    (1/15 : ℝ) ≤ phi (1/2) ∧
    2 / ((1 - (1/2 : ℝ)) * phi (1/2)) ≤ (64 : ℝ) ∧
    (1/2 : ℝ) * phi (1/2) * (64 : ℝ) ^ (2 - (1/2 : ℝ)) ≤ vectorRegret 64 ∧
    (256/15 : ℝ) ≤ vectorRegret 64 ∧ (17 : ℝ) < vectorRegret 64 ∧
    (∃ loss : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ,
      (∀ t < 64, ConvexOn ℝ univ (loss t) ∧ LipschitzWith 1 (loss t)) ∧
      (1/2 : ℝ) * phi (1/2) * (64 : ℝ) ^ (2 - (1/2 : ℝ)) ≤
        BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace
          (powerSteps (1/2)) (fun t z => (loss t z : EReal)) 0 0 64)''')]
write(CONTRACT/'canary-headers-draft-v1.json',dict(prefix=prefix,targets=[dict(name='BanditRL.OnlineUnboundedOSDCanary.'+n,header=h,raw_header_sha256=hashlib.sha256(h.encode('utf8')).hexdigest()) for n,h in headers],scope='Exact closed propositions only, no proof yet. Scalar T2 is below threshold; E2D T64 proves threshold and nonzero actual same-run lower bound.'))
write(RUN/'CanaryTypeProbeV1.lean',prefix+'\n'+''.join('#check ('+h.split(' :\n',1)[1]+')\n' for n,h in headers)+'\nend BanditRL.OnlineUnboundedOSDCanary\n')
code,out=capture('canary-type-probe-v1','lake','env','lean',RUN/'CanaryTypeProbeV1.lean',required=False)
write(RUN/'canary-type-probe-inspected-v1.json',dict(actual_exit=code,raw_stdout=out,types_only=True,bodies_lowered=False))
assert code==0
write(RUN/'full-body-obligations-v1.json',dict(task=TASK,all11_frozen_terminals_focused_compiled=True,terminal_evidence=versions,full_source_BODY_review='required/open',exact_canary_contract_review='required/open',canary_bodies='required/open',root_Tests_full_harness='required/open',registry_readers_site='required/open',final_native_postnative_delivery='required/open',chapter2='partial/null',whole_Goal='ACTIVE'))
paths=[PUBLIC,RUN/'full-body-source-v1.lean',CONTRACT/'headers-draft-v1.json',CONTRACT/'definitions-frozen-v1.json',CONTRACT/'stabilized-v1.json',CONTRACT/'canary-headers-draft-v1.json',RUN/'CanaryTypeProbeV1.lean',RUN/'canary-type-probe-v1.json',RUN/'canary-type-probe-inspected-v1.json',RUN/'FullPublicAuditV1.lean',RUN/'full-public-axiom-v1.json',RUN/'full-public-inspected-v1.json',RUN/'full-body-obligations-v1.json',RUN/'seven-leaf-review-inputs-v1.json',RUN/'seven-leaf-body-review-v1.md',RUN/'seven-leaf-body-review-v1.json',RUN/'blind-reconstruction-v1.md',RUN/'contract-source-review-v1.md',RUN/'baseline-v1.json',RUN/'prior-readonly-source-pdf64.png',RUN/'prior-readonly-source-pdf65.png',RUN/'prior-readonly-source-pdf64.txt',RUN/'prior-readonly-source-pdf65.txt',PDF]
for n,(tag,v) in versions.items():
    paths.extend([CONTRACT/('frozen-'+n+'-v1.json'),RUN/(tag+'-focused-build-v'+str(v)+'.json'),RUN/(tag+'-focused-inspected-v'+str(v)+'.json'),RUN/(tag+'-fence-compared-v'+str(v)+'.json')])
paths.extend(p for p in RUN.iterdir() if p.is_file() and ('-attempt' in p.name or '-repair-' in p.name or '-focused-build-' in p.name))
write(RUN/'full-body-canary-review-inputs-v1.json',dict(task=TASK,kind='Full source BODY and exact pre-proof canary CONTRACT review; no package/final acceptance',baseline=BASE,immutable_rows=[dict(path=r['path'],sha256=r['sha256'],before_raw_base64=base64.b64encode(Path(r['path']).read_bytes()).decode('ascii')) for r in rows(paths)],allow_only=['full-body-canary-review-v1.md','full-body-canary-review-v1.json'],scope='All11 source terminal bodies now compiled. Exact canary statements/abbreviations only; no Test lowering yet. Root/Tests/full harness/fullcanary/reader/site/final/native/delivery remain required/open. Prior33852 baseline unchanged. Chapter2 partial/null; all8 forwardcontainers requiredOPEN pending dedicated reconciliation; whole Goal ACTIVE.'))
guard()
