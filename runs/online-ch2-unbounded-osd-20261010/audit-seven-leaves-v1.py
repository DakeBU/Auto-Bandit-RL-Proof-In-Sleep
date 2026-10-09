from leaf_driver import *
guard()
leaves=[('currentSubgradient_affine','selector',2),('step_affine_fullSpace','step_affine_fullSpace',1),('iterate_affine_prefix','iterate_affine_prefix',1),('powerSteps_pos','powerSteps_pos',1),('phi_limit','phi_limit',2),('switching_loss_regular','switching_loss_regular',2),('phi_range','phi_range',3)]
for name,tag,v in leaves:
    assert load(RUN/(tag+'-focused-build-v'+str(v)+'.json'))['actual_exit']==0
    assert load(RUN/(tag+'-fence-compared-v'+str(v)+'.json'))['unchanged']
write(RUN/'SevenLeafPublicAuditV1.lean','import BanditRLProof.OnlineUnboundedOSD\n'+''.join('#check '+targets[n]['name']+'\n#print axioms '+targets[n]['name']+'\n' for n,_,_ in leaves)+'''#check (BanditRL.OnlineUnboundedOSD.step_affine_fullSpace (2 : ℝ) (3 : ℝ) 5 7)
#check (BanditRL.OnlineUnboundedOSD.iterate_affine_prefix (fun t => ((t+1 : ℕ) : ℝ)) (fun t => ((t+2 : ℕ) : ℝ)) (fun _ => (7 : ℝ)) (3 : ℝ) 4)
#check (BanditRL.OnlineUnboundedOSD.powerSteps_pos (1/2 : ℝ) 3)
#check (BanditRL.OnlineUnboundedOSD.switching_loss_regular 4 (1 : ℝ) (by norm_num) 3)
#check (BanditRL.OnlineUnboundedOSD.phi_range (1/2 : ℝ) (by norm_num) (by norm_num))
''')
code,out=capture('seven-leaf-public-axiom-v1','lake','env','lean',RUN/'SevenLeafPublicAuditV1.lean')
assert 'sorryAx' not in out and 'axioms [' in out
write(RUN/'seven-leaf-public-inspected-v1.json',dict(actual_exit=code,raw_stdout=out,leaves=[targets[n]['name'] for n,_,_ in leaves],scope='Seven dependency leaves named and applied proofs only; full source theorem/canary/package acceptance remain open.'))
write(RUN/'seven-leaf-body-source-v1.lean',PUBLIC.read_bytes())
state=dict(task=TASK,stage='proving',locally_compiled=[dict(name=targets[n]['name'],focused_receipt=tag+'-focused-build-v'+str(v)+'.json',fence_receipt=tag+'-fence-compared-v'+str(v)+'.json') for n,tag,v in leaves],required_open=[targets[n]['name'] for n in targets if n not in [a for a,_,_ in leaves]],source_regret_lower_bound_closed=False,package_BODY_accepted=False,chapter_complete=False,whole_Goal='ACTIVE')
write(RUN/'proof-obligations-seven-leaf-v1.json',state)
write(RUN/'memory-digest-seven-leaf-v1.md','Seven frozen dependency terminals have actual focused compiler/fence/public/axiom evidence. Failed attempts retained: selector dependent-motive rewrite; phi_limit function-evaluation/filter endpoint; switching_regular unfactored abs difference; phi_range namespace/interval/numeral adaptations. Four mandatory source terminals remain open: scalar identity, scalar lower bound, vector same-run lift and complete Theorem5.4. No Test/full source canary/root/full harness/site/native acceptance or delivery for this package. Prior tracked baseline unchanged. Whole16chapter Goal ACTIVE; Chapter2 partial/totalnull.\n')
for path in [ROOT/'proof-obligations'/ (TASK+'.md'),ROOT/'research-wiki/retrieval-index'/(TASK+'.md')]:
    old=path.read_bytes()
    write(RUN/(path.parent.name+'-seven-leaf-before-v1.json'),dict(path=path.as_posix(),sha256=sha(path),raw_base64=base64.b64encode(old).decode('ascii')))
    path.write_bytes(old+b'\nSeven dependency leaves focused-compiled with frozen statements and named public axiom evidence: see runs/online-ch2-unbounded-osd-20261010/proof-obligations-seven-leaf-v1.json. Scalar identity/lower bound, vector same-run lift, complete source theorem and all package acceptance gates remain REQUIRED OPEN. Chapter2 partial; whole Goal ACTIVE.\n')
guard()
