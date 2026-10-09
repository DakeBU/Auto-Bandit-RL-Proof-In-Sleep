from common_nonsmooth_publication_v4 import *
fixed()
p=RUN/'nonsmooth-formula-linebreak-review-v5.json'
assert sha(p)=='c054b274af7b16c323f30690bb836d512fff6fc3fa8899d7139c5a2da45b3c5c'
r=load(p);assert r['verdict']==r['materialization_verdict']=='accepted' and not r['required_repairs']
for row in r['raw_input_checks']:assert sha(row['path'])==row['before_sha256']==row['after_sha256']
guard=(RUN/'common_nonsmooth_publication_v4.py').read_text('utf8')
guard=guard.replace("SITE=ROOT/'tmp/online-ch2-nonsmooth-site-v3'","SITE=ROOT/'tmp/online-ch2-nonsmooth-site-v4'")
anchor="    transitions=[dict(path=patch['mutable_path']"
assert guard.count(anchor)==1
addition="""    p5=RUN/'nonsmooth-formula-linebreak-review-v5.json'
    assert sha(p5)=='c054b274af7b16c323f30690bb836d512fff6fc3fa8899d7139c5a2da45b3c5c'
    r5=load(p5);assert r5['verdict']==r5['materialization_verdict']=='accepted' and not r5['required_repairs']
    assert r5['plan_sha256']==sha(CONTRACT/'nonsmooth-formula-linebreak-plan-v5.json')
    assert r5['proposal_sha256']==sha(RUN/'nonsmooth-reader-proposal-v5.json')
"""
guard=guard.replace(anchor,addition+anchor)
assert guard.count("*r4['approved_exact_materialization']]")==1
guard=guard.replace("*r4['approved_exact_materialization']]","*r4['approved_exact_materialization'],*r5['approved_exact_materialization']]")
guard=guard.replace('assert len(transitions)==3','assert len(transitions)==4').replace('for review in [r3,r4]:','for review in [r3,r4,r5]:')
write(RUN/'common_nonsmooth_publication_v5.py',guard)
for a in r['approved_exact_materialization']:
    assert sha(a['path'])==a['before_sha256'] and sha(a['after_snapshot'])==a['after_sha256']
    Path(a['path']).write_bytes(Path(a['after_snapshot']).read_bytes())
import common_nonsmooth_publication_v5 as current
current.fixed()
write(RUN/'nonsmooth-formula-lines-applied-v5.json',dict(actual_review_sha256=sha(p),
    exact_materialization=r['approved_exact_materialization'],all_actual_proofs_source_roots_and_previous_formulas_unchanged=True,
    strict_geometry_and_pixel_check_still_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
registry=(RUN/'verify-nonsmooth-registry-v3.py').read_text('utf8').replace('common_nonsmooth_publication_v4','common_nonsmooth_publication_v5').replace('nonsmooth-registry-inspected-v1.json','nonsmooth-registry-inspected-v2.json')
write(RUN/'verify-nonsmooth-registry-v4.py',registry)
browser=(RUN/'capture-nonsmooth-reader-v3.py').read_text('utf8')
for a,b in [('common_nonsmooth_publication_v4','common_nonsmooth_publication_v5'),('nonsmooth-registry-inspected-v1.json','nonsmooth-registry-inspected-v2.json'),
    ('online-ch2-nonsmooth-playwright-v1-profile','online-ch2-nonsmooth-playwright-v2-profile'),
    ('nonsmooth-browser-server-v1.log','nonsmooth-browser-server-v2.log'),('nonsmooth-browser-node-v1','nonsmooth-browser-node-v2')]:
    assert a in browser,a;browser=browser.replace(a,b)
assert browser.count("str(reg['source_cards']),str(reg['source_cards'])")==1
browser=browser.replace("str(reg['source_cards']),str(reg['source_cards'])","str(reg['source_cards']),'8'")
browser=browser.replace("reg=load(RUN/'nonsmooth-registry-inspected-v2.json')","reg=load(RUN/'nonsmooth-registry-inspected-v2.json')\ndiagnostic=load(RUN/'nonsmooth-browser-diagnostic-v2.json')['diagnostics']\nassert reg['source_cards']==diagnostic['sourceCards']==2\nassert diagnostic['sourceMathContainers']==diagnostic['sourceMathTex']==8 and diagnostic['mathErrors']==0")
write(RUN/'capture-nonsmooth-reader-v4.py',browser)
checkpoint=(RUN/'checkpoint-nonsmooth-site-v5.py').read_text('utf8')
for a,b in [('common_nonsmooth_publication_v4','common_nonsmooth_publication_v5'),('nonsmooth-layout-repair','nonsmooth-formula-lines-repair'),
    ('nonsmooth-contributor-stack-v5','nonsmooth-contributor-stack-v6'),('nonsmooth-contributor-main-v5','nonsmooth-contributor-main-v6'),
    ('nonsmooth-site-build-v3','nonsmooth-site-build-v4'),('nonsmooth-site-check-v3','nonsmooth-site-check-v4'),
    ('nonsmooth-clean-candidate-binding-v3','nonsmooth-clean-candidate-binding-v4'),
    ('verify-nonsmooth-registry-v3.py','verify-nonsmooth-registry-v4.py'),('nonsmooth-registry-command-v1','nonsmooth-registry-command-v2'),
    ('Feature nonsmooth teaching notes and clarify chapter boundary','Wrap nonsmooth source formulas in three preserved rows')]:
    assert a in checkpoint,a;checkpoint=checkpoint.replace(a,b)
write(RUN/'checkpoint-nonsmooth-site-v6.py',checkpoint)
print('Exactly reviewed one-field display change applied; capture now requires actual8 source formulas and unchanged strict geometry checks.')
