from common_reader_v2 import *
fixed_integrated()
assert load(RUN/'site-build-v2-exit.json')['actual_exit']==1
old=load(RUN/'reader-proposal-v2.json');new=json.loads(json.dumps(old))
changes=[]
for i in [0,1]:
    note=new['notes'][i]
    external=[n for n in note['dependencies'] if not n.startswith('BanditRL.')]
    assert external
    note['dependencies']=[n for n in note['dependencies'] if n.startswith('BanditRL.')]
    if i==0:note['dependencies']=['BanditRL.OnlineLearning.privateSeedPastInformation']
    note['lean_notes']+=' Actual pinned mathlib proof APIs: '+', '.join(external)+'. These names are in the compiled VALUE audit; the reader dependency links use the existing ABRL registry.'
    changes.append(dict(note=note['full_name'],old_dependencies=old['notes'][i]['dependencies'],
        new_dependencies=note['dependencies'],explicit_external_API_text=external))
write(RUN/'reader-proposal-v3.json',new)
p=ROOT/'website/content/highlights.json'
write(RUN/'snapshots/highlights-before-dependency-repair-v2.raw',p.read_bytes())
d=load(p);byname={n['full_name']:n for n in new['notes']}
assert d['highlights'][-3:]==old['notes']
d['highlights'][-3:]=new['notes']
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
b=load(RUN/'reader-integration-bindings-v2.json');b['reader_proposal_sha256']=sha(RUN/'reader-proposal-v3.json');b['reader_proposal_version']=3
write(RUN/'reader-integration-bindings-v3.json',b)
write(RUN/'reader-dependency-repair-v3.json',dict(actual_failed_site_receipt='site-build-v2-exit.json',
    actual_error='Highlight dependency links must resolve in the shared ABRL declaration registry; pinned mathlib API names are not local registry nodes.',
    changes=changes,preserved_external_VALUE_edges=True,no_new_or_duplicate_registry_for_mathlib=True,
    source_or_public_header_or_proof_change=False,combined_Lean_gate_remains_applicable=True))
print('Exact own reader dependency links repaired; actual external VALUE APIs remain explicit.',flush=True)
