from common import *
fixed()
headers=load(CONTRACT/'headers-draft-v2.json')
probe=headers['imports']+'set_option autoImplicit false\nset_option linter.unusedVariables false\n'
for row in headers['targets']:
    binders=row['header'].split('theorem '+row['name'].rsplit('.',1)[1],1)[1]
    binders, conclusion=binders.rsplit(' :\n',1)
    namespace=row['context'].splitlines()[0].split('namespace ',1)[1]
    probe+=row['context']+'#check fun '+binders.strip()+' =>\n  ('+conclusion.strip()+' : Prop)\nend '+namespace+'\n'
write(RUN/'TargetTypesV3.lean',probe)
code,out=capture('draft-type-probe-v3','lake','env','lean',RUN/'TargetTypesV3.lean',required=False)
write(RUN/'draft-type-probe-inspected-v3.json',dict(actual_exit=code, target_count=6,header_manifest=rows([CONTRACT/'headers-draft-v2.json']),actual_stdout=out,repair='v2 unnamed namespace ends were invalid Lean4.29 syntax, causing nested namespace unknown identifiers. v3 explicit end namespace; same six header bytes/scoped contexts, autoImplicit false. v2 actual1/errors retained. No theorem proof/stub authored; compiler error-recovery terms in failed v2 stdout are not accepted proof evidence.'))
assert code==0 and 'error:' not in out and 'error(' not in out
