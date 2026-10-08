from common_body_v2 import *
import gzip
integrated_fixed()
assert load(RUN/'registry-check-v1-exit.json')['actual_exit']==1
old=json.loads(gzip.decompress((RUN/'registry-baseline-v1.json.gz').read_bytes()).decode('utf8'))
current=load(SITE/'books/registry.json');manifest=load(SITE/'site-manifest.json')
ob={n['id']:n for n in old['nodes']};nb={n['id']:n for n in current['nodes']}
assert len(ob)==10964 and all(nb.get(i)==n for i,n in ob.items())
new={i:nb[i] for i in sorted(set(nb)-set(ob))}
assert len(new)==13
public={i:n for i,n in new.items() if n['identity_basis']=='source-qualified-name'}
private={i:n for i,n in new.items() if n['identity_basis']=='source-private-name'}
assert len(public)==5 and len(private)==8
write(RUN/'registry-repair-v2.json',dict(actual_v1_exit=1,failed_expectation='Total10969 and only5new nodes; ignored source-private inventory behavior.',
    actual_registry_API='website/scripts/book_registry.py:187 explicitly uses source-private-name for private source declarations.',
    actual_total=10977,retained_complete_old_records=10964,new_public_records=public,new_source_private_records=private,
    private_records_not_public_instantiable=True,public_theorem_terminals=4,public_supporting_definitions=1,
    original_verify_helper_unchanged=True,public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    no_source_proof_statement_reader_root_pin_registry_API_change=True,no_required_obligation_count_change=True,
    BODY_scope_exactly5_PUBLIC_nodes_still_satisfied=True,FINAL_repair_review_required=True,goal_complete=False))
source=(RUN/'verify-registry-v1.py').read_text(encoding='utf8')
source=source.replace('len(nb)==10969','len(nb)==10977')
source=source.replace('assert set(nb)-set(ob)==expected','''private_names=['dyadicObservation_binary','dyadic_pair','dyadic_prefix_pair','dyadic_high_count',
    'dyadic_low_count','dyadic_high_mean','dyadic_low_mean','dyadic_horizons_tendsto']
private_expected={'declaration:BanditRL.OnlineLearning.'+n for n in private_names}
assert set(nb)-set(ob)==expected|private_expected
assert all(nb[i]['identity_basis']=='source-qualified-name' for i in expected)
assert all(nb[i]['identity_basis']=='source-private-name' for i in private_expected)''')
source=source.replace('total_nodes=10969,','new_source_private_nodes=8,private_ids=sorted(private_expected),private_nodes_not_public_instantiable=True,total_nodes=10977,')
source=source.replace("write(RUN/'registry-v1.json'","write(RUN/'registry-v2.json'")
source=source.replace("plus4 production theorems and1 definition.","plus4 PUBLIC production theorems/1 PUBLIC definition and8 source-private helpers.")
write(RUN/'verify-registry-v2.py',source)
gate('registry-check-v2',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v2.py')
# Real contributor checks use the already committed candidate, never an empty precommit diff.
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert head==current['source_commit']==manifest['source_commit'] and not manifest['source_dirty']
for label,base in [('candidate-contributor-stack-v1',BASE),('candidate-contributor-main-v1','origin/main')]:
    gate(label,sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base)
    text=(RUN/(label+'.log')).read_text(encoding='utf8')
    assert 'Contributor contract: N/A' not in text and PUBLIC.relative_to(ROOT).as_posix() in text
write(RUN/'candidate-contributor-gates-v1.json',dict(actual_head=head,both_nonempty_bases_cover_new_production=True,
    receipts=['candidate-contributor-stack-v1-exit.json','candidate-contributor-main-v1-exit.json'],
    FINAL_required=True,package_accepted=False,chapter_complete=False,goal_complete=False))
integrated_fixed()
