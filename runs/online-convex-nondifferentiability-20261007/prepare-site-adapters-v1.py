"""Task-owned site/browser adapters, based on actual shared registry and renderer schema."""
from common_v4 import *
old=Path('runs/online-lipschitz-migration-20261007')
p=Path('research-wiki/contribution-contracts/online-convex-nondifferentiability-20261007.json');d=load(p)
write(RUN/'snapshots/manifest-before-registry-schema-clarification-v1.txt',p.read_bytes())
d['graph_contribution']['visual_review']='Actual9node selectedvaluegraph. Shared Bookregistry has declaration-ID nodes: exportfournewowneddeclarationnodes, preserveallold10811IDsURLs; newownLeanmodule belongsmoduleview, notanextraBookregistrynode. Curated3links/highlights/cards,4notations; actualcurrentpixelsafterfullLean gate.'
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
write(RUN/'registry-schema-clarification-v1.json',dict(actual_prior_registry_identity=load('tmp/online-lipschitz-migration-site-v1/books/registry.json')['identity'],actual_prior_registry_nodes=10811,expected_new_declaration_nodes=4,module_view_distinct=True,not_extra_module_ID_node_in_Book_registry=True,source_headers_or_bodies_changed=False,prior_integration_record_preserved=True))
t=(old/'browser-v1.py').read_text(encoding='utf-8').replace('online-lipschitz-migration-site-v1','online-convex-nondifferentiability-site-v1').replace('online-lipschitz-migration-reader-v1','online-convex-nondifferentiability-reader-v1').replace('online-lipschitz-migration-browser-v1','online-convex-nondifferentiability-browser-v1')
compile(t,str(RUN/'browser-v1.py'),'exec');write(RUN/'browser-v1.py',t)
t=(old/'render-source-card-v2.cjs').read_text(encoding='utf-8').replace('length>=2','length>=3').replace('count()!==2','count()!==3').replace('exactly TWO source definition/theorem cards','exactly THREE source definition/theorem/example cards').replace('i<2','i<3').replace('actual-two-source-cards-visible-and-rendered','actual-three-source-cards-visible-and-rendered')
write(RUN/'render-source-card-v1.cjs',t)
t=(old/'render-source-card-v3.py').read_text(encoding='utf-8').replace('from common_v2','from common_v4').replace('online-lipschitz-migration-site-v1','online-convex-nondifferentiability-site-v1').replace('online-lipschitz-playwright-v1-profile','online-convex-nondifferentiability-playwright-v1-profile').replace('render-source-card-v2.cjs','render-source-card-v1.cjs').replace("len(rendered['cards'])==2","len(rendered['cards'])==3").replace('actual-two-source-cards-rendered-awaiting-pixel-review','actual-three-source-cards-rendered-awaiting-pixel-review').replace('for i in [1,2]','for i in [1,2,3]').replace('TWO actual source cards','THREE actual source cards')
compile(t,str(RUN/'render-source-card-v1.py'),'exec');write(RUN/'render-source-card-v1.py',t)
generated('site-adapters-before-first-use-v1.json',[RUN/'browser-v1.py',RUN/'render-source-card-v1.cjs',RUN/'render-source-card-v1.py'])
print('Actualdecl-onlyregistry clarified; task-ownedTHREEcard/browser adapters preparedbeforefirstuse.')
