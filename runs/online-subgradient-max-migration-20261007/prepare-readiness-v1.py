from common_v2 import *
f=fixed(); c=load(CONTRACT/'scoped-contexts.json'); clean=json.loads(json.dumps(c)); corrections=[]
for kind in ['owned_definitions','borrowed_definitions']:
 for n,row in c[kind].items():
  owner=PUBLIC if kind=='owned_definitions' else Path(row['owner'])
  raw=owner.read_text(encoding='utf-8')
  match=re.search(r'(?m)^def '+re.escape(n)+r'\b.*?(?=\n\s*(?:/--|theorem\b|def\b))',raw,re.S); assert match,n
  body=match.group(0).strip(); old=row if isinstance(row,str) else row['body']
  if kind=='owned_definitions':clean[kind][n]=body
  else:clean[kind][n]['body']=body
  corrections.append(dict(name=n,owner=owner.as_posix(),old_context_slice_sha256=hashlib.sha256(old.encode()).hexdigest(),complete_definition_sha256=hashlib.sha256(body.encode()).hexdigest(),adjacent_comment_only_removed=old!=body,original_source_sha256=sha(owner)))
clean['owned_full_body_sha256']={n:hashlib.sha256(t.encode()).hexdigest() for n,t in clean['owned_definitions'].items()}
write(CONTRACT/'scoped-contexts-v2.json',clean)
write(RUN/'definition-context-overlay-v2.json',dict(status='pre-use-context-slice-correction',v1_preserved=True,statement_or_proof_or_definition_changed=False,reason='Regex word boundary after /-- did not match the following space; complete definitions were present with adjacent source comments. v2 removes those comments and labels full-body hashes exactly.',rows=corrections))
p=RUN/'leaves/export-public-dependencies-v1.lean';t=p.read_text(encoding='utf-8'); old='Lean.importModules #[{ module := `BanditRLProof }]';new='Lean.importModules #[{ module := `BanditRLProof }, { module := `Tests.OnlineSubgradientMaxCanary }]';assert t.count(old)==1
q=RUN/'leaves/export-public-dependencies-v2.lean';write(q,t.replace(old,new))
write(RUN/'public-exporter-pre-use-correction-v2.json',dict(reason='Compile-time module import does not add canaries to a separately imported runtime environment. Explicitly import root AND the actual canary module in the exporter environment.',original_unused=True,original_path=p.as_posix(),original_sha256=sha(p),corrected_path=q.as_posix(),corrected_sha256=sha(q),math_changed=False))
write(RUN/'API-route-before-proof-v1.json',dict(source_card='ORABONA-V10-T2.26',mathlib_card='MLIB-CONVEX-LINALG; actual pinned finite extrema/convex hull/compact sequence/filter/HB/Riesz probes',status='retained project-local producers; pinned imported candidates await actual build',new_general_lemma=False,external_dependency=False,pin_change=False,intended_route=load(CONTRACT/'initial-dependency-DAG.json'),whole_canary_proofs=19,whole_canary_definitions=2,new_math_or_tests=0))
write(RUN/'read-only-path-lookup-diagnostics-v1.json',dict(tool_chunks=['66bdac','992a85'],issue='Read-only template file guesses record-readiness/prepare-neutral/prepare-contract-review did not exist. rg returned actual prepare-readiness/prepare-contract and review-packets names. These PowerShell Get-Content diagnostics did not modify source and are not Lean or harness gate evidence. Entire command exit0 did not certify the missing reads.',retry_by_actual_search=True))
generated('readiness-generated-before-use-v1.json',[CONTRACT/'scoped-contexts-v2.json',q,RUN/'common_v2.py',RUN/'run-command.py',RUN/'API-route-before-proof-v1.json'])
gate('retained-focused-v1-01','lake','build','BanditRLProof.OnlineSubgradientMax','Tests.OnlineSubgradientMaxCanary')
gate('actual-types-v1-01','lake','env','lean',RUN/'leaves/actual-types-v1.lean')
gate('pinned-APIs-v1-01','lake','env','lean',RUN/'leaves/pinned-APIs-v1.lean')
gate('compiled-ready-graph-v1-01','lake','env','lean','--run',RUN/'leaves/export-ready-dependencies-v1.lean',RUN/'compiled-ready-graph-v1.json')
for command in ['statement-fence','retrieval-record','lifecycle-event','list-lean-decls','search-memory']:
 native(command+'-help-v1-01',command,'--help')
fixed();print('Current unchanged producer/canary focused build,40 actualtypes,20 pinned APIs and19 production-node compiled-readiness export passed; source semantic review remains pending.')
