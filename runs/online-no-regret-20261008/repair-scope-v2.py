from common_integrated_v1 import *
fixed_integrated();assert load(RUN/'scope-pre-gates-v1-exit.json')['exit_code']==1
write(RUN/'scope-repair-v2.json',dict(failed_gate='scope-pre-gates-v1',reason='Append-only MANIFEST contains eight actual reference-index rows in the already disclosed current RUN/native-reference-index directory, with lower-case run id rather than uppercase TASK id.',repair='Retain native eight rows and original prefix; validate exactly the eight known actual same-schema files under this task-owned output directory. No unrelated MANIFEST/journal mutation authorized.',source_and_terminal_unchanged=True))
s=(RUN/'audit-scope-v1.py').read_text(encoding='utf8')
s=s.replace("assert all(TASK in line for line in new[len(old):].decode('utf8').splitlines() if line.strip())", "extra=[line for line in new[len(old):].decode('utf8').splitlines() if line.strip() and TASK not in line]\nindex_names={'lml_bandit_cards.json','mathlib_bandit_cards.json','bandit_textbook_cards.json','bandit_paper_cards.json','bandit_scenario_cards.json','proof_weapon_cards.json','local_leaf_cards.json','local_lean_declarations.json'}\nassert len(extra)==8\nfor line in extra:\n assert '`bandit.py reference-index` `retrieval-index`' in line\n assert any('`'+(RUN.relative_to(ROOT)/'native-reference-index'/n).as_posix()+'`' in line for n in index_names),line")
write(RUN/'audit-scope-v2.py',s)
native('scope-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(reason='Task-owned native reference-index rows did not contain uppercase TASK literal',evidence=(RUN/'scope-repair-v2.json').as_posix(),source_or_terminal_unchanged=True)))
native('scope-recandidate-event-v2','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(reason='Exact eight task-owned native reference-index append rows audited',source_body_review_unchanged=True)))
gate('scope-pre-gates-v2',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v2.py','pre-gates-v2')
old=(RUN/'integrated-gates-v1.py').read_text(encoding='utf8');suffix=old[old.index("gate('stage-owned-public-tests-v1'"):]
write(RUN/'integrated-gates-v2.py','from common_integrated_v1 import *\nfixed_integrated()\n'+suffix)
gate('integrated-gates-driver-v2',sys.executable,'-B','-X','utf8',RUN/'integrated-gates-v2.py')
fixed_integrated()
