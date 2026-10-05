from pathlib import Path
import json
run=Path(__file__).parent;target=run/'pr-payload-v1.json'
assert not target.exists()
assert json.loads((run/'native-acceptance-overlay-v1.json').read_text(encoding='utf-8'))['status']=='passed'
payload=dict(title='Qualify and revalidate signed expectation foundations for source Jensen',head='codex/research-online-expectation-migration',base='codex/research-online-optimality-migration',draft=True,body=(run/'pr-body-v1.md').read_text(encoding='utf-8'))
with target.open('w',encoding='utf-8',newline='\n') as handle:json.dump(payload,handle,ensure_ascii=False,indent=2);handle.write('\n')
print('Structured draft payload prepared after actual bounded acceptance; no remote mutation.')
