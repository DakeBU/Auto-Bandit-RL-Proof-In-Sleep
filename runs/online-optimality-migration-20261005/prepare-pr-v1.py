from pathlib import Path
import json
root=Path(__file__).resolve().parent
target=root/'pr-payload-v1.json'
assert not target.exists()
payload={
 'title':'Qualify and revalidate Orabona convex optimality and interior consequence',
 'head':'codex/research-online-optimality-migration',
 'base':'codex/research-online-first-order-migration',
 'draft':True,
 'body':(root/'pr-body-v1.md').read_text(encoding='utf-8')
}
with target.open('w',encoding='utf-8',newline='\n') as handle:
 json.dump(payload,handle,ensure_ascii=False,indent=2);handle.write('\n')
print('Prepared exact structured draft PR payload; no remote mutation.')
