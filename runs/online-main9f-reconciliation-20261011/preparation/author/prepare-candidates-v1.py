import copy
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[2]
out = Path(__file__).resolve().parent
candidate = out / 'candidate-v1'
candidate.mkdir(exist_ok=False)
changes = []

def load(side, path):
    return json.loads((out / side / path).read_text(encoding='utf-8'))

def put(path, data):
    dest = candidate / path
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(data)

def jsonput(path, data):
    put(path, (json.dumps(data, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))

def replace_field(local, incoming, field, locator):
    if local.get(field) != incoming.get(field):
        changes.append({'locator': locator + '/' + field, 'before': copy.deepcopy(local.get(field)),
                        'after': copy.deepcopy(incoming.get(field)), 'reason': 'reviewed incoming main correction'})
        local[field] = copy.deepcopy(incoming[field])

path = 'website/content/readings.json'
local = load('local', path)
main = load('main', path)
base = load('base', path)
lm = {x['slug']: x for x in local['readings']}
bm = {x['slug']: x for x in base['readings']}
for incoming in main['readings']:
    slug = incoming['slug']
    previous = bm.get(slug)
    if incoming == previous:
        continue
    item = lm[slug]
    for field in incoming:
        if previous is not None and incoming[field] == previous.get(field):
            continue
        if field == 'source_theorems':
            cards = {x['label']: x for x in item.get(field, [])}
            old_cards = {x['label']: x for x in (previous or {}).get(field, [])}
            for card in incoming[field]:
                label = card['label']
                if card == old_cards.get(label):
                    continue
                current = cards.get(label)
                if current is None:
                    item.setdefault(field, []).append(copy.deepcopy(card))
                    changes.append({'locator': f'{path}/{slug}/{field}/{label}', 'before': None, 'after': card,
                                    'reason': 'reviewed incoming source card'})
                elif current != card:
                    pos = item[field].index(current)
                    changes.append({'locator': f'{path}/{slug}/{field}/{label}', 'before': copy.deepcopy(current),
                                    'after': copy.deepcopy(card), 'reason': 'reviewed incoming source-card correction'})
                    item[field][pos] = copy.deepcopy(card)
        else:
            replace_field(item, incoming, field, f'{path}/{slug}')
jsonput(path, local)

path = 'website/content/highlights.json'
local = load('local', path)
main = load('main', path)
base = load('base', path)
bm = {x['full_name']: x for x in base['highlights']}
for incoming in main['highlights']:
    name = incoming['full_name']
    previous = bm.get(name)
    if incoming == previous:
        continue
    matches = [x for x in local['highlights'] if x['full_name'] == name]
    assert len(matches) == 1, ('No new duplicate or missing declaration accepted', name)
    item = matches[0]
    for field in incoming:
        if previous is not None and incoming[field] == previous.get(field):
            continue
        replace_field(item, incoming, field, f'{path}/{name}')
jsonput(path, local)

path = 'website/content/chapters.json'
local = load('local', path)
main = load('main', path)
base = load('base', path)
lm = {x['slug']: x for x in local['chapters']}
bm = {x['slug']: x for x in base['chapters']}
for incoming in main['chapters']:
    slug = incoming['slug']
    previous = bm.get(slug)
    if incoming == previous:
        continue
    item = lm[slug]
    # Preserve precise already-correct local completion descriptions and open obligations.
    for field in incoming:
        if field in {'completion_definition', 'completion_blockers'}:
            continue
        if previous is not None and incoming[field] == previous.get(field):
            continue
        replace_field(item, incoming, field, f'{path}/{slug}')

replacements = {
 'online-expectation': {
  'completion_definition': 'Seven retained library proofs and three unchanged definitions support signed-integral semantics in the shared library. This foundation route alone is not completion of Orabona Theorem2.9 or Chapter2; the separately integrated Jensen route includes its finite-negative-part producer.',
  'completion_blockers': ['Chapter2 mandatory total remains incomplete/null; all remaining main-text obligations and the whole Goal remain open. The separately integrated Jensen route retains the source probability and finite-mean premises without adding loss integrability.']},
 'online-barycenter': {
  'completion_blockers': ['Chapter2 mandatory total remains incomplete/null; remaining main-text obligations and the Chapters1-16 Goal stay open. The separately integrated Jensen route includes its affine-minorant negative-part producer and probability-loss canaries.']},
 'online-minorant': {
  'completion_definition': 'Four retained proofs: two touching-support helpers and two global-minorant results, zero new proof code/nodes. All four are linked in the teaching route. This dependency route alone is not completion of Orabona Theorem2.9 or Chapter2.',
  'completion_blockers': ['Chapter2 mandatory total remains incomplete/null; all remaining main-text obligations and the Chapters1-16 Goal remain open. The separately integrated source Jensen proof includes its finite-negative-part producer and probability-loss canaries; loss integrability is not a source assumption.']}}
for slug, fields in replacements.items():
    for field, value in fields.items():
        replace_field(lm[slug], {field: value}, field, f'{path}/{slug}')
jsonput(path, local)

path = 'website/content/books.json'
local = load('local', path)
item = next(x for x in local['books'] if x['id'] == 'online-learning')
value = item['summary'] + ' Constrained optimality, signed-integral foundations and the qualified Jensen theorem are separately integrated into this shared library; their bounded scopes do not complete Chapter 2.'
replace_field(item, {'summary': value}, 'summary', f'{path}/online-learning')
jsonput(path, local)

for path in ['BanditRLProof.lean', 'Tests.lean']:
    put(path, (out / 'local' / path).read_bytes())
for path in ['BanditRLProof/OnlineConstraintFiniteLoss.lean', 'BanditRLProof/OnlineConvexMinorant.lean']:
    before = (out / 'local' / path).read_bytes()
    after = (out / 'main' / path).read_bytes()
    assert before.split(b'-/', 1)[1] == after.split(b'-/', 1)[1]
    put(path, after)

files = []
for path in candidate.rglob('*'):
    if path.is_file():
        data = path.read_bytes()
        files.append({'path': path.relative_to(candidate).as_posix(), 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)})
report = {'status': 'CANDIDATE_ONLY_REQUIRES_INDEPENDENT_CONCRETE_REVIEW',
          'local': '3db67ccf41c1c5a312c625b7ed9a2440f1183b7f', 'incoming_main': '9f031681d3697b82b210edd9ab736a6d4ad391f5',
          'changes': changes, 'files': files,
          'untouched_resolution': 'Keep entire current tools/test_book_registry.py; it already includes all incoming coverage with richer schema3/ownership dynamic count assertions. Generator/README/governance accept normal main three-way merge.',
          'gates': 'not run', 'production': 'not changed'}
(out / 'candidate-plan-v1.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print(json.dumps({'candidate_files': len(files), 'explicit_object_corrections': len(changes), 'production_changed': False}))
