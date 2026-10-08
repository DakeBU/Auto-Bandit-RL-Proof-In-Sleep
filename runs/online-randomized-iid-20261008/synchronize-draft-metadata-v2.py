from common_v1 import *

fixed()
targets = load(CONTRACT / 'targets-v2.json')['rows']
paths = [Path('tasks') / (TASK + '.md'), Path('conversion-windows') / (TASK + '.md'),
    Path('proof-obligations') / (TASK + '.md'), Path('proof-blueprints') / (TASK + '.md')]
for p in paths:
    write(RUN / 'snapshots' / ('native-bootstrap--' + p.as_posix().replace('/','--') + '.raw'), p.read_bytes())
source = 'Orabona arXiv1912.13213v10/2026-06-21, printed1–2/PDF13–14, SHA' + PDF_SHA
body = '# Private seed and predictable strict-past IID guessing variance benchmark\n\n'
body += 'Task id: `' + TASK + '`\nKind: `lean`\nStatus: `draft`\nHarness: `hierarchical`\n\n'
body += '## Goal\n\nProduce current-target independence and cumulative expected-fixed excess for independent private tape and measurable strict-past predictions. Frozen exact prospective headers in `' + CONTRACT.as_posix() + '/targets-v2.json`; source contract review pending, no body accepted. Total Chapters1–16 Goal ACTIVE.\n\n'
body += '## Source\n\n' + source + '. Source card `' + CONTRACT.as_posix() + '/source-card-v2.json`; scenario private tape independent WHOLE IID stream, subordinate pre-reveal information.\n\n'
body += '## Lean Target\n\nTarget file: `' + PUBLIC.as_posix() + '`\n\n'
body += '\n'.join('- `' + r['name'] + '` (' + r['id'] + '): ' + r['source_class'] for r in targets)
body += '\n\n## Boundaries\n\nProbability/measurable/a.s.unit targets, same laws/joint IID, whole-process seed independence. Legal history cube only; general predictions a.s.feasible. Minimum of expected FIXED loss outside integration; no E[min], future inputs, supplied current independence, full kernel representation or asymptotic claim. t0 extension; source1..T=Lean0..T−1. Original16/null, C1C2open, remaining asymptotic/oldfive/3–16/appendices required. OPENdraftPR194 exactb08 stack, not main/live.\n\n'
body += '## Mathlib-Ready Leaf Contract\n\nCards MLIB-PROBABILITY-INDEPENDENCE/MLIB-MEASURE-INTEGRAL/MLIB-PROBABILITY-VARIANCE. R001 mathlib-candidate (not upstream); R002–R007 project-local. Exact typed API evidence in runs/' + RUN.name + '/draft-types-and-API-v2.log; staged ROOT director/architect and single lower route. Distinct mandatory semantic roundtrip before proving. Focused build/public canary/axiom/fences/root/Tests/fullharness/site and semantic reviewer all separate before acceptance.\n'
(paths[0]).write_bytes(body.encode('utf8'))
conversion = '# Conversion Window: ' + TASK + '\n\nSource card: `' + CONTRACT.as_posix() + '/source-card-v2.json`\nScenario: independent private tape and strict-past IID prediction.\n\n'
conversion += (CONTRACT / 'conversion-window-v2.md').read_text(encoding='utf8')
conversion += '\n## Lean Mapping\n\n| Source | Lean | Role |\n| --- | --- | --- |\n| private randomness | S, hseed | independent whole-process tape |\n| pre-reveal history | privateSeedPastInformation S Y t | generated comap, strict i<t |\n| general causal prediction | Measurable[F t](prediction t), F t≤generated | information-constrained producer |\n| randomized policy | policy t(S,past) | jointly measurable actual finite-history implementation |\n| variance benchmark | expectedFixedMinimum, expectedFixedRegret | actual PR194 minE, same stream/prefix |\n'
paths[1].write_bytes(conversion.encode('utf8'))
ob = '# Proof Obligations: ' + TASK + '\n\nStatus: draft. All seven exact v2 terminals unproved; source stabilization pending. Source card `' + CONTRACT.as_posix() + '/source-card-v2.json`.\n\n'
ob += '| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |\n| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |\n'
for r in targets:
    ob += '| `' + r['id'] + '` | ' + r['source_class'] + ' | ' + (', '.join(r['dependencies']) or 'typed Mathlib APIs') + ' | OnlineGuessingIIDBenchmark; Independence.Basic | MLIB-PROBABILITY-INDEPENDENCE/MEASURE-INTEGRAL | exact DAG single route | exact header v2, no weakening | ' + ('mathlib-candidate' if r['id']=='R001' else 'project-local') + ' | ROOT staged worker | `' + r['name'] + '` | focused/public/root/Tests/fullharness + semantic | draft-unproved |\n'
ob += '\nFailure classification: preserve actual source translation/local Lean gap/regularity/counterexample/invalid route record; no placeholder or certificate consumer completion. Chapter/Goal remain open.\n'
paths[2].write_bytes(ob.encode('utf8'))
native('blueprint-refreshed-draft-v2', 'blueprint-refresh', TASK)
write(RUN / 'draft-native-metadata-v2.json', dict(actual_native_blueprint=True, rows=[
    dict(path=p.as_posix(),sha256=sha(p)) for p in paths], exact_targets=sha(CONTRACT / 'targets-v2.json'),
    status='draft-not-stabilized', semantic_review_pending=True))
fixed()
print('Own native metadata now describes actual source/info/seven terminals; old boilerplate retained.')
