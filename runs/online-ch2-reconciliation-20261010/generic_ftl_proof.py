from common import *
LEAF = CONTRACT / 'generic-ftl-v1'
MODULE = ROOT / 'BanditRLProof/OnlineFTLSelector.lean'
END = 'end BanditRL.OnlineFTLSelector\n'

def header(name):
    return next(row['exact_header'] for row in load(LEAF / 'frozen-headers-draft-v1.json')['rows']
                if row['declaration'].endswith('.' + name))

def check_context():
    context = (LEAF / 'definition-context-v1.lean.txt').read_text(encoding='utf8')
    source = MODULE.read_text(encoding='utf8')
    assert source.startswith(context[:-len(END)])
    assert source.endswith(END)
    assert not any(token in source.split() for token in ['sorry', 'admit', 'axiom'])
    for row in load(LEAF / 'frozen-headers-draft-v1.json')['rows']:
        name = row['declaration'].split('.')[-1]
        if 'theorem ' + name + ' ' in source:
            assert row['exact_header'] + ' := by' in source, name

def append_proofs(proofs):
    check_context()
    source = MODULE.read_text(encoding='utf8')
    for name, body in proofs:
        assert 'theorem ' + name + ' ' not in source
        source = source[:-len(END)] + header(name) + ' := by\n' + body.rstrip() + '\n\n' + END
    MODULE.write_bytes(source.encode('utf8'))
    check_context()

def attempt(label):
    fixed()
    check_context()
    snapshot = RUN / 'snapshots' / (label + '.lean.raw')
    write(snapshot, MODULE.read_bytes())
    code, out = capture(label, 'lake', 'env', 'lean', MODULE.relative_to(ROOT), required=False)
    write(RUN / (label + '-binding.json'), dict(
        snapshot=rows([snapshot]), production_module=rows([MODULE]),
        frozen_headers=rows([LEAF / 'frozen-headers-draft-v1.json']),
        command_receipt=rows([RUN / (label + '.json')]),
        actual_compiler_exit=code, named_BODY_compilation_succeeded=(code == 0),
        semantic_BODY_accepted=False, combined_gate=False, chapter_complete=False))
    print(out)
    return code
