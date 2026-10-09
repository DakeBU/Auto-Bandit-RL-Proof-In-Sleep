from generic_ftl_proof import *
CANARY = LEAF / 'canary-v2'
TEST = ROOT / 'Tests/OnlineFTLSelectorCanary.lean'
TEST_END = 'end Tests.OnlineFTLSelector\n'

def canary_fixed():
    fixed()
    frozen = load(CANARY / 'stabilized-v2.json')
    assert sha(MODULE) == frozen['production_sha256']
    assert sha(CANARY / 'definition-context-v2.lean.txt') == frozen['definition_context_sha256']
    assert sha(CANARY / 'frozen-headers-draft-v2.json') == frozen['headers_sha256']
    source = TEST.read_text(encoding='utf8')
    context = (CANARY / 'definition-context-v2.lean.txt').read_text(encoding='utf8')
    assert source.startswith(context[:-len(TEST_END)]) and source.endswith(TEST_END)
    assert not any(token in source.split() for token in ['sorry', 'admit', 'axiom'])
    for row in load(CANARY / 'frozen-headers-draft-v2.json')['rows']:
        name = row['declaration'].split('.')[-1]
        if 'theorem ' + name + ' ' in source:
            assert row['exact_header'] + ' := by' in source, name

def append_canary(proofs, helpers=''):
    canary_fixed()
    source = TEST.read_text(encoding='utf8')
    if helpers:
        source = source[:-len(TEST_END)] + helpers.rstrip() + '\n\n' + TEST_END
    for name, body in proofs:
        row = next(row for row in load(CANARY / 'frozen-headers-draft-v2.json')['rows']
                   if row['declaration'].endswith('.' + name))
        assert 'theorem ' + name + ' ' not in source
        source = source[:-len(TEST_END)] + row['exact_header'] + ' := by\n' + body.rstrip() + '\n\n' + TEST_END
    TEST.write_bytes(source.encode('utf8'))
    canary_fixed()

def canary_attempt(label):
    canary_fixed()
    snapshot = RUN / 'snapshots' / (label + '.lean.raw')
    write(snapshot, TEST.read_bytes())
    code, out = capture(label, 'lake', 'env', 'lean', TEST.relative_to(ROOT), required=False)
    write(RUN / (label + '-binding.json'), dict(snapshot=rows([snapshot]), actual_Test_module=rows([TEST]),
        production=rows([MODULE]), frozen_headers=rows([CANARY / 'frozen-headers-draft-v2.json']),
        command_receipt=rows([RUN / (label + '.json')]), actual_compiler_exit=code,
        named_BODY_compilation_succeeded=(code == 0), semantic_canary_BODY_accepted=False,
        combined_gate=False, chapter_complete=False))
    print(out)
    return code
