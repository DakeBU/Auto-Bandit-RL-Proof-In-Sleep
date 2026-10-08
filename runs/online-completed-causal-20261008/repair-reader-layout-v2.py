from common_body_v2 import *
from commit_owned_v1 import commit_owned

fixed_integrated()
assert load(RUN / 'formula-render-v1-node-exit.json')['actual_exit'] == 1
assert 'Horizontal overflow completed-causal-source-card-v1.png' in (
    RUN / 'formula-render-v1-node.log').read_text(encoding='utf8')
proposal = load(RUN / 'reader-proposal-v1.json')
old_math = proposal['card']['math']
new_math = (r'\begin{aligned}\overline{F}^{\mu}&=\{A:\exists B\in F,\ A=_{\mu\text{-AE}}B\},\\'
    r'P\text{ measurable on }\overline{F}^{\mu}&\Longrightarrow\exists Q\text{ measurable on }F,\\'
    r'&P=Q\quad\mu\text{-AE},\\'
    r'F_t\subseteq\sigma(S,Y_{<t}),\ P_t\in[0,1]\text{ AE}&\Longrightarrow\\'
    r'&P_t=\pi_t(S,Y_{<t})\quad\text{AE for all }t,\\'
    r'R_T^{\mathrm{expected\ fixed}}&=\sum_{t<T}\mathbb E(P_t-\mathbb EY_0)^2\ge0.\end{aligned}')
assert new_math.replace(r'\\&', '') != old_math
proposal['card']['math'] = new_math
write(RUN / 'reader-proposal-v2.json', proposal)
p = ROOT / 'website/content/readings.json'
original = load(p)
write(RUN / 'snapshots/reader-layout-before-v2.raw', p.read_bytes())
row = next(x for x in original['readings'] if x['slug'] == ROUTE)
assert row['source_theorems'][-1] == load(RUN / 'reader-proposal-v1.json')['card']
row['source_theorems'][-1]['math'] = new_math
p.write_bytes((json.dumps(original, ensure_ascii=False, indent=2) + '\n').encode('utf8'))
guard = (RUN / 'common_body_v2.py').read_text(encoding='utf8')
assert guard.count("'reader-proposal-v1.json'") == 1
write(RUN / 'common_reader_v2.py', guard.replace("'reader-proposal-v1.json'", "'reader-proposal-v2.json'"))
write(RUN / 'reader-layout-repair-v2.json', dict(
    actual_failure_receipt='formula-render-v1-node-exit.json',
    actual_failure_log_sha256=sha(RUN / 'formula-render-v1-node.log'),
    failed_site_registry_remain_preserved=True,
    old_source_card_math=old_math, new_source_card_math=new_math,
    scope='Only two additional aligned line breaks in the new source card formula; all assumptions/quantifiers/conclusions and old entries unchanged.',
    first_viewport_v1_png_preserved=True, outer_stderr_not_separately_saved=True,
    public_canary_root_Test_pins_unchanged=True, no_Lean_rerun_claim=True))
for filename in ['build-clean-site-v1.py', 'verify-registry-v1.py', 'capture-reader-v1.py']:
    source = (RUN / filename).read_text(encoding='utf8')
    source = source.replace('from common_body_v2 import *', 'from common_reader_v2 import *')
    source = source.replace('online-completed-causal-site-v1', 'online-completed-causal-site-v2')
    source = source.replace('online-completed-causal-site-build-v1', 'online-completed-causal-site-build-v2')
    source = source.replace('online-completed-causal-playwright-v1', 'online-completed-causal-playwright-v2')
    for prefix in ['site-build', 'site-check', 'registry-check', 'verify-registry',
                   'registry', 'capture-reader', 'formula-render']:
        source = source.replace(prefix + '-v1', prefix + '-v2')
    source = source.replace('reader-proposal-v1.json', 'reader-proposal-v2.json')
    # The previous package's actual v1-named browser baseline remains unchanged.
    source = source.replace("online-ae-causal-20261008/formula-render-v2-browser.json",
                            "online-ae-causal-20261008/formula-render-v1-browser.json")
    write(RUN / filename.replace('-v1.py', '-v2.py'), source)
source = (RUN / 'capture-reader-v1.cjs').read_text(encoding='utf8')
source = source.replace('-v1.', '-v2.').replace('-v1.png', '-v2.png')
write(RUN / 'capture-reader-v2.cjs', source)
from common_reader_v2 import fixed_integrated as fixed_repaired
fixed_repaired()
commit_owned('Wrap new completed-information source formula after actual overflow')
command = [sys.executable, '-B', '-X', 'utf8', str(RUN / 'build-clean-site-v2.py')]
child = subprocess.run(command)
write(RUN / 'clean-local-site-workflow-v2-exit.json', dict(command=command,
    actual_exit=child.returncode, outer_stdout_inherited=True,
    same_applicable_combined_Lean_gate=True, rendering_capture_and_FINAL_pending=True))
assert child.returncode == 0
