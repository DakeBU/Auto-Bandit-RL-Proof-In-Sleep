"""Extract the reviewed cumulative scratch chain; default is read-only verification."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
RUN = Path(__file__).resolve().parent
LAYERS = [
    ('Exploration', 'Exploration'), ('Reward', 'Reward'),
    ('Collision', 'Collision'), ('Population', 'Population'),
    ('Ranking', 'Ranking'), ('Handoff', 'Handoff'),
    ('Marginal', 'Marginal'), ('Comparator', 'LearnerRegret'),
    ('Realized', 'Realized'), ('NoisyLearner', None),
]
PATTERN = re.compile(r'^namespace ([\w.]*Canary)\n(.*?)^end \1\s*$', re.M | re.S)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    previous = ''
    parent = 'BanditRLProof.Algorithms.MusicalChairsCoordinationRegret'
    imports = []
    tests = []
    outputs = {}
    layers = []
    for label, target in LAYERS:
        src = RUN / ('MusicalChairs' + label + 'Prototype.lean')
        raw = src.read_text(encoding='utf-8')
        for line in raw.splitlines():
            if line.startswith('import ') and line not in imports:
                imports.append(line)
        body = '\n'.join(line for line in raw.split('\n')
                         if not line.startswith('import ')).lstrip()
        assert body.startswith(previous), 'Changed earlier layer: ' + label
        delta = body[len(previous):]
        previous = body
        local_tests = []

        def move_test(match):
            name, text = match.groups()
            full = name if '.' in name else 'BanditRLProof.MusicalChairs.' + name
            local_tests.append('namespace ' + full + '\n' + text + 'end ' + full + '\n')
            return ''

        production = PATTERN.sub(move_test, delta)
        tests.extend(local_tests)
        if target:
            name = 'MusicalChairs' + target
            path = 'BanditRLProof/Algorithms/' + name + '.lean'
            header = '\n'.join(dict.fromkeys(imports + ['import ' + parent]))
            header += '\n\nopen scoped Classical ENNReal\nset_option autoImplicit false\n\n'
            outputs[path] = header + production.lstrip()
            parent = 'BanditRLProof.Algorithms.' + name
        else:
            assert not production.strip(), 'Unowned non-canary declarations'
        layers.append({'source': str(src.relative_to(ROOT)).replace('\\', '/'),
                       'source_sha256': digest(src.read_bytes()),
                       'delta_sha256': digest(delta.encode('utf-8')),
                       'test_blocks': len(local_tests),
                       'production_module': parent if target else None})

    # Every fixture retains its declaration namespace and proof text. The import
    # intentionally goes through the combined public root.
    outputs['Tests/MusicalChairsLearnerCanary.lean'] = (
        'import BanditRLProof\n\nopen scoped Classical ENNReal\n'
        'open MeasureTheory ProbabilityTheory\nset_option autoImplicit false\n\n'
        + '\n'.join(tests))
    for path, text in outputs.items():
        dest = ROOT / path
        if args.write:
            dest.write_text(text, encoding='utf-8')
        else:
            assert dest.read_text(encoding='utf-8') == text, 'Extraction differs: ' + path
    receipt = {'schema_version': 1, 'kind': 'deterministic-reviewed-scratch-extraction',
               'source_layers': layers, 'test_blocks': len(tests),
               'generated_files': {path: digest((ROOT / path).read_bytes()) for path in outputs},
               'boundary': 'Extraction equivalence only; compilation, independent promotion review and publication gates are separate.'}
    out = RUN / 'multi-agent-extraction.json'
    if args.write:
        out.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    else:
        assert json.loads(out.read_text(encoding='utf-8')) == receipt
    print('Verified %d production modules and %d canary blocks in one public-root test module'
          % (len(outputs) - 1, len(tests)))


if __name__ == '__main__':
    main()
