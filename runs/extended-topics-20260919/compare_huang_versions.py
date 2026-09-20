"""Reproduce source-byte and page-text comparisons; does not certify mathematics.

Usage: python compare_huang_versions.py --sources DIR --output FILE
Requires pdftotext on PATH, or --pdftotext ABSOLUTE_PATH.
PDF inputs are private source artifacts, not bundled in this repository.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import zipfile


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sources', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--pdftotext', default='pdftotext')
    args = parser.parse_args()
    expected = {
        'huang23-official-http-supp.zip': '4fa7ed0857cc07339ea8884a5bdc64d8039bc68513f043648bc45cb72dee087c',
        'huang23-official-supp-full.pdf': 'af3f298ba5489c2931c00f41b42b76bb16b389d2217787d5c25d3060180784ef',
        'huang23-v3.pdf': '84ea805fae998deeea63273932b207ac5edd0c10616c2f1ba1f260aec4ff527f',
    }
    for name, digest in expected.items():
        if sha((args.sources / name).read_bytes()) != digest:
            raise ValueError('Pinned source hash mismatch: ' + name)
    with zipfile.ZipFile(args.sources / 'huang23-official-http-supp.zip') as archive:
        if archive.testzip() is not None:
            raise ValueError('ZIP CRC failure')
        if archive.read('full.pdf') != (args.sources / 'huang23-official-supp-full.pdf').read_bytes():
            raise ValueError('Extracted PDF differs from archive member')
    pages = []
    with tempfile.TemporaryDirectory(prefix='huang-versions-') as tmp:
        for index, name in enumerate(['huang23-official-supp-full.pdf', 'huang23-v3.pdf']):
            target = Path(tmp) / ('source-%s.txt' % index)
            subprocess.run([args.pdftotext, '-layout', str(args.sources / name), str(target)], check=True)
            extracted = target.read_text(encoding='utf-8').split('\f')
            if extracted and not extracted[-1].strip():
                extracted.pop()
            pages.append(extracted)
    if [len(p) for p in pages] != [54, 54]:
        raise ValueError('Unexpected page counts')
    equal = [i + 1 for i, (a, b) in enumerate(zip(*pages)) if a == b]
    different = [i for i in range(1, 55) if i not in equal]
    result = {
        'source_sha256': expected,
        'archive_member_verified': 'full.pdf',
        'page_counts': [54, 54],
        'comparison': 'exact UTF-8 page text from the same pdftotext -layout invocation; no normalization',
        'exact_text_equal_pages': equal,
        'different_pages': different,
        'appendix_pages_14_through_54_text_equal': all(i in equal for i in range(14, 55)),
        'boundary': 'Text equality is version-comparison evidence, not proof correctness or PDF-byte identity.',
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print('Compared 54 pages; differing pages:', different)


if __name__ == '__main__':
    main()
