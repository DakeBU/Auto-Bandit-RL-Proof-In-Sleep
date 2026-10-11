from pathlib import Path
import hashlib
import json
import re
from pypdf import PdfReader

ROOT = Path(__file__).resolve().parents[2]
RUN = Path(__file__).resolve().parent
PDF = ROOT.parent / 'research-online-ogd/tmp/pdfs/orabona-v10.pdf'
SOURCE_SHA = 'cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
assert hashlib.sha256(PDF.read_bytes()).hexdigest() == SOURCE_SHA
prior = RUN / 'full-book-numbered-discovery-20261011-v1.json'
assert prior.is_file()

# PDF extraction often joins the result number to its first word, e.g.
# "Theorem 11.3In". A word-boundary after the number loses those results.
# Keep the line-start condition to reduce ordinary in-text cross-references.
pattern = re.compile(
    r'^\s*(Theorem|Lemma|Proposition|Corollary|Definition|Algorithm|Example|Remark)'
    r'\s*(\d+)\.(\d+)(?!\d|\.\d)([^\n]{0,130})', re.M)
reader = PdfReader(str(PDF))
rows = []
for page_number, page in enumerate(reader.pages, 1):
    text = page.extract_text() or ''
    for match in pattern.finditer(text):
        chapter = int(match.group(2))
        if 1 <= chapter <= 16:
            rows.append(dict(kind=match.group(1), anchor=match.group(2)+'.'+match.group(3),
                chapter=chapter, pdf_page=page_number,
                line_excerpt=match.group(0).strip(),
                classification='unreviewed-extraction-hit'))
counts = {str(ch): dict(numbered_extraction_hits=sum(r['chapter'] == ch for r in rows),
    required_maintext_total=None, scope_frozen=False,
    unreviewed_unnumbered_performance_guarantees=True) for ch in range(1, 17)}
data = dict(source_path=PDF.as_posix(), source_sha256=SOURCE_SHA,
    pages=len(reader.pages), status='discovery-only', rows=rows, chapters=counts,
    method='Pinned PDF pypdf line-start numbered-anchor extraction; digit boundary accepts number-to-word joins.',
    previous_discovery=dict(path=prior.as_posix(), sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
        limitation='Word boundary after result number missed joins such as Theorem11.3In; v1 retained.'),
    mandatory_boundary='Not exhaustive or reviewed. Does not replace chapter inventories, freeze targets, infer mandatory counts, or exclude any result. Maintext results with proof left as exercise and unnumbered principal bounds remain required. Appendix dependencies and history/exercises need independent classification.',
    chapter_progress='No mathematical, semantic or chapter-gate promotion. Chapter2 partial; Chapters3-16 pending exact source audit.',
    goal='active')
out = RUN / 'full-book-numbered-discovery-20261011-v2.json'
with out.open('x', encoding='utf8', newline='\n') as stream:
    stream.write(json.dumps(data, ensure_ascii=False, indent=2)+'\n')
print('Unreviewed numbered anchor hits:', len(rows))
print({ch: d['numbered_extraction_hits'] for ch, d in counts.items()})
