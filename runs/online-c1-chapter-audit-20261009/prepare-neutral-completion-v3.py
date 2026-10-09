from common_v1 import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import _strip_lean_comments,statement_hash,normalize_statement
import re
fixed()
targets=load(CONTRACT/'targets-v1.json')['targets']; neutral=[]; checks=[]
for t in targets:
    p=Path(t['path']); assert sha(p)==t['file_sha256']
    text=_strip_lean_comments(p.read_text(encoding='utf8'))
    short=t['name'].rsplit('.',1)[-1]
    m=re.search(r'(?m)^\s*(?:theorem|lemma)\s+'+re.escape(short)+r'\b',text)
    assert m,t['name']
    rest=text[m.start():]; body=re.search(r':=\s*by\b',rest)
    assert body,t['name']
    header=rest[:body.start()].strip()
    assert statement_hash(header)==t['statement_hash'],t['name']
    assert normalize_statement(header)==t['header']
    item=re.sub(r'^(theorem|lemma)\s+'+re.escape(short)+r'\b',r'\1 '+t['id'],header)
    assert item!=header
    neutral.append(item)
    checks.append(dict(id=t['id'],public_statement_hash=t['statement_hash'],raw_multiline_normalizes_to_frozen_public_header=True))
write(CONTRACT/'neutral-targets-v2.lean.txt','\n\n'.join(neutral))
addendum='''Exact additional context definitions only, with scoped ambient notation already supplied in context-v1.lean.txt. No proof body or source identity is supplied.

Actual scoped name BanditRL.OnlineLearning.kernelUniformTapeLaw
noncomputable abbrev kernelUniformTapeLaw : Measure (ℕ → I) :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure I))

Actual scoped name BanditRL.OnlineLearning.kernelGameLaw
noncomputable abbrev kernelGameLaw (ν : ProbabilityMeasure (ℕ → ℝ)) : Measure ((ℕ → I) × (ℕ → ℝ)) :=
  kernelUniformTapeLaw.prod (ν : Measure (ℕ → ℝ))

Actual scoped global name harmonic
def harmonic : ℕ → ℚ := fun n => ∑ i ∈ Finset.range n, (↑(i + 1))⁻¹
'''
for snippet,path in [
 ('noncomputable abbrev kernelUniformTapeLaw : Measure (ℕ → I) :=\n  Measure.infinitePi (fun _ : ℕ => (volume : Measure I))',ROOT/'BanditRLProof/OnlineGuessingKernelCausal.lean'),
 ('noncomputable abbrev kernelGameLaw (ν : ProbabilityMeasure (ℕ → ℝ)) : Measure ((ℕ → I) × (ℕ → ℝ)) :=\n  kernelUniformTapeLaw.prod (ν : Measure (ℕ → ℝ))',ROOT/'BanditRLProof/OnlineGuessingKernelCausal.lean'),
 ('def harmonic : ℕ → ℚ := fun n => ∑ i ∈ Finset.range n, (↑(i + 1))⁻¹',ROOT/'.lake/packages/mathlib/Mathlib/NumberTheory/Harmonic/Defs.lean')]:
    assert normalize_statement(snippet) in normalize_statement(path.read_text(encoding='utf8'))
write(CONTRACT/'context-addendum-v2.lean.txt',addendum)
write(RUN/'neutral-layout-checks-v2.json',dict(target_count=50,all_public_statement_hashes_unchanged=True,checks=checks))
write(RUN/'blind-inputs-v2.json',dict(rows=rows([CONTRACT/'neutral-targets-v2.lean.txt',CONTRACT/'context-v1.lean.txt',CONTRACT/'context-addendum-v2.lean.txt']),target_count=50,source_identity_or_prior_verdict_included=False,previous_decoder_outputs=rows([RUN/'blind-reconstruction-v1.md',RUN/'blind-receipt-v1.json'])))
write(RUN/'neutral-review-packet-v2.md','''Versioned context/layout completion, preserving the v1 inputs/report/receipt. Read ONLY this packet, blind-inputs-v2.json, its three indexed inputs and your own prior v1 outputs. All fifty actual public signatures are unchanged; neutral v2 preserves actual multiline whitespace. Complete A003 exact tape/product measure interpretation, A046 actual result-level let scope, and A050 rational harmonic indexing/coercion from exact added definitions. Reassess all fifty entries for any dependent ambiguity; all seven semantic slots remain required. You may reference the unchanged full v1 entries and write explicit replacement entries/complete reconciliation in v2. No source identity/intention/map/fingerprint/verdict/proof bodies are supplied or permitted. Output ONLY blind-reconstruction-v2.md and blind-receipt-v2.json, binding all three raw input hashes plus packet/index and v1 report/receipt, before/after unchanged checks, fifty-target completeness and explicit any remaining gaps. Disclose reused history/requested Astra medium/no runtime/absolute-blind/human/external attestation. This is mathematical reconstruction, never a source/proof/chapter acceptance verdict.''')
fixed()
print('v2 exact multiline headers: 50 unchanged public normalized hashes; three definitions added; prior v1 preserved.',flush=True)
