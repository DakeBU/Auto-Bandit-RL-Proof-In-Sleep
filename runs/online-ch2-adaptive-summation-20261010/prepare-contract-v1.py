from common import *
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle
fixed()
write(RUN/'bootstrap-command-v1.json',(ROOT/'tmp/online-ch2-adaptive-start-v1/bootstrap-command-v1.json').read_bytes())
capture('reference-index-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','reference-index')
refs=sorted((RUN/'reference-index').glob('*.json'));assert len(refs)==8
attrs=RUN/'.gitattributes';before=attrs.read_bytes()
extra=''.join('reference-index/'+p.name+' whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol\n' for p in refs)
assert all(b'\r\n' in p.read_bytes() for p in refs)
attrs.write_bytes(before+extra.encode('utf8'))
write(RUN/'draft-reference-attributes-v1.json',dict(before_sha256=hashlib.sha256(before).hexdigest(),before_raw_base64=base64.b64encode(before).decode('ascii'),exact_append=extra,after_sha256=sha(attrs),actual_native_files=rows(refs),scope='Draft-only exact eight native JSON CRLF filenames; RAW bytes retained, ordinary default whitespace checks preserved; no wildcard CRLF or code/binary exemption.'))
commands=[('list-mathlib',['list-mathlib']),('list-papers',['list-papers']),('list-weapons',['list-weapons']),('memory-integral',['search-memory','sum_integral']),('memory-cumulative',['search-memory','weighted_potential']),('memory-sqrt',['search-memory','two_mul_sqrt']),('decl-integral',['list-lean-decls','integral','--statement']),('decl-weighted',['list-lean-decls','weighted_potential_sum','--statement']),('decl-sqrt',['list-lean-decls','two_mul_sqrt_sub_sqrt_le_sub_div_sqrt','--statement']),('decl-current-name',['list-lean-decls','OnlineAdaptiveSummation','--statement'])]
for label,args in commands:capture(label+'-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py',*args)
capture('pinned-integral-API-v1','rg','-n','integral_mono_on|sum_integral_adjacent_intervals|ContinuousOn.intervalIntegrable_of_Icc',ROOT/'.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean')
capture('pinned-unit-interval-comparison-v1','rg','-n','sum_Ico_le_integral_of_le|sum_mul_Ico_le_integral_of_monotone_antitone',ROOT/'.lake/packages/mathlib/Mathlib/Analysis/SumIntegralComparisons.lean')
context='''import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section
open Set Finset MeasureTheory

namespace BanditRL.OnlineAdaptiveSummation

end BanditRL.OnlineAdaptiveSummation
'''
header='''theorem lemma_4_13 (a₀ : ℝ) (a : ℕ → ℝ) (f : ℝ → ℝ) (T : ℕ)
    (h₀ : 0 ≤ a₀) (ha : ∀ t < T, 0 ≤ a t)
    (hcont : ContinuousOn f (Ici 0)) (hmono : AntitoneOn f (Ici 0))
    (hf : ∀ x ∈ Ici 0, 0 ≤ f x) :
    (∑ t ∈ range T, a t * f (a₀ + ∑ i ∈ range (t + 1), a i)) ≤
      ∫ x in a₀..(a₀ + ∑ i ∈ range T, a i), f x'''
prop='''∀ (a₀ : ℝ) (a : ℕ → ℝ) (f : ℝ → ℝ) (T : ℕ),
    0 ≤ a₀ → (∀ t < T, 0 ≤ a t) →
    ContinuousOn f (Ici 0) → AntitoneOn f (Ici 0) →
    (∀ x ∈ Ici 0, 0 ≤ f x) →
    (∑ t ∈ range T, a t * f (a₀ + ∑ i ∈ range (t + 1), a i)) ≤
      ∫ x in a₀..(a₀ + ∑ i ∈ range T, a i), f x'''
write(CONTRACT/'definition-context-v1.lean.txt',context)
write(CONTRACT/'frozen-headers-draft-v1.json',dict(rows=[dict(declaration='BanditRL.OnlineAdaptiveSummation.lemma_4_13',exact_header=header,normalized_header_sha256=lifecycle.statement_hash(header),exact_Prop=prop,BODY='unwritten',terminal_closed=False)],source_family_count=1,algorithm_guarantee_closed=False,chapter_complete=False))
probe=context.replace('end BanditRL.OnlineAdaptiveSummation\n','#check ('+prop+')\n#check ContinuousOn.intervalIntegrable_of_Icc\n#check intervalIntegral.integral_mono_on\n#check intervalIntegral.sum_integral_adjacent_intervals\n#check intervalIntegral.integral_const\nend BanditRL.OnlineAdaptiveSummation\n')
write(RUN/'SummationTypeProbeV1.lean',probe)
capture('summation-type-probe-v1','lake','env','lean',RUN/'SummationTypeProbeV1.lean')
neutral=prop.replace('a₀','b').replace('(a :','(d :').replace('a t','d t').replace('a i','d i').replace('(f :','(q :').replace(' f ',' q ').replace('f (','q (').replace('f x','q x').replace('(T :','(N :').replace('range T','range N').replace('< T','< N')
assert all(s not in neutral for s in ['lemma_4_13','Orabona','Chapter','a₀'])
neutral_context=context.replace('BanditRL.OnlineAdaptiveSummation','NeutralIntegralBoundPacketV1')
neutral_packet=neutral_context.replace('end NeutralIntegralBoundPacketV1\n','#check ('+neutral+')\nend NeutralIntegralBoundPacketV1\n')
write(RUN/'NeutralIntegralBoundPacketV1.lean',neutral_packet)
capture('neutral-integral-type-probe-v1','lake','env','lean',RUN/'NeutralIntegralBoundPacketV1.lean')
write(CONTRACT/'semantic-signature-draft-v1.json',dict(source='ORABONA-V10-L4.13',source_sha256=PDF_SHA,source_page=52,printed_page=40,target='BanditRL.OnlineAdaptiveSummation.lemma_4_13',statement_hash=lifecycle.statement_hash(header),context_sha256=sha(CONTRACT/'definition-context-v1.lean.txt'),slots=dict(objects='Nonnegative real initial offset, finite prefix of nonnegative real increments and real extension of a continuous nonincreasing nonnegative function on Ici0.',quantifiers='For every offset, increment stream, function and natural finite horizon; assumptions only on prefix/half-line; no uniform-in-horizon hypothesis.',assumptions='Offset nonnegative; played increments nonnegative; continuous, antitone and nonnegative on Ici0. No strictly positive increment, offset or horizon; no global continuity/monotonicity.',conclusion='Endpoint-weighted finite sum bounded by oriented real interval integral from initial offset to offset+total increments.',constants_indices='Lean t=0..T-1 corresponds to source increment1..T; endpoint includes current increment; source a0 separate; exact factor1.',information='Deterministic numerical inequality; no learner/oracle/probability/filtration or regret bound.',boundary='Includes zero horizon/zero increments/offset0. Does not apply inverse sqrt directly at0 without the source limit argument or another reviewed proof; does not close adaptive OSD or displayed minimum equality.'),deltas=[dict(kind='generalization',detail='Real ambient extension only restricted to source half-line; no behavior outside Ici0 is assumed or used.'),dict(kind='same',detail='Natural increment stream is observed only on finite prefix, equivalent to source finite list; a0 kept separate.')],state='draft',BODY_closed=False,chapter_complete=False,whole_Goal='active'))
write(CONTRACT/'contract-v1.md','''# Integral comparison contract v1

Source card ORABONA-V10-L4.13: Orabona arXiv:1912.13213v10, 2026-06-21, printed40/PDF52. The frozen theorem compares the sum of each nonnegative increment times f at its cumulative right endpoint with the integral over the full cumulative interval. Source a0 is the initial offset; Lean increment a t is source a_(t+1). T=0 and all zero cases remain included. f is continuous, nonincreasing and nonnegative on [0,infinity); its arbitrary real extension is unconstrained elsewhere.

The exact one public terminal and full import/scoped context are frozen in the neighboring JSON/text files. Native type probes elaborate the complete Prop and actual imported API signatures; they do not prove a theorem. Neutral packet bijectively renames the mathematical parameters and removes source identity; only its Lean type/context is supplied to the distinct decoder. Formalizer, decoder and anti-anchored source reviewer are distinct actors with reused-role history disclosed, requested Astra/medium, no human/external/runtime attestation.

After favorable source CONTRACT review, only NEW BanditRLProof/OnlineAdaptiveSummation.lean may be written, preserving the exact context and public header. Necessary private helpers may implement cumulative interval facts without new assumptions or terminal weakening. First finite leaf is lemma_4_13 using interval integrability, endpoint monotonicity, finite summation and adjacent integral telescoping. Root/Test/reader/registry/coverage/old source edits require separate future integration review.

This general inequality is a mathlib-candidate and a required reusable prerequisite toward the Chapter2 adaptive-rate forward claim. Actual causal adaptive OSD, zero-gradient skip, zero-radius/zero-energy cases, (4.4), Theorem4.14 and the displayed min/infimum distinction remain separate open obligations. Chapter4 full inventory is still unenumerated/null and is not the new main chapter. No source container, Chapter2, Chapter4 or whole-Goal closure is claimed by a foundation proof.

Candidate gates: actual public theorem BODY, meaningful nonconstant-function/zero-increment canary, frozen statement/context checks, compiler/axioms and BODY semantic review; combined root/Tests/full harness, shared registry/reader/site/visual checks; FINAL/native/postnative/commit/push/draft PR. Current state draft; BODY unwritten. One lower route, existing old baseline immutable, global SGB untouched.
''')
write(CONTRACT/'DAG-draft-v1.json',dict(nodes=[dict(id='pinned-source',status='inspected'),dict(id='imported-integral-APIs',status='type-elaborated',dependencies=[]),dict(id='lemma_4_13',status='BODY-unwritten',dependencies=['imported-integral-APIs'],ready_after='favorable-source-CONTRACT-review'),dict(id='inverse-sqrt-energy-sum',status='planned-unfrozen',dependencies=['existing-Tsallis-square-root-supporting-line-API or reviewed-limit-route']),dict(id='actual-causal-adaptive-OSD',status='required-open-unfrozen',dependencies=['Chapter2-source-subgradients/projection','zero-gradient-branch','weighted-potential-zero-energy-treatment','inverse-sqrt-energy-sum']),dict(id='Chapter2-adaptive-forward-mathematics',status='required-open',dependencies=['actual-causal-adaptive-OSD','precise-source-regret-bound','separate-zero-energy-minimum-correction-review'])],first_leaf='lemma_4_13',current_public_proof_terminal_count=1,whole_chapter_denominator=None,chapter_complete=False,whole_Goal='active'))
write(CONTRACT/'source-card-v1.md','# ORABONA-V10-L4.13\n\nPinned arXiv:1912.13213v10 (2026-06-21), printed40/PDF52. Continuous nonincreasing nonnegative f on the nonnegative half-line; nonnegative initial offset and finite increments. Each increment weights f at the cumulative right endpoint; their sum is bounded by the integral from the initial offset to the final cumulative endpoint. Source proof compares each constant endpoint integral on one increment interval and telescopes. This is a deterministic integration lemma, not a regret guarantee. Exact source PDF SHA and original page pixels/text bindings are in source-fingerprint-v1.json.\n')
write(RUN/'retrieval-packet-v1.json',dict(status='mathlib-candidate',source_card='ORABONA-V10-L4.13',Mathlib_cards=['MLIB-FINSET-SUMS','MLIB-MEASURE-INTEGRAL','MLIB-ORDER-ALGEBRA'],paper_card='source-qualified OWN ORABONA-V10-L4.13; no false pre-existing Orabona global card',weapon='none; source interval comparison directly determines route',actual_command_receipts=rows(RUN/(n+'-v1.json') for n,_ in commands),reference_index=rows(refs),read_card_files=rows(ROOT/p for p in ['research-wiki/mathlib/theorem-cards.md','research-wiki/mathlib-candidates/README.md','research-wiki/papers/bandit-frontier-cards.md','research-wiki/proof-weapons/bandit-proof-weapons.md']),exact_imports=['Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic','Mathlib.Tactic'],API_files=rows([ROOT/'.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean',ROOT/'.lake/packages/mathlib/Mathlib/Analysis/SumIntegralComparisons.lean']),reuse='adapt_existing; finite sum and arbitrary cumulative endpoints require a thin composition of actual imported integral APIs. Existing unit-interval/natural-grid comparisons do not state this arbitrary-increment theorem.',upstream_submission='not performed',graph=dict(Lean='planned one shared source-qualified public theorem; actual dependencies determined after BODY',Overview='Chapter2 required forward prerequisite only; no chapter badge',Functor='none-found-with-reason: deterministic interval comparison alone is not a cross-setting formal functor; future Tsallis supporting-line reuse remains a candidate API, not an edge here.')))
fixed()
print('Exact draft Prop/context/source/retrieval and neutral packet prepared; distinct reconstruction/CONTRACT review pending.',flush=True)
