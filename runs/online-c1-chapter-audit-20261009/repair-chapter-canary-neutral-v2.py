from common_v1 import *
import re
fixed()
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import _strip_lean_comments
write(RUN/'chapter-canary-neutral-context-repair-v1.md','The v1 local context extractor omitted example/#print as declaration boundaries and therefore captured theorem/example bodies after two definitions. Detected by formalizer before any decoder dispatch; v1 neutral inputs/packet/context remain immutable and unused by decoder. Version2 extracts only explicit required definitions with example/hash-command boundaries and excludes unrelated definitions/private helpers. All27 terminal headers and actual Prop typecheck unchanged; no mathematical/source terminal repair.')
groups={
'Tests/OnlineLearningChapterOneCanary.lean':{'demoLoss','demoLeader'},
'Tests/OnlineLearningRegretDomainsCanary.lean':{'sourceV','outputW','domainLoss','output','referenceOne'},
'Tests/OnlineGuessingIIDBenchmarkCanary.lean':{'coinLaw','iidLaw','observation','hindsightMinimum'},
'Tests/OnlineGuessingKernelCausalCanary.lean':{'lowLaw','highLaw','switchSet','decisionKernel','oneHistory','selectedSampler','observationLaw','gameLaw','prediction','target'},
'Tests/OnlineGuessingLogLowerCanary.lean':{'coinMeasure','seededPolicy'},
'BanditRLProof/OnlineGuessingKernelCausal.lean':{'KernelDecisionHistory','KernelDecisionSampler','kernelGeneratedActions','kernelCausalPolicy','kernelGeneratedHistory','kernelGeneratedPrediction','kernelUniformTapeLaw','kernelGameLaw'},
'BanditRLProof/OnlineLearningFTLState.lean':{'ftlMeanStep','ftlState'},
'BanditRLProof/OnlineFTLOscillation.lean':{'dyadicObservation'},
'BanditRLProof/OnlineNoRegretSemantics.lean':{'LimitNoRegret'},
'BanditRLProof/OnlineGuessingIIDBenchmark.lean':{'expectedFixedMinimum','expectedFixedRegret'},
'BanditRLProof/OnlineGuessingLogLower.lean':{'binaryStream','binaryValues','causalPredict','pathRegret'},
'BanditRLProof/Exp3ConditionalMoments.lean':{'finiteActionMeasure'},
}
context=(CONTRACT/'general-initialization-neutral-context-v2.lean.txt').read_text('utf8')+'\n\nAmbient: open Filter Asymptotics MeasureTheory ProbabilityTheory BanditRL.OnlineLearning unitInterval; open scoped ENNReal. Namespace annotations below identify actual imported definitions. Only necessary mathematical definition bodies and a supporting existential type are supplied, never theorem proof bodies.\n\nabbrev unitInterval : Set ℝ := Set.Icc 0 1\nscoped[unitInterval] notation "I" => unitInterval\n\n'
pattern=re.compile(r'(?m)^(?:@\[[^\n]*\]\s*)*(?:(?:noncomputable|private|partial)\s+)*(?:def|abbrev|theorem|lemma|instance|example|namespace|end|open)\b|^#(?:check|print|eval)\b')
extracted=[]
for rel,wanted in groups.items():
    source=_strip_lean_comments((ROOT/rel).read_text('utf8'))
    matches=list(pattern.finditer(source));stack=[];found=set()
    for i,m in enumerate(matches):
        part=source[m.start():matches[i+1].start() if i+1<len(matches) else len(source)].strip()
        first=part.splitlines()[0]
        if first.startswith('namespace '):stack.append(first.split()[1]);continue
        if first.startswith('end'):
            if stack:stack.pop()
            continue
        decl=re.match(r'(?:(?:noncomputable|private|partial)\s+)*(?:def|abbrev)\s+(\w+)\b',first)
        if not decl or decl.group(1) not in wanted:continue
        name=decl.group(1);found.add(name);ns='.'.join(stack)
        assert not re.search(r'(?m)^\s*(?:example|theorem|lemma|#print|#check)\b',part)
        context+='\nActual scoped definition '+ns+'.'+name+'\n'+('namespace '+ns+'\n' if ns else '')+part+'\n'+('end '+ns+'\n' if ns else '')
        extracted.append(dict(name=ns+'.'+name,path=(ROOT/rel).as_posix(),file_sha256=sha(ROOT/rel)))
    assert found==wanted,(rel,wanted-found)
context+='\nExact rational sequence: def harmonic : ℕ → ℚ := fun n => ∑ i ∈ Finset.range n, (↑(i + 1))⁻¹\n'
context+='\nSupporting existential HEADER ONLY in BanditRL.OnlineLearning; selectedSampler uses its chosen f. The imported concrete decisionKernel has an IsMarkovKernel instance at every time and switchSet_measurable supplies its measurable predicate. No proof is supplied.\n'+next(t['header'] for t in load(CONTRACT/'targets-v1.json')['targets'] if t['name'].endswith('.causal_kernel_realization_and_expectedFixed_excess'))+'\n'
assert 'example :' not in context and '#print' not in context
write(CONTRACT/'chapter-canary-neutral-context-v2.lean.txt',context)
write(RUN/'chapter-canary-neutral-definition-audit-v2.json',dict(extracted_actual_definitions=extracted,old_six_context_preserved=True,harmonic_definition_matches_actual_source=True,unitInterval_actual_notation_explicit=True,no_example_or_theorem_proof_bodies=True,old_neutral_v1_not_dispatched=True,all27_header_hashes_unchanged=True))
packet=RUN/'chapter-canary-neutral-packet-v2.md'
write(packet,'Decode only27 neutral proposed theorem headers in chapter-canary-neutral-targets-v1.lean.txt plus exact repaired supporting definition context-v2. No source identity/intent/review/proof/compilation result supplied. Earlier local v1 context was not dispatched; do not read it. Reconstruct eachC001-C027 in prose/LaTeX and seven semantic slots, full quantifiers/constants/T0/metric/expected-fixed-vs-hindsight/current-vs-past/causal-sampler law/signed-regret/limits and excluded scope. Pure definition proof terms are only definitions, not theorem bodies. Supporting existential HEADER clarifies selectedSampler type; no proof truth is assumed from that header. Types are proposals only. Reused staged decoder history disclosed, requestedAstra/medium/no absolute blindness/human/external/runtimeattestation. Output ONLY chapter-canary-blind-reconstruction-v2.md and chapter-canary-blind-receipt-v2.json in this RUN; bind exact two indexedfiles/index/packetRAWbeforeafter, missingcontext/ambiguity lists/all27reconstructioncompleteness. Do not read other source/intent/review/body/logs/editinputs.')
write(RUN/'chapter-canary-neutral-inputs-v2.json',dict(rows=rows([CONTRACT/'chapter-canary-neutral-targets-v1.lean.txt',CONTRACT/'chapter-canary-neutral-context-v2.lean.txt']),exact_targets=27,source_identity_provided=False,theorem_proofs_provided=False,source_review_provided=False))
fixed()
print('27 headers unchanged; context-v2',len(extracted),'exact necessary definitions plus six core/notation/harmonic/supporting type; source-blind packet ready.',flush=True)
