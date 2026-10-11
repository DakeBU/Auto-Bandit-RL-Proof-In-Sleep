from common import *
public = ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean'
r = load(RUN/'parent-BODY-review-v1.json')
assert sha(public) == r['production_sha256']
d = load(RUN/'specialization-blind-decoder-v2.json')
assert sha(d['report']) == d['report_sha256'] and not d['unresolved_ambiguities']
assert sha(d['input_path']) == d['input_sha256']
v1 = (CONTRACT/'specialization-neutral-packet-v1.lean.txt').read_bytes()
assert (CONTRACT/'specialization-neutral-packet-v2.lean.txt').read_bytes().startswith(v1)
capture('specialization-retrieval-v1', 'rg', '-n',
    'theorem (regret_bound|canonical_feedback)|def (IsConvexExtended|realEpigraph)|sqrt_mul|sq_sqrt',
    public, ROOT/'BanditRLProof/OnlineConvexExtended.lean', RUN/'SpecializationTypeProbeV1.lean')
files = [PDF, public, ROOT/'BanditRLProof/OnlineConvexExtended.lean',
    ROOT/'BanditRLProof/OnlineSubgradientDescent.lean', ROOT/'BanditRLProof/OnlineSubgradientPolicy.lean',
    ROOT/'runs/online-ch2-adaptive-summation-20261010/source-pdf51-v1.png',
    ROOT/'runs/online-ch2-adaptive-summation-20261010/source-pdf52-v1.png',
    ROOT/'runs/online-ch2-reconciliation-20261010/forward-readonly-retrieval/source-pdf51-text-v1.txt',
    ROOT/'runs/online-ch2-reconciliation-20261010/forward-readonly-retrieval/source-pdf52-text-v1.txt']
files += [Path(row['path']) for row in load(CONTRACT/'specialization-fingerprints-draft-v1.json')['headers'].values()]
files += [CONTRACT/n for n in ['algorithm-definition-context-draft-v2.lean.txt',
    'algorithm-regret_bound-header-draft-v1.lean.txt', 'specialization-fingerprints-draft-v1.json',
    'specialization-source-card-draft-v1.md', 'specialization-conversion-window-draft-v1.md',
    'specialization-neutral-packet-v1.lean.txt', 'specialization-neutral-packet-v2.lean.txt',
    'minimum-infimum-repair-proposed-v1.md']]
files += [RUN/n for n in ['parent-BODY-review-v1.md', 'parent-BODY-review-v1.json',
    'parent-body-attempt-v2.lean.txt', 'parent-public-probe-v1.json', 'parent-value-native-v1.json',
    'SpecializationTypeProbeV1.lean', 'specialization-type-probe-v1.json', 'specialization-retrieval-v1.json',
    'draft-source-specializations-v1.py', 'repair-specialization-neutral-context-v2.py',
    'specialization-neutral-context-repair-v2.json', 'specialization-blind-decoder-v1.md',
    'specialization-blind-decoder-v1.json', 'specialization-blind-decoder-v2.md',
    'specialization-blind-decoder-v2.json', 'director-specializations-draft-v1.md',
    'architect-specializations-draft-v1.md', 'potential-canary-BODY-minimum-review-v1.md',
    'potential-canary-BODY-minimum-review-v1.json']]
assert all(p.is_file() for p in files)
write(RUN/'specialization-CONTRACT-review-inputs-v1.json', dict(files=rows(files),
    scope='Four explicit source-convex and canonical endpoint CONTRACTs only; BODYs absent.'))
write(RUN/'specialization-CONTRACT-review-packet-v1.md', '''# Four source endpoint CONTRACTs, not BODY acceptance

Independently hash all indexed RAW before/after. Personally read original pinned PDF51/52 images or disclose exact prior personal-view reuse; source PDF unchanged. Read complete four frozen headers, actual algorithm context/current parent BODY and favorable distinct parent review, actual declaration retrieval and successful TYPE-only probe, FULL v1 and v2 neutral reconstructions/context repair. V1 had missing IsConvexExtended expansion; v2 preserves every v1 packet byte and appends exact realEpigraph definition, with all actual headers unchanged. Inspect no unresolved ambiguity after v2. Review seven slots individually for source_eq4_4, canonical_eq4_4, source_theorem4_14, canonical_theorem4_14.

Search for mismatch: source convexity retained via actual shared IsConvexExtended; properness/global ambient supports and finite toReal losses; shared closed nonempty convex Domain, initial/comparator membership; current actual-prefix legality versus all-input law; canonical variant fixes existing selector and uses actual canonical_feedback. Same fixed alpha on score/energy/history; alpha1 and sqrt2/2 trajectories must not be compared as if energies independent of stepsize. Inclusive source t1..T maps Lean0..<T and outputT; explicit zero skip, D0/T0/allzero energy extension, no gradient/Lipschitz bound, stochastic premise, exogenous eta or known future. Existing parent retains negative terminal; these printed displays drop only a nonnegative term. Examine alpha=sqrt2/2 eta equality and sqrt2 coefficient/source D sqrt(2S). No printed attained-minimum claim is made by these headers; it remains required separate mathematical repair/Lean benchmark, not excluded or considered proved. Withdrawn missing-/2 allegation stays withdrawn.

Only if all CONTRACTs/dependencies favorable, approve a finite append-only window of EXACT four unchanged headers/BODYs in OnlineAdaptiveOSD.lean before relocated final namespace end, preserving current prefix/import/context/eight definitions/parent BODY. No extra helper/import/context/benchmark/canary/root/reader/registry/global edits or package acceptance. Proof order: source_eq4_4 then canonical_eq4_4, source_theorem4_14 then canonical_theorem4_14, with predecessor focused success before downstream append; two source groups may be source endpoints then canonical adapters if explicitly bounded in receipt. Require actual focused/public/axiom/fence/VALUE checks and distinct BODY review afterward.

Create-only specialization-CONTRACT-review-v1.md/.json UTF8singleLF in RUN. Return per-header seven-slot CONTRACT verdicts, required blocking repairs or precise append window with current RAW/preserved prefix/end/header/context hashes and ordered groups, all actual input RAW checks/index/report/source bindings, truthful staged actor/history/source-view disclosures and remaining gates. No tactic/build/production edit/native acceptance. Requested Astra/medium, no runtime/human/external/absolute-blind claims. Whole Chapter2 partial/null, all8 forward containers open and total Goal ACTIVE.
''')
print(sha(RUN/'specialization-CONTRACT-review-inputs-v1.json'), len(rows(files)), flush=True)
