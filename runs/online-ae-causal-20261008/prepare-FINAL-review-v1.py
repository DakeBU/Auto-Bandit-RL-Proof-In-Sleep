from common_reader_v4 import *
fixed_integrated()
g=load(RUN/'combined-gates-v1.json')
assert g['actual_exit_codes']==[0,0,0] and g['public_sha256']==sha(PUBLIC) and g['canary_sha256']==sha(CANARY)
pixels=load(RUN/'pixel-review-v5.json');reg=load(RUN/'registry-v4.json')
assert pixels['actual_original_images_viewed']==8 and all(sha(x['path'])==x['sha256'] for x in pixels['images'])
for label in ['site-build-v4','site-check-v4','registry-check-v4','contributor-current-stacked-v4','contributor-current-origin-main-v4','candidate-frontier-shadow-v2']:
    assert load(RUN/(label+'-exit.json'))['actual_exit']==0
write(RUN/'prospective-PR-title-v1.txt','Online Learning C1: AE causal versions and original IID excess')
write(RUN/'prospective-PR-body-v1.md',
    'Given a prediction process with a strict-past measurable version almost everywhere, this package proves one globally unit-valued history-policy family agrees with the original process on one event for all natural times. It derives current-target independence from joint target independence and a private seed independent of the entire stream, then proves the exact original-process IID expected-fixed excess identity and nonnegativity for every natural horizon, including zero.\n\n'
    'These are three derived formalization targets for Orabona v10 printed1/PDF13 and printed3/PDF15, not three printed theorems or an executable unknown-law algorithm constructor. The AE-only canary is not pointwise predictable or everywhere unit, yet has the same causal version; its independently random seed/positive-variance IID targets give two-round original-process excess1/2.\n\n'
    'Validation: actual focused builds, complete public-type proof VALUE witnesses, 42 named standard-axiom records, 39 selected compiled nodes/2136 coalesced TYPE_VALUE edges/12 required direct VALUE pairs, frozen statement fences, combined root/Tests and full harness (472 tests,7 skips), both contributor bases, own shadow, and an applicable clean local site. All10935 old registry IDs/URLs/statement hashes are preserved; three new declarations use the same Online Learning Book graph. Eight original current reader/catalogue images undergo separate formalizer and source-reviewer inspection. Actual proof, canary and publication-helper failures are retained with scoped repairs. Distinct staged automated roles have disclosed reused history; no human/external/absolute-blind or runtime model attestation. FINAL/native acceptance and delivery evidence are separately recorded.\n\n'
    'Only these three bounded obligations may close. Original16 Chapter1 source objects/null unknown proof total, general completed-information augmentation, full causal stochastic-kernel representation, remaining Chapter1/2, unenumerated Chapters3–16 and required appendices remain required; whole Goal active. Stacked on OPEN draft unmerged PR197 exact4ca57025a2cdc4f4ba0d5cc2423b55786b0a7afe, base codex/research-online-c1-core-audit. Main/live remain unchanged; no merge/deployment. Evidence: docs/contracts/online-ae-causal-v1 and runs/online-ae-causal-20261008. Active worktree retained for the next required bridge.\n')
scope=dict(manifest_fields=['semantic_roundtrip.remaining_semantic_delta','graph_contribution.visual_review',
    'verification.independent_review','verification.bandit_check','verification.site_build','verification.site_check'],
    own_metadata_only='Append exact own-task four status suffixes and task/session journal rows; actual reviewer trial/lifecycle/memory/retrieval commands, own versioned accepted ledger/decision/digest/obligations and scoped delivery evidence. No global SGB replacement.',
    conditions=['Freeze all actual public/canary/root/Test/readers/pins and every reviewed receipt/input.',
        'Bind exact prechange RAW metadata snapshots and every native suffix/ownership; startswith alone does not certify scope. Separate post-native review required.',
        'Close only three derived AE causal obligations3->0; no original source-object or chapter/wholeGoal completion.',
        'Keep capture-time candidate reader boundaries immutable; record later scoped acceptance separately.',
        'Use only the exact prospectively reviewed PR title/body after favorable FINAL and native gates, with actual scoped commit/push/draft/app attachment evidence; no predicted PR/head or merge/deploy/live.'])
write(RUN/'FINAL-future-metadata-scope-v1.json',scope)
paths=[MANIFEST,ROOT/'MANIFEST.md',ROOT/'runs/trials.jsonl',ROOT/'runs/lifecycle_sessions.jsonl',ROOT/'runs/lifecycle_memory.jsonl']
paths += [ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','proof-blueprints','conversion-windows']]
snapshots=[]
for i,p in enumerate(paths):
    q=RUN/'snapshots'/('FINAL-metadata-'+str(i)+'-v1.raw');write(q,p.read_bytes())
    snapshots.append(dict(live_path=p.as_posix(),snapshot=q.as_posix(),sha256=sha(q)))
write(RUN/'FINAL-metadata-snapshots-v1.json',snapshots)
rows={}
def add(p):
    p=Path(p).resolve();assert p.is_file();rows[p.as_posix()]=dict(path=p.as_posix(),sha256=sha(p))
for row in load(RUN/'body-review-inputs-v1.json')['rows']:add(row['path'])
for folder in [RUN,CONTRACT]:
    for p in folder.rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts:add(p)
for p in paths+[PUBLIC,CANARY,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',PDF]+READERS:add(p)
site=ROOT/'tmp/online-ae-causal-site-v4'
for rel in ['books/registry.json','site-manifest.json','chapters/online-foundations/index.html']+list(reg['module_HTML_sha256']):add(site/rel)
for p in (ROOT/'research-wiki/retrieval-index').glob('*.json'):add(p)
write(RUN/'FINAL-review-inputs-v1.json',dict(phase='FINAL actual bounded AE causal package/readers/Book mapping',
    rows=sorted(rows.values(),key=lambda x:x['path']),fixed_input_count=len(rows),
    original_CONTRACT_count=118,original_BODY_count=236,source_commit=reg['source_commit'],
    original_R1_R6=load(CONTRACT/'reader-requirements-v1.json'),future_metadata_scope=scope,
    allowed_outputs=['final-reader-review-v1.md','final-reader-receipt-v1.json'],
    chapter_complete=False,goal_complete=False))
write(RUN/'FINAL-review-packet-v1.md',
    'Distinct anti-anchored FINAL: hash every fixed RAW index row independently before/after. Reinspect actual three complete public types and bodies, 14 actual AE-only canary proofs and definition, neutral decoder, accepted CONTRACT118/BODY236 and original source PDF13/15 pixels. Preserve all original hashes through exact source-contract snapshots and five BODY-mutable-integration snapshots; current changed live reader/root files are not claimed identical to old receipts.\n\n'
    'Inspect successful root9100/Tests9260/fullharness472skip7 actual logs and artifacts, whole-type proofVALUE/42 axioms/39 selected nodes2136 coalesced edges12 direct VALUE pairs, exact three v2 fences and current both-base contributor/own shadow. All three bodies and canary raw bytes remain frozen; no target weakened.\n\n'
    'Personally view ALL EIGHT original v4 images listed by formula-render-v5.json using view_image original. Browser execution actually v4 passed. The actual browser JSON/DOM filenames retained v1 after copying helpers, and Python v4 normalization failed on the absent v4 filename. capture-output-audit-v5 binds the genuine outputs without rerunning or relabeling images; inspect the disclosed outer raw-stderr limitation. No DOM/schema/manual output pass substitutes for pixels.\n\n'
    'Review retained site failures: v1 unsupported local_status.declarations removed only from own card; v2 mathlib external dependency links made explicit in note text while actual local links/compiled VALUE edges retained; v3 site build/check passed but registry found new module defaulted to Bandit Foundations. repair-book-mapping-v4 adds precisely one actual module_globs path to implement the explicit same-registry Online Learning Book requirement. This field was omitted from the initial helper and is separately flagged for scope review; all old IDs/URLs/header hashes/statuses and reader entries remain preserved. Actual v4 clean site/registry passes10935old+3new declarations,16cards,3newnotes,4oldcuratedlinks. No generated _site/source/pins/parent edit.\n\n'
    'Original unchanged R1-R6 require per-row verdict and evidence. Search for source mismatch, AE versus pointwise/completion/kernel confusion, current-independence consumer substitution, fixed expected minimum versus expected hindsight minimum, wrong all-time quantifiers and T0/convergence claim. Assess the exact prospective title/body and FINAL-future-metadata-scope-v1 separately; native acceptance, post-native review and delivery remain future. Only three derived obligations may close; original16/null and full remaining chapters/appendix/completion/kernel obligations remain required. Reused distinct automated actor/history disclosed, requested Astra/medium only, no human/external/absolute blind/runtime attestation.\n\n'
    'Write only final-reader-review-v1.md and final-reader-receipt-v1.json. Record actual fixed count, all reviewed RAW rows and before/after checks, reportSHA, seven slots, personally viewed original image rows, exact R1-R6/evidence, blockers, verdict accepted|accepted-with-explicit-delta|rejected and approved permitted_future_metadata exactly if acceptable. Do not edit inputs or execute native/publication actions.\n')
print('Actual FINAL fixed RAW inputs:',len(rows),'native/delivery still pending.',flush=True)
