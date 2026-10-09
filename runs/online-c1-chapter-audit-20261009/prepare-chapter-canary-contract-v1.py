from common_proving_v2 import *
fixed()
receipt=RUN/'chapter-canary-blind-receipt-v2.json'
assert sha(receipt)=='c752312c0745850e6cd566adf457a95f66d713bf3f736b7ebbdf19c0cb51edf2'
r=load(receipt)
assert r['target_count']==r['reconstructed_propositions']==27 and r['inputs_unchanged']
assert not r['ambiguities'] and not r['missing_context']
assert sha(RUN/'chapter-canary-blind-reconstruction-v2.md')==r['report_sha256']=='767831b10ede15b69e67a93aa4e5bd46420fde8564f84097cf55c6689ef2dc90'
for row in load(RUN/'chapter-canary-neutral-inputs-v2.json')['rows']:assert sha(row['path'])==row['sha256']
assert not (ROOT/'Tests/OnlineLearningChapterAuditCanary.lean').exists()
packet=RUN/'chapter-canary-CONTRACT-packet-v1.md'
write(packet,'''# Whole Chapter1: independent CANARY CONTRACT review

Read exact27 draft Test headers/setup/2probe definitions, independent27seven-slot reconstruction, repaired neutral context, explicit source-intent/17source mapping, actual old/public54 statements and4BODY-reviewed new initialized-FTL proofs, v3source17inventory and v4corrected reviewer example. Formalizer personally read complete27 reconstruction and found types consistent with intent; this is not a reviewer verdict. All27 actual closed Props typechecked0, no actual Test body/productioncanary exists. Target counts27/54 are distinct from17required source objects/proof-totalnull; one additionalrequired source family has actual4producers but source/chapter acceptance pending.

Review CANARY CONTRACT ONLY: verify each of27 exact seven slots/source-vs-Lean delta/nondegenerate behavior, mapping coverage for all17sourceobjects as complementary probes of generic54actualpublic contracts. Generic IID lower retains strictpast/jointIID/independentprivateentirerandomness/model/AE/completed/kernel premises; concrete kernel samechosenf allT is not allunspecifiedsideinfoprotocols. Source printed ordinarylimitdefinition and corrected uppersemantic plus SAMEactualdyadiccounterexample/conditionalmeaniff/truebest0 remain distinct. Corrected v4 initializedFTL rising0,1 regret+1/2/negativecorrection-1/4; withdrawn reviewer false negative example and generalized nonnegativity exclusion remain oldbytes. G004 BODY seven-slot copied decoder's stale proposed-tense: actualBODY/readiness establish its proof exists; do not carry that tense into currentreader/verdict. No newsourcecorrection/theoremscope required.

Permission proposed only after accepted CANARY CONTRACT: create sole Tests/OnlineLearningChapterAuditCanary.lean with exact reviewed import/setup2rising/fallingdefinitions/27exacttheoremheaders and actual bodies, necessary privateprooflocalhelpers only; keep canonical4module unchanged, no othernewpublicproductiondefinition/theorem or oldTest edits. Exact sharedTests import appends only after CANARY BODY/public readiness (oldprefixsnapshot/exactplan binding). Bounds/limits/minima/BTL/stability/IID/kernel/lower/harmonic must consume actual public producers or explicit oldpublicTest instantiations; numerical behavioral checks compute substantive concrete values; no performance/oracleassumption supplied. ExactTestmodule/headers/privatehelper/sourcequalifiednames/axioms/directcompiledVALUEfences then independentCANARY BODY review. Scope sourceproof/inventory and readerR1-R10 unchanged. No silentterminalweakening or declarationcountprogress.

OriginalBODY293index is immutable: rootnowhas only reviewed exact4moduleimport afterBODY/readiness. root-integration-receipt and immutable originalroot snapshot resolve oldrootbinding; currentCANARYindex binds currentROOTactualSHA. Otheroriginal293rows remain unchanged; approved earlierOWNmetadata snapshots/receipts resolve CONTRACT196history. Rootactualsharedbuild0 includesoldBandit/Books/new4proofs; noTests/fullharness/chapteracceptance. Newreader/coverage edits still pendingtheirguards/review; no generatedsite/globalSGB/memory/indexmutation/merge/deploy/retirement. RequestedAstramedium/reuseddistinctactors/no runtimehumanexternalabsoluteblindreview.

Write ONLY chapter-canary-CONTRACT-review-v1.md and chapter-canary-CONTRACT-receipt-v1.json in this RUN. ActualindexedRAWbeforeafter,27fullseven-slot source verdicts/completeness/nondegenerate findings, exactpermittedTestsetup/headerhashes/bodyediting/privatehelpers/importphase, source/correction/4BODY/currentroot/baseline bindings and requiredrepairs. accepted|accepted-with-explicit-delta|rejected CANARY CONTRACT only, not Testproof/chapter/Goalacceptance. Subsequent R1-R10/focusedcanary/Tests/fullharness/nonemptytwobasecontributor/ownshadow/sameregistry/siteDOMpersonalpixels/FINAL/native/postnative/scopedPR mandatory. Do not editindexedfiles/proof/native/site/Git.
''')
paths=[Path(row['path']) for row in load(RUN/'general-init-BODY-inputs-v1.json')['rows']]
root_plan=load(CONTRACT/'exact-import-plans-draft-v3.json')['rows'][0]
for row in load(RUN/'general-init-BODY-inputs-v1.json')['rows']:
    if sha(row['path'])!=row['sha256']:
        assert Path(row['path']).resolve()==Path(root_plan['path']).resolve()
        assert sha(root_plan['snapshot'])==row['sha256'] and sha(row['path'])==root_plan['permitted_result_sha256']
paths += [RUN/p for p in ['general-init-BODY-review-v1.md','general-init-BODY-receipt-v1.json','root-integration-receipt-v1.json','shared-root-general-init-v1.json','shared-root-general-init-v1.log','shared-root-general-init-v1-exit.json','chapter-canary-blind-reconstruction-v2.md','chapter-canary-blind-receipt-v2.json','chapter-canary-neutral-inputs-v2.json','chapter-canary-neutral-packet-v2.md','chapter-canary-neutral-context-repair-v1.md','chapter-canary-neutral-definition-audit-v2.json','chapter-canary-draft-types-v1.lean','chapter-canary-draft-types-v1.log','chapter-canary-draft-types-v1-exit.json','20_architect-chapter-canaries-draft-v1.md']]
paths += [CONTRACT/p for p in ['chapter-canary-targets-draft-v1.json','chapter-canary-neutral-targets-v1.lean.txt','chapter-canary-neutral-context-v2.lean.txt','chapter-canary-source-intent-draft-v1.json','chapter-canary-source-intent-draft-v1.md']]
paths += list((ROOT/'Tests').glob('Online*.lean'))+[ROOT/'Tests/OnlineSquareMinimumCanary.lean',ROOT/'Tests/OnlineNoRegretSemanticsCanary.lean',packet]
assert all(p.is_file() for p in paths)
index=rows(paths)
write(RUN/'chapter-canary-CONTRACT-inputs-v1.json',dict(rows=index,fixed_input_count=len(index),canary_targets=27,new_probe_definitions=2,actual_canary_bodies=0,actual_public_canonical_proofs=4,source_audit_objects=17,proof_total=None,chapter_complete=False,goal_complete=False))
fixed()
print('CANARY CONTRACT ready:',len(index),'current RAW inputs/27 exacttypes/2probes/no Test bodies.',flush=True)
