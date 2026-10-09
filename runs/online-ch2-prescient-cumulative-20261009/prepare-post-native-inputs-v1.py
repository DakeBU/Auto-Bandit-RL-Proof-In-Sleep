from publication_guard_v4 import *
fixed()
assert load(RUN/'FINAL-review-v1.json')['package_verdict'] in ['accepted','accepted-with-explicit-delta']
assert load(RUN/'post-native-root-audit-v1.json')['all_other_FINAL_inputs_unchanged']
for n in ['record-acceptance-v2.py','deliver-v1.py','collect-actual-delivery-v1.py','final-evidence-delivery-v1.py']:
    compile((RUN/n).read_text(encoding='utf8'),n,'exec')
write(RUN/'post-native-packet-v1.md','''# Actual bounded native closure and prospective cumulative PR delivery

Independently review actual OWN trial/lifecycle5->0 for ONLY five exact frozen conditional cumulative proofs; two full16/22conjunct canaries separately inventoried, zero new definitions/generatedTestauxiliary. Actual CLI receipts, contemporaneous exact beforeRAW, one appended accepted trial/session event, correct sequence/parent/state, unchangedOWNjournal/globalSGB, acceptedshadowmismatches[]/would_mutatefalse. Rawliteralheader hashes and normalizednativefences are distinct and must match their own conventions. No fullsourceAlgorithm15.8/T15.30/Chapter6/15/Chapter2/all8forwards/whole16Goal closure.

Independently hash all current inputsbeforeafter; trace every permitted transition from FINAL-inputs through pre-native-exact-bytes and rootaudit. Onlyexactthree contributionfields/OWNtask-proof-retrievalsuffixes/trial-session-statechanged; fullmath/Test/root/reader/source/pins/contracts/current12pixels unchanged. Ownjournalunchanged. Clean repairedSITEv2 applies to source in clean-candidate-site-binding-v2, notlateracceptance/deliveryhead. Priorambiguity/13fieldrepair/oldpixels/failedscopeplan/nativeconversiondelay/resolvermissingfield and allproof/API failures retained.

New create-only delivery helper generation failed twice afterFINALinputs: generator-v1 actual1 beforeoutputs due suffix newline string search; generator-v2 actual1 afterwriting4prospectivehelpers when syntax compilation rejectedmemorywrite in record-acceptance-v1. NONEof those prospective helpers executed. Versioned record-acceptance-v2 repairsONLY memorysource string and syntacticallypassed, then afteractualFINALacceptance ranactualnative closure. Otherthree prospectivehelpers syntacticallypassed and remainunexecuted. Bothfailure receipts/generators/invalidhelper retained. Review actualrecord-acceptance-v2 bytes/receipt and no targetweakening, not futuretruthfromsyntax alone.

Review prospective PR-plan/body and deliver-v1/collect-actual-delivery-v1/final-evidence-delivery-v1. ExactOWNscopedstages/fullpackagewhitespace0/RAWCRLFsnapshots/two nonemptycontributorbases/currentOPENdraftunmergedparentPR211 exact24de0231aa067f141251aac5c20deb58e448ea66. Percommandcredentialhelper/nonforce/no globalcredentialedits. Actualscopedcommit/push/newdraftPR/officialattachment/durableactualdeliveryreviewnext, no merge/deploy/retirement/main/live/CI. PRbody leads mathematical behavior and explicitconditionalsourceboundary, not claimcompletefullsourcerun. AllfullsourceX/interiorgenerator/loss transport/validrunwrapper and8forwards REQUIREDOPEN/GoalACTIVE.

Create-only post-native-review-v1.md/json: verdict/native_verdict/metadata_verdict/prospective_publication_prose_verdict/delivery_helper_verdict/required_repairs/report/report_sha256/input_manifest_sha256/FINAL_sha256/raw_input_checks. Do notpublish/editinputs. Distinctreusedstagedautomatedactor/requestedAstra-medium/historydisclosed, nohuman/external/absolute-blind/runtimeattestation.
''')
paths={p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update(Path(row['path']) for row in load(RUN/'FINAL-inputs-v1.json')['rows'])
write(RUN/'post-native-inputs-v1.json',dict(rows=rows(paths),FINAL_sha256=sha(RUN/'FINAL-review-v1.json'),scope='ActualOWN5proofnative/metadata closure; prospective scoped delivery only',actual_delivery_PENDING=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Actual postnative and prospective delivery packet ready for distinct review.')
