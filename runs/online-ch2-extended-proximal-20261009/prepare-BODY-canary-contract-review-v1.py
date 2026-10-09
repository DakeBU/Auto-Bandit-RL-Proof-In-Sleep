from common import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash
fixed();assert not (ROOT/'Tests/OnlineBregmanExtendedCanary.lean').exists()
assert sha(RUN/'canary-neutral-types-v1.txt')=='2dc511727d2c311def3cca06f293ac386eec19bcd13bacd03fe861fa3bf5dce4'
assert sha(RUN/'canary-blind-v1.md')=='eae77a78544c6d8572c1811693a785b3e03f36205c2972453bdcf1347f3fd44e'
assert sha(RUN/'canary-blind-v1.json')=='da5a7d08a9f6fdc144d77f2358ae8540ed5cad329dd60041932bbbc810969736'
assert load(RUN/'kernel-and-fence-inspected-v1.json')['standard_only']
assert load(RUN/'production-dependency-inspected-v1.json')['coalesced_direct_TYPE_VALUE_presences']==396
text=(RUN/'canary-neutral-types-v1.txt').read_text(encoding='utf8');targets=[]
for short,count in [('restricted_absolute_nonquadratic',12),('restricted_linear_outside_center',11)]:
    tail='theorem '+short+text.split('theorem '+short,1)[1]
    ends=[i for i in [tail.find('\n\ntheorem '),tail.find('\n\nend ')] if i>=0];header=tail[:min(ends)]
    targets.append(dict(declaration='BanditRL.OnlineBregmanExtendedCanary.'+short,exact_proposed_header=header,statement_hash=statement_hash(header),header_raw_sha256=hashlib.sha256(header.encode('utf8')).hexdigest(),statement_hash_convention='native normalize_statement, not raw header bytes',file='Tests/OnlineBregmanExtendedCanary.lean',context='scalar real; three fully explicit local let bindings V/f/psi, no new named definitions',complete_conjunction_items=count))
write(CONTRACT/'canary-targets-draft-v1.json',dict(stage='draft',targets=targets,neutral_sha256=sha(RUN/'canary-neutral-types-v1.txt'),blind_md_sha256=sha(RUN/'canary-blind-v1.md'),blind_json_sha256=sha(RUN/'canary-blind-v1.json'),proof_plan='Each family proves properness/global supports/top outsideV/finitePartconvexONLYV and actualglobalnonconvexity witness endpoints0,2/midpoint1. Reuse accepted prior concrete strictpsi/minimum/divergence facts where exact; prove actualERealminimum via public finitePartminiff, universalcomparison via publicextendedoneStep. Both final numericalbranches MUST individually retain actual extendedhelper proof by equalitytransport, not norm_num. Actualpsi ambientderivatives proved locally. No Testbody yet.',no_test_body=True,source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
snapshot={r['path']:r for r in load(RUN/'pre-stabilization-exact-own-metadata-v1.json')['rows']};changes=[]
for row in load(RUN/'contract-review-inputs-v1.json')['rows']:
    if sha(row['path'])!=row['sha256']:
        old=snapshot[row['path']];assert old['sha256']==row['sha256']
        assert hashlib.sha256(base64.b64decode(old['raw_base64'])).hexdigest()==row['sha256']
        changes.append(dict(path=row['path'],historical_sha256=row['sha256'],current_sha256=sha(row['path']),exact_RAW_snapshot='pre-stabilization-exact-own-metadata-v1.json',reason='Explicit OWN source-reviewed draft-to-stabilized/proving metadata only'))
assert len(changes)==3
write(RUN/'BODY-historical-binding-resolution-v1.json',dict(original_contract_review_sha256=sha(RUN/'contract-review-v1.json'),changed_live_rows=changes,all_other_source_contract_inputs_unchanged=True,not_false_current_live_RAW_claim=True))
write(RUN/'BODY-canary-contract-review-packet-v1.md','''# Production BODY and exact infinity-canary CONTRACT review

Independently rehash all current RAW and actual2925baseline before/after; run common.fixed. Original contract review56rows3changed OWNmetadata resolved through immutable exactpre-stabilization RAW; no falsely current-live historical hash claim. Three frozen production headers/context unchanged and full actual bodies compiled firstpass: twoleaves then terminal each3297cached-inclusivejobs0. Three fullgenericpublicVALUE probes/sixstandard-onlyaxioms/three nativefences-safechecks0. Actualcompiledproductiongraph3nodes/396coalesceddirectTYPE_VALUEpresences/sixrequiredVALUEpairs; notfulltransitive/source/registry denominator. Existing dependency warnings replayed, no new ownwarnings/suppression.

Read all actualbodies: properness+global support derivefiniteeveryVpoint; actualsupport atfeasibleconvexcombination evaluatedatfeasibleendpoints, weightedrealinnercancellation yields ConvexOnVfinitePart. No naiveglobal T2.21 application orassumedconvexity. ExistingminOn_finitePart_iff onactualEReal sum then feasiblefiniteembedding rewriting, no duplicateorderproof. Terminalderivesfeasiblefiniteness and invokesbothactualbridges plusacceptedrealproximalproducer, bothnegative residuals/bothpsi derivatives/positiveeta/actualERealminimum/hp retained. Firsttheorem noComplete/FiniteDim; other2explicitComplete inheritedminAPI, asfrozen. Actualsourceproofrouteadaptation visible; notsourceVIvectorproducer/attainment/causalregret.

Review two COMPLETE Testtypes beforebodies, neutralreconstruction12/11items. ExactlocalletV/f/psi definitions, actualtopoutsideV, propernessandallambientglobal supports, ConvexOnONLYV andexplicitNOTglobalfinitePartconvexity. Restrictedabs[-1,1]/nonquadraticpsi/actualERealminimum0/absnondiff/asymmetric9/64,11/64/final-1/2<=-5/16. Restrictedlinear[0,1]/quadraticpsi/center-1outsideVANDlossdomain/actualboundaryminimum0/movement1/2/final-1/2<=1/2. Both universalcomparisons allfeasibleu mustcallactualextendedhelper; BOTH finalnumericbranches individuallyretainactualhelper throughEq.mp, notunrelatednorm_num. Reuse exactpriorTeststrict/min/divergencefacts, actualsourceglobal supports andpsi derivatives locallyproved, minimumpublicbridge used. No globallyfinite/coercive/regularizerstrongconvexity/sourcecausalassumptions sneakedin. Headerhash is NATIVE normalized; rawheaderSHA separate fromstart.

OnlyproductionBODY pluscanaryCONTRACT now. No Testbody/roots/readers/materialization/nativeacceptance/combinedgate/site/registry/pixel/FINAL yet. FullsourcepsiX/interior/totalextensionlocality, actualattainedcurrentcausalrecursion/interiority andsame-runsharpfixed-variabletelescopesincludingmaintextfixedexercise/all8forwards REQUIREDOPEN; Ch2partial/denominatornull/whole16GoalACTIVE, noChapter6/15acceptance. Create-only BODY-canary-contract-review-v1.md/json onefinalLF/no trailingwhitespace with BODY_verdict/canary_CONTRACT_verdict/overallverdict/required_repairs/allowednewTestbodiesandfrozenproductionpreservation/report+inputSHAs/rawbefore-after/seven-slotdeltas. Requested Astra/medium distinct reusedstagedautomatedrole, nohuman/external/absolute-blind/runtimeattestation. No source/reader/codeinputs editedbyreviewer, no nativeevents/publication.
''')
paths={p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name not in ['trials.jsonl','lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md']}
paths.update(Path(row['path']) for row in load(RUN/'contract-review-inputs-v1.json')['rows'])
paths.update([PUBLIC,ROOT/'Tests/OnlineBregmanProximalCanary.lean',ROOT/'BanditRLProof/OnlineSubgradientAbsolute.lean',*[ROOT/x/(TASK+'.md') for x in ['tasks','proof-obligations','conversion-windows','research-wiki/retrieval-index']]])
write(RUN/'BODY-canary-contract-review-inputs-v1.json',dict(rows=rows(paths),production_sha256=sha(PUBLIC),canary_body_absent=True,baseline_count=2925,whole_Goal_status='ACTIVE'))
print('Actual3BODY/2completeinfinitycanary CONTRACT packet ready; distinctreviewpending.')
