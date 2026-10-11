$ErrorActionPreference='Stop'
$root=(Get-Location).Path
$out='tmp/online-ch2-b4-next-strong-convex-freeze-20261011'
$hd='tmp/online-ch2-b4-next-strong-convex-header-20261011'
$rd='tmp/online-ch2-b4-next-strong-convex-source-review-20261011'
$bd='tmp/online-ch2-b4-next-strong-convex-blind-20261011'
function Bind([string]$path) { $f=Get-Item -LiteralPath $path; [ordered]@{path=$path;sha256=(Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash.ToLower();bytes=$f.Length} }
function Save([string]$name,$obj) { $s=$obj|ConvertTo-Json -Depth 80; [IO.File]::WriteAllText((Join-Path $root "$out/$name"),$s+"`n",[Text.UTF8Encoding]::new($false)) }
$head=(git rev-parse HEAD).Trim()
$before=@(git status --porcelain=v1)
$review=Get-Content "$rd/source-header-review-v1.json" -Raw | ConvertFrom-Json
$topology=Get-Content "$hd/topology-proposal-v2.json" -Raw | ConvertFrom-Json
$topreview=Get-Content "$rd/source-topology-review-v2.json" -Raw | ConvertFrom-Json
$binders=Get-Content "$hd/binder-obligations-v1.json" -Raw | ConvertFrom-Json
$expected=[ordered]@{
"$hd/neutral-complete-header-v1.txt"='ded5adebef211f810552abbc4eced856dd9fff59f268989e9c1ff5a4ecd3d590'
"$hd/topology-proposal-v2.json"='9b60dfbf2628a57e4411d9816849e88f802c305e78d7f58f581c1734bc649e1d'
"$bd/fresh-blind-v1.json"='9d84f60e2a5f272922a68bb8c1745d98de4c7779e154a5e53fde4c4560525152'
"$rd/source-header-review-v1.json"='0a23a79c8f1c9a32059441af10f204c1bbe6afcdc27ed28cb684c52a07ed0665'
"$rd/source-topology-review-v2.json"='7522a6a6cc07e7957f5be0bb3e1040469b424fc9f8af60d5cc11ba2c8ae569bf'
'docs/contracts/online-ch2-complete-target-freeze-v1/effective-targets-frozen-v3.2.json'='61cf1901a632aeee35ee71511ba53b115ae0958649ea78b786536a4404684ba1'
}
foreach($p in $expected.Keys) { if((Bind $p).sha256 -ne $expected[$p]) { throw "Hash mismatch: $p" } }
Copy-Item -LiteralPath "$hd/neutral-complete-header-v1.txt" -Destination "$out/neutral-proposed-frozen-header-v1.txt"
$source=Bind $review.source.path
if($source.sha256 -ne $review.source.sha256){throw 'PDF hash mismatch'}
$context=[ordered]@{workspace=$root;canonical_source='E:/ABRL/research';branch=(git branch --show-current).Trim();head=$head;git_common_dir=(git rev-parse --git-common-dir).Trim();status_before=$before;captured_utc=[DateTime]::UtcNow.ToString('o');clean_at_capture=($before.Count -eq 0);not_final_preproof_context=$true;upstream_gate_results='Parent owns running gates; no results inferred here';remote_fetch='Not repeated by preparation worker against shared Git store'}
Save 'context-before-v1.json' $context
$inputs=@($expected.Keys | ForEach-Object {Bind $_})
$extras=@("$hd/header-proposal-v1.json","$hd/binder-obligations-v1.json","$hd/source-topology-proposal-v1.json","$hd/topology-repair-response-v2.json","$rd/independent-source-topology-v1.json","$hd/elaboration-receipt-v1.json","$hd/context-before-v1.json","$hd/context-after-v1.json","$hd/bounded-retrieval-v1.json","$hd/bounded-retrieval-v1.stdout.raw",'BanditRLProof/OnlineClosedProper.lean','BanditRLProof/OnlineConvexExtended.lean','.lake/packages/mathlib/Mathlib/Analysis/Convex/Strong.lean','.lake/packages/mathlib/Mathlib/Order/Filter/Extr.lean','.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean','lean-toolchain','lakefile.lean','lake-manifest.json','runs/process_memory.json') | ForEach-Object {Bind $_}
$pages=@(Get-ChildItem $rd -File | Where-Object {$_.Name -match '^(page-|lemma7-1-page112-independent).+\.(txt|png)$'} | ForEach-Object {Bind "$rd/$($_.Name)"})
$contract=[ordered]@{
schema_version=1;status='PROPOSAL_ONLY_NOT_FROZEN_NO_BODY_AUTHORIZATION';actor='/root/strongconvex_growth_formalizer';model_request='GPT-6 Astra / medium; runtime not independently attested';context=$context
sole_leaf=[ordered]@{id='online-ch2-b4/conditional-strong-convex-minimum-growth';module='BanditRLProof/OnlineStrongConvexMinimum.lean';declaration='BanditRL.OnlineConvex.stronglyConvex_minimum_growth';public_theorems=1;public_definitions=0;header=(Bind "$out/neutral-proposed-frozen-header-v1.txt");imports=@('BanditRLProof.OnlineClosedProper','Mathlib.Analysis.Convex.Strong');scoped_context='noncomputable section; open Set; namespace BanditRL.OnlineConvex';meaning='For SourceProper EReal f on literal convex V contained in effectiveDomain f, nonnegative lam and the exact interior strong-convexity inequality, supplied feasible attained minimizer p and feasible q satisfy toReal(f p)+(lam/2)*norm(q-p)^2 <= toReal(f q).';source_delta='Explicit conditional generalization to any real normed space; no existence, uniqueness, closedness, finite-dimensionality, completeness or whole cumulative algorithm assertion.'}
source=[ordered]@{title='Francesco Orabona, A Modern Introduction to Online Learning';version='arXiv:1912.13213v10';pdf=$source;primary_bounds=@('Definition 2.18: PDF28/printed16','Definition 4.1: PDF46/printed34','Lemma 4.2: PDF46-47/printed34-35; source support route remains distinct');reviewed_route_bounds=$review.source.pages;additional_pdf112=$topreview.source;inspection_attribution='Reviewers personally inspected the recorded source pixels; this preparation worker binds their evidence and does not claim a fresh pixel audit.';source_page_artifacts=$pages}
source_inventory=(Bind 'docs/contracts/online-ch2-complete-target-freeze-v1/effective-targets-frozen-v3.2.json')
review_bindings=$inputs;retained_context_bindings=$extras
semantic_roundtrip=[ordered]@{status='Header semantics reviewed as conditional generalization; freeze decision pending';blind=(Bind "$bd/fresh-blind-v1.json");source_header=(Bind "$rd/source-header-review-v1.json");source_verdict=$review.verdict;seven_slots=$review.seven_slots;independence='Existing distinct blind/source reviewers are attributed; preparation formalizer does not self-certify their roles.'}
binder_audit=$binders;expanded_definitions=[ordered]@{SourceProper='(forall x:E, f x != bottom) AND exists x:E, exists r:R, f x = coe r';effectiveDomain='{x | f x < top}; alone does not exclude bottom';IsMinOn='forall v in V, f p <= f v; membership hp separate';Convex='Nonnegative real barycentric weights summing to one preserve literal V';toReal='Both infinities totalize to zero; finite transport must be proved internally';definition_policy='No new public definition/selector/choice; no fallback branch'}
source_topology=[ordered]@{v2=(Bind "$hd/topology-proposal-v2.json");review=(Bind "$rd/source-topology-review-v2.json");verdict=$topreview.verdict;historical_v1=(Bind "$hd/source-topology-proposal-v1.json");historical_v1_repair=(Bind "$rd/independent-source-topology-v1.json");literal_graph=$topology.literal_source_graph;alternate_graph=$topology.alternate_implementation_graph;corrected_targets=$topology.corrected_targets;coverage_rule='Preserve literal BTRL15.31 -> FTRL7.47 -> Lemma4.2/7.1/7.5, optimality, sum inclusion and qualified existence dependencies. Direct segment implementation does not certify this source topology or remove its OPEN obligations.'}
proof_obligations=@(
[ordered]@{id='FINITE_TRANSPORT';status='UNPROVED';scope='Derive no-top from hdom and no-bottom from hf on all V points, including segments; transport EReal order and arithmetic into real values without adding a public bridge premise'},
[ordered]@{id='SEGMENT_FEASIBILITY';status='UNPROVED';scope='Use literal Convex V and supplied hp/hq; do not replace V with V intersect effectiveDomain'},
[ordered]@{id='CONDITIONAL_GROWTH';status='UNPROVED';scope='Derive exact lam/2 quadratic minimum growth including lam=0 and coincident points using the frozen header; no proof search in this preparation'},
[ordered]@{id='OPTIONAL_CLOSED_WEIGHTS';status='CONDITIONAL_IMPLEMENTATION_OBLIGATION';scope='Only if using Mathlib StrongConvexOn: derive endpoint weights and exact coefficient normalization internally; no added hypothesis or source necessity claim'}
)
reuse_plan=[ordered]@{decision='new_shared';existing_search=(Bind "$hd/bounded-retrieval-v1.stdout.raw");extent='Retains earlier bounded declaration/API retrieval only; no exhaustive absence claim and no new proof search';planned_consumers=@('Corrected BTRL interior movement bound for actual inclusive G_s, s<T','Corrected BTRL optional terminal comparator-distance sharpening');no_duplicate_wrapper=$true;imports_and_dependency_pins_unchanged=$true;dependency_api_candidates='Prior retrieval names EReal.toReal_le_toReal, EReal.coe_toReal, StrongConvexOn; actual BODY use unverified'}
remaining_mandatory=@('Actual cumulative properness, finite literal feasible-domain inclusion, modulus and attainment/selector characterization','FTRL constrained support and nonzero-hint stability, qualified sum inclusion, dual norm, Young and zero-hint ghost','BTRL corrected movement sum s<T, terminal x_(T+1)=x_T, finite-identity join','Literal source Lemma4.2 converse and Theorem4.3/A.1 qualification corrections if routes claimed','All seven forward containers, six future claims, B1-B7 including full B4 and both corrected parent targets remain OPEN')
learning=[ordered]@{process_memory=(Bind 'runs/process_memory.json');ids=@('ABRL-PM-ATOMIC-SOURCE-ASSUMPTIONS','ABRL-PM-MATCHED-HARNESS-EVIDENCE','ABRL-NK-WINDOWS-PATH-LENGTH');control_plane_math_authority=$false;failure_class='NONE';salvage='V1 repair and all prior artifacts retained; no proof fragments created or discarded';parallelism='Serial mathematical construction; distinct independent review actors; no parallel proof routes';purification='pending';exposition_seal='pending'}
reader_and_graph_plan=[ordered]@{reader='Conditional growth card with source Definition4.1, explicit ambient generalization, full assumptions, exact coefficient, actual eventual proof/dependencies and open producer boundary';lean_graph='Prospective single node; zero new verified edges';source_graph='Reviewed V2 open plan retained';compressed_spine='Pending proof; candidate mechanism is quadratic growth at an attained feasible minimum';overview='No completion count change';functor='none-found-with-reason: no reviewed transport established';all_canonical_surfaces='No changes authorized during this proposal preparation'}
chapter_state=[ordered]@{chapter2='partial';required_open_forward_containers=7;future_claims_open=6;B1_B7='OPEN';B4='OPEN';corrected_full_parents='OPEN';Goal='ACTIVE';target_removal=$false}
authorization='Independent freeze audit, committed exact reviewed inputs, clean preproof capture and independent verification, then explicit parent frozen-header/BODY authorization are still required. This file is not a freeze receipt.'
}
Save 'source-contract-proposal-v1.json' $contract
$checks=@(
[ordered]@{id='HASH_BINDINGS';state='PASS';detail='All six supplied exact SHA256 pins and original PDF checked locally'},
[ordered]@{id='HEADER_BYTE_COPY';state='PASS';detail='Copied unchanged header bytes; no BODY appended'},
[ordered]@{id='INDEPENDENT_CONTRACT_AUDIT';state='PENDING';detail='Distinct reviewer must inspect this assembled proposal'},
[ordered]@{id='MAINTENANCE_GATES';state='PARENT_OWNED_PENDING_EVIDENCE';detail='Do not infer success from parent report that gates are running'},
[ordered]@{id='COMMITTED_FREEZE';state='PENDING';detail='Parent seals/promotes exact packet only after independent review'},
[ordered]@{id='CLEAN_PREPROOF_REPLAY';state='PENDING';detail='Capture current HEAD, dirty state, imports, pins and header/read dependencies after freeze; independently verify before BODY'},
[ordered]@{id='EXPLICIT_BODY_AUTHORIZATION';state='PENDING';detail='Parent explicit frozen-header authorization required'},
[ordered]@{id='FUTURE_ACCEPTANCE';state='NOT_RUN';detail='Exact header fence; focused compilation; TYPE/VALUE and axioms; distinct BODY review; separately frozen canary; shared root/Tests/full harness; schema3 contribution/process-memory; site source/pixel review; independent acceptance and delivery'}
)
Save 'preproof-checklist-v1.json' ([ordered]@{status='PREPARATION_ONLY';checks=$checks;no_proof_search=$true;no_BODY=$true;no_build_claim=$true})
Save 'leaf-freeze-proposal-v1.json' ([ordered]@{status='AWAITING_INDEPENDENT_FREEZE_AUDIT';source_contract=(Bind "$out/source-contract-proposal-v1.json");header=(Bind "$out/neutral-proposed-frozen-header-v1.txt");checklist=(Bind "$out/preproof-checklist-v1.json");not_a_receipt=$true;authorization_granted=$false;head=$head;scope='One conditional growth theorem only';canonical_changes=$false})
$after=@(git status --porcelain=v1)
Save 'preparation-verification-v1.json' ([ordered]@{all_expected_hashes_match=$true;pdf_hash_matches=$true;header_copy_exact=((Bind "$out/neutral-proposed-frozen-header-v1.txt").sha256 -eq $expected["$hd/neutral-complete-header-v1.txt"]);head_before=$head;head_after=(git rev-parse HEAD).Trim();status_before=$before;status_after=$after;tracked_files_edited=$false;proof_search=$false;BODY=$false;gates_run=@();claim='Preparation integrity only, not independent review or proof acceptance'})
$manifest=@(Get-ChildItem $out -File | Where-Object {$_.Name -ne 'artifact-manifest-v1.json'} | ForEach-Object {Bind "$out/$($_.Name)"})
Save 'artifact-manifest-v1.json' ([ordered]@{schema_version=1;status='PROPOSAL_ARTIFACTS';artifacts=$manifest})
Get-ChildItem $out -File | Select-Object Name,Length
