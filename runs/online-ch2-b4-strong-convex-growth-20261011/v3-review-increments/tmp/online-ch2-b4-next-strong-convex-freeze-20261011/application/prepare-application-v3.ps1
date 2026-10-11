$ErrorActionPreference='Stop'
$out='tmp/online-ch2-b4-next-strong-convex-freeze-20261011/application'
$rd='tmp/online-ch2-b4-next-strong-convex-freeze-audit-20261011'
function Bind([string]$s){$f=Get-Item -LiteralPath $s;[ordered]@{path=$s;sha256=(Get-FileHash -LiteralPath $s -Algorithm SHA256).Hash.ToLower();bytes=$f.Length}}
function Save([string]$n,$o){$p=Join-Path (Get-Location) "$out/$n";if(Test-Path -LiteralPath $p){throw 'Create only'};[IO.File]::WriteAllText($p,($o|ConvertTo-Json -Depth 90)+"`n",[Text.UTF8Encoding]::new($false))}
$p=Get-Content "$out/canonical-freeze-application-proposal-v2.json" -Raw|ConvertFrom-Json -AsHashtable
$prior=Bind "$out/canonical-freeze-application-proposal-v2.json"
$historical=@(Get-ChildItem $out -File|Where-Object Name -Match '-v[12]\.'|ForEach-Object {Bind "$out/$($_.Name)"})
$ready=Bind "$rd/preproof-source-readiness-v1.json"
if($ready.sha256 -ne 'f9fb655d7932598e0a799865c1e56be6b8853f0675ee5d6bec54fdea1b8a0e93'){throw 'readiness changed'}
$elig=Bind "$rd/preproof-reorder-eligibility-v1.json"
if($elig.sha256 -ne 'e3ac44d8b3a1d91399ce2a23947be59c0883b78f04e0599b13c60e10777757b1'){throw 'eligibility changed'}
$source=Get-Content $ready.path -Raw|ConvertFrom-Json -AsHashtable
$spec=Get-Content 'tmp/online-main-reconciliation-final-review-20261011/evidence-spec-4034-prepared-v2.json' -Raw|ConvertFrom-Json -AsHashtable
$p.status='V3_PREPROOF_ONLY_SUCCESSOR_UNEXECUTED_AWAITING_INDEPENDENT_DESIGN_REVIEW'
$p.successor_of=$prior
$p.reorder_authority=$elig
$p.observed_current_head=(git rev-parse HEAD).Trim();if($LASTEXITCODE -ne 0){throw 'git failure'}
$p.gate_source_head='4034f9d3c63acbb3a1b62a2683ed35c204923246'
$p.independent_readiness=$ready
$p.emitter=Bind "$out/emit-canonical-freeze-v3.ps1"
$p.expected_baseline_gates=$spec.gates
$p.required_readiness_sha256=@('aae24add096d1a78e6d1be0c75a5f9141703d196eb2a264f70ea51e74dc5e767','ded5adebef211f810552abbc4eced856dd9fff59f268989e9c1ff5a4ecd3d590','9b60dfbf2628a57e4411d9816849e88f802c305e78d7f58f581c1734bc649e1d','9d84f60e2a5f272922a68bb8c1745d98de4c7779e154a5e53fde4c4560525152','0a23a79c8f1c9a32059441af10f204c1bbe6afcdc27ed28cb684c52a07ed0665','7522a6a6cc07e7957f5be0bb3e1040469b424fc9f8af60d5cc11ba2c8ae569bf',$elig.sha256,'61cf1901a632aeee35ee71511ba53b115ae0958649ea78b786536a4404684ba1')
$p.required_current_dependencies=@($p.archival_rows|Where-Object {-not $_.source.StartsWith('tmp/')}|ForEach-Object {[ordered]@{path=$_.source;sha256=$_.sha256;bytes=$_.bytes}})
$already=@($p.archival_rows.source)
$inc=@($historical|Where-Object {$_.path -notin $already})+@($elig,(Bind "$rd/preproof-reorder-eligibility-v1.md"),(Bind "$rd/freeze-application-review-v2.json"),(Bind "$rd/freeze-application-review-v2.md"))
$reader=@($source.reader_state.actual_failure,$source.reader_state.actual_execution)
$inc+= $reader
$p.required_v3_increments=@($inc|ForEach-Object {[ordered]@{path=$_.path;sha256=$_.sha256;bytes=$_.bytes;destination=($p.canonical_run+'/v3-review-increments/'+$_.path)}})
$p.authorization_protocol=[ordered]@{action='AUTHORIZE_CANONICAL_FREEZE_ONLY';proposal_sha256='actual reviewed V3 proposal hash';emitter_sha256=$p.emitter.sha256;source_head='actual clean current HEAD';preproof_readiness=[ordered]@{path=$ready.path;sha256=$ready.sha256;head_json_pointer='/source_head';verdict_json_pointer='/status';success_verdict='PASS_PREPROOF_SOURCE_READINESS';maintenance_accepted_json_pointer='/maintenance_accepted';reader_pending_json_pointer='/reader_state/repair_pending';gate_source_head_json_pointer='/gate_source_head';raw_bindings_json_pointer='/static_archive_source_bindings';gates_json_pointer='/nine_baseline_gate_receipts'};freeze_application_review='Future exact independent V3 review path/SHA, head/verdict selectors as appropriate, exact proposal/emitter/readiness SHA selectors; success required';source_continuity_review='Only if actual current HEAD differs from4034: independently reviewed actual HEAD, original gate_source_head and readiness SHA';additional_archive_bindings='Optional explicit hash-bound rows under RUN/authorized-review-increments, including parent-readiness sidecar; no invented success';not_an_authorization=$true}
$p.emitter_scope='Exact canonical freeze evidence copy only after independent V3 design review, actual independent preproof readiness and parent exact authorization. No maintenance final acceptance prerequisite; no BODY/commit/native install.'
$p.remaining_gates=@('Independent V3 application design review','Parent canonical-freeze-only exact authorization','Applied canonical freeze independent review and clean commit','Separate bounded candidate BODY authorization','Future BODY/canary/source/semantic/root/Tests/fullharness/axiom/TYPE-VALUE/purification/reader/site/Exposition/contribution/PR gates at lifecycle boundaries')
$p.workflow_successor_delta='Only extra V1/V2 maintenance-final workflow condition replaced under explicit independent reorder authority. Historical source-contract V2/header and old prerequisite prose are immutable history; this V3 controls ordering only. maintenance_accepted=false, reader pending and IMPLEMENTATION_FAILED preserved; publication/merge/chapter gates not waived.'
$p.dynamic_archive_policy='Archive actual independent readiness, its nine gate receipts, independent V3 application review, explicit V3 history/reader failure increments, parent authorization, proposal and emitter. Optional exact parent sidecar or later reviews need additional_archive_bindings. No maintenance final success claim.'
Save 'canonical-freeze-application-proposal-v3.json' $p
Save 'application-repair-response-v3.json' ([ordered]@{status='V3_PREPROOF_ORDER_SUCCESSOR_AWAITING_DESIGN_REVIEW';proposal=Bind "$out/canonical-freeze-application-proposal-v3.json";emitter=$p.emitter;eligibility=$elig;independent_readiness=$ready;historical_v1_v2=$historical;static_rows=133;static_rows_unchanged=$true;mathematical_header_and_sourcecontract_unchanged=$true;maintenance_accepted=$false;reader_pending=$true;changes='Direct independently authored readiness plus independent application review binding; no redundant self-review or parent final-maintenance success. Safety from reviewed V2 retained.';remaining_gates=$p.remaining_gates;emitter_executed=$false;BODY=$false;tracked_edit=$false})
$errors=$null;$tokens=$null;[System.Management.Automation.Language.Parser]::ParseFile((Join-Path (Get-Location) "$out/emit-canonical-freeze-v3.ps1"),[ref]$tokens,[ref]$errors)|Out-Null;if($errors.Count){throw ($errors|Out-String)}
foreach($row in $p.archival_rows){$b=Bind $row.source;if($b.sha256 -ne $row.sha256 -or $b.bytes -ne $row.bytes){throw 'static source mismatch'}}
foreach($row in $p.required_v3_increments){$b=Bind $row.path;if($b.sha256 -ne $row.sha256){throw 'increment changed'}}
foreach($b in $historical){if((Bind $b.path).sha256 -ne $b.sha256){throw 'history changed'}}
Save 'application-verification-v3.json' ([ordered]@{status='STATIC_CHECKS_ONLY_NO_EXECUTION';static_rows_verified=133;V1_V2_preserved=$true;emitter_parse_errors=0;head=$p.observed_current_head;git_status=@(git status --porcelain=v1);independent_design_review='PENDING';maintenance_accepted=$false;reader_pending=$true;emitter_executed=$false;BODY=$false})
Save 'application-artifact-manifest-v3.json' (@(Get-ChildItem $out -File|Where-Object Name -Match '-v3\.'|ForEach-Object {Bind "$out/$($_.Name)"}))
@((Bind "$out/canonical-freeze-application-proposal-v3.json"),(Bind "$out/emit-canonical-freeze-v3.ps1"),(Bind "$out/application-repair-response-v3.json"))|ConvertTo-Json
