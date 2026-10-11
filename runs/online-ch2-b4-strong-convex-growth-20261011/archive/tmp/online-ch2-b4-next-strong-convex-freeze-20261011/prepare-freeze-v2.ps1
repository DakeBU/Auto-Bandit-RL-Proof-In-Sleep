$ErrorActionPreference='Stop'
$root=(Get-Location).Path
$out='tmp/online-ch2-b4-next-strong-convex-freeze-20261011'
function Bind([string]$path) {$f=Get-Item -LiteralPath $path; [ordered]@{path=$path;sha256=(Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLower();bytes=$f.Length}}
function Save([string]$name,$obj) {$p=Join-Path $root "$out/$name"; if(Test-Path -LiteralPath $p){throw "Refusing overwrite: $p"}; [IO.File]::WriteAllText($p,($obj|ConvertTo-Json -Depth 90)+"`n",[Text.UTF8Encoding]::new($false))}
$audit='tmp/online-ch2-b4-next-strong-convex-freeze-audit-20261011/freeze-contract-review-v1.json'
if((Bind $audit).sha256 -ne '530c3f5257342cbef44f32b9a8cd53781b84948671bbfef424ba08a6e5558d02'){throw 'Audit hash mismatch'}
$oldFiles=@(Get-ChildItem $out -File | Where-Object {$_.Name -match '-v1\.'} | ForEach-Object {Bind "$out/$($_.Name)"})
$head=(git rev-parse HEAD).Trim(); $before=@(git status --porcelain=v1)
$c=Get-Content "$out/source-contract-proposal-v1.json" -Raw|ConvertFrom-Json -AsHashtable
$c.schema_version=2
$c.status='V2_METADATA_REPAIR_PROPOSAL_ONLY_NOT_FROZEN_NO_BODY_AUTHORIZATION'
$c.successor_of=Bind "$out/source-contract-proposal-v1.json"
$c.repair_audit=Bind $audit
$c.binder_audit_historical=[ordered]@{status='HISTORICAL_ORIGINAL_PROPOSAL_NOT_AUTHORITATIVE';authority='Superseded as classification authority by authoritative_reviewed_binder_audit; retained without editing original artifact bytes';original=$c.binder_audit}
$c.Remove('binder_audit')
$r=Get-Content 'tmp/online-ch2-b4-next-strong-convex-source-review-20261011/source-header-review-v1.json' -Raw | ConvertFrom-Json -AsHashtable
$c.authoritative_reviewed_binder_audit=[ordered]@{authority='Independent source-header-review-v1 atomic_binders; classification overlay requested by freeze-contract-review-v1';source_review=Bind 'tmp/online-ch2-b4-next-strong-convex-source-review-20261011/source-header-review-v1.json';atomic_binders=$r.atomic_binders;conditional_target_overlay=@([ordered]@{binder='hp';classification='CONDITIONAL_TARGET';meaning='Supplied feasible minimum point p in literal V'},[ordered]@{binder='hmin';classification='CONDITIONAL_TARGET';meaning='Supplied attained minimum order IsMinOn f V p; actual algorithm producer remains OPEN'},[ordered]@{binder='hq';classification='CONDITIONAL_TARGET';meaning='Supplied comparator q in literal V'});scope='These binders belong to the explicit conditional target, not source existence claims or discharged cumulative producer results';header_changed=$false;excess_found=$false}
$c.chapter_state.accepted=$false
$c.chapter_state.complete_proof_denominator=$null
Save 'source-contract-proposal-v2.json' $c
$check=Get-Content "$out/preproof-checklist-v1.json" -Raw|ConvertFrom-Json -AsHashtable
$check.status='V2_METADATA_REPAIRED_AWAITING_DISTINCT_REREVIEW'
$check.successor_of=Bind "$out/preproof-checklist-v1.json"
$check.metadata_repairs=@('META-BINDERS applied: authoritative CONDITIONAL_TARGET overlay; old binder audit historical','META-STATE applied: accepted false; complete_proof_denominator null')
Save 'preproof-checklist-v2.json' $check
Save 'leaf-freeze-proposal-v2.json' ([ordered]@{status='AWAITING_INDEPENDENT_V2_FREEZE_AUDIT';successor_of=Bind "$out/leaf-freeze-proposal-v1.json";source_contract=Bind "$out/source-contract-proposal-v2.json";header=Bind "$out/neutral-proposed-frozen-header-v1.txt";checklist=Bind "$out/preproof-checklist-v2.json";not_a_receipt=$true;authorization_granted=$false;head=$head;scope='One conditional growth theorem only; metadata repair only';canonical_changes=$false})
Save 'metadata-repair-response-v2.json' ([ordered]@{status='APPLIED_AWAITING_DISTINCT_REREVIEW';audit=Bind $audit;repairs=@([ordered]@{id='META-BINDERS';resolution='Moved original embedded binder audit to explicitly historical nonauthoritative object. Authoritative independent atomic audit plus explicit hp/hmin/hq CONDITIONAL_TARGET overlay added.'},[ordered]@{id='META-STATE';resolution='chapter_state.accepted=false; chapter_state.complete_proof_denominator=null'});v1_preserved=$oldFiles;math_header_change=$false;topology_change=$false;source_inventory_change=$false;BODY=$false;proof_search=$false;tracked_edit=$false;authorization=$false;successor=Bind "$out/source-contract-proposal-v2.json"})
$bad=@($oldFiles|Where-Object {(Bind $_.path).sha256 -ne $_.sha256}); if($bad.Count){throw 'V1 changed'}
$hdr=Bind "$out/neutral-proposed-frozen-header-v1.txt"; if($hdr.sha256 -ne 'ded5adebef211f810552abbc4eced856dd9fff59f268989e9c1ff5a4ecd3d590'){throw 'Header changed'}
Save 'preparation-verification-v2.json' ([ordered]@{v1_files_unchanged=$true;v1_file_count=$oldFiles.Count;header_unchanged=$true;header=$hdr;head_before=$head;head_after=(git rev-parse HEAD).Trim();status_before=$before;status_after=@(git status --porcelain=v1);BODY=$false;proof_search=$false;tracked_edit=$false;build=$false;independent_rereview='PENDING'})
Save 'artifact-manifest-v2.json' ([ordered]@{schema_version=2;status='METADATA_REPAIR_PROPOSAL';v1_manifest=Bind "$out/artifact-manifest-v1.json";artifacts=@(Get-ChildItem $out -File|Where-Object {$_.Name -match '-v2\.' -and $_.Name -ne 'artifact-manifest-v2.json'}|ForEach-Object {Bind "$out/$($_.Name)"})})
Get-ChildItem $out -File | Where-Object {$_.Name -match '-v2\.'} | ForEach-Object {Bind "$out/$($_.Name)"} | ConvertTo-Json -Depth 5
