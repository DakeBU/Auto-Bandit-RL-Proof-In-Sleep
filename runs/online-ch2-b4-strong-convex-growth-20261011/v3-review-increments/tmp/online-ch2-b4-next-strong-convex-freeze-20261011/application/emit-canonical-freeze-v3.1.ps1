param([Parameter(Mandatory=$true)][string]$AuthorizationFile)
$ErrorActionPreference='Stop'
function GitChecked([string[]]$Argv){$result=@(& git @Argv);if($LASTEXITCODE -ne 0){throw "Git failed: $($Argv -join ' ')"};return ($result -join "`n").Trim()}
function Hash([string]$p){return (Get-FileHash -LiteralPath $p -Algorithm SHA256).Hash.ToLower()}
function JsonPointer($obj,[string]$pointer){if(-not $pointer.StartsWith('/')){throw 'Explicit JSON pointer required'};$v=$obj;foreach($key in $pointer.Substring(1).Split('/')){$key=$key.Replace('~1','/').Replace('~0','~');if($null -eq $v -or -not $v.Contains($key)){throw "Missing JSON pointer: $pointer"};$v=$v[$key]};return $v}
function RejectReparse([string]$p){$cursor=[IO.Path]::GetFullPath($p);while($cursor){if(Test-Path -LiteralPath $cursor){$item=Get-Item -LiteralPath $cursor -Force;if(($item.Attributes -band [IO.FileAttributes]::ReparsePoint) -ne 0){throw "Reparse point forbidden: $cursor"}};$parent=[IO.Path]::GetDirectoryName($cursor);if($parent -eq $cursor){break};$cursor=$parent}}
$root=GitChecked @('rev-parse','--show-toplevel')
$root=[IO.Path]::GetFullPath($root)
RejectReparse $root
$proposal=Join-Path $PSScriptRoot 'canonical-freeze-application-proposal-v3.1.json'
$p=Get-Content -LiteralPath $proposal -Raw|ConvertFrom-Json -AsHashtable
$a=Get-Content -LiteralPath $AuthorizationFile -Raw|ConvertFrom-Json -AsHashtable
$proposalHash=Hash $proposal
$emitterHash=Hash $PSCommandPath
$head=GitChecked @('rev-parse','HEAD')
if($a.action -ne 'AUTHORIZE_CANONICAL_FREEZE_ONLY' -or $a.proposal_sha256 -cne $proposalHash -or $a.emitter_sha256 -cne $emitterHash -or $a.source_head -cne $head){throw 'Exact parent proposal/emitter/actual HEAD authorization required'}
if((GitChecked @('status','--porcelain=v1')) -ne ''){throw 'Clean source context required'}
if($p.canonical_doc -cne 'docs/contracts/online-ch2-b4-strong-convex-growth-v1' -or $p.canonical_run -cne 'runs/online-ch2-b4-strong-convex-growth-20261011'){throw 'Canonical roots differ from reviewed scope'}
$approvedRoots=@([IO.Path]::GetFullPath((Join-Path $root $p.canonical_doc)),[IO.Path]::GetFullPath((Join-Path $root $p.canonical_run)))
foreach($ar in $approvedRoots){RejectReparse $ar}
function Destination([string]$relative){if([IO.Path]::IsPathRooted($relative)){throw 'Relative destination required'};$full=[IO.Path]::GetFullPath((Join-Path $root $relative));$inside=$false;foreach($ar in $approvedRoots){if($full.StartsWith($ar.TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar,[StringComparison]::OrdinalIgnoreCase)){$inside=$true}};if(-not $inside){throw "Destination outside normalized approved roots: $relative"};RejectReparse $full;return $full}
function SourcePath([string]$s){if([IO.Path]::IsPathRooted($s)){return [IO.Path]::GetFullPath($s)};return [IO.Path]::GetFullPath((Join-Path $root $s))}
function ReviewBinding($b,[string]$label,[bool]$needHead){
 if(-not $b.path -or $b.sha256 -notmatch '^[0-9a-f]{64}$'){throw "Exact $label path/hash required"}
 $src=SourcePath $b.path
 if((Hash $src) -cne $b.sha256){throw "$label receipt hash mismatch"}
 $o=Get-Content -LiteralPath $src -Raw|ConvertFrom-Json -AsHashtable
 if($needHead -and (JsonPointer $o $b.head_json_pointer) -cne $head){throw "$label accepted HEAD differs from actual HEAD"}
 $verdict=[string](JsonPointer $o $b.verdict_json_pointer)
 if($verdict -cne $b.success_verdict -or $verdict -notmatch '^(ACCEPTED|PASS)(_|$)' -or $verdict -match 'PENDING|STRUCTURAL|REPAIR|CONDITIONAL|ELIGIBLE|NOT_ACCEPTED'){throw "$label requires final successful bounded verdict"}
 return $o
}
$readiness=ReviewBinding $a.preproof_readiness 'preproof source readiness' $true
if((JsonPointer $readiness $a.preproof_readiness.verdict_json_pointer) -cne 'PASS_PREPROOF_SOURCE_READINESS' -or (JsonPointer $readiness $a.preproof_readiness.maintenance_accepted_json_pointer) -cne $false -or (JsonPointer $readiness $a.preproof_readiness.reader_pending_json_pointer) -cne $true){throw 'Exact readiness-only state required; maintenance not accepted and reader pending'}
if((JsonPointer $readiness $a.preproof_readiness.gate_source_head_json_pointer) -cne $p.gate_source_head){throw 'Historical gate source HEAD relabelled'}
$readinessText=Get-Content -LiteralPath (SourcePath $a.preproof_readiness.path) -Raw
foreach($pin in $p.required_readiness_sha256){if(-not $readinessText.Contains($pin)){throw 'Readiness omits reviewed source/header/topology/blind/eligibility pin'}}
$rawBindings=JsonPointer $readiness $a.preproof_readiness.raw_bindings_json_pointer
foreach($expected in $p.required_current_dependencies){$matches=@($rawBindings|Where-Object {([IO.Path]::GetFullPath((SourcePath $_.path))) -ieq ([IO.Path]::GetFullPath((SourcePath $expected.path))) -and $_.sha256 -ceq $expected.sha256});if($matches.Count -ne 1 -or (Hash (SourcePath $expected.path)) -cne $expected.sha256){throw 'Readiness omits or changes current key raw dependency'}}
$gates=JsonPointer $readiness $a.preproof_readiness.gates_json_pointer
if(@($gates).Count -ne 9){throw 'Nine actual 4034 gate bindings required'}
foreach($expected in $p.expected_baseline_gates){$matches=@($gates|Where-Object {$_.path -ceq $expected.receipt.path -and $_.sha256 -ceq $expected.receipt.sha256});if($matches.Count -ne 1){throw 'Readiness gate binding differs'};$src=SourcePath $matches[0].path;if((Hash $src) -cne $matches[0].sha256){throw 'Gate receipt changed'};$gr=Get-Content -LiteralPath $src -Raw|ConvertFrom-Json -AsHashtable;if($gr.actual_exit -ne 0 -or $gr.capture_integrity_ok -cne $true -or $gr.pre_git.HEAD -cne $p.gate_source_head -or $gr.post_git.HEAD -cne $p.gate_source_head){throw 'Invalid actual baseline gate'}}
if($head -cne $p.gate_source_head){$continuity=ReviewBinding $a.source_continuity_review 'independent source continuity review' $true;if((JsonPointer $continuity $a.source_continuity_review.gate_source_head_json_pointer) -cne $p.gate_source_head -or (JsonPointer $continuity $a.source_continuity_review.readiness_sha256_json_pointer) -cne $a.preproof_readiness.sha256){throw 'Changed HEAD requires exact reviewed continuity'}}
$freezeReview=ReviewBinding $a.freeze_application_review 'independent freeze application V3 review' $false
if((JsonPointer $freezeReview $a.freeze_application_review.readiness_sha256_json_pointer) -cne $a.preproof_readiness.sha256){throw 'Independent application review must bind the independent readiness report'}
if((JsonPointer $freezeReview $a.freeze_application_review.proposal_sha256_json_pointer) -cne $proposalHash -or (JsonPointer $freezeReview $a.freeze_application_review.emitter_sha256_json_pointer) -cne $emitterHash){throw 'Independent application review does not bind executing proposal/emitter'}
$rows=[Collections.Generic.List[object]]::new()
foreach($row in $p.archival_rows){$rows.Add($row)}
function AddExact([string]$src,[string]$dest,[string]$expected){$src=SourcePath $src;$f=Get-Item -LiteralPath $src;if((Hash $src) -cne $expected){throw 'Dynamic archive binding mismatch'};$rows.Add([ordered]@{source=$src;destination=$dest;sha256=$expected;bytes=$f.Length})}
AddExact $a.preproof_readiness.path ($p.canonical_run+'/preproof-readiness/readiness.json') $a.preproof_readiness.sha256
if($a.source_continuity_review){AddExact $a.source_continuity_review.path ($p.canonical_run+'/preproof-readiness/source-continuity-review.json') $a.source_continuity_review.sha256}
foreach($g in $p.expected_baseline_gates){AddExact $g.receipt.path ($p.canonical_run+'/preproof-readiness/gates/'+$g.role+'/receipt.json') $g.receipt.sha256}
foreach($inc in $p.required_v3_increments){AddExact $inc.path $inc.destination $inc.sha256}
AddExact $a.freeze_application_review.path ($p.canonical_run+'/freeze-review/independent-application-review-v3.1.json') $a.freeze_application_review.sha256
foreach($extra in @($a.additional_archive_bindings)){if($null -eq $extra){continue};if(-not $extra.destination.StartsWith($p.canonical_run+'/authorized-review-increments/')){throw 'Additional archive must use authorized-review-increments subtree'};AddExact $extra.path $extra.destination $extra.sha256}
AddExact $proposal ($p.canonical_doc+'/canonical-freeze-application-proposal-v3.1.json') $proposalHash
AddExact $PSCommandPath ($p.canonical_run+'/plans/emit-canonical-freeze-v3.1.ps1') $emitterHash
$authHash=Hash $AuthorizationFile
AddExact $AuthorizationFile ($p.canonical_doc+'/parent-freeze-authorization-v3.1.json') $authHash
$destinations=[Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
foreach($r in $rows){$dest=Destination $r.destination;if(-not $destinations.Add($dest)){throw 'Duplicate destination'};if(Test-Path -LiteralPath $dest){throw "Destination exists: $dest"};$src=SourcePath $r.source;$f=Get-Item -LiteralPath $src;if($f.Length -ne $r.bytes -or (Hash $src) -cne $r.sha256){throw "Source changed: $src"}}
$receipt=Destination ($p.canonical_doc+'/freeze-application-receipt-v3.1.json')
if(-not $destinations.Add($receipt) -or (Test-Path -LiteralPath $receipt)){throw 'Receipt collision'}
if((GitChecked @('rev-parse','HEAD')) -cne $head -or (GitChecked @('status','--porcelain=v1')) -ne ''){throw 'Context changed during preflight'}
foreach($r in $rows){$src=SourcePath $r.source;$dest=Destination $r.destination;if((Hash $src) -cne $r.sha256){throw 'Source changed before copy'};[IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($dest))|Out-Null;RejectReparse $dest;[IO.File]::Copy($src,$dest,$false);if((Hash $dest) -cne $r.sha256){throw 'Copied bytes mismatch'}}
$receipt=Destination ($p.canonical_doc+'/freeze-application-receipt-v3.1.json')
$r=[ordered]@{status='CANONICAL_FREEZE_EVIDENCE_COPIED_NO_BODY_AUTHORIZATION';source_head=$head;proposal_sha256=$proposalHash;emitter_sha256=$emitterHash;authorization_sha256=$authHash;preproof_readiness=$a.preproof_readiness;maintenance_accepted=$false;reader_pending=$true;gate_source_head=$p.gate_source_head;freeze_application_review=$a.freeze_application_review;archival_rows=@($rows.ToArray());header_sha256=$p.header_sha256;BODY=$false;proof_acceptance=$false;native_manifest_installed=$false;commit_created=$false;next='Commit and independently verify clean preproof context; separate explicit BODY authorization required'}
$bytes=[Text.UTF8Encoding]::new($false).GetBytes(($r|ConvertTo-Json -Depth 40)+"`n")
$stream=[IO.File]::Open($receipt,[IO.FileMode]::CreateNew,[IO.FileAccess]::Write,[IO.FileShare]::None)
try{$stream.Write($bytes,0,$bytes.Length);$stream.Flush()}finally{$stream.Dispose()}
Write-Output "Freeze evidence copied; receipt: $receipt; no BODY authorization."
