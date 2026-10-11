param([Parameter(Mandatory=$true)][string]$AuthorizationFile)
$ErrorActionPreference='Stop'
$root=(git rev-parse --show-toplevel).Trim()
$proposal=Join-Path $PSScriptRoot 'canonical-freeze-application-proposal-v1.json'
$p=Get-Content -LiteralPath $proposal -Raw|ConvertFrom-Json
$a=Get-Content -LiteralPath $AuthorizationFile -Raw|ConvertFrom-Json
$proposalHash=(Get-FileHash -LiteralPath $proposal -Algorithm SHA256).Hash.ToLower()
$head=(git rev-parse HEAD).Trim()
if($a.action -ne 'AUTHORIZE_CANONICAL_FREEZE_ONLY' -or $a.proposal_sha256 -ne $proposalHash -or $a.source_head -ne $head -or $a.maintenance_final_accepted -ne $true){throw 'Parent explicit matching freeze authorization and maintenance final acceptance required'}
if(@(git status --porcelain=v1).Count -ne 0){throw 'Clean source context required'}
function ResolveWorkspace([string]$relative){$full=[IO.Path]::GetFullPath((Join-Path $root $relative));if(-not $full.StartsWith($root.TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar,[StringComparison]::OrdinalIgnoreCase)){throw 'Destination escapes workspace'};return $full}
$destinations=[Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
foreach($r in $p.archival_rows){
 if(-not ($r.destination.StartsWith($p.canonical_doc+'/') -or $r.destination.StartsWith($p.canonical_run+'/'))){throw 'Out-of-scope destination'}
 $dest=ResolveWorkspace $r.destination
 if(-not $destinations.Add($dest)){throw 'Duplicate destination'}
 if(Test-Path -LiteralPath $dest){throw "Destination already exists: $dest"}
 $src=if([IO.Path]::IsPathRooted($r.source)){$r.source}else{Join-Path $root $r.source}
 $f=Get-Item -LiteralPath $src
 if($f.Length -ne $r.bytes -or (Get-FileHash -LiteralPath $src -Algorithm SHA256).Hash.ToLower() -ne $r.sha256){throw "Source changed: $src"}
}
foreach($reserved in @(($p.canonical_doc+'/canonical-freeze-application-proposal-v1.json'),($p.canonical_doc+'/parent-freeze-authorization-v1.json'),($p.canonical_doc+'/freeze-application-receipt-v1.json'),($p.canonical_run+'/plans/emit-canonical-freeze-v1.ps1'))){$dest=ResolveWorkspace $reserved;if(Test-Path -LiteralPath $dest){throw 'Reserved destination exists'};if(-not $destinations.Add($dest)){throw 'Reserved destination collision'}}
$receipt=ResolveWorkspace ($p.canonical_doc+'/freeze-application-receipt-v1.json')
if(Test-Path -LiteralPath $receipt){throw 'Receipt already exists'}
foreach($r in $p.archival_rows){$src=if([IO.Path]::IsPathRooted($r.source)){$r.source}else{Join-Path $root $r.source};$dest=ResolveWorkspace $r.destination;[IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($dest))|Out-Null;[IO.File]::Copy($src,$dest,$false);if((Get-FileHash -LiteralPath $dest -Algorithm SHA256).Hash.ToLower() -ne $r.sha256){throw 'Copied hash mismatch'}}
foreach($pair in @(@($proposal,($p.canonical_doc+'/canonical-freeze-application-proposal-v1.json')),@($AuthorizationFile,($p.canonical_doc+'/parent-freeze-authorization-v1.json')),@($PSCommandPath,($p.canonical_run+'/plans/emit-canonical-freeze-v1.ps1')))){$dest=ResolveWorkspace $pair[1];[IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($dest))|Out-Null;[IO.File]::Copy($pair[0],$dest,$false)}
$r=[ordered]@{status='CANONICAL_FREEZE_EVIDENCE_COPIED_NO_BODY_AUTHORIZATION';source_head=$head;proposal_sha256=$proposalHash;authorization_sha256=(Get-FileHash -LiteralPath $AuthorizationFile -Algorithm SHA256).Hash.ToLower();header_sha256=$p.header_sha256;rows_verified=$p.archival_rows.Count;BODY=$false;proof_acceptance=$false;native_manifest_installed=$false;commit_created=$false;next='Parent commit and independent clean preproof context verification, then separate explicit BODY authorization'}
[IO.File]::WriteAllText($receipt,($r|ConvertTo-Json -Depth 10)+"`n",[Text.UTF8Encoding]::new($false))
$r|ConvertTo-Json
