$ErrorActionPreference='Stop'
$out='tmp/online-ch2-b4-next-strong-convex-freeze-20261011/application'
function Bind([string]$s){$f=Get-Item -LiteralPath $s;[ordered]@{path=$s;sha256=(Get-FileHash -LiteralPath $s -Algorithm SHA256).Hash.ToLower();bytes=$f.Length}}
function SaveText([string]$n,[string]$s){$p=Join-Path (Get-Location) "$out/$n";if(Test-Path $p){throw 'exists'};[IO.File]::WriteAllText($p,$s,[Text.UTF8Encoding]::new($false))}
function Save([string]$n,$o){SaveText $n (($o|ConvertTo-Json -Depth 90)+"`n")}
$p=Get-Content "$out/canonical-freeze-application-proposal-v3.1.json" -Raw|ConvertFrom-Json -AsHashtable
$p.archival_rows=@($p.archival_rows[0..132])
$attr=Bind "$out/canonical-byte-preservation.gitattributes"
foreach($dest in @(($p.canonical_doc+'/.gitattributes'),($p.canonical_run+'/.gitattributes'))){$p.archival_rows+= [ordered]@{source=$attr.path;destination=$dest;sha256=$attr.sha256;bytes=$attr.bytes;purpose='Exact-byte archival protection; ASCII LF'}}
$p.status='V3_2_PREPROOF_ONLY_BYTE_PRESERVATION_UNEXECUTED'
$p.successor_of=Bind "$out/canonical-freeze-application-proposal-v3.1.json"
$p.assembly_repair='V3.1 rejected before execution: PowerShell concatenation combined attribute destinations into one string. V3.2 creates two separately parenthesized destinations; historical failed candidate preserved.'
$e=Get-Content "$out/emit-canonical-freeze-v3.1.ps1" -Raw
$e=$e.Replace('-v3.1.','-v3.2.')
SaveText 'emit-canonical-freeze-v3.2.ps1' $e
$p.emitter=Bind "$out/emit-canonical-freeze-v3.2.ps1"
$p.authorization_protocol.emitter_sha256=$p.emitter.sha256
foreach($f in Get-ChildItem $out -File|Where-Object Name -Match '-v3\.1\.'){ $b=Bind "$out/$($f.Name)";$p.required_v3_increments+=[ordered]@{path=$b.path;sha256=$b.sha256;bytes=$b.bytes;destination=($p.canonical_run+'/v3-review-increments/'+$b.path)}}
Save 'canonical-freeze-application-proposal-v3.2.json' $p
$root=(Get-Location).Path
$seen=[Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
foreach($r in $p.archival_rows){$b=Bind $r.source;if($b.sha256 -ne $r.sha256 -or $b.bytes -ne $r.bytes){throw 'static mismatch'};if(-not $seen.Add([IO.Path]::GetFullPath((Join-Path $root $r.destination)))){throw 'duplicate'}}
if($p.archival_rows.Count -ne 135){throw 'expected135'}
if($p.archival_rows[133].destination -cne ($p.canonical_doc+'/.gitattributes') -or $p.archival_rows[134].destination -cne ($p.canonical_run+'/.gitattributes')){throw 'attrs bad'}
$old=Get-Content "$out/canonical-freeze-application-proposal-v2.json" -Raw|ConvertFrom-Json -AsHashtable
if(($old.archival_rows|ConvertTo-Json -Depth 20 -Compress) -cne ($p.archival_rows[0..132]|ConvertTo-Json -Depth 20 -Compress)){throw 'original rows changed'}
$err=$null;$tok=$null;[System.Management.Automation.Language.Parser]::ParseFile((Join-Path $root "$out/emit-canonical-freeze-v3.2.ps1"),[ref]$tok,[ref]$err)|Out-Null;if($err.Count){throw 'parse errors'}
Save 'application-repair-response-v3.2.json' ([ordered]@{status='READY_FOR_DISTINCT_DESIGN_REVIEW_NOT_EXECUTED';proposal=Bind "$out/canonical-freeze-application-proposal-v3.2.json";emitter=$p.emitter;original133_exact=$true;static135_hash_sizes_and_unique_destinations=$true;attrs_destinations=@($p.archival_rows[133].destination,$p.archival_rows[134].destination);V3_1_assembly_failure_retained=$true;emitter_parse_errors=0;maintenance_accepted=$false;reader_pending=$true;head=(git rev-parse HEAD).Trim();git_status=@(git status --porcelain=v1);BODY=$false;tracked_edits=$false})
Save 'application-artifact-manifest-v3.2.json' (@(Get-ChildItem $out -File|Where-Object Name -Match '-v3\.2\.'|ForEach-Object {Bind "$out/$($_.Name)"}))
@((Bind "$out/canonical-freeze-application-proposal-v3.2.json"),$p.emitter,(Bind "$out/application-repair-response-v3.2.json"))|ConvertTo-Json
