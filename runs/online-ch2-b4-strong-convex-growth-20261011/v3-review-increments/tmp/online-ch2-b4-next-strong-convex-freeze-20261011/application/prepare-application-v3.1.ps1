$ErrorActionPreference='Stop'
$out='tmp/online-ch2-b4-next-strong-convex-freeze-20261011/application'
function Bind([string]$s){$f=Get-Item -LiteralPath $s;[ordered]@{path=$s;sha256=(Get-FileHash -LiteralPath $s -Algorithm SHA256).Hash.ToLower();bytes=$f.Length}}
function TextNew([string]$n,[string]$s){$p=Join-Path (Get-Location) "$out/$n";if(Test-Path $p){throw 'create only'};[IO.File]::WriteAllText($p,$s,[Text.UTF8Encoding]::new($false))}
function Save([string]$n,$o){TextNew $n (($o|ConvertTo-Json -Depth 90)+"`n")}
TextNew 'canonical-byte-preservation.gitattributes' "* -text`n* whitespace=cr-at-eol,-blank-at-eof`n*.png -diff`n*.zip -diff`n*.raw -diff`n*.diff -diff`n"
$p=Get-Content "$out/canonical-freeze-application-proposal-v3.json" -Raw|ConvertFrom-Json -AsHashtable
$attr=Bind "$out/canonical-byte-preservation.gitattributes"
foreach($dest in @($p.canonical_doc+'/.gitattributes',$p.canonical_run+'/.gitattributes')){$p.archival_rows+= [ordered]@{source=$attr.path;destination=$dest;sha256=$attr.sha256;bytes=$attr.bytes;purpose='Exact-byte archival protection under core.autocrlf=true; ASCII LF attrs; no mathematical change'}}
$p.successor_of=Bind "$out/canonical-freeze-application-proposal-v3.json"
$p.byte_preservation='133 original V2 rows unchanged in order +2 .gitattributes rows; raw archives/header remain byte-exact through Git commit; no mathematical premise added'
$p.status='V3_1_PREPROOF_ONLY_WITH_BYTE_PRESERVATION_UNEXECUTED'
$e=Get-Content "$out/emit-canonical-freeze-v3.ps1" -Raw
foreach($name in @('canonical-freeze-application-proposal','emit-canonical-freeze','parent-freeze-authorization','freeze-application-receipt','independent-application-review')){$e=$e.Replace($name+'-v3.',$name+'-v3.1.')}
TextNew 'emit-canonical-freeze-v3.1.ps1' $e
$p.emitter=Bind "$out/emit-canonical-freeze-v3.1.ps1"
$p.authorization_protocol.emitter_sha256=$p.emitter.sha256
foreach($f in Get-ChildItem $out -File|Where-Object Name -Match '-v3\.'){ $b=Bind "$out/$($f.Name)"; $p.required_v3_increments+= [ordered]@{path=$b.path;sha256=$b.sha256;bytes=$b.bytes;destination=($p.canonical_run+'/v3-review-increments/'+$b.path)}}
Save 'canonical-freeze-application-proposal-v3.1.json' $p
Save 'application-repair-response-v3.1.json' ([ordered]@{status='BYTE_PRESERVATION_ADDED_NO_EXECUTION';successor_of=Bind "$out/application-repair-response-v3.json";proposal=Bind "$out/canonical-freeze-application-proposal-v3.1.json";emitter=$p.emitter;original_rows_unchanged=133;attributes_rows_added=2;attributes_source=$attr;mathematical_header_sourcecontract_unchanged=$true;maintenance_accepted=$false;reader_pending=$true;BODY=$false;tracked_edits=$false})
$err=$null;$tok=$null;[System.Management.Automation.Language.Parser]::ParseFile((Join-Path (Get-Location) "$out/emit-canonical-freeze-v3.1.ps1"),[ref]$tok,[ref]$err)|Out-Null;if($err.Count){throw ($err|Out-String)}
foreach($r in $p.archival_rows){$b=Bind $r.source;if($b.sha256 -ne $r.sha256 -or $b.bytes -ne $r.bytes){throw 'static mismatch'}}
$old=Get-Content "$out/canonical-freeze-application-proposal-v2.json" -Raw|ConvertFrom-Json -AsHashtable
if(($old.archival_rows|ConvertTo-Json -Depth 20 -Compress) -cne ($p.archival_rows[0..132]|ConvertTo-Json -Depth 20 -Compress)){throw 'original rows changed'}
Save 'application-verification-v3.1.json' ([ordered]@{static_rows_verified=135;original133_exact=$true;emitter_parse_errors=0;head=(git rev-parse HEAD).Trim();status=@(git status --porcelain=v1);emitter_executed=$false;BODY=$false;maintenance_accepted=$false;reader_pending=$true})
Save 'application-artifact-manifest-v3.1.json' (@(Get-ChildItem $out -File|Where-Object Name -Match '-v3\.1\.'|ForEach-Object {Bind "$out/$($_.Name)"}))
@((Bind "$out/canonical-freeze-application-proposal-v3.1.json"),$p.emitter,(Bind "$out/application-repair-response-v3.1.json"))|ConvertTo-Json
