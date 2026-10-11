from pathlib import Path
p=Path('tmp/online-ch2-b4-next-strong-convex-freeze-20261011/application')
e=(p/'emit-canonical-freeze-v2.ps1').read_text(encoding='utf-8-sig')
for a,b in [('canonical-freeze-application-proposal-v2','canonical-freeze-application-proposal-v3'),('emit-canonical-freeze-v2','emit-canonical-freeze-v3'),('parent-freeze-authorization-v2','parent-freeze-authorization-v3'),('freeze-application-receipt-v2','freeze-application-receipt-v3'),('independent-application-review-v2','independent-application-review-v3'),('application V2 review','application V3 review')]: e=e.replace(a,b)
a=e.index('$maintenance=ReviewBinding');b=e.index('$freezeReview=ReviewBinding')
e=e[:a]+r'''$readiness=ReviewBinding $a.preproof_readiness 'preproof source readiness' $true
if((JsonPointer $readiness $a.preproof_readiness.verdict_json_pointer) -cne 'PASS_PREPROOF_SOURCE_READINESS' -or (JsonPointer $readiness $a.preproof_readiness.maintenance_accepted_json_pointer) -cne $false -or (JsonPointer $readiness $a.preproof_readiness.reader_pending_json_pointer) -cne $true){throw 'Exact readiness-only state required; maintenance not accepted and reader pending'}
$readinessReview=ReviewBinding $a.preproof_readiness_review 'independent preproof readiness review' $true
if((JsonPointer $readinessReview $a.preproof_readiness_review.readiness_sha256_json_pointer) -cne $a.preproof_readiness.sha256){throw 'Independent review must bind actual readiness receipt'}
if((JsonPointer $readiness $a.preproof_readiness.gate_source_head_json_pointer) -cne $p.gate_source_head){throw 'Historical gate source HEAD relabelled'}
$readinessText=Get-Content -LiteralPath (SourcePath $a.preproof_readiness.path) -Raw
foreach($pin in $p.required_readiness_sha256){if(-not $readinessText.Contains($pin)){throw 'Readiness omits reviewed source/header/topology/blind/eligibility pin'}}
$rawBindings=JsonPointer $readiness $a.preproof_readiness.raw_bindings_json_pointer
foreach($expected in $p.required_current_dependencies){$matches=@($rawBindings|Where-Object {([IO.Path]::GetFullPath((SourcePath $_.path))) -ieq ([IO.Path]::GetFullPath((SourcePath $expected.path))) -and $_.sha256 -ceq $expected.sha256});if($matches.Count -ne 1 -or (Hash (SourcePath $expected.path)) -cne $expected.sha256){throw 'Readiness omits or changes current key raw dependency'}}
$gates=JsonPointer $readiness $a.preproof_readiness.gates_json_pointer
if(@($gates).Count -ne 9){throw 'Nine actual 4034 gate bindings required'}
foreach($expected in $p.expected_baseline_gates){$matches=@($gates|Where-Object {$_.role -ceq $expected.role -and $_.path -ceq $expected.receipt.path -and $_.sha256 -ceq $expected.receipt.sha256});if($matches.Count -ne 1){throw 'Readiness gate binding differs'};$src=SourcePath $matches[0].path;if((Hash $src) -cne $matches[0].sha256){throw 'Gate receipt changed'};$gr=Get-Content -LiteralPath $src -Raw|ConvertFrom-Json -AsHashtable;if($gr.actual_exit -ne 0 -or $gr.capture_integrity_ok -cne $true -or $gr.pre_git.HEAD -cne $p.gate_source_head -or $gr.post_git.HEAD -cne $p.gate_source_head){throw 'Invalid actual baseline gate'}}
if($head -cne $p.gate_source_head){$continuity=ReviewBinding $a.source_continuity_review 'independent source continuity review' $true;if((JsonPointer $continuity $a.source_continuity_review.gate_source_head_json_pointer) -cne $p.gate_source_head -or (JsonPointer $continuity $a.source_continuity_review.readiness_sha256_json_pointer) -cne $a.preproof_readiness.sha256){throw 'Changed HEAD requires exact reviewed continuity'}}
''' + e[b:]
a=e.index('AddExact $a.maintenance_final_receipt.path');b=e.index('AddExact $a.freeze_application_review.path')
e=e[:a]+r'''AddExact $a.preproof_readiness.path ($p.canonical_run+'/preproof-readiness/readiness.json') $a.preproof_readiness.sha256
AddExact $a.preproof_readiness_review.path ($p.canonical_run+'/preproof-readiness/independent-review.json') $a.preproof_readiness_review.sha256
if($a.source_continuity_review){AddExact $a.source_continuity_review.path ($p.canonical_run+'/preproof-readiness/source-continuity-review.json') $a.source_continuity_review.sha256}
foreach($g in $gates){AddExact $g.path ($p.canonical_run+'/preproof-readiness/gates/'+$g.role+'/receipt.json') $g.sha256}
foreach($inc in $p.required_v3_increments){AddExact $inc.path $inc.destination $inc.sha256}
''' + e[b:]
e=e.replace('maintenance_final_receipt=$a.maintenance_final_receipt;maintenance_final_review=$a.maintenance_final_review;', 'preproof_readiness=$a.preproof_readiness;preproof_readiness_review=$a.preproof_readiness_review;maintenance_accepted=$false;reader_pending=$true;gate_source_head=$p.gate_source_head;')
with (p/'emit-canonical-freeze-v3.ps1').open('x',encoding='utf-8',newline='\n') as f:f.write(e)
