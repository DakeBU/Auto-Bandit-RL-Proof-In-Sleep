from common_v1 import *
fixed(proving=True,integrated=True)
raw=(RUN/'main-relative-diagnostic-v1.log').read_text(encoding='utf-8');gaps=sorted(set(re.findall(r'BanditRLProof/OnlineLearning\w+\.lean',raw)))
expected=sorted('BanditRLProof/OnlineLearning'+n+'.lean' for n in ['Asymptotic','Foundations','History','IID','Information','Regret','Stochastic'])
assert gaps==expected and load(RUN/'main-relative-diagnostic-v1-exit.json')['exit_code']==1
write(RUN/'main-diagnostic-parser-repair-v2.json',dict(actual_failed_helper='source-site-gates-v1.py, exit1 after contributor/scoped/source passed',reason='Old helper matched per-file missing-valid-contract wording; actual current checker emits one production paths missing from all changed contribution manifests aggregate line.',original_raw_log_sha256=sha(RUN/'main-relative-diagnostic-v1.log'),actual_gate_exit_code=1,actual_gaps=gaps,repair='Parse exact paths from actual aggregate failure; preserve FAILUNWAIVED/no gate waiver, no mathematical edits.'))
native('main-parser-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(scope='Diagnostic parser only',repair=(RUN/'main-diagnostic-parser-repair-v2.json').as_posix(),math_targets_unchanged=True)))
native('main-parser-candidate-event-v2','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(scope='Same compiled frozen proofs; actual main gap remains fail-unwaived',math_targets_unchanged=True)))
s=(RUN/'source-site-gates-v1.py').read_text(encoding='utf-8');tail=s[s.index("write(RUN/'main-relative-diagnostic-v1.json'"):]
tail=tail.replace("child.returncode==0","actual_exit==0",1).replace("actual_exit_code=child.returncode","actual_exit_code=actual_exit",1)
marker="subprocess.run([sys.executable,'-B','-X','utf8',RUN/'commit-owned-v1.py','Record exact-base acceptance checks and actual unwaived main gaps'],check=True)"
assert marker in tail
replacement="""subprocess.run([sys.executable,'-B','-X','utf8',RUN/'commit-owned-v1.py','Record actual seven main gaps and diagnostic parser repair'],check=True)
gate('contributor-reader-v2',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-reader-v2',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','reader-v2')
gate('source-scope-reader-v2',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','reader-v2')
native('full-harness-reader-v2','check')
raw=(RUN/'full-harness-reader-v2.log').read_text(encoding='utf-8');assert 'Ran 466 tests' in raw and 'OK (skipped=7)' in raw and 'check passed' in raw
write(RUN/'combined-gates-reader-v2.json',{**load(RUN/'combined-gates-v1.json'),'current_reader_main_gap_boundary_checked':True,'current_harness_log_sha256':sha(RUN/'full-harness-reader-v2.log')})
subprocess.run([sys.executable,'-B','-X','utf8',RUN/'commit-owned-v1.py','Bind current FTL-state reader and source-scope gates'],check=True)"""
tail=tail.replace(marker,replacement)
write(RUN/'continue-source-site-v2.py',"from common_v1 import *\nfixed(proving=True,integrated=True)\nactual_exit=load(RUN/'main-relative-diagnostic-v1-exit.json')['exit_code']\nraw=(RUN/'main-relative-diagnostic-v1.log').read_text(encoding='utf-8')\ngaps=sorted(set(re.findall(r'BanditRLProof/OnlineLearning\\w+\\.lean',raw)))\nassert actual_exit==1 and len(gaps)==7\n"+tail)
