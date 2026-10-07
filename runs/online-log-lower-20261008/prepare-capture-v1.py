from common_integrated_v1 import *
fixed_integrated()
old=Path('runs/online-regret-domains-20261007/capture-reader-v1.cjs')
s=old.read_text(encoding='utf8')
s=s.replace("const names=['comparatorRegret','NoRegret','comparatorRegret_eq_sum','noRegret_of_vanishing_bound'];", "const names=['pathWeight','causalPredict','randomized_harmonic_lower','randomized_log_lower']; const proofNames=['prefix_mass_one','expected_next_variance','causalPredict_prefix','binary_mean_minimizer','expected_pathRegret_lower','randomized_harmonic_lower','randomized_log_lower'];")
s=s.replace('declaration:BanditRL.OnlineLearning.','declaration:BanditRL.OnlineLearning.GuessingLower.')
s=s.replace('length===11','length===12')
start=s.index(' const specs=');end=s.index('\n  async function openAncestors',start)
s=s[:start]+" const proofNodes=proofNames.map(n=>registry.nodes.find(x=>x.id==='declaration:BanditRL.OnlineLearning.GuessingLower.'+n));if(proofNodes.some(x=>!x))throw Error('Missing public proof notes');\n const specs=[['article.source-theorem-card',8,'log-lower-source-card-v1.png',1,9],...proofNodes.map((n,i)=>['#'+n.url.split('#')[1]+'-teaching',0,`public-note-${i+1}-v1.png`,1,1])],panels=[];"+s[end:]
s=s.replace('module-existing-declaration-','module-new-declaration-').replace('actual-current-panels-and-existing-catalog-captured','actual-current-lower-panels-and-catalog-captured').replace('actualSourceGuideMathContainers:11,newPublicNoteMathContainers:2','actualSourceGuideMathContainers:12,newPublicNoteMathContainers:7')
write(RUN/'capture-reader-v1.cjs',s)
write(RUN/'capture-preparation-v1.json',dict(template=old.as_posix(),template_sha256=sha(old),expected_source_cards=9,expected_source_math=12,expected_new_notes=7,expected_module_panels=4,expected_images=13,prior_inline_shell_preparation_failure='PowerShell ParserError Missing argument in parameter list before execution; no file or source mutations. Replaced inline shell code with saved Python template transformation.',new_capture_sha256=sha(RUN/'capture-reader-v1.cjs')))
print('Saved capture code prepared; thirteen actual images required.')
