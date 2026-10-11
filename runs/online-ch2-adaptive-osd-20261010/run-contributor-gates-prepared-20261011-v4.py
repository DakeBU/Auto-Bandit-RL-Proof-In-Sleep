from delivery_guard_20261011_v3 import *
sys.path.insert(0,str(ROOT))
from tools import check_contributor_contract as checker
a=arguments();fixed(a,require_index=True);binding=source_binding()
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,encoding='utf8').strip()
assert head=='39e4bc0102227fce549c692bd5f18f20cc4b9983','Exact committed candidate H0 required'
required={'BanditRLProof/'+name+'.lean' for name in ['OnlineAdaptivePotential','OnlineAdaptiveOSD','OnlineAdaptiveBenchmark']}
own_manifest='research-wiki/contribution-contracts/'+TASK+'.json'
checks=[]
for label,base in [('stack',CONFIG['base']),('main',CONFIG['origin_main_at_preparation'])]:
    entries=checker.diff_entries(base)
    production={p for status,p in entries if checker.is_production(p)}
    contracts=checker.changed_contract_paths(entries)
    assert entries and required.issubset(production) and own_manifest in contracts
    code,out=capture('contributor-'+label+'-'+a.tag,sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base,required=False)
    assert code==0 and 'contributor contract passed.' in out.lower() and 'n/a' not in out.lower() and 'not applicable' not in out.lower(),out
    def number(label):
        matches=re.findall(r'^'+re.escape(label)+r': (\d+)\s*$',out,re.M)
        assert len(matches)==1,(label,out)
        return int(matches[0])
    counts=dict(changed_paths=number('changed paths'),affected_production_paths=number('affected production paths'),changed_contribution_contracts=number('changed contribution contracts'))
    assert counts==dict(changed_paths=len(entries),affected_production_paths=len(production),changed_contribution_contracts=len(contracts))
    assert all(v>0 for v in counts.values())
    covered=set(re.findall(r'^ - covered: (.+?)\s*$',out,re.M))
    assert covered==production and required.issubset(covered),(covered,production)
    assert 'contributor base: '+base in out
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,encoding='utf8').strip()==head
    checks.append(dict(base=base,head=head,three_dot_commit_diff=True,counts=counts,covered_production_paths=sorted(covered),OSD_three_new_modules_covered=True,own_contribution_manifest_changed=True,receipt=rows([RUN/('contributor-'+label+'-'+a.tag+'.json')])[0]))
fixed(a,require_index=True);same_binding(binding)
write(RUN/('contributor-inspected-'+a.tag+'.json'),dict(checks=checks,source_binding=binding,head=head,nonempty_substantive_diff=True,actual_checker_positive_coverage=True,origin_main_is_pinned_historical_snapshot=True,supersedes_NA_inspection=rows([RUN/'contributor-inspected-20261011-v2.json']),boundary='Actual committed H0 checks replace the earlier N/A result; no native/package/chapter or merge acceptance'))
