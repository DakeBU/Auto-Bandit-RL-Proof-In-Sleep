from pathlib import Path
import hashlib,json
run=Path(__file__).resolve().parent
s=(run/'freeze-draft-v1.py').read_text(encoding='utf-8-sig').replace("C.mkdir()","C.mkdir(exist_ok=True)")
s=s.replace("p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)","p=Path(p);p.parent.mkdir(parents=True,exist_ok=True)")
s=s.replace("p.write_bytes(x if isinstance(x,bytes) else (x.rstrip('\\n')+'\\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\\n').encode())", "raw=x if isinstance(x,bytes) else (x.rstrip('\\n')+'\\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\\n').encode()\n if p.exists():assert p.read_bytes()==raw,('Existing draft bytes differ; never overwrite',p)\n else:p.write_bytes(raw)")
s=s.replace("fixed=['BanditRLProof/OnlineSubgradientBasic.lean'", "fixed=['BanditRLProof/OnlineSubgradientBasic.lean','BanditRLProof/OnlineConvexExtended.lean','BanditRLProof/OnlineClosedProper.lean'")
s=s.replace("indicator=re.search(r'def extendedIndicator.*?(?=\\n\\s*(?:theorem|lemma|def|/--))',basic,re.S)", "indicator=re.search(r'def extendedIndicator.*?(?=\\n\\s*(?:theorem|lemma|def|/--))',Path('BanditRLProof/OnlineConvexExtended.lean').read_text(encoding='utf-8'),re.S)")
p=run/'freeze-draft-v2.py';assert not p.exists();p.write_bytes(s.encode())
wrapper=Path('runs/online-subgradient-absolute-migration-20261007/run-command.py').read_text(encoding='utf-8')
wrapper=wrapper.replace("label=sys.argv[1];cmd=sys.argv[2:]", "label=sys.argv[1];cmd=sys.argv[2:]\nassert not (root/(label+'.log')).exists() and not (root/(label+'-exit.json')).exists(), 'Evidence labels are immutable; choose a new attempt version'")
w=run/'run-command.py';assert not w.exists();w.write_bytes(wrapper.encode())
meta=dict(before_first_use=True,rows=[dict(path=q.as_posix(),sha256=hashlib.sha256(q.read_bytes()).hexdigest()) for q in [p,w]],initial_failure=dict(command='python -B -X utf8 runs/online-normal-cone-migration-20261007/freeze-draft-v1.py',tool_chunk_id='c805eb',observed_exit_code=1,observed_error='AttributeError: regex extendedIndicator search in OnlineSubgradientBasic returned None',evidence_limit='Initial terminal failure observed directly through exec tool, not a separately captured raw wrapper log; partial exact source snapshots preserved.',repair='rg located actual borrowed definition in OnlineConvexExtended; v2 adds owning shared files and resumes only if every already written raw snapshot byte equals original. No Lean proof/target change.'))
(run/'draft-preparer-before-use-v2.json').write_bytes((json.dumps(meta,ensure_ascii=False,indent=2)+'\n').encode())
