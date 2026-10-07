from common_v1 import *
fixed()
old=(RUN/'prepare-contract-v1.py').read_text(encoding='utf-8')
tail=old[old.index("write(Path('conversion-windows')"):]
context=(CONTRACT/'public-context-v1.txt').read_text(encoding='utf-8')
targets=load(CONTRACT/'headers-v1.json')
def replace_generated(p,value):
 p=Path(p);assert p.as_posix() in ['conversion-windows/'+TASK+'.md','proof-obligations/'+TASK+'.json']
 if p.exists():write(RUN/'snapshots'/('native-scaffold-'+p.as_posix().replace('/','--')),p.read_bytes())
 raw=value if isinstance(value,bytes) else (json.dumps(value,ensure_ascii=False,indent=2)+'\n').encode('utf-8')
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
tail=tail.replace("write(Path('conversion-windows')","replace_generated(Path('conversion-windows')").replace("write(Path('proof-obligations')","replace_generated(Path('proof-obligations')")
write(RUN/'contract-resume-v2.json',dict(original_script_sha256=sha(RUN/'prepare-contract-v1.py'),resume='Only unexecuted suffix starting native-scaffold conversion replacement. Original generated files separately preserved; actual statement hashes unchanged.',original_failure='prepare-contract-v1-failure.txt',stage='draft',chapter_complete=False,goal_complete=False))
exec(compile(tail,str(RUN/'prepare-contract-v1.py')+'#unexecuted-suffix-v2','exec'))
