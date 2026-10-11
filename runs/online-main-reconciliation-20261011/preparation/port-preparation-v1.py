from pathlib import Path
import hashlib,json,subprocess,datetime
root=Path.cwd(); prep=root/'tmp/online-main-reconciliation-20261011'; out=root/'runs/online-main-reconciliation-20261011'
assert not out.exists()
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root).decode().strip()=='c445c93f7e4cda1408279d614858c904e346ad47'
assert subprocess.check_output(['git','rev-parse','MERGE_HEAD'],cwd=root).decode().strip()=='f07aa9a2a5df241087ffab1c3579d1b59d8bf6f6'
extra={'validation_failures':[{'tool_chunk':'a19ae6','actual_exit_code':1,'reason':'Direct script execution omitted repository sys.path; import tools failed before native or structural validation. Corrected helper and V2 actual0 retained.'},{'tool_chunk':'0f0685','actual_exit_code':1,'reason':'Bundled Python jsonschema unavailable; no package validation claimed; dependency not installed.'}],'failed_path_reads':[{'tool_chunk':'c95677','reason':'Assumed old gate folder root missing; correct production-root-v1 found by directory listing.'},{'tool_chunk':'651381','reason':'Assumed old gate folder root-v1 missing; no child gate or proof command run.'}],'truth':'Preparation/setup failures only; not negative mathematics or candidate gate results.'}
(prep/'metadata/setup-followup-failures-v1.json').write_bytes((json.dumps(extra,indent=2)+'\n').encode())
rows=[]
for srcroot,sub in [(prep,'preparation'),(root/'tmp/online-main-reconciliation-gates-20261011','dirty-preflight'),(root/'tmp/online-ch2-b4-finite-identity-delivery-20261011','predecessor-delivery')]:
    for src in sorted(srcroot.rglob('*')):
        if not src.is_file():continue
        assert not src.is_symlink()
        data=src.read_bytes(); dst=out/sub/src.relative_to(srcroot); dst.parent.mkdir(parents=True,exist_ok=True)
        with dst.open('xb') as f:f.write(data)
        assert dst.read_bytes()==data
        rows.append({'from':src.relative_to(root).as_posix(),'to':dst.relative_to(root).as_posix(),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
out.joinpath('.gitattributes').write_bytes(b'* -text\n* whitespace=cr-at-eol\n*.png -diff\n*.zip -diff\n*.raw -diff\n')
p=prep/'metadata/ONLINE-MAIN-RECONCILIATION-20261011.draft-v2.json'
dst=root/'research-wiki/contribution-contracts/ONLINE-MAIN-RECONCILIATION-20261011.json';assert not dst.exists();dst.write_bytes(p.read_bytes())
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'exact archival port only; no clean gate, merge commit or new mathematical closure','rows':rows,'copied_files':len(rows),'copied_bytes':sum(x['bytes'] for x in rows),'native_manifest':{'path':dst.relative_to(root).as_posix(),'sha256':hashlib.sha256(dst.read_bytes()).hexdigest()},'old_head':'c445c93f7e4cda1408279d614858c904e346ad47','merge_parent':'f07aa9a2a5df241087ffab1c3579d1b59d8bf6f6','original_ignored_paths_retained':True,'canonical_paths_are_byte_identical_aliases':True}
out.joinpath('exact-preparation-port-v1.json').write_bytes((json.dumps(receipt,indent=2)+'\n').encode())
print(json.dumps({k:v for k,v in receipt.items() if k!='rows'},indent=2))
