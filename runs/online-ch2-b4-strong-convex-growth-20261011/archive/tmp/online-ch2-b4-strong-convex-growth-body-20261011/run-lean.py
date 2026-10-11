import pathlib,hashlib,json,subprocess,datetime,sys
root=pathlib.Path.cwd();out=root/'tmp/online-ch2-b4-strong-convex-growth-body-20261011'
p=pathlib.Path(sys.argv[1]);tag=sys.argv[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],text=True).strip()
receipt={'argv':['lake','env','lean',str(p)],'candidate':str(p),'candidate_sha256':sha(p),'candidate_bytes':p.stat().st_size,'head_before':git('rev-parse','HEAD'),'status_before':git('status','--porcelain=v1'),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
r=subprocess.run(receipt['argv'],stdout=subprocess.PIPE,stderr=subprocess.PIPE,cwd=root)
(out/(tag+'.stdout.raw')).write_bytes(r.stdout);(out/(tag+'.stderr.raw')).write_bytes(r.stderr)
receipt.update(actual_exit=r.returncode,stdout_sha256=sha(out/(tag+'.stdout.raw')),stderr_sha256=sha(out/(tag+'.stderr.raw')),head_after=git('rev-parse','HEAD'),status_after=git('status','--porcelain=v1'),candidate_sha256_after=sha(p))
(out/(tag+'.json')).write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print(r.stdout.decode('utf-8',errors='replace'));print(r.stderr.decode('utf-8',errors='replace'));print('ACTUAL_EXIT',r.returncode)
