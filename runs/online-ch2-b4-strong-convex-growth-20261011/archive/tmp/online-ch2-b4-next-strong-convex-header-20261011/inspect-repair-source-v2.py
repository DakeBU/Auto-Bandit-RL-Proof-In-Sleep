from pathlib import Path
import subprocess,json,hashlib,datetime
root=Path('E:/ABRL/worktrees/research-online-book');out=root/'tmp/online-ch2-b4-next-strong-convex-header-20261011'
pdf=Path('E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert hashlib.sha256(pdf.read_bytes()).hexdigest()=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
argv=['pdftotext','-layout','-f','107','-l','114',str(pdf),str(out/'source-pages107-114-v2.txt')];t=datetime.datetime.now(datetime.timezone.utc).isoformat();p=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
for n,b in [('source-extraction-v2.stdout.raw',p.stdout),('source-extraction-v2.stderr.raw',p.stderr)]:
 with (out/n).open('xb') as f:f.write(b)
with (out/'source-extraction-v2.json').open('xb') as f:f.write((json.dumps(dict(argv=argv,startUTC=t,endUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),actual_exit=p.returncode),indent=2)+'\n').encode())
data=json.loads((root/'docs/contracts/online-ch2-complete-target-freeze-v1/effective-targets-frozen-v3.2.json').read_text(encoding='utf-8'))
def visit(x,path='$'):
 if isinstance(x,dict):
  if x.get('target_id') in ['repair:7.47-terminal','repair:15.31-terminal']:
   b=json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode();print(path,x['target_id'],hashlib.sha256(b).hexdigest())
   with (out/(x['target_id'].replace(':','-')+'-row-v2.json')).open('xb') as f:f.write(b+b'\n')
  for k,v in x.items():visit(v,path+'.'+k)
 elif isinstance(x,list):
  for i,v in enumerate(x):visit(v,path+'['+str(i)+']')
visit(data)