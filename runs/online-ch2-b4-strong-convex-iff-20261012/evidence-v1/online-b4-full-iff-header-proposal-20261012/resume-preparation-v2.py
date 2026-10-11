from pathlib import Path
p=Path(__file__).resolve().parent
source=(p/'prepare-proposal-v1.py').read_text(encoding='utf-8')
source=source.replace("with (P/name).open('xb') as f:f.write(b)","if (P/name).exists():\n  assert (P/name).read_bytes()==b\n else:\n  with (P/name).open('xb') as f:f.write(b)")
source=source.replace('capture_output=True,text=True','capture_output=True,text=True,encoding="utf-8"')
exec(compile(source,str(p/'prepare-proposal-v1.py'),'exec'))
