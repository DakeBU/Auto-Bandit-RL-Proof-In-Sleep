"""Trusted reference artifact writer; not an evaluated agent."""
import argparse
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
reference=Path(__file__).parent/('proof.txt' if (Path(__file__).parent/'proof.txt').exists() else 'reference.txt')
with a.output.open('x',encoding='utf-8',newline='\n') as f:f.write(reference.read_text(encoding='utf-8'))
