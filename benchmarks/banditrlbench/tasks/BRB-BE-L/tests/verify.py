"""Evaluator entry point; never copy into the agent workspace."""
import subprocess, sys
from pathlib import Path
root=Path(__file__).resolve().parents[5]
raise SystemExit(subprocess.call([sys.executable,str(root/'tools/bench_expansion.py'),'verify','--task',Path(__file__).resolve().parents[1].name,*sys.argv[1:]],cwd=root))
