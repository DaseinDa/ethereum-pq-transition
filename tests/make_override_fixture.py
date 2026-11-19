#!/usr/bin/env python3
"""Fresh real F proof for overriding an attacker enrollment; public credential only."""
import argparse,json,subprocess,sys
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--lab',type=Path,required=True);ap.add_argument('--build',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
v=json.loads((a.lab/'demo/public-input.json').read_text());assert v['credential']['public'] is True
v['name']='held-attacker-after-override';v['pi']['migration_nonce']=1
subprocess.run([sys.executable,str(a.lab/'prover/prove.py'),'--build',str(a.build),'--input','-','--out',str(a.out)],input=json.dumps(v).encode(),check=True)
