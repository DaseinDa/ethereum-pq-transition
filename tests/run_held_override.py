#!/usr/bin/env python3
import argparse,os,subprocess,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--proof',type=Path,required=True);ap.add_argument('--genesis',type=Path,required=True);ap.add_argument('--clients',type=Path,required=True);ap.add_argument('--go-mod',type=Path,required=True);ap.add_argument('--go-cache',type=Path,required=True);ap.add_argument('--log',default='held.log');a=ap.parse_args()
(a.work/'held-results').mkdir(exist_ok=True)
e=dict(os.environ,PATH='/usr/local/go1.25/bin:/usr/bin:/bin',GOTOOLCHAIN='local',GOPROXY='off',GOSUMDB='off',GOMODCACHE=str(a.go_mod),GOCACHE=str(a.go_cache),GOAMD64='v1',CGO_ENABLED='1',GOMAXPROCS='2',RAYON_NUM_THREADS='1',CGO_LDFLAGS='-L'+str(a.clients/'lib'),LD_LIBRARY_PATH=str(a.clients/'lib'),PQ_HELD_PROOF_DIR=str(a.proof),PQ_HELD_GENESIS=str(a.genesis),PQ_HELD_OUT=str(a.work/'held-results'))
subprocess.run(['gofmt','-w','miner/pq_held_override_test.go'],cwd=a.work/'geth',env=e,check=True)
with (a.work/a.log).open('xb') as f:r=subprocess.run(['go','test','-p','1','-tags','pq_final','-trimpath','-buildvcs=false','-count=1','-json','./miner','-run','^TestPQHeldAttackerAfterRealFOverride$'],cwd=a.work/'geth',env=e,stdout=f,stderr=subprocess.STDOUT)
if r.returncode:raise RuntimeError('held transaction test failed; inspect '+a.log)
