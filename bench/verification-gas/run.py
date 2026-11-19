#!/usr/bin/env python3
"""Offline, serial, pinned-CPU portable geth calibration. Public fixtures only."""
import argparse, hashlib, importlib.util, json, math, os, platform, shutil, statistics, subprocess, time, uuid
from pathlib import Path
HERE = Path(__file__).resolve().parent
LIB_SHA = "3b073c6dcde075e1cfdcb5072774a42ad4fb58a67795b68f9b251515f63d2633"
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,v): Path(p).write_text(json.dumps(v,indent=2)+"\n")
def stats(xs): return dict(n=len(xs),mean=statistics.mean(xs),sd=statistics.stdev(xs),min=min(xs),max=max(xs),median=statistics.median(xs))
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 for k in ['lab','archive-cache','clients','go-mod','fixtures','out']: ap.add_argument('--'+k,type=Path,required=True)
 ap.add_argument('--phase',choices=['prepare','measure','recovery'],required=True)
 ap.add_argument('--lock',type=Path,default=Path.home()/'pq-heavy-job.lock')
 a=ap.parse_args(); a.out.mkdir(parents=True,exist_ok=True)
 token='gas-calibration-'+str(uuid.uuid4())
 with a.lock.open('x') as f: f.write(token)
 try:
  cpu=min(os.sched_getaffinity(0))
  env=dict(os.environ, PATH='/usr/local/go1.25/bin:/root/.cargo/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin',GOTOOLCHAIN='local',GOPROXY='off',GOSUMDB='off',GOAMD64='v1',CGO_ENABLED='1',GOMAXPROCS='1',RAYON_NUM_THREADS='1',GOMODCACHE=str(a.go_mod),GOCACHE=str(a.out/'go-cache'),CGO_LDFLAGS='-L'+str(a.clients/'lib'),LD_LIBRARY_PATH=str(a.clients/'lib'),PQ_CAL_ROOT=str(a.out/'inputs'),PQ_CAL_OUT=str(a.out/'raw'))
  assert sha(a.clients/'lib/libpq_final_native.so')==LIB_SHA, 'portable library identity'
  def run(name,cmd,cwd,extra=None,pinned=False):
   e=env| (extra or {}); start=time.time()
   with (a.out/(name+'.log')).open('xb') as f:
    p=subprocess.run(list(map(str,cmd)),cwd=cwd,env=e,stdout=f,stderr=subprocess.STDOUT,preexec_fn=(lambda: os.sched_setaffinity(0,{cpu})) if pinned else None)
   write(a.out/(name+'.command.json'),dict(command=list(map(str,cmd)),seconds=time.time()-start,returncode=p.returncode,cpu=cpu if pinned else None))
   if p.returncode: raise RuntimeError(name+' failed; inspect retained log')
  if a.phase=='prepare':
   s=importlib.util.spec_from_file_location('sources',a.lab/'client/sources.py');mod=importlib.util.module_from_spec(s);s.loader.exec_module(mod)
   source=mod.prepare('geth',a.archive_cache,a.out/'geth')
   shutil.copyfile(HERE/'pq_gas_calibration_test.go',a.out/'geth/core/pq_gas_calibration_test.go')
   inp=a.out/'inputs';inp.mkdir();(inp/'carriers').mkdir();(a.out/'raw').mkdir()
   hashes={}
   for i in range(1,11):
    name=f'mode0-{i:02}'
    for rel in [name+'/f/proof.postcard',name+'/statement/pi198.hex','carriers/'+name+'.bin']:
     dst=inp/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(a.fixtures/rel,dst);hashes[rel]=sha(dst)
    pi=bytes.fromhex((inp/name/'statement/pi198.hex').read_text().strip());assert len(pi)==198
    # Decode expiry with the canonical parser elsewhere; the transaction execution
    # checks the actual PI window. No fixture mutation or clock manipulation.
   genesis=json.loads((a.lab/'demo/templates/migration-genesis.json').read_text())
   pq=genesis['config']['pqMigrate'];now=int(time.time());pq.update(t0=now-24,t=now-12,receivingTime=now-24);pq['fullResearch']['activation']=now-24
   write(inp/'genesis.json',genesis);hashes['genesis.json']=sha(inp/'genesis.json')
   write(a.out/'IDENTITY.json',dict(source=source,fixtureFilesSHA256=hashes,nativeLibrarySHA256=LIB_SHA,portableRust='-C target-cpu=x86-64',GOAMD64='v1',GOMAXPROCS=1,RAYON_NUM_THREADS=1,cpu=cpu,uname=platform.uname()._asdict(),cpuinfo=Path('/proc/cpuinfo').read_text(),meminfo=Path('/proc/meminfo').read_text(),harnessSHA256=sha(HERE/'pq_gas_calibration_test.go')))
   run('gofmt',['gofmt','-w','core/pq_gas_calibration_test.go'],a.out/'geth')
   run('build-calibration',['go','test','-p','2','-c','-tags','pq_final','-trimpath','-buildvcs=false','-o',a.out/'calibration.test','./core'],a.out/'geth')
  elif a.phase=='measure':
   for i in range(1,11):
    run(f'calibration-{i:02}',[a.out/'calibration.test','-test.run','^TestPQGasCalibration$','-test.v','-test.timeout','2m'],a.out/'geth/core',{'PQ_CAL_REP':str(i)},True)
   raw=[json.loads((a.out/f'raw/calibration-{i:02}.json').read_text()) for i in range(1,11)]
   summary={name:stats([next(op['meanNs'] for op in r['operations'] if op['name']==name) for r in raw]) for name in ['F','ecrecover','BN254-pairing','BLS12-381-pairing']}
   ratios={op['name']:op['gas']/summary[op['name']]['median'] for op in raw[0]['operations'] if op['name']!='F'}
   r=statistics.median(ratios.values());gas=math.ceil(r*summary['F']['median']/1000)*1000
   write(a.out/'PRICE.json',dict(review='loop-internal self-review; not independently reviewed',status='measured',timingsNs=summary,coldKeyNs=stats([r['coldKeyNs'] for r in raw]),anchorGasPerNs=ratios,medianGasPerNs=r,FVerifyGas=gas,rounding='ceil to 1000 gas',calibrationBinarySHA256=sha(a.out/'calibration.test'),samples=10))
   print(json.dumps(json.loads((a.out/'PRICE.json').read_text()),indent=2))
  else:
   gas=json.loads((a.lab/'demo/identity/lean-migration-profile.json').read_text())['verifyGas']
   genesis=json.loads((a.out/'inputs/genesis.json').read_text());genesis['config']['pqMigrate']['fullResearch']['verifyGas']=gas;write(a.out/'inputs/genesis.json',genesis)
   run('build-recovery',['go','test','-p','2','-c','-tags','pq_final','-trimpath','-buildvcs=false','-o',a.out/'recovery.test','./core'],a.out/'geth')
   run('recovery-gas',[a.out/'recovery.test','-test.run','^TestPQCalibratedRecoveryGas$','-test.v','-test.timeout','2m'],a.out/'geth/core',pinned=True)
 finally:
  if a.lock.exists() and a.lock.read_text()==token: a.lock.unlink()
if __name__=='__main__': main()
