"""Start actual Ream validators/peers. Never sends FCU, newPayload or fake votes.
Internal N1 regression only; three validators on two nodes. No stake-ledger or full N1 acceptance claim.
"""
from pathlib import Path
import argparse,base64,hashlib,hmac,json,os,shutil,socket,subprocess,time,urllib.request

ROOT=Path(__file__).resolve().parents[2]
import sys
sys.dont_write_bytecode=True
sys.path.insert(0,str(ROOT/'tools'))
from install import require_installed,preflight
from request_boundary import boundary_schedule,check_boundary_pair
installed=require_installed(ROOT)
HERE=Path(__file__).resolve().parent

ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--run-id',required=True);ap.add_argument('--keys',type=Path,required=True);ap.add_argument('--keys-b',type=Path,required=True);ap.add_argument('--keys-c',type=Path,required=True);ap.add_argument('--inputs',type=Path,required=True);ap.add_argument('--request-window',type=int,default=612,help='explicit synthetic request deadline window in seconds');args=ap.parse_args()
assert args.run_id.isalnum() and args.keys.is_absolute()
OUT=args.work.resolve();assert not OUT.is_relative_to(ROOT) and not ROOT.is_relative_to(OUT);OUT.mkdir(exist_ok=False)
(OUT/'driver-at-run.py').write_bytes(Path(__file__).read_bytes())
RUN=OUT/'runtime';RUN.mkdir(mode=0o700)
REAM=ROOT/'bin/ream';GETH=ROOT/'bin/geth';TOOL=ROOT/'bin/profile-tool-three'
result={'status':'RUNNING','review':'loop-internal self-review; not independently reviewed','scope':'actual Ream consensus, two geth nodes, N1 request gate and seed recovery, restart; synthetic EL state; no stake-ledger claim','samples':1,'commands':[]}
processes=[];files=[]
def save(): (OUT/'result.json').write_text(json.dumps(result,indent=2)+'\n')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def port(udp=False):
 with socket.socket(socket.AF_INET,socket.SOCK_DGRAM if udp else socket.SOCK_STREAM) as s:s.bind(('127.0.0.1',0));return s.getsockname()[1]
def command(label,argv):
 q=subprocess.run(list(map(str,argv)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,env=dict(os.environ,RAYON_NUM_THREADS='2',TOKIO_WORKER_THREADS='2'),timeout=90)
 (OUT/(label+'.log')).write_bytes(q.stdout);result['commands'].append({'label':label,'argv':list(map(str,argv)),'exit':q.returncode});save()
 assert q.returncode==0,(label,q.returncode);return q.stdout.decode().strip()
def spawn(label,argv,env=None):
 f=(OUT/(label+'.log')).open('wb');files.append(f)
 e={k:os.environ[k] for k in ['HOME','PATH','LANG'] if k in os.environ}
 e.update(RAYON_NUM_THREADS='2',TOKIO_WORKER_THREADS='2',GOMAXPROCS='2',RUST_BACKTRACE='1')
 e.update(env or {})
 p=subprocess.Popen(list(map(str,argv)),stdout=f,stderr=subprocess.STDOUT,env=e);processes.append(p)
 result['commands'].append({'label':label,'argv':list(map(str,argv)),'pid':p.pid});save();return p
def stop(p):
 if p.poll() is None:
  p.terminate()
  try:p.wait(timeout=15)
  except subprocess.TimeoutExpired:p.kill();p.wait(timeout=10)
def rpc(url,method,params):
 req=urllib.request.Request(url,json.dumps({'jsonrpc':'2.0','id':1,'method':method,'params':params}).encode(),{'Content-Type':'application/json'})
 with urllib.request.urlopen(req,timeout=5) as r:data=json.load(r)
 assert 'error' not in data,(method,data.get('error'));return data['result']
def rest(port,path):
 request=urllib.request.Request(f'http://127.0.0.1:{port}/lean/v0/{path}',headers={'Accept':'application/json'})
 with urllib.request.urlopen(request,timeout=4) as r:return json.load(r)
def wait_ready(check,timeout=50):
 end=time.monotonic()+timeout;last=None
 while time.monotonic()<end:
  try:return check()
  except Exception as e:last=type(e).__name__;time.sleep(.25)
 raise RuntimeError('readiness timeout: '+str(last))
try:
 public={};registry={'A':[],'B':[]};keydirs={'A':args.keys,'B':args.keys_b,'C':args.keys_c}
 for name in ['A','B']:(RUN/name).mkdir()
 for index,label in enumerate(['A','B','C']):
  node='A' if label=='A' else 'B';keys=RUN/node/('hash-sig-keys-'+label);keys.mkdir()
  public[label]={role:'0x'+(keydirs[label]/(role+'.pub')).read_bytes().hex() for role in ['attestation','proposal']}
  for role in ['attestation','proposal']:
   shutil.copyfile(keydirs[label]/(role+'.ssz'),keys/(role+'.ssz'))
   registry[node].append({'index':index,'pubkey_hex':public[label][role],'privkey_file':str(keys/(role+'.ssz'))})
 (RUN/'registry.yaml').write_text(json.dumps(registry))
 genesis_time=int(time.time())+90
 cl=json.loads(command('cl-genesis',[TOOL,'genesis',args.keys,str(genesis_time),args.keys_b,args.keys_c]))
 network={'GENESIS_TIME':genesis_time,'NUM_VALIDATORS':3,'GENESIS_VALIDATORS':[{'attestation_public_key':public[name]['attestation'],'proposal_public_key':public[name]['proposal']} for name in ['A','B','C']],'SECONDS_PER_SLOT':12,'JUSTIFICATION_LOOKBACK_SLOTS':3}
 (OUT/'lean-network.yaml').write_text(json.dumps(network,indent=2))
 genesis=json.loads((ROOT/'share/templates/generator-el-genesis.json').read_text())
 proof=args.inputs/'recovery';fields=json.loads((proof/'config.json').read_text())['fields']
 assert len((proof/'pi.bin').read_bytes())==198
 profile=json.loads((ROOT/'share/identity/lean-migration-profile.json').read_text())
 old=json.loads((ROOT/'share/templates/migration-genesis.json').read_text())['config']['pqMigrate']
 old.update(t0=genesis_time+12,t=genesis_time+180,receivingTime=genesis_time+12,w=args.request_window)
 boundary_cases=boundary_schedule(genesis_time,old['t'],old['w'])
 result['requestBoundary']={'windowSeconds':old['w'],'deadline':old['t']+old['w'],'cases':[]}
 old['fullResearch'].update({k:profile[k] for k in ('version','backend','nativeAlgorithmDigest','finalKeyDigest','maxProofBytes','maxTxBytes','imageId','guestSha','verifierSha','verifyGas')})
 old['fullResearch']['activation']=genesis_time+12
 genesis['config']['pqMigrate']=old;genesis['config']['chainId']=13378;genesis['timestamp']=hex(genesis_time)
 # Explicit synthetic credit; no claim of mainnet state or real owned funds.
 owner=fields['legacy_address'];genesis['alloc'][owner[2:]]={'balance':hex(2*10**18),'nonce':'0x0','code':'0x','storage':{}}
 sponsor=json.loads((ROOT/'share/l1/PUBLIC-sponsor.json').read_text())['address']
 genesis['alloc'][sponsor]={'balance':hex(2*10**18),'nonce':'0x0','code':'0x','storage':{}}
 command('encode-transactions',[ROOT/'bin/pqlean-txs','-config',proof/'config.json','-root',proof/'proof.postcard','-out',OUT/'txs'])
 txmeta=json.loads((OUT/'txs/txs.json').read_text())
 for address in [txmeta['preTEnrollmentOwner'],txmeta['legacyCutoffOwner']]:
  genesis['alloc'][address[2:]]={'balance':hex(2*10**18),'nonce':'0x0','code':'0x','storage':{}}
 command('n1-carriers',[ROOT/'bin/pq-n1-txs','-config',proof/'config.json','-out',OUT/'txs'])
 n1meta=json.loads((OUT/'txs/n1-carriers.json').read_text())
 for kind in ['7002','7251']:
  forward=n1meta['forward-'+kind];genesis['alloc'][forward['address'][2:]]={'balance':'0x0','nonce':'0x0','code':forward['code'],'storage':{}}
 (OUT/'txs/txs.json').write_text(json.dumps(txmeta,indent=2)+'\n')
 (OUT/'el-genesis.json').write_text(json.dumps(genesis,indent=2))
 result['preflight']=preflight(ROOT,OUT/'el-genesis.json',args.inputs,research_window_seconds=args.request_window);save()
 nodes={};anchors=[]
 for index,name in enumerate(['A','B']):
  d=RUN/name;(d/'jwt').write_text(os.urandom(32).hex());(d/'jwt').chmod(0o600)
  n={'dir':d,'rpc':port(),'engine':port(),'elport':port(),'rest':port(),'p2p':port(True),'material':port()};nodes[name]=n
  command(name+'-init',[GETH,'--datadir',d/'el','--state.scheme=hash','init',OUT/'el-genesis.json'])
  n['gethargs']=[GETH,f'--datadir={d}/el','--state.scheme=hash','--syncmode=full','--gcmode=archive','--snapshot=false','--cache=256','--maxpeers=0','--nodiscover','--bootnodes=','--nat=none',f'--port={n["elport"]}','--ipcdisable','--http','--http.addr=127.0.0.1',f'--http.port={n["rpc"]}','--http.vhosts=localhost,127.0.0.1','--http.api=eth,net,web3,pqpool,debug','--authrpc.addr=127.0.0.1',f'--authrpc.port={n["engine"]}','--authrpc.vhosts=localhost,127.0.0.1',f'--authrpc.jwtsecret={d}/jwt','--miner.gasprice=1','--verbosity=3']
  n['gethargs'].append('--log.format=json')
  n['geth']=spawn(name+'-geth-1',n['gethargs'],{'PQ_LEAN_FENCE_PATH':str(d/'signing-fence')})
  n['url']=f'http://127.0.0.1:{n["rpc"]}'
  anchor=wait_ready(lambda:rpc(n['url'],'eth_getBlockByNumber',['0x0',False]));assert anchor is not None;anchors.append(anchor)
  n['peerid']=command(name+'-network-identity',[ROOT/'bin/profile-tool','peer',args.keys,d/'node-key'])
  n['materials']=d/'public-materials';n['materials'].mkdir()
  n['server']=spawn(name+'-material-server',['python3',ROOT/'tools/lean/material_server.py','--directory',n['materials'],'--port',str(n['material'])])
 assert anchors[0]['hash']==anchors[1]['hash'] and anchors[0]['stateRoot']==anchors[1]['stateRoot']
 anchor=anchors[0]
 identity=hashlib.sha256(b'PQ-LEAN-FENCED-v1'+(13378).to_bytes(8,'big')+bytes.fromhex(cl['clRoot'][2:])+bytes.fromhex(anchor['hash'][2:])+bytes.fromhex(anchor['stateRoot'][2:])).hexdigest()
 for index,name in enumerate(['A','B']):
  history=RUN/name/'signing-history';nodes[name]['history']=history
  command(name+'-fresh-history',[TOOL,'history',keydirs[name],history,'0x'+identity,str(index)]+([args.keys_c,'2'] if name=='B' else []))
  (RUN/name/'signer.json').write_text(json.dumps({'format':1,'network_identity':'0x'+identity,'history':str(history),'start_slot':0,'end_slot':4096}))
 for name,n in nodes.items():
  other=nodes['B' if name=='A' else 'A'];d=n['dir'];(d/'session-1').write_bytes(os.urandom(32));(d/'session-1').chmod(0o600)
  n['config']={'profile':'pq-lean-fenced-v1','engine_url':f'http://127.0.0.1:{n["engine"]}','rpc_url':n['url'],'jwt_path':str(d/'jwt'),'session_path':str(d/'session-1'),'materials_directory':str(n['materials']),'material_peers':[f'http://127.0.0.1:{other["material"]}/'],'chain_id':13378,'anchor_cl_root':cl['clRoot'],'anchor_el_hash':anchor['hash'],'anchor_state_root':anchor['stateRoot'],'timeout_seconds':10,'exclusive_unsigned_instance':False}
  (d/'engine-1.json').write_text(json.dumps(n['config'],indent=2))
  boot='none'
  n['reamargs']=[REAM,'--data-dir',d/'cl','lean_node','--network',OUT/'lean-network.yaml','--validator-registry-path',RUN/'registry.yaml','--node-id',name,'--private-key-path',d/'node-key','--socket-address','127.0.0.1','--socket-port',str(n['p2p']),'--http-port',str(n['rest']),'--bootnodes',boot]
  n['reamargs']+=['--is-aggregator']
 result['installedManifestSHA256']=sha(ROOT/'manifest.json')
 result['runtimeHashes']={n:installed['payloads']['libexec/'+n]['sha256'] for n in ['ream','geth']}
 result['manifest']={'chainId':13378,'slotSeconds':12,'cl':cl,'elAnchor':{'hash':anchor['hash'],'stateRoot':anchor['stateRoot']},'networkIdentity':'0x'+identity,'signature':'official ordinary devnet5, distinct proposer/attester keys, 262144 active epochs','noFakeProofs':True,'randomness':'SHA256(parentCLRoot || slot_le64), verified on ingress; local Lean rule, no mainnet RANDAO claim','withdrawals':'empty local registry, no withdrawal bridge','engineTuple':['forkchoiceUpdatedV3','getPayloadV5','newPayloadV4'],'hashes':{str(p):sha(p) for p in [REAM,GETH,TOOL,OUT/'el-genesis.json',OUT/'lean-network.yaml',proof/'proof.postcard',proof/'pi.bin',ROOT/'share/source-locks/ream-Cargo.lock',ROOT/'share/profile.json']},'runtimeSourceManifest':installed['reamSourceManifestSHA256']}
 (OUT/'manifest-before-start.json').write_text(json.dumps(result['manifest'],indent=2));save()
 def start_ream(name,round):
  n=nodes[name];env={'PQ_MIGRATE_EXTERNAL_ENGINE_CONFIG':str(n['dir']/f'engine-{round}.json')}
  env['PQ_REAM_SIGNER_CONFIG']=str(RUN/name/'signer.json')
  n['ream']=spawn(f'{name}-ream-{round}',n['reamargs'],env)
 a=nodes['A'];b=nodes['B'];a['reamargs'][a['reamargs'].index('--bootnodes')+1]=f'/ip4/127.0.0.1/udp/{b["p2p"]}/quic-v1/p2p/{b["peerid"]}'
 start_ream('B',1);start_ream('A',1)
 def snapshot():
  data={}
  for name,n in nodes.items():
   if n['ream'].poll() is not None:raise RuntimeError(name+' Ream exited '+str(n['ream'].returncode))
   b=rest(n['rest'],'blocks/head');e=rpc(n['url'],'eth_getBlockByNumber',['latest',False]);f=rest(n['rest'],'blocks/finalized')
   data[name]={'cl':b,'el':e,'finalized':f}
  return data
 def account(n):return rpc(n['url'],'eth_getPQAccount',[owner,'latest'])
 observations=[]
 def observe(phase):
  data=snapshot();observations.append({'phase':phase,'time':time.time(),'data':data})
  (OUT/'observations.json').write_text(json.dumps(observations,indent=2));return data

 result['steps']={}
 def wait_timestamp(target):
  end=time.monotonic()+300
  while time.monotonic()<end:
   blocks={name:rpc(n['url'],'eth_getBlockByNumber',['latest',False]) for name,n in nodes.items()}
   if all(int(block['timestamp'],16)>=target for block in blocks.values()):return blocks
   for name,n in nodes.items():
    if n['ream'].poll() is not None:raise RuntimeError(name+' Ream stopped')
   time.sleep(.5)
  raise RuntimeError('canonical timestamp did not reach '+str(target))
 def submit(kind,status,request=None,source=None,before_t=False):
  raw=(OUT/'txs'/(kind+'.bin')).read_bytes();meta=txmeta.get(kind,n1meta.get(kind));txh=meta['hash']
  before={name:account(n) for name,n in nodes.items()}
  assert rpc(nodes['A']['url'],'eth_sendRawTransaction',['0x'+raw.hex()])==txh
  end=time.monotonic()+180
  while time.monotonic()<end:
   receipts={name:rpc(n['url'],'eth_getTransactionReceipt',[txh]) for name,n in nodes.items()}
   if all(receipts.values()) and receipts['A']==receipts['B']:break
   time.sleep(.5)
  else:raise RuntimeError(kind+' not included identically on A/B')
  rc=receipts['A'];assert int(rc['status'],16)==status,(kind,rc)
  blocks={name:rpc(n['url'],'eth_getBlockByHash',[rc['blockHash'],False]) for name,n in nodes.items()}
  assert blocks['A']==blocks['B'];block=blocks['A'];ts=int(block['timestamp'],16)
  assert (ts-genesis_time)%12==0 and ((ts-genesis_time)//12)%3==0, 'expected actual A proposer slot'
  assert ts>=old['t0']
  if before_t:assert ts<old['t'],(kind,ts,old['t'])
  step={'hash':txh,'rawSHA256':sha(OUT/'txs'/(kind+'.bin')),'receipts':receipts,'block':block,'before':before,'after':{name:account(n) for name,n in nodes.items()}}
  if request:
   target={'7002':'0x00000961ef480eb55e80d19ad83579a64c007002','7251':'0x0000bbddc7ce488642fb579f8b00f3a590007251'}[request]
   logs=[x for x in rc['logs'] if x['address'].lower()==target]
   if status:
    assert len(logs)==1,(kind,logs)
    body=bytes.fromhex(logs[0]['data'][2:]);assert body[:20]==bytes.fromhex(source[2:])
    expected=bytes.fromhex(n1meta['data-'+request][2:]);assert body[20:]==expected
    rh='0x'+hashlib.sha256(hashlib.sha256(bytes([1 if request=='7002' else 2])+body).digest()).hexdigest()
    assert block['requestsHash']==rh,(kind,block['requestsHash'],rh)
    step['source']=source;step['verifiedRequestsHash']=rh
   else:assert not logs
  result['steps'][kind]=step;save();print(kind+': '+('reverted' if not status else 'accepted')+'; A built, B imported',flush=True)
  return rc
 wait_timestamp(old['t0'])
 result['feeReads']={}
 for kind,target in [('7002','0x00000961ef480eb55e80d19ad83579a64c007002'),('7251','0x0000bbddc7ce488642fb579f8b00f3a590007251')]:
  result['feeReads'][kind]={name:rpc(n['url'],'eth_call',[{'from':n1meta['legacy'],'to':target,'data':'0x'},'latest']) for name,n in nodes.items()}
  assert all(int(x,16)==1 for x in result['feeReads'][kind].values())
 for kind in ['7002','7251']:submit('legacy-request-'+kind,0,kind,before_t=True)
 submit('pre-enroll',1,before_t=True);submit('pre-activate',1,before_t=True)
 for kind in ['7002','7251']:submit('marker-request-'+kind,0,kind)
 wait_timestamp(old['t'])
 submit('migrate',1)
 for n in nodes.values():
  state=account(n);assert state['mode']=='0x2' and not state['activated'] and state['pqPkCommit'].lower()=='0x'+(proof/'pi.bin').read_bytes()[93:125].hex()
 submit('activate',1)
 for kind in ['7002','7251']:submit('owner-request-'+kind,1,kind,owner)
 for kind in ['7002','7251']:submit('contract-request-'+kind,1,kind,n1meta['forward-'+kind]['address'])
 # A's queue is local; both nonces must be submitted before waiting for either receipt.
 # The first pair is queued one A proposal ahead of the requested before-deadline block.
 def submit_boundary_pair(phase,target,status):
  if phase=='before':wait_timestamp(target-36)
  latest={name:rpc(n['url'],'eth_getBlockByNumber',['latest',False]) for name,n in nodes.items()}
  assert all(int(block['timestamp'],16)<target for block in latest.values()), 'missed boundary submission slot'
  before={name:account(n) for name,n in nodes.items()}
  kinds={kind:'marker-deadline-'+phase+'-'+kind for kind in ['7002','7251']}
  hashes={kind:n1meta[label]['hash'] for kind,label in kinds.items()}
  for kind,label in kinds.items():
   raw=(OUT/'txs'/(label+'.bin')).read_bytes()
   assert rpc(nodes['A']['url'],'eth_sendRawTransaction',['0x'+raw.hex()])==hashes[kind]
  end=time.monotonic()+180
  while time.monotonic()<end:
   receipts={name:{kind:rpc(n['url'],'eth_getTransactionReceipt',[txh]) for kind,txh in hashes.items()} for name,n in nodes.items()}
   if all(all(rows.values()) for rows in receipts.values()) and receipts['A']==receipts['B']:break
   for name,n in nodes.items():
    if n['ream'].poll() is not None:raise RuntimeError(name+' Ream stopped during boundary check')
   time.sleep(.5)
  else:raise RuntimeError(phase+' boundary pair not included identically on A/B')
  blockhash=receipts['A']['7002']['blockHash']
  blocks={name:rpc(n['url'],'eth_getBlockByHash',[blockhash,False]) for name,n in nodes.items()}
  assert blocks['A']==blocks['B'];block=blocks['A'];ts=int(block['timestamp'],16)
  assert (ts-genesis_time)%36==0,'expected actual A proposer slot'
  checked=check_boundary_pair(phase,old['t']+old['w'],ts,receipts['A'],block,n1meta['enrolled'],
                             {kind:bytes.fromhex(n1meta['data-'+kind][2:]) for kind in kinds})
  assert checked['expectedStatus']==status
  for kind,label in kinds.items():
   result['steps'][label]={'hash':hashes[kind],'rawSHA256':sha(OUT/'txs'/(label+'.bin')),
                          'receipts':{name:rows[kind] for name,rows in receipts.items()},'block':block,
                          'before':before,'after':{name:account(n) for name,n in nodes.items()},
                          'requestBoundary':checked}
  result['requestBoundary']['cases'].append(checked);save()
  print(phase+': both request contracts checked at canonical timestamp '+str(ts),flush=True)
 for phase,target,status in boundary_cases:submit_boundary_pair(phase,target,status)
 data=observe('before-restart');before_accounts={name:account(n) for name,n in nodes.items()}
 for n in nodes.values():stop(n['ream'])
 for n in nodes.values():stop(n['geth']);assert not (n['dir']/'signing-fence').exists()
 histories={name:n['history'].read_bytes() for name,n in nodes.items()}
 for name,n in nodes.items():
  (OUT/(name+'-history-before-restart.bin')).write_bytes(histories[name])
  n['geth']=spawn(name+'-geth-2',n['gethargs'],{'PQ_LEAN_FENCE_PATH':str(n['dir']/'signing-fence')})
  wait_ready(lambda:rpc(n['url'],'eth_blockNumber',[]))
  (n['dir']/'session-2').write_bytes(os.urandom(32));n['config']['session_path']=str(n['dir']/'session-2')
  (n['dir']/'engine-2.json').write_text(json.dumps(n['config']))
 start_ream('B',2);start_ream('A',2)
 end=time.monotonic()+240
 while time.monotonic()<end:
  time.sleep(1)
  try:after=observe('restart')
  except (OSError,ValueError):continue
  if after['A']['cl']==after['B']['cl'] and int(after['A']['cl']['slot'])>max(int(data[n]['cl']['slot']) for n in nodes):break
 else:raise RuntimeError('restart did not resume')
 for name,n in nodes.items():
  assert n['history'].read_bytes().startswith(histories[name]);assert account(n)==before_accounts[name]
  (OUT/(name+'-final-signing-history.bin')).write_bytes(n['history'].read_bytes())
  for step in result['steps'].values():assert rpc(n['url'],'eth_getTransactionReceipt',[step['hash']])==step['receipts'][name]
 result.update(status='PASS',afterRestart=after,historyAppendOnly=True,stakeLedger='NOT_IMPLEMENTED_IN_THIS_RUN')
except Exception as error:
 import traceback
 result.update(status='FAIL',failure=type(error).__name__+': '+str(error),traceback=traceback.format_exc())
finally:
 for p in reversed(processes):stop(p)
 for f in files:f.close()
 result['processesStopped']=all(p.poll() is not None for p in processes);save()
 print(json.dumps({k:result.get(k) for k in ['status','failure','historyAppendOnly','processesStopped']}))
raise SystemExit(0 if result['status']=='PASS' else 1)
