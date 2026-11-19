"""Start actual Ream validators/peers. Never sends FCU, newPayload or fake votes.
Internal regression only; three validators on two nodes; actual migration orphan and canonical reinclusion (recorded reinjection or eligible submitter retry).
"""
from pathlib import Path
import argparse,base64,hashlib,hmac,json,os,shutil,socket,subprocess,time,urllib.request

ROOT=Path(__file__).resolve().parents[2]
import sys
sys.dont_write_bytecode=True
sys.path.insert(0,str(ROOT/'tools'))
from install import require_installed,preflight
installed=require_installed(ROOT)
HERE=Path(__file__).resolve().parent
import l1_carriers,l1_live
ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--run-id',required=True);ap.add_argument('--keys',type=Path,required=True);ap.add_argument('--keys-b',type=Path,required=True);ap.add_argument('--keys-c',type=Path,required=True);ap.add_argument('--inputs',type=Path,required=True);args=ap.parse_args()
assert args.run_id.isalnum() and args.keys.is_absolute()
OUT=args.work.resolve();assert not OUT.is_relative_to(ROOT) and not ROOT.is_relative_to(OUT);OUT.mkdir(exist_ok=False)
(OUT/'driver-at-run.py').write_bytes(Path(__file__).read_bytes())
RUN=OUT/'runtime';RUN.mkdir(mode=0o700)
REAM=ROOT/'bin/ream';GETH=ROOT/'bin/geth';TOOL=ROOT/'bin/profile-tool-three'
result={'status':'RUNNING','review':'loop-internal self-review; not independently reviewed','scope':'ordinary devnet5 Ream; three validators on two independent geth nodes; one minority migration block orphaned by majority; original submitter retries only after actual pre-T rejection and restored eligibility','samples':1,'commands':[]}
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
 old.update(t0=genesis_time+12,t=genesis_time+180,receivingTime=genesis_time+12)
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
 l1meta=l1_carriers.generate(ROOT,OUT/'txs',args.inputs)
 for kind in ['activate','spend']:txmeta[kind]=l1meta['carriers'][kind]
 (OUT/'txs/txs.json').write_text(json.dumps(txmeta,indent=2)+'\n')
 (OUT/'el-genesis.json').write_text(json.dumps(genesis,indent=2))
 result['preflight']=preflight(ROOT,OUT/'el-genesis.json',args.inputs);save()
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
 for name in nodes:start_ream(name,1)
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
 # The majority branch uses ordinary raw submission before T. Ream alone
 # advances Engine state; the driver never manufactures a block or vote.
 result['preT']={'steps':{}}
 print('Pre-T: waiting for the enrollment window',flush=True)
 deadline=time.monotonic()+180
 while time.monotonic()<deadline:
  try:
   block=rpc(nodes['B']['url'],'eth_getBlockByNumber',['latest',False])
   if int(block['timestamp'],16)>=old['t0']:break
  except (OSError,ValueError):pass
  time.sleep(.5)
 else:raise RuntimeError('pre-T receiving window did not start')
 for kind in ['pre-legacy','pre-enroll','pre-activate']:
  subject=txmeta['legacyCutoffOwner'] if kind=='pre-legacy' else txmeta['preTEnrollmentOwner']
  pre_before=rpc(nodes['B']['url'],'eth_getPQAccount',[subject,'latest'])
  tx=txmeta[kind];raw_pre=(OUT/'txs'/(kind+'.bin')).read_bytes()
  assert rpc(nodes['B']['url'],'eth_sendRawTransaction',['0x'+raw_pre.hex()])==tx['hash']
  deadline=time.monotonic()+90
  while time.monotonic()<deadline:
   receipt_pre=rpc(nodes['B']['url'],'eth_getTransactionReceipt',[tx['hash']])
   if receipt_pre:break
   time.sleep(.5)
  else:raise RuntimeError(kind+' was not included')
  block=rpc(nodes['B']['url'],'eth_getBlockByHash',[receipt_pre['blockHash'],False])
  assert receipt_pre['status']=='0x1' and int(block['timestamp'],16)<old['t'],(kind,receipt_pre,block['timestamp'])
  result['preT']['steps'][kind]={'receipt':receipt_pre,'timestamp':int(block['timestamp'],16),
       'accountAddress':subject,'beforeAccount':pre_before,'account':rpc(nodes['B']['url'],'eth_getPQAccount',[subject,'latest'])};save()
  print(kind+': included before T',flush=True)
 assert result['preT']['steps']['pre-activate']['account']['activated']
 deadline=time.monotonic()+240
 while time.monotonic()<deadline:
  time.sleep(1)
  try:data=observe('partition-start')
  except (OSError,ValueError):continue
  if min(int(data[n]['cl']['slot']) for n in nodes)>=3 and all(account(n)['ecdsaDead'] for n in nodes.values()):break
 else:raise RuntimeError('partition did not advance to recovery window')
 result['legacyAfterT']=[]
 for name,n in nodes.items():
  request=urllib.request.Request(n['url'],json.dumps({'jsonrpc':'2.0','id':1,'method':'eth_sendRawTransaction','params':['0x'+(OUT/'txs/post-legacy.bin').read_bytes().hex()]}).encode(),{'Content-Type':'application/json'})
  with urllib.request.urlopen(request,timeout=10) as response:answer=json.load(response)
  assert 'error' in answer and 'ECDSA_DISABLED' in json.dumps(answer['error']),(name,answer)
  assert rpc(n['url'],'eth_getTransactionReceipt',[txmeta['post-legacy']['hash']]) is None
  result['legacyAfterT'].append({'node':name,'error':answer['error']})
 save()
 # Both actual nodes must refuse altered carriers before any honest migration.
 result['negativeSubmissions']=[]
 for name,n in nodes.items():
  before=account(n)
  for kind,reason in [('over-proof','PROOF_TOO_LARGE'),('over-cap','STOCK_REJECTION')]:
   bad=(OUT/'txs'/(kind+'.bin')).read_bytes()
   request=urllib.request.Request(n['url'],json.dumps({'jsonrpc':'2.0','id':1,'method':'eth_sendRawTransaction','params':['0x'+bad.hex()]}).encode(),{'Content-Type':'application/json'})
   with urllib.request.urlopen(request,timeout=10) as response:answer=json.load(response)
   assert 'error' in answer and reason in json.dumps(answer['error']),(name,kind,answer)
   badhash=txmeta[kind]['hash']
   assert rpc(n['url'],'eth_getTransactionReceipt',[badhash]) is None
   assert badhash not in json.dumps(rpc(n['url'],'pqpool_content',[]))
   result['negativeSubmissions'].append({'node':name,'kind':kind,'hash':badhash,'error':answer['error']})
  assert account(n)==before
 save()

 result['recoveryBefore']={name:account(n) for name,n in nodes.items()}
 raw=(OUT/'txs/migrate.bin').read_bytes();txhash=txmeta['migrate']['hash']
 assert rpc(nodes['A']['url'],'eth_sendRawTransaction',['0x'+raw.hex()])==txhash
 result['rawSubmissions']=[{'node':'A','kind':'migrate','hash':txhash}]
 result['admission']={'A':rpc(nodes['A']['url'],'pqpool_content',[]),'B':rpc(nodes['B']['url'],'pqpool_content',[])};save()
 deadline=time.monotonic()+180
 while time.monotonic()<deadline:
  time.sleep(.5)
  receipt=rpc(nodes['A']['url'],'eth_getTransactionReceipt',[txhash])
  if receipt:break
 else:raise RuntimeError('minority recovery was not included')
 assert receipt['status']=='0x1' and rpc(nodes['B']['url'],'eth_getTransactionReceipt',[txhash]) is None
 data=observe('minority-included');minority_slot=int(data['A']['cl']['slot'])
 result['orphanCandidate']={'receipt':receipt,'cl':data['A']['cl'],'account':account(nodes['A'])}
 (OUT/'minority-migration-block.rlp').write_bytes(bytes.fromhex(rpc(nodes['A']['url'],'debug_getRawBlock',[receipt['blockHash']])[2:]))
 old_histories={name:n['history'].read_bytes() for name,n in nodes.items()}
 for name,h in old_histories.items():(OUT/(name+'-history-before-rejoin.bin')).write_bytes(h)
 # A stops signing while the two other real validators continue the majority
 # branch. No Engine command, vote, block or finalized pointer is manufactured.
 stop(nodes['A']['ream']);assert not (nodes['A']['dir']/'signing-fence').exists()
 deadline=time.monotonic()+180
 while time.monotonic()<deadline:
  time.sleep(1)
  majority=rest(nodes['B']['rest'],'blocks/finalized')
  if int(majority['slot'])>minority_slot:break
 else:raise RuntimeError('real majority did not finalize beyond minority inclusion')
 assert rpc(nodes['B']['url'],'eth_getTransactionReceipt',[txhash]) is None
 result['majorityBeforeRejoin']=majority;save()
 a=nodes['A'];b=nodes['B']
 a['reamargs'][a['reamargs'].index('--bootnodes')+1]=f'/ip4/127.0.0.1/udp/{b["p2p"]}/quic-v1/p2p/{b["peerid"]}'
 (a['dir']/'session-2').write_bytes(os.urandom(32));a['config']['session_path']=str(a['dir']/'session-2')
 (a['dir']/'engine-2.json').write_text(json.dumps(a['config']));start_ream('A',2)
 deadline=time.monotonic()+240;requeued=False;changed=False;rollback_observed=False;retried=False
 while time.monotonic()<deadline:
  time.sleep(.25)
  try:
   current=rpc(a['url'],'eth_getBlockByNumber',[receipt['blockNumber'],False])
   rec={name:rpc(n['url'],'eth_getTransactionReceipt',[txhash]) for name,n in nodes.items()}
   state=account(a)
  except (OSError,ValueError):continue
  changed=changed or current is None or current['hash']!=receipt['blockHash']
  rollback_observed=rollback_observed or (changed and state['mode']=='0x0')
  log=(OUT/'A-geth-1.log').read_text(errors='replace')
  requeued=any('PQPOOL_REORG_REINJECT' in line and txhash[2:].lower() in line.lower() for line in log.splitlines())
  rejected=[]
  for line in log.splitlines():
   try:event=json.loads(line)
   except ValueError:continue
   if event.get('msg')=='PQPOOL_REORG_REJECT' and event.get('txhash')==txhash and 'FORK_NOT_ACTIVE' in event.get('err',''):rejected.append(event)
  if changed and rejected and not retried and state['mode']=='0x0' and not any(rec.values()):
   # Spec 20.17(b,d): no node queues a recovery for a future chain state.
   # The original submitter waits for actual canonical eligibility, then
   # explicitly re-submits unchanged bytes. This is not automatic reinjection.
   heads={name:rpc(n['url'],'eth_getBlockByNumber',['latest',False]) for name,n in nodes.items()}
   if heads['A']['hash']==heads['B']['hash'] and all(int(h['timestamp'],16)>=old['t'] for h in heads.values()):
    assert all(txhash not in rpc(n['url'],'pqpool_content',[]) for n in nodes.values())
    assert all(account(n)['mode']=='0x0' and account(n)['migrationNonce']=='0x0' for n in nodes.values())
    assert rpc(a['url'],'eth_sendRawTransaction',['0x'+raw.hex()])==txhash
    retried=True
    result['ownerRetryAfterPreTReorg']={'reason':'FORK_NOT_ACTIVE at intermediate canonical head; spec 20.17(b,d)','rejections':rejected,'eligibleHeads':heads,'time':time.time(),'rawSHA256':hashlib.sha256(raw).hexdigest()}
    result['rawSubmissions'].append({'node':'A','kind':'migrate','hash':txhash,'reason':'explicit original submitter retry after canonical eligibility'});save()

  if changed and (requeued or retried) and all(rec.values()) and rec['A']==rec['B'] and rec['A']['blockHash']!=receipt['blockHash']:break
 else:raise RuntimeError(f'migration reorg/reinjection/reinclusion timeout: changed={changed}, requeued={requeued}')
 assert rec['A']['status']=='0x1'
 result['recoveryReinclusion']={'receipts':rec,'canonicalOldHeight':current,'reinjectLogObserved':requeued,'rollbackStateSampled':rollback_observed,'rawRecoverySubmissions':len([x for x in result['rawSubmissions'] if x['kind']=='migrate']),'method':'original-submitter-retry' if retried else 'automatic-reinjection'}
 for name,n in nodes.items():
  state=account(n);assert state['mode']=='0x2' and state['migrationNonce']=='0x1' and state['pqPkCommit']==fields['pq_pk_commit'] and not state['activated']
  assert rpc(n['url'],'eth_getRawTransactionByHash',[txhash])=='0x'+raw.hex()
  assert n['history'].read_bytes().startswith(old_histories[name])
 result['afterRejoin']=observe('reincluded')
 result['recoveryReinclusion']['accounts']={name:account(n) for name,n in nodes.items()}
 result['recoveryReinclusion']['accountAddress']=owner
 result['recoveryReinclusion']['beforeAccounts']=result['recoveryBefore'];save()
 print('Recovery: A included; B imported; reorg removed and re-included the transaction',flush=True)
 for kind,step in result['preT']['steps'].items():
  receipts={name:rpc(n['url'],'eth_getTransactionReceipt',[txmeta[kind]['hash']]) for name,n in nodes.items()}
  assert receipts['A']==receipts['B']==step['receipt'],(kind,receipts)
  step['receipts']=receipts
 for n in nodes.values():
  prestate=rpc(n['url'],'eth_getPQAccount',[txmeta['preTEnrollmentOwner'],'latest'])
  assert prestate['activated'] and prestate['pqPkCommit'].lower()==txmeta['preTEnrollmentCommit'].lower()
 result['preT']['status']='PASS';save()
 l1_live.before_activation(globals())
 activation_before={name:account(n) for name,n in nodes.items()}
 raw_activation=(OUT/'txs/activate.bin').read_bytes();activation_hash=txmeta['activate']['hash']
 assert rpc(a['url'],'eth_sendRawTransaction',['0x'+raw_activation.hex()])==activation_hash
 result['rawSubmissions'].append({'node':'A','kind':'activate','hash':activation_hash});save()
 deadline=time.monotonic()+180
 while time.monotonic()<deadline:
  time.sleep(1);activation={name:rpc(n['url'],'eth_getTransactionReceipt',[activation_hash]) for name,n in nodes.items()}
  if all(activation.values()) and activation['A']==activation['B']:break
 else:raise RuntimeError('activation inclusion timeout')
 result['activationBeforeAssertion']={'receipts':activation,'accounts':{name:account(n) for name,n in nodes.items()}};save()
 assert activation['A']['status']=='0x1'
 result['activation']={'accountAddress':owner,'beforeAccounts':activation_before,'receipts':activation,'accounts':{name:account(n) for name,n in nodes.items()}}
 assert result['activation']['accounts']['A']==result['activation']['accounts']['B']
 assert all(x['activated'] for x in result['activation']['accounts'].values())
 l1_live.after_activation(globals())
 # The rotated key authorizes the first spend.
 spend_before={name:account(n) for name,n in nodes.items()}
 raw_spend=(OUT/'txs/spend.bin').read_bytes();spend_hash=txmeta['spend']['hash']
 assert rpc(a['url'],'eth_sendRawTransaction',['0x'+raw_spend.hex()])==spend_hash
 result['rawSubmissions'].append({'node':'A','kind':'spend','hash':spend_hash});save()
 deadline=time.monotonic()+180
 while time.monotonic()<deadline:
  time.sleep(1);spending={name:rpc(n['url'],'eth_getTransactionReceipt',[spend_hash]) for name,n in nodes.items()}
  if all(spending.values()) and spending['A']==spending['B']:break
 else:raise RuntimeError('first PQ spend inclusion timeout')
 assert spending['A']['status']=='0x1'
 result['spend']={'accountAddress':owner,'beforeAccounts':spend_before,'receipts':spending,'accounts':{name:account(n) for name,n in nodes.items()},'recipient':txmeta['recipient'],'value':txmeta['spendValue']}
 for n in nodes.values():
  assert int(rpc(n['url'],'eth_getBalance',[txmeta['recipient'],'latest']),16)==txmeta['spendValue']
  assert int(rpc(n['url'],'eth_getTransactionCount',[owner,'latest']),16)==4
 save()

 data=observe('before-restart');result['beforeRestart']=data;save()
 for n in nodes.values():stop(n['ream'])
 for n in nodes.values():stop(n['geth']);assert not (n['dir']/'signing-fence').exists()
 histories={name:n['history'].read_bytes() for name,n in nodes.items()}
 for name,n in nodes.items():
  (OUT/(name+'-history-before-restart.bin')).write_bytes(histories[name])
  n['geth']=spawn(name+'-geth-3',n['gethargs'],{'PQ_LEAN_FENCE_PATH':str(n['dir']/'signing-fence')})
  wait_ready(lambda:rpc(n['url'],'eth_blockNumber',[]))
  (n['dir']/'session-3').write_bytes(os.urandom(32));n['config']['session_path']=str(n['dir']/'session-3')
  (n['dir']/'engine-3.json').write_text(json.dumps(n['config']))
 for name in nodes:start_ream(name,3)
 deadline=time.monotonic()+240
 while time.monotonic()<deadline:
  time.sleep(1)
  try:after=observe('restart');final={name:rpc(n['url'],'eth_getBlockByNumber',['finalized',False]) for name,n in nodes.items()}
  except (OSError,ValueError):continue
  if after['A']['cl']==after['B']['cl'] and int(after['A']['cl']['slot'])>max(int(data[n]['cl']['slot']) for n in nodes) and all(x and int(x['number'],16)>=int(spending['A']['blockNumber'],16) for x in final.values()):break
 else:raise RuntimeError('restart/finality timeout')
 for name,n in nodes.items():
  assert n['history'].read_bytes().startswith(histories[name]) and histories[name].startswith(old_histories[name])
  (OUT/(name+'-final-signing-history.bin')).write_bytes(n['history'].read_bytes())
  assert rpc(n['url'],'eth_getTransactionReceipt',[txhash])==rec[name]
  assert rpc(n['url'],'eth_getTransactionReceipt',[activation_hash])==activation[name]
  assert rpc(n['url'],'eth_getTransactionReceipt',[spend_hash])==spending[name]
  assert account(n)==result['spend']['accounts'][name]
  assert int(rpc(n['url'],'eth_getBalance',[txmeta['recipient'],'latest']),16)==txmeta['spendValue']
  assert int(rpc(n['url'],'eth_getTransactionCount',[owner,'latest']),16)==4
 for name,n in nodes.items():
  for kind,step in result['preT']['steps'].items():
   assert rpc(n['url'],'eth_getTransactionReceipt',[txmeta[kind]['hash']])==step['receipt']
  prestate=rpc(n['url'],'eth_getPQAccount',[txmeta['preTEnrollmentOwner'],'latest'])
  assert prestate['activated'] and prestate['pqPkCommit'].lower()==txmeta['preTEnrollmentCommit'].lower()
 result['preT']['preservedAfterRestart']=True
 result['walletQuery']={}
 for name,n in nodes.items():
  queried=json.loads(command('wallet-query-'+name,[sys.executable,'-B',ROOT/'wallet/cli.py','query','--rpc',n['url'],'--address',owner]))
  assert queried['account']==account(n) and int(queried['nonce'],16)==4
  result['walletQuery'][name]=queried
 l1_live.after_restart(globals())
 print('Restart: both nodes resumed; receipts, balances and signing histories preserved',flush=True)
 result.update(status='PASS',afterRestart=after,finalizedExecution=final,historyAppendOnly=True,reorg='migration-bearing block replaced; '+result['recoveryReinclusion']['method'])
except Exception as error:
 import traceback
 result.update(status='FAIL',failure=type(error).__name__+': '+str(error),traceback=traceback.format_exc())
finally:
 for p in reversed(processes):stop(p)
 for f in files:f.close()
 result['processesStopped']=all(p.poll() is not None for p in processes);save()
 print(json.dumps({k:result.get(k) for k in ['status','failure','historyAppendOnly','processesStopped']}))

raise SystemExit(0 if result["status"]=="PASS" else 1)
