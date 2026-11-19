"""L1 assertions inside the installed real Lean driver; never calls Engine RPC."""
import json,time,urllib.request

def setup(g):
 global rpc,nodes,a,OUT,result,save,meta,owner
 rpc,nodes,a,OUT,result,save,owner=(g[k] for k in ['rpc','nodes','a','OUT','result','save','owner'])
 meta=json.loads((OUT/'txs/l1-carriers.json').read_text())
 result['l1']={'status':'RUNNING','steps':{},'negativeSubmissions':[],'walletScope':meta['scope']};save()

def balances():
 return {n:{role:int(rpc(x['url'],'eth_getBalance',[addr,'latest']),16) for role,addr in [('owner',owner),('sponsor',meta['sponsor'])]} for n,x in nodes.items()}

def submit(kind):
 subject=meta['sponsor'] if kind=='sponsor-activate' else owner
 before_accounts={n:rpc(x['url'],'eth_getPQAccount',[subject,'latest']) for n,x in nodes.items()}
 tx=meta['carriers'][kind];raw=(OUT/'txs'/(kind+'.bin')).read_bytes();before=balances()
 assert rpc(a['url'],'eth_sendRawTransaction',['0x'+raw.hex()])==tx['hash']
 result['rawSubmissions'].append({'node':'A','kind':kind,'hash':tx['hash']});save()
 end=time.monotonic()+180
 while time.monotonic()<end:
  rec={n:rpc(x['url'],'eth_getTransactionReceipt',[tx['hash']]) for n,x in nodes.items()}
  if all(rec.values()) and rec['A']==rec['B']:break
  time.sleep(.5)
 else:raise RuntimeError(kind+' inclusion/import timeout')
 assert rec['A']['status']=='0x1',(kind,rec)
 after=balances();accounts={n:rpc(x['url'],'eth_getPQAccount',[subject,'latest']) for n,x in nodes.items()};assert accounts['A']==accounts['B']
 step={'accountAddress':subject,'beforeAccounts':before_accounts,'receipts':rec,'beforeBalances':before,'afterBalances':after,'accounts':accounts}
 result['l1']['steps'][kind]=step;save()
 print(kind+': A and B agree; gas '+str(int(rec['A']['gasUsed'],16)),flush=True)
 return step

def reject(kind,reason,only=None):
 raw=(OUT/'txs'/(kind+'.bin')).read_bytes();tx=meta['carriers'][kind]
 for n,x in nodes.items():
  if only is not None and n!=only:continue
  before=rpc(x['url'],'eth_getPQAccount',[owner,'latest'])
  req=urllib.request.Request(x['url'],json.dumps({'jsonrpc':'2.0','id':1,'method':'eth_sendRawTransaction','params':['0x'+raw.hex()]}).encode(),{'Content-Type':'application/json'})
  with urllib.request.urlopen(req,timeout=15) as r:answer=json.load(r)
  assert 'error' in answer and reason in json.dumps(answer['error']),(kind,n,answer)
  assert rpc(x['url'],'eth_getTransactionReceipt',[tx['hash']]) is None
  assert tx['hash'] not in json.dumps(rpc(x['url'],'pqpool_content',[]))
  assert rpc(x['url'],'eth_getPQAccount',[owner,'latest'])==before
  result['l1']['negativeSubmissions'].append({'kind':kind,'node':n,'hash':tx['hash'],'error':answer['error']})
 save()

def before_activation(g):
 setup(g);submit('sponsor-activate')
 for n,x in nodes.items():
  s=rpc(x['url'],'eth_getPQAccount',[meta['sponsor'],'latest']);assert s['activated'] and s['mode']=='0x3'
 for mode in [1,2,3]:
  kind='mode'+str(mode)
  # Keep below the unchanged four-invalid-proofs/hour local-source budget.
  # Both controls are exercised per mode, on alternate real nodes; valid
  # proofs are still verified on both nodes during build/import.
  reject(kind+'-bad-proof','INVALID_PROOF',only='A' if mode%2 else 'B')
  reject(kind+'-bad-pi','INVALID_PROOF',only='B' if mode%2 else 'A')
  step=submit(kind);expected=meta['carriers'][kind]['reimbursement']
  for n,x in nodes.items():
   rc=step['receipts'][n];fee=int(rc['gasUsed'],16)*int(rc['effectiveGasPrice'],16)
   assert step['beforeBalances'][n]['owner']-step['afterBalances'][n]['owner']==expected
   assert step['afterBalances'][n]['sponsor']-step['beforeBalances'][n]['sponsor']==expected-fee
   st=step['accounts'][n];assert st['migrationNonce']==hex(mode+1) and not st['activated'] and st['pqPkCommit']==g['fields']['pq_pk_commit']
   assert int(rpc(x['url'],'eth_getTransactionCount',[owner,'latest']),16)==0
   assert int(rpc(x['url'],'eth_getTransactionCount',[meta['sponsor'],'latest']),16)==1
  step['exactReimbursementWei']=expected;save()

def after_activation(g):
 for s in g['result']['activation']['accounts'].values():assert s['migrationNonce']=='0x5' and s['pqPkCommit']==g['fields']['pq_pk_commit']
 logs=g['result']['activation']['receipts']['A']['logs'];assert len(logs)==2
 assert logs[0]['topics'][0]=='0x0cc43938d137e7efade6a531f663e78c1fc75257b0d65ffda2fdaf70cb49cdf9'
 assert logs[1]['topics'][0]=='0x83e6ff4be6ffbd30ceb79255896a32e7ff2a13554a5088cff7379480602fbb1e'
 for kind,migrationNonce in [('rotate-new',6),('rotate-same',7)]:
  step=submit(kind)
  for s in step['accounts'].values():assert s['migrationNonce']==hex(migrationNonce) and s['pqPkCommit']==meta['newCommit'] and s['activated']
  assert len(step['receipts']['A']['logs'])==1
 reject('old-key-spend','BAD_PQ_SIG')
 result['l1']['status']='PASS';save()

def after_restart(g):
 for n,x in nodes.items():
  for kind,step in result['l1']['steps'].items():
   assert rpc(x['url'],'eth_getTransactionReceipt',[meta['carriers'][kind]['hash']])==step['receipts'][n],(n,kind,'restart receipt')
  st=rpc(x['url'],'eth_getPQAccount',[owner,'latest'])
  assert st['activated'] and st['pqPkCommit']==meta['newCommit'] and int(st['migrationNonce'],16)==meta['finalMigrationNonce']
  assert int(rpc(x['url'],'eth_getTransactionCount',[owner,'latest']),16)==meta['finalNonce']
  assert int(rpc(x['url'],'eth_getTransactionCount',[meta['sponsor'],'latest']),16)==1
 result['l1']['restartVerified']=True;save()
