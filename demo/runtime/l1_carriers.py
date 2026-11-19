"""L1 public test carriers using the frozen wallet wire/signing implementation.
This exercises client execution, not the wallet's compromise-tracking acceptance.
"""
import argparse,ctypes,hashlib,json,sys,time
from pathlib import Path
from types import SimpleNamespace
sys.dont_write_bytecode=True

def generate(root,out,inputs):
 sys.path.insert(0,str(root/'wallet'));import wallet as w
 helper=root/'prover-runtime/bin/pq-test-crypto'
 build=json.loads((root/'prover-runtime/BUILD.json').read_text())
 assert build['status']=='PASS' and hashlib.sha256(helper.read_bytes()).hexdigest()==build['binaries']['pq-test-crypto']
 cr=w.wire.Worker(helper)
 try:
  cfg=json.loads((inputs/'recovery/config.json').read_text());owner=bytes.fromhex(cfg['fields']['legacy_address'][2:]);xi=bytes.fromhex(cfg['xi_hex']);pk=bytes.fromhex(cfg['public_key_hex']);key=w.KeyMaterial(0,xi,pk,cr('hash',b'\x01'+pk))
  sp=json.loads((root/'share/l1/PUBLIC-sponsor.json').read_text());sxi=bytes.fromhex(sp['xi']);spk=bytes.fromhex(sp['pk']);saddr=bytes.fromhex(sp['address'])
  assert cr('pk',sxi)==spk and cr('hash',b'PQ-ADDR\x01'+spk)[12:]==saddr
  config=dict(chain_id=13378,registry='0x'+'00'*18+'0800',max_priority_fee_per_gas=10**9,max_fee_per_gas=2*10**9,migration_gas_limit=16000000,pq_transaction_gas_limit=1500000)
  meta=dict(owner='0x'+owner.hex(),sponsor='0x'+saddr.hex(),recipient='0x'+'00'*18+'beef',spendValue=1000000,publicTestOnly=True,scope='wallet wire/signing plus real client; no full wallet UI/tracking claim',carriers={})
  def save(name,raw,**info):
   (out/(name+'.bin')).write_bytes(raw);meta['carriers'][name]=dict(hash='0x'+cr('hash',raw).hex(),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),**info)
  def sign_tx(sender,signer,nonce,to,value=0,data=b'',activate=False,gas=1500000):
   tx=[13378,sender,nonce,10**9,2*10**9,gas,to,value,data,[],1,[signer.public_key] if activate else [],b''];msg=w.PQ_TX_TAG+cr('hash',b'\x7c'+w.wire.rlp(tx));tx[12]=cr('sign',signer.xi,msg,w.PQ_TX_TAG);assert cr.text('verify',signer.public_key,msg,w.PQ_TX_TAG,tx[12])=='true';return b'\x7c'+w.wire.rlp(tx)
  skey=w.KeyMaterial(0,sxi,spk,cr('hash',b'\x01'+spk))
  save('sponsor-activate',sign_tx(saddr,skey,0,saddr,activate=True))
  # A fixed authenticated native F verifier binds the complete PI in process.
  native=ctypes.CDLL(str(root/'lib/libpq_final_native.so'))
  native.pq_f_ready_v1.restype=ctypes.c_int32;assert native.pq_f_ready_v1()==0
  native.pq_f_verify_v1.argtypes=[ctypes.c_char_p,ctypes.c_size_t,ctypes.c_char_p,ctypes.c_size_t];native.pq_f_verify_v1.restype=ctypes.c_int32
  for mode in [1,2,3]:
   d=inputs/('mode'+str(mode));pi=bytes.fromhex((d/'pi198.hex').read_text().strip());proof=(d/'proof.postcard').read_bytes()
   assert pi[64:84]==owner and int.from_bytes(pi[84:92],'big')==mode and pi[93:125]==key.commitment and pi[169]==mode
   assert native.pq_f_verify_v1(proof,len(proof),pi,len(pi))==0
   expiry=int.from_bytes(pi[129:137],'big');cap=int.from_bytes(pi[137:169],'big');until=int.from_bytes(pi[190:198],'big');assert int(time.time())+1800<expiry<=int(time.time())+7*86400
   consent=w.fee_consent(layout=2,max_account_fee=cap,verifier_version=0x80000008,fee_auth_until=until) if mode==3 else None
   fee=w.FeeChoice(fee_mode=mode,fee_sponsor=pi[170:190].hex(),fee_auth_until=until,consent=consent['token'] if consent else None)
   sponsor=w.Sponsor(saddr.hex(),expiry,lambda msg,ctx:cr('sign',sxi,msg,ctx),spk)
   state=SimpleNamespace(chain_id=13378,legacy_address=owner.hex())
   raw=w._encode_0x7e(state,mode,pi,proof,config,fee,sponsor=sponsor,crypto=cr)
   save('mode'+str(mode),raw,piSHA256=hashlib.sha256(pi).hexdigest(),proofSHA256=hashlib.sha256(proof).hexdigest(),proofBytes=len(proof),reimbursement=cap if mode!=2 else 0,consent=consent)
   bad=bytearray(proof);bad[len(bad)//2]^=1
   save('mode'+str(mode)+'-bad-proof',w._encode_0x7e(state,mode,pi,bytes(bad),config,fee,sponsor=sponsor,crypto=cr))
   badpi=bytearray(pi);badpi[124]^=1
   save('mode'+str(mode)+'-bad-pi',w._encode_0x7e(state,mode,bytes(badpi),proof,config,fee,sponsor=sponsor,crypto=cr))
  raw,row=w._signed_rotate_0x7c(cr,config,owner,key,0,True);save('activate',raw,wallet=row,kind='activating-same-key-rotate')
  seed=hashlib.pbkdf2_hmac('sha512',(' '.join(['abandon']*11+['about'])).encode(),b'mnemonic',2048,64)
  nextxi=w.derive_epoch_seed(seed,'ML-DSA-44',(44+2**31,60+2**31,2**31,0,0),1);nextpk=cr('pk',nextxi);nextkey=w.KeyMaterial(1,nextxi,nextpk,cr('hash',b'\x01'+nextpk))
  pop=w.ROTATE_POP_TAG+cr('hash',w.rotate_pop_preimage(13378,owner,1,1,nextpk));ps=cr('sign',nextxi,pop,w.ROTATE_POP_TAG)
  data=w.rotate_calldata(1,nextpk,ps);save('rotate-new',sign_tx(owner,key,1,bytes.fromhex(config['registry'][2:]),data=data))
  raw,row=w._signed_rotate_0x7c(cr,config,owner,nextkey,2,False);save('rotate-same',raw,wallet=row,kind='activated-same-key-rotate')
  recipient=bytes.fromhex(meta['recipient'][2:]);save('old-key-spend',sign_tx(owner,key,3,recipient,value=1000000,gas=250000))
  save('spend',sign_tx(owner,nextkey,3,recipient,value=1000000,gas=250000))
  meta['newCommit']='0x'+nextkey.commitment.hex();meta['finalNonce']=4;meta['finalMigrationNonce']=7
  (out/'l1-carriers.json').write_text(json.dumps(meta,indent=2)+'\n');return meta
 finally:cr.close()

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--inputs',type=Path,required=True);a=ap.parse_args();a.out.mkdir(exist_ok=True);generate(a.root,a.out,a.inputs)
