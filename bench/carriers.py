"""Build public-test wallet carriers, without changing the frozen wallet or PI."""
import argparse, hashlib, json, sys, time
from pathlib import Path
from types import SimpleNamespace
REPO=Path(__file__).resolve().parents[1]
sys.dont_write_bytecode=True
def main(root,build):
 sys.path.insert(0,str(REPO/'wallet')); import wallet as w
 out=root/'carriers';out.mkdir(exist_ok=False)
 tool=build/'bin/pq-test-crypto'
 assert hashlib.sha256(tool.read_bytes()).hexdigest()==json.loads((build/'BUILD.json').read_text())['binaries']['pq-test-crypto']
 cr=w.wire.Worker(tool)
 try:
  keyj=json.loads((root/'mode0-01/statement/pq-key.json').read_text())
  # The statement exports the same wallet epoch rule. No private user credential is used.
  seed=hashlib.pbkdf2_hmac('sha512',(' '.join(['abandon']*11+['about'])).encode(),b'mnemonic',2048,64)
  path=(44+2**31,60+2**31,2**31,0,0)
  def key(epoch):
   xi=w.derive_epoch_seed(seed,'ML-DSA-44',path,epoch);pk=cr('pk',xi)
   return w.KeyMaterial(epoch,xi,pk,cr('hash',b'\x01'+pk))
  k0,k1=key(0),key(1)
  assert k0.public_key.hex()==keyj['public_key_hex'] and k0.commitment.hex()==keyj['pq_pk_commit']
  owner=bytes.fromhex('9858effd232b4033e47d90003d41ec34ecaeda94')
  sj=json.loads((root/'PUBLIC-sponsor.json').read_text());sa=bytes.fromhex(sj['address']);sx=bytes.fromhex(sj['xi']);spk=bytes.fromhex(sj['pk'])
  sk=w.KeyMaterial(0,sx,spk,cr('hash',b'\x01'+spk));recipient=bytes.fromhex('00'*18+'beef')
  cfg=dict(chain_id=13378,registry='0x'+'00'*18+'0800',max_priority_fee_per_gas=10**9,max_fee_per_gas=2*10**9,migration_gas_limit=16000000,pq_transaction_gas_limit=1500000)
  info=dict(publicTestOnly=True,owner='0x'+owner.hex(),recipient='0x'+recipient.hex(),sponsor='0x'+sa.hex(),ownerKey=k0.public_key.hex(),newKey=k1.public_key.hex(),ownerCommit='0x'+k0.commitment.hex(),newCommit='0x'+k1.commitment.hex(),sponsorKey=spk.hex(),carriers={})
  def save(name,raw):
   (out/(name+'.bin')).write_bytes(raw);info['carriers'][name]=dict(bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),hash='0x'+cr('hash',raw).hex())
  def sign(sender,k,nonce,to,value=0,data=b'',activate=False,gas=1500000):
   tx=[13378,sender,nonce,10**9,2*10**9,gas,to,value,data,[],1,[k.public_key] if activate else [],b'']
   msg=w.PQ_TX_TAG+cr('hash',b'\x7c'+w.wire.rlp(tx));tx[12]=cr('sign',k.xi,msg,w.PQ_TX_TAG)
   assert cr.text('verify',k.public_key,msg,w.PQ_TX_TAG,tx[12])=='true'
   return b'\x7c'+w.wire.rlp(tx)
  for row in json.loads((root/'PLAN.json').read_text())['samples']:
   name=row['name'];d=root/name;pi=bytes.fromhex((d/'statement/pi198.hex').read_text().strip());proof=(d/'f/proof.postcard').read_bytes();mode=row['mode']
   assert pi[64:84]==owner and int.from_bytes(pi[84:92],'big')==0 and pi[93:125]==k0.commitment and pi[169]==mode
   expiry=int.from_bytes(pi[129:137],'big');cap=int.from_bytes(pi[137:169],'big');until=int.from_bytes(pi[190:198],'big')
   assert time.time()+1800<expiry<=time.time()+604800
   consent=w.fee_consent(layout=2,max_account_fee=cap,verifier_version=0x80000008,fee_auth_until=until) if mode==3 else None
   fee=w.FeeChoice(fee_mode=mode,fee_sponsor=pi[170:190].hex(),fee_auth_until=until,consent=consent['token'] if consent else None)
   sponsor=w.Sponsor(sa.hex(),expiry,lambda msg,ctx:cr('sign',sx,msg,ctx),spk) if mode else None
   save(name,w._encode_0x7e(SimpleNamespace(chain_id=13378,legacy_address=owner.hex()),0,pi,proof,cfg,fee,sponsor=sponsor,crypto=cr))
  save('activate',sign(owner,k0,0,owner,activate=True))
  save('spend',sign(owner,k0,1,recipient,value=1000000,gas=250000))
  def rotate(name,old,new,nonce,activate):
   pop=w.ROTATE_POP_TAG+cr('hash',w.rotate_pop_preimage(13378,owner,nonce,1,new.public_key))
   sig=cr('sign',new.xi,pop,w.ROTATE_POP_TAG)
   save(name,sign(owner,old,nonce,bytes.fromhex(cfg['registry'][2:]),data=w.rotate_calldata(1,new.public_key,sig),activate=activate))
  rotate('rotate-new',k0,k1,2,False);rotate('rotate-same',k1,k1,3,False)
  rotate('rotate-activating',k0,k1,0,True)
  save('sponsor-activate',sign(sa,sk,0,sa,activate=True))
  (out/'manifest.json').write_text(json.dumps(info,indent=2)+'\n')
 finally: cr.close()
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--build',type=Path,required=True);a=ap.parse_args();main(a.root,a.build)
