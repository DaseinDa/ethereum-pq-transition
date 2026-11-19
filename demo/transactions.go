// Public test carriers for F/PI198; same geth encoder and ML-DSA-44 verifier as execution.
package main
import (
    "bytes"
    "encoding/binary"
    "encoding/hex"
    "encoding/json"
    "flag"
    "math/big"
    "os"
    "path/filepath"
    "strings"
    "github.com/cloudflare/circl/sign/mldsa/mldsa44"
    "github.com/ethereum/go-ethereum/common"
    "github.com/ethereum/go-ethereum/core"
    "github.com/ethereum/go-ethereum/core/types"
    "github.com/ethereum/go-ethereum/crypto"
)
func must(err error){if err!=nil{panic(err)}}
func read(p string)[]byte{b,e:=os.ReadFile(p);must(e);return b}
func main(){
    config:=flag.String("config","","fixture config")
    root:=flag.String("root","","F proof")
    out:=flag.String("out","","fresh output")
    flag.Parse()
    var cfg struct {PI string `json:"pi198_hex"`;Xi string `json:"xi_hex"`;PK string `json:"public_key_hex"`}
    must(json.Unmarshal(read(*config),&cfg))
    pi,e:=hex.DecodeString(cfg.PI);must(e);if len(pi)!=198{panic("PI length")}
    seed,e:=hex.DecodeString(cfg.Xi);must(e);if len(seed)!=32{panic("xi length")}
    var xi [32]byte;copy(xi[:],seed);pk,sk:=mldsa44.NewKeyFromSeed(&xi);pub,e:=pk.MarshalBinary();must(e)
    if hex.EncodeToString(pub)!=strings.TrimPrefix(cfg.PK,"0x"){panic("FIPS204/CIRCL public key differs")}
    commit:=crypto.Keccak256Hash([]byte{1},pub);if !bytes.Equal(commit[:],pi[93:125]){panic("PQ commitment")}
    m:=&types.PQMigrateTx{ChainID:new(big.Int).SetBytes(pi[:32]),LegacyAddress:common.BytesToAddress(pi[64:84]),
        MigrationNonce:binary.BigEndian.Uint64(pi[84:92]),AlgID:pi[92],PQPKCommit:commit,
        VerifierVersion:binary.BigEndian.Uint32(pi[125:129]),Expiry:binary.BigEndian.Uint64(pi[129:137]),
        MaxAccountFee:new(big.Int).SetBytes(pi[137:169]),FeeMode:pi[169],FeeSponsor:common.BytesToAddress(pi[170:190]),FeeAuthUntil:binary.BigEndian.Uint64(pi[190:198]),
        GasTipCap:big.NewInt(1000000000),GasFeeCap:big.NewInt(2000000000),Gas:16000000,
        ProofCarrier:types.PQMigrationCarrier{Route:0,Proof:read(*root)}}
    if m.FeeMode!=0 || m.MigrationNonce!=0 {panic("this first E2E fixture requires fresh mode0")}
    if !bytes.Equal(m.PublicInputs(),pi){panic("encoder PI differs")}
    if _,err:=os.Stat(*out);!os.IsNotExist(err){panic("fresh output required")};must(os.MkdirAll(*out,0700))
    meta:=map[string]interface{}{}
    save:=func(name string,tx *types.Transaction){raw,err:=tx.MarshalBinary();must(err);must(os.WriteFile(filepath.Join(*out,name+".bin"),raw,0600));meta[name]=map[string]interface{}{"hash":tx.Hash().Hex(),"bytes":len(raw)}}
    save("migrate",types.NewTx(m))
    bad:=*m;bad.ProofCarrier.Proof=bytes.Clone(m.ProofCarrier.Proof);bad.ProofCarrier.Proof[len(bad.ProofCarrier.Proof)/2]^=1;save("tampered-proof",types.NewTx(&bad))
    bad=*m;bad.Expiry--;save("tampered-pi",types.NewTx(&bad))
    bad=*m;bad.Gas=16777217;save("over-cap",types.NewTx(&bad))
    bad=*m;bad.ProofCarrier.Proof=make([]byte,196609);save("over-proof",types.NewTx(&bad))
    recipient:=common.HexToAddress("0x000000000000000000000000000000000000beef")
    for _,kind:=range []string{"activate","spend"}{
        p:=&types.PQTx{ChainID:m.ChainID,From:m.LegacyAddress,Nonce:0,GasTipCap:big.NewInt(1000000000),GasFeeCap:big.NewInt(2000000000),Gas:800000,
            To:recipient,Value:new(big.Int),AccessList:types.AccessList{},AlgID:1,PublicKey:[][]byte{pub}}
        if kind=="spend"{p.Nonce=1;p.PublicKey=nil;p.To=recipient;p.Value=big.NewInt(1000000);p.Gas=250000}
        digest:=p.SigningHash();tag:=[]byte("ETH-PQ-TX/v1");msg:=append(bytes.Clone(tag),digest[:]...)
        p.Signature=make([]byte,mldsa44.SignatureSize);must(mldsa44.SignTo(sk,msg,tag,false,p.Signature))
        if !mldsa44.Verify(pk,msg,tag,p.Signature){panic("signature self check")}
        save(kind,types.NewTx(p))
    }
    // Disjoint, explicitly public test credentials for pre-T enrollment and
    // the global legacy cutoff. They never control the recovery account.
    enrollmentKey,e:=crypto.HexToECDSA(strings.Repeat("11",32));must(e)
    legacyKey,e:=crypto.HexToECDSA(strings.Repeat("22",32));must(e)
    enrollmentOwner:=crypto.PubkeyToAddress(enrollmentKey.PublicKey)
    legacyOwner:=crypto.PubkeyToAddress(legacyKey.PublicKey)
    var enrollmentSeed [32]byte;for i:=range enrollmentSeed{enrollmentSeed[i]=0x45}
    epk,esk:=mldsa44.NewKeyFromSeed(&enrollmentSeed);epub:=epk.Bytes()
    en:=&types.PQEnrollTx{ChainID:m.ChainID,Nonce:0,GasTipCap:big.NewInt(1000000000),GasFeeCap:big.NewInt(2000000000),Gas:1500000,AlgID:1,PublicKey:epub}
    tag:=[]byte("ETH-PQ-ENROLL-POP/v1");dg:=core.PQEnrollmentDigest(m.ChainID,enrollmentOwner,0,1,epub)
    en.PoPSignature=make([]byte,mldsa44.SignatureSize);must(mldsa44.SignTo(esk,append(bytes.Clone(tag),dg[:]...),tag,false,en.PoPSignature))
    sig,e:=crypto.Sign(en.SigningHash().Bytes(),enrollmentKey);must(e)
    en.R,en.S,en.V=new(big.Int).SetBytes(sig[:32]),new(big.Int).SetBytes(sig[32:64]),new(big.Int).SetUint64(uint64(sig[64]));save("pre-enroll",types.NewTx(en))
    act:=&types.PQTx{ChainID:m.ChainID,From:enrollmentOwner,Nonce:1,GasTipCap:big.NewInt(1000000000),GasFeeCap:big.NewInt(2000000000),Gas:1500000,To:enrollmentOwner,Value:new(big.Int),AlgID:1,PublicKey:[][]byte{epub}}
    tag=[]byte("ETH-PQ-TX/v1");dg=act.SigningHash();act.Signature=make([]byte,mldsa44.SignatureSize);must(mldsa44.SignTo(esk,append(bytes.Clone(tag),dg[:]...),tag,false,act.Signature));save("pre-activate",types.NewTx(act))
    for n,name:=range []string{"pre-legacy","post-legacy"}{
        tx:=types.NewTx(&types.DynamicFeeTx{ChainID:m.ChainID,Nonce:uint64(n),GasTipCap:big.NewInt(1000000000),GasFeeCap:big.NewInt(2000000000),Gas:21000,To:&legacyOwner,Value:new(big.Int)})
        signed,e:=types.SignTx(tx,types.LatestSignerForChainID(m.ChainID),legacyKey);must(e);save(name,signed)
    }
    meta["preTEnrollmentOwner"]=enrollmentOwner.Hex();meta["preTEnrollmentCommit"]=core.PQKeyCommit(1,epub).Hex();meta["legacyCutoffOwner"]=legacyOwner.Hex()
    meta["publicTestOnly"]=true;meta["recipient"]=recipient.Hex();meta["spendValue"]=1000000
    j,e:=json.MarshalIndent(meta,"","  ");must(e);must(os.WriteFile(filepath.Join(*out,"txs.json"),j,0600))
}
