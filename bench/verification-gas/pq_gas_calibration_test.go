// Research measurement harness. Real native F and upstream precompile implementations.
package core

import (
 "bytes"
 "context"
 "crypto/sha256"
 "encoding/hex"
 "encoding/json"
 "fmt"
 "math/big"
 "os"
 "path/filepath"
 "strconv"
 "strings"
 "testing"
 "time"

 "github.com/ethereum/go-ethereum/common"
 "github.com/ethereum/go-ethereum/core/state"
 "github.com/ethereum/go-ethereum/core/tracing"
 "github.com/ethereum/go-ethereum/core/types"
 "github.com/ethereum/go-ethereum/core/vm"
 "github.com/ethereum/go-ethereum/params"
 "github.com/holiman/uint256"
)
func calRead(t *testing.T, path string) []byte { t.Helper(); b,e:=os.ReadFile(path);if e!=nil {t.Fatal(e)};return b }
func calJSON(t *testing.T, path string, v any) {t.Helper();b,e:=json.MarshalIndent(v,"","  ");if e!=nil {t.Fatal(e)};if e=os.WriteFile(path,append(b,'\n'),0600);e!=nil {t.Fatal(e)}}
func calConfig(t *testing.T) *params.ChainConfig {t.Helper();var g Genesis;if e:=json.Unmarshal(calRead(t,filepath.Join(os.Getenv("PQ_CAL_ROOT"),"genesis.json")),&g);e!=nil {t.Fatal(e)};if e:=g.Config.CheckConfigForkOrder();e!=nil{t.Fatal(e)};return g.Config}
func calProof(t *testing.T,rep int)([]byte,[]byte){t.Helper();root:=filepath.Join(os.Getenv("PQ_CAL_ROOT"),fmt.Sprintf("mode0-%02d",rep));proof:=calRead(t,filepath.Join(root,"f/proof.postcard"));pi,e:=hex.DecodeString(strings.TrimSpace(string(calRead(t,filepath.Join(root,"statement/pi198.hex")))));if e!=nil||len(pi)!=198{t.Fatal("PI",e)};return proof,pi}
func calVector(t *testing.T,file,name string)([]byte,[]byte){t.Helper();var vs []struct{Input,Expected,Name string};if e:=json.Unmarshal(calRead(t,filepath.Join("vm/testdata/precompiles",file+".json")),&vs);e!=nil{t.Fatal(e)};for _,v:=range vs{if v.Name==name{in,e:=hex.DecodeString(v.Input);if e!=nil{t.Fatal(e)};out,e:=hex.DecodeString(v.Expected);if e!=nil{t.Fatal(e)};if len(in)==0||bytes.Equal(in,make([]byte,len(in))){t.Fatal("degenerate anchor")};return in,out}};t.Fatal("missing upstream vector",file,name);return nil,nil}
type calOperation struct{Name string; Gas uint64; InputBytes int; InputSHA256 string; Vector string; Run func()error; BatchNs []float64}
func TestPQGasCalibration(t *testing.T){
 rep,e:=strconv.Atoi(os.Getenv("PQ_CAL_REP"));if e!=nil||rep<1||rep>10{t.Fatal("rep")}
 cfg:=calConfig(t).PQMigrate.FullResearch
 proof,pi:=calProof(t,rep)
 start:=time.Now();if e:=CheckPQFullVerifierConfig(cfg);e!=nil{t.Fatal(e)};cold:=time.Since(start).Nanoseconds()
 ops:=[]*calOperation{{Name:"F",InputBytes:len(proof),InputSHA256:fmt.Sprintf("%x",sha256.Sum256(proof)),Vector:fmt.Sprintf("mode0-%02d",rep),Run:func()error{return VerifyPQFull(cfg,pi,proof)}}}
 for _,v:=range []struct{name,file,vector string; address byte}{{"ecrecover","ecRecover","ValidKey",1},{"BN254-pairing","bn256Pairing","jeff1",8},{"BLS12-381-pairing","blsPairing","bls_pairing_e(2*G1,3*G2)=e(6*G1,G2)",15}}{
  input,want:=calVector(t,v.file,v.vector);pc:=vm.PrecompiledContractsOsaka[common.BytesToAddress([]byte{v.address})]
  ops=append(ops,&calOperation{Name:v.name,Gas:pc.RequiredGas(input),InputBytes:len(input),InputSHA256:fmt.Sprintf("%x",sha256.Sum256(input)),Vector:v.file+"/"+v.vector,Run:func()error{got,e:=pc.Run(input);if e!=nil{return e};if !bytes.Equal(got,want){return fmt.Errorf("precompile output mismatch")};return nil}})
 }
 // Fixed cyclic interleaving is declared before measurements, no discarded timed sample.
 for _,op:=range ops{if e:=op.Run();e!=nil{t.Fatal(e)}}
 for round:=0;round<10;round++{for j:=0;j<len(ops);j++{op:=ops[(j+round+rep)%len(ops)];start:=time.Now();for i:=0;i<10;i++{if e:=op.Run();e!=nil{t.Fatal(e)}};op.BatchNs=append(op.BatchNs,float64(time.Since(start).Nanoseconds())/10)}}
 rows:=[]map[string]any{};for _,op:=range ops{total:=float64(0);for _,ns:=range op.BatchNs{total+=ns};rows=append(rows,map[string]any{"name":op.Name,"gas":op.Gas,"inputBytes":op.InputBytes,"inputSHA256":op.InputSHA256,"vector":op.Vector,"meanNs":total/10,"batchMeanNs":op.BatchNs,"calls":100})}
 changed:=bytes.Clone(pi);changed[124]^=1;if e:=VerifyPQFull(cfg,changed,proof);e==nil{t.Fatal("changed PI accepted")};bad:=bytes.Clone(proof);bad[len(bad)/2]^=1;if e:=VerifyPQFull(cfg,pi,bad);e==nil{t.Fatal("changed proof accepted")}
 calJSON(t,filepath.Join(os.Getenv("PQ_CAL_OUT"),fmt.Sprintf("calibration-%02d.json",rep)),map[string]any{"rep":rep,"coldKeyNs":cold,"operations":rows,"negativeControls":"changed PI and proof rejected","scope":"real-backend in-process geth; no result cache; precompile Run and VerifyPQFull"})
}
func TestPQCalibratedRecoveryGas(t *testing.T){
 cfg:=calConfig(t);if e:=CheckPQFullVerifierConfig(cfg.PQMigrate.FullResearch);e!=nil{t.Fatal(e)}
 now:=uint64(time.Now().Unix());if now<cfg.PQMigrate.T{t.Fatal("must execute post-T; no clock rollback")}
 rows:=[]map[string]any{}
 for rep:=1;rep<=10;rep++{func(){
  raw:=calRead(t,filepath.Join(os.Getenv("PQ_CAL_ROOT"),"carriers",fmt.Sprintf("mode0-%02d.bin",rep)));var tx types.Transaction;if e:=tx.UnmarshalBinary(raw);e!=nil{t.Fatal(e)}
  encoded,e:=tx.MarshalBinary();if e!=nil||!bytes.Equal(encoded,raw)||tx.Gas()>params.MaxTxGas{t.Fatal("carrier encoding/gas cap")}
  _,pi:=calProof(t,rep);owner:=common.BytesToAddress(pi[64:84]);expectedCommit:=common.BytesToHash(pi[93:125])
  s,e:=state.New(types.EmptyRootHash,state.NewDatabaseForTesting());if e!=nil{t.Fatal(e)};s.SetBalance(owner,uint256.NewInt(2000000000000000000),tracing.BalanceChangeUnspecified);s.SetCode(cfg.PQMigrate.Registry,[]byte{0},tracing.CodeChangeUnspecified);s.SetNonce(cfg.PQMigrate.Registry,1,tracing.NonceChangeUnspecified)
  h:=&types.Header{Number:big.NewInt(1),Time:now,GasLimit:44999185,BaseFee:big.NewInt(1000000000),Difficulty:new(big.Int),Coinbase:common.HexToAddress("900")};random:=common.Hash{}
  evm:=vm.NewEVM(vm.BlockContext{CanTransfer:CanTransfer,Transfer:Transfer,GetHash:func(uint64)common.Hash{return common.Hash{}},Coinbase:h.Coinbase,BlockNumber:h.Number,Time:h.Time,Difficulty:h.Difficulty,BaseFee:h.BaseFee,GasLimit:h.GasLimit,Random:&random},s,cfg,vm.Config{});defer evm.Release();s.SetTxContext(tx.Hash(),0,1)
  start:=time.Now();receipt,_,e:=ApplyTransaction(context.Background(),evm,NewGasPool(h.GasLimit),s,h,&tx);ns:=time.Since(start).Nanoseconds();if e!=nil{t.Fatal(e)};if receipt.Status!=1{t.Fatal("recovery reverted")};r:=ReadPQRecord(s,cfg.PQMigrate.Registry,owner);if r.Mode!=2||r.MigrationNonce!=1||r.Commit!=expectedCommit||s.GetNonce(owner)!=0{t.Fatal("recovery state mismatch")}
  rows=append(rows,map[string]any{"rep":rep,"gas":receipt.GasUsed,"bytes":len(raw),"executionNs":ns,"status":receipt.Status,"hash":tx.Hash(),"stateRoot":s.IntermediateRoot(evm.GetRules()),"migrationNonce":r.MigrationNonce,"commit":r.Commit,"blockTimestamp":now})
 }()}
 calJSON(t,filepath.Join(os.Getenv("PQ_CAL_OUT"),"recovery-gas.json"),map[string]any{"verifyGas":cfg.PQMigrate.FullResearch.VerifyGas,"blockGasLimit":44999185,"txGasCap":params.MaxTxGas,"rows":rows})
}
