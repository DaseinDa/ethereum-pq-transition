// Public request-gate fixtures. All signing keys are public test vectors.
package main

import (
	"bytes"
	"encoding/hex"
	"encoding/json"
	"flag"
	"math/big"
	"os"
	"path/filepath"
	"strings"

	"github.com/cloudflare/circl/sign/mldsa/mldsa44"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/params"
)

func main() {
	config := flag.String("config", "", "public fixture config")
	out := flag.String("out", "", "existing public carrier directory")
	flag.Parse()
	must := func(e error) {
		if e != nil {
			panic(e)
		}
	}
	raw, e := os.ReadFile(*config)
	must(e)
	var cfg struct {
		Xi string `json:"xi_hex"`
		PI string `json:"pi198_hex"`
	}
	must(json.Unmarshal(raw, &cfg))
	pi, e := hex.DecodeString(cfg.PI)
	must(e)
	if len(pi) != 198 {
		panic("PI198")
	}
	owner := common.BytesToAddress(pi[64:84])
	chain := new(big.Int).SetBytes(pi[:32])
	if chain.Uint64() != 13378 {
		panic("local chain only")
	}
	xi, e := hex.DecodeString(cfg.Xi)
	must(e)
	if len(xi) != 32 {
		panic("public seed length")
	}
	var seed [32]byte
	copy(seed[:], xi)
	_, sk := mldsa44.NewKeyFromSeed(&seed)
	var attacker [32]byte
	for i := range attacker {
		attacker[i] = 0x45
	}
	_, ask := mldsa44.NewKeyFromSeed(&attacker)
	ek, e := crypto.HexToECDSA(strings.Repeat("11", 32))
	must(e)
	enrolled := crypto.PubkeyToAddress(ek.PublicKey)
	legacy, e := crypto.HexToECDSA(strings.Repeat("22", 32))
	must(e)
	la := crypto.PubkeyToAddress(legacy.PublicKey)
	meta := map[string]any{"publicTestOnly": true, "legacy": la.Hex(), "enrolled": enrolled.Hex(), "owner": owner.Hex()}
	save := func(name string, tx *types.Transaction) {
		b, e := tx.MarshalBinary()
		must(e)
		must(os.WriteFile(filepath.Join(*out, name+".bin"), b, 0600))
		meta[name] = map[string]any{"hash": tx.Hash().Hex(), "bytes": len(b)}
	}
	signPQ := func(name string, from common.Address, key *mldsa44.PrivateKey, nonce uint64, to common.Address, data []byte, value int64) {
		p := &types.PQTx{ChainID: chain, From: from, Nonce: nonce, GasTipCap: big.NewInt(1000000000), GasFeeCap: big.NewInt(2000000000), Gas: 1500000, To: to, Value: big.NewInt(value), Data: data, AlgID: 1}
		tag := []byte("ETH-PQ-TX/v1")
		dg := p.SigningHash()
		p.Signature = make([]byte, mldsa44.SignatureSize)
		must(mldsa44.SignTo(key, append(bytes.Clone(tag), dg[:]...), tag, false, p.Signature))
		save(name, types.NewTx(p))
	}
	for i, target := range []common.Address{params.WithdrawalQueueAddress, params.ConsolidationQueueAddress} {
		name := []string{"7002", "7251"}[i]
		size := []int{56, 96}[i]
		data := bytes.Repeat([]byte{0x42}, size)
		if i == 0 {
			copy(data[48:], make([]byte, 8))
		}
		tx := types.NewTx(&types.DynamicFeeTx{ChainID: chain, Nonce: uint64(i), GasTipCap: big.NewInt(1000000000), GasFeeCap: big.NewInt(2000000000), Gas: 300000, To: &target, Value: big.NewInt(1), Data: data})
		signed, e := types.SignTx(tx, types.LatestSignerForChainID(chain), legacy)
		must(e)
		save("legacy-request-"+name, signed)
		signPQ("marker-request-"+name, enrolled, ask, uint64(2+i), target, data, 1)
		// Each boundary queues both request types together; failed calls still consume nonces.
		for phase, base := range map[string]uint64{"before": 4, "at": 6, "after": 8} {
			signPQ("marker-deadline-"+phase+"-"+name, enrolled, ask, base+uint64(i), target, data, 1)
		}
		signPQ("owner-request-"+name, owner, sk, uint64(1+i), target, data, 1)
		// Forwarders execute CALL with their own address and retain normal contract semantics.
		forward := common.BytesToAddress([]byte{0x4e, byte(0x20 + i)})
		code := append(common.FromHex("0x365f5f375f5f365f3473"), target[:]...)
		code = append(code, common.FromHex("0x5af115601f57005b5f5ffd")...)
		// The jump destination is computed explicitly to avoid fixed-offset ambiguity.
		code[len(code)-7] = byte(len(code) - 4)
		meta["forward-"+name] = map[string]any{"address": forward.Hex(), "code": "0x" + hex.EncodeToString(code)}
		signPQ("contract-request-"+name, owner, sk, uint64(3+i), forward, data, 1)
		meta["data-"+name] = "0x" + hex.EncodeToString(data)
	}
	b, e := json.MarshalIndent(meta, "", "  ")
	must(e)
	must(os.WriteFile(filepath.Join(*out, "n1-carriers.json"), b, 0600))
}
