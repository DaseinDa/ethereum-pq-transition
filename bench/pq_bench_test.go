// Measurement harness only. Real native F and real ML-DSA signatures; no verifier replacement.
package core

import (
	"bytes"
	"context"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/tracing"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/params"
	"github.com/holiman/uint256"
	"math/big"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
	"time"
)

func paperRead(t *testing.T, p string) []byte {
	t.Helper()
	b, e := os.ReadFile(p)
	if e != nil {
		t.Fatal(e)
	}
	return b
}
func paperSave(t *testing.T, p string, v any) {
	t.Helper()
	b, e := json.MarshalIndent(v, "", "  ")
	if e != nil {
		t.Fatal(e)
	}
	if e = os.WriteFile(p, append(b, '\n'), 0644); e != nil {
		t.Fatal(e)
	}
}
func paperOutput(t *testing.T, name string) string {
	t.Helper()
	p := os.Getenv("PQ_BENCH_OUT")
	if p == "" {
		t.Fatal("PQ_BENCH_OUT required")
	}
	return filepath.Join(p, name)
}
func paperConfig(t *testing.T, root string) *params.ChainConfig {
	var g Genesis
	if e := json.Unmarshal(paperRead(t, filepath.Join(root, "genesis.json")), &g); e != nil {
		t.Fatal(e)
	}
	if e := g.Config.CheckConfigForkOrder(); e != nil {
		t.Fatal(e)
	}
	return g.Config
}

func TestPQPaperVerifier(t *testing.T) {
	root := os.Getenv("PQ_BENCH_ROOT")
	if root == "" {
		t.Fatal("PQ_BENCH_ROOT required")
	}
	rep, e := strconv.Atoi(os.Getenv("PQ_BENCH_REP"))
	if e != nil || rep < 1 || rep > 10 {
		t.Fatal("rep")
	}
	f := paperConfig(t, root).PQMigrate.FullResearch
	name := fmt.Sprintf("mode0-%02d", rep)
	proof := paperRead(t, filepath.Join(root, name, "f/proof.postcard"))
	pi, e := hex.DecodeString(strings.TrimSpace(string(paperRead(t, filepath.Join(root, name, "statement/pi198.hex")))))
	if e != nil {
		t.Fatal(e)
	}
	start := time.Now()
	if e = CheckPQFullVerifierConfig(f); e != nil {
		t.Fatal(e)
	}
	cold := time.Since(start).Nanoseconds()
	var ns []int64
	for i := 0; i < 10; i++ {
		start = time.Now()
		if e = VerifyPQFull(f, pi, proof); e != nil {
			t.Fatal(e)
		}
		ns = append(ns, time.Since(start).Nanoseconds())
	}
	p := bytes.Clone(pi)
	p[124] ^= 1
	if err := VerifyPQFull(f, p, proof); !errors.Is(err, ErrPQInvalidFullProof) || errors.Is(err, ErrPQFullUnavailable) {
		t.Fatal("mutated PI not classified as invalid proof", err)
	}
	q := bytes.Clone(proof)
	q[len(q)/2] ^= 1
	if err := VerifyPQFull(f, pi, q); !errors.Is(err, ErrPQInvalidFullProof) || errors.Is(err, ErrPQFullUnavailable) {
		t.Fatal("mutated proof not classified as invalid proof", err)
	}
	paperSave(t, paperOutput(t, fmt.Sprintf("geth-verifier-%02d.json", rep)), map[string]any{"rep": rep, "keyInitNs": cold, "verifyNs": ns, "proofBytes": len(proof), "verifyGas": f.VerifyGas, "cache": "direct VerifyPQFull; no pool result cache", "mutationControls": "PI and proof rejected", "tier": "real-backend in-process geth component"})
}

type paperRow struct {
	Rep            int         `json:"rep"`
	Name           string      `json:"name"`
	Gas            uint64      `json:"gas"`
	Bytes          int         `json:"bytes"`
	ExecutionNs    int64       `json:"executionNs"`
	Status         uint64      `json:"status"`
	Hash           common.Hash `json:"hash"`
	StateRoot      common.Hash `json:"stateRoot"`
	Nonce          uint64      `json:"nonce"`
	MigrationNonce uint64      `json:"migrationNonce"`
	Commit         common.Hash `json:"commit"`
}

func TestPQPaperGas(t *testing.T) {
	root := os.Getenv("PQ_BENCH_ROOT")
	if root == "" {
		t.Fatal("PQ_BENCH_ROOT required")
	}
	cfg := paperConfig(t, root)
	if err := CheckPQFullVerifierConfig(cfg.PQMigrate.FullResearch); err != nil {
		t.Fatal(err)
	}
	var meta struct{ Owner, Recipient, Sponsor, OwnerKey, NewKey, OwnerCommit, NewCommit, SponsorKey string }
	if e := json.Unmarshal(paperRead(t, filepath.Join(root, "carriers/manifest.json")), &meta); e != nil {
		t.Fatal(e)
	}
	owner, sponsor, recipient := common.HexToAddress(meta.Owner), common.HexToAddress(meta.Sponsor), common.HexToAddress(meta.Recipient)
	pk, e := hex.DecodeString(meta.OwnerKey)
	if e != nil {
		t.Fatal(e)
	}
	spk, e := hex.DecodeString(meta.SponsorKey)
	if e != nil {
		t.Fatal(e)
	}
	var rows []paperRow
	now := uint64(time.Now().Unix())
	if now < cfg.PQMigrate.T {
		t.Fatal("measurement must be post-T, no clock reversal")
	}
	makeEnv := func(sponsorActive bool) (*state.StateDB, *vm.EVM, *types.Header) {
		s, e := state.New(types.EmptyRootHash, state.NewDatabaseForTesting())
		if e != nil {
			t.Fatal(e)
		}
		for _, a := range []common.Address{owner, sponsor} {
			s.SetBalance(a, uint256.NewInt(2000000000000000000), tracing.BalanceChangeUnspecified)
		}
		s.SetCode(cfg.PQMigrate.Registry, []byte{0}, tracing.CodeChangeUnspecified)
		s.SetNonce(cfg.PQMigrate.Registry, 1, tracing.NonceChangeUnspecified)
		if sponsorActive {
			// Exact state shape after native-account activation (measured separately).
			writePQRecord(s, cfg.PQMigrate.Registry, sponsor, PQRecord{Mode: 3, AlgID: 1, MigrationNonce: 1, Commit: PQKeyCommit(1, spk)})
			s.SetNonce(sponsor, 1, tracing.NonceChangeUnspecified)
			s.SetCode(sponsor, append([]byte{0xef, 1, 1}, spk...), tracing.CodeChangeUnspecified)
		}
		h := &types.Header{Number: big.NewInt(1), Time: now, GasLimit: 44999185, BaseFee: big.NewInt(1000000000), Difficulty: new(big.Int), Coinbase: common.HexToAddress("900")}
		random := common.Hash{}
		evm := vm.NewEVM(vm.BlockContext{CanTransfer: CanTransfer, Transfer: Transfer, GetHash: func(uint64) common.Hash { return common.Hash{} }, Coinbase: h.Coinbase, BlockNumber: h.Number, Time: h.Time, Difficulty: h.Difficulty, BaseFee: h.BaseFee, GasLimit: h.GasLimit, Random: &random}, s, cfg, vm.Config{})
		return s, evm, h
	}
	apply := func(rep int, name, file string, s *state.StateDB, evm *vm.EVM, h *types.Header) {
		raw := paperRead(t, filepath.Join(root, "carriers", file+".bin"))
		var tx types.Transaction
		if e := tx.UnmarshalBinary(raw); e != nil {
			t.Fatal(e)
		}
		round, e := tx.MarshalBinary()
		if e != nil || !bytes.Equal(raw, round) {
			t.Fatal("noncanonical carrier")
		}
		if tx.Gas() > params.MaxTxGas {
			t.Fatal("tx gas cap")
		}
		s.SetTxContext(tx.Hash(), 0, 1)
		start := time.Now()
		rc, _, e := ApplyTransaction(context.Background(), evm, NewGasPool(h.GasLimit), s, h, &tx)
		duration := time.Since(start).Nanoseconds()
		if e != nil {
			t.Fatalf("%s: %v", name, e)
		}
		if rc.Status != 1 {
			t.Fatalf("%s reverted", name)
		}
		record := ReadPQRecord(s, cfg.PQMigrate.Registry, owner)
		rows = append(rows, paperRow{rep, name, rc.GasUsed, len(raw), duration, rc.Status, tx.Hash(), s.IntermediateRoot(evm.GetRules()), s.GetNonce(owner), record.MigrationNonce, record.Commit})
	}
	for rep := 1; rep <= 10; rep++ {
		func() {
			s, e, h := makeEnv(false)
			defer e.Release()
			name := fmt.Sprintf("mode0-%02d", rep)
			apply(rep, "recovery", name, s, e, h)
			r := ReadPQRecord(s, cfg.PQMigrate.Registry, owner)
			if r.Mode != 2 || r.MigrationNonce != 1 || r.Commit != common.HexToHash(meta.OwnerCommit) || s.GetNonce(owner) != 0 {
				t.Fatal("recovery state")
			}
			apply(rep, "activation", "activate", s, e, h)
			if !bytes.Equal(s.GetCode(owner), append([]byte{0xef, 1, 1}, pk...)) {
				t.Fatal("activation code")
			}
			apply(rep, "first-spend", "spend", s, e, h)
			if s.GetBalance(recipient).Uint64() != 1000000 {
				t.Fatal("spend amount")
			}
			apply(rep, "rotate-new", "rotate-new", s, e, h)
			if ReadPQRecord(s, cfg.PQMigrate.Registry, owner).Commit != common.HexToHash(meta.NewCommit) {
				t.Fatal("rotate commit")
			}
			apply(rep, "rotate-same", "rotate-same", s, e, h)
			if ReadPQRecord(s, cfg.PQMigrate.Registry, owner).MigrationNonce != 3 || s.GetNonce(owner) != 4 {
				t.Fatal("final nonces")
			}
		}()
		func() {
			s, e, h := makeEnv(false)
			defer e.Release()
			apply(rep, "setup-recovery", fmt.Sprintf("mode0-%02d", rep), s, e, h)
			apply(rep, "rotate-activating", "rotate-activating", s, e, h)
			if ReadPQRecord(s, cfg.PQMigrate.Registry, owner).Commit != common.HexToHash(meta.NewCommit) || len(s.GetCode(owner)) != 1315 || s.GetNonce(owner) != 1 {
				t.Fatal("activating rotate state")
			}
		}()
		for mode := 1; mode <= 3; mode++ {
			func() {
				s, e, h := makeEnv(true)
				defer e.Release()
				name := fmt.Sprintf("sponsored-mode%d", mode)
				before := s.GetBalance(owner).ToBig()
				sponsorBefore := s.GetBalance(sponsor).ToBig()
				apply(rep, name, fmt.Sprintf("mode%d-01", mode), s, e, h)
				want := new(big.Int).Set(before)
				if mode != 2 {
					want.Sub(want, big.NewInt(1000000000000000))
				}
				if s.GetBalance(owner).CmpBig(want) != 0 {
					t.Fatal("owner reimbursement", mode)
				}
				payerWant := new(big.Int).Sub(sponsorBefore, new(big.Int).Mul(new(big.Int).SetUint64(rows[len(rows)-1].Gas), big.NewInt(2000000000)))
				if mode != 2 {
					payerWant.Add(payerWant, big.NewInt(1000000000000000))
				}
				if s.GetBalance(sponsor).CmpBig(payerWant) != 0 {
					t.Fatal("sponsor fee payment", mode)
				}
				r := ReadPQRecord(s, cfg.PQMigrate.Registry, owner)
				if r.Mode != 2 || r.MigrationNonce != 1 || r.Commit != common.HexToHash(meta.OwnerCommit) {
					t.Fatal("sponsored state")
				}
			}()
		}
		func() {
			s, e, h := makeEnv(false)
			defer e.Release()
			apply(rep, "sponsor-activation", "sponsor-activate", s, e, h)
			if len(s.GetCode(sponsor)) != 1315 {
				t.Fatal("native sponsor activation")
			}
		}()
	}
	var packing []map[string]any
	for _, r := range rows {
		if r.Name != "recovery" {
			continue
		}
		for _, limit := range []uint64{16000000, params.MaxTxGas, r.Gas} {
			gp := NewGasPool(44999185)
			n := 0
			for gp.CheckGasLegacy(limit) == nil {
				if e := gp.ChargeGasLegacy(limit-r.Gas, r.Gas); e != nil {
					t.Fatal(e)
				}
				n++
			}
			formula := 1 + (uint64(44999185)-limit)/r.Gas
			if uint64(n) != formula {
				t.Fatal("capacity formula")
			}
			packing = append(packing, map[string]any{"rep": r.Rep, "declaredGasLimit": limit, "usedGas": r.Gas, "transactions": n, "remaining": gp.Gas()})
		}
	}
	paperSave(t, paperOutput(t, "geth-gas.json"), map[string]any{"rows": rows, "packing": packing, "packingTier": "stock geth GasPool component, hypothetical distinct accounts at repeated measured cost; not a network throughput test", "verifyGas": cfg.PQMigrate.FullResearch.VerifyGas, "blockTimestamp": now, "blockGasLimit": 44999185, "txGasCap": params.MaxTxGas, "baseFeeWei": 1000000000, "tier": "real-backend geth state transition; fresh in-memory state, not network throughput", "sponsorSetup": "already activated native PQ sponsor, except separate sponsor-activation row", "repeatNote": "mode0 uses 10 fresh proofs; other rows repeat identical fixed carrier bytes 10 times; no no-op verifier"})
}
