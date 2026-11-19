"""Public-test migration wallet: authorization tracking and monotonic key-exposure state."""

from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
import hashlib
import hmac
import json
import os
from pathlib import Path
import struct
import tempfile
import time
from typing import Callable, Iterator

UINT32_MAX = (1 << 32) - 1
UINT64_MAX = (1 << 64) - 1
HARDENED = 1 << 31

# Spec l. 97, in mode-number order. Any other value is invalid metadata (31.2 rule 1).
MODES = ("LEGACY", "PQ_BY_ENROLL", "PQ_BY_PROOF", "PQ_NATIVE")
# code(a) at the bound block: empty, a 7702 designator 0xef0100||addr, a PQ marker
# (l. 106), or any other code (a contract; check 5 gives NOT_AN_EOA, l. 1161).
CODE_KINDS = ("EMPTY", "DELEGATION", "PQ_MARKER", "OTHER")


def _uint(value: int, maximum: int, name: str) -> None:
    if type(value) is not int or not 0 <= value <= maximum:
        raise ValueError(f"{name} is outside its unsigned range")


def validate_path(path: tuple[int, ...]) -> tuple[int, int, int, int, int]:
    path = tuple(path)
    if len(path) != 5:
        raise ValueError("the exact five-level BIP-44 path is required")
    for index in path:
        _uint(index, UINT32_MAX, "path index")
    if path[:2] != (44 | HARDENED, 60 | HARDENED):
        raise ValueError("the path must start with 44'/60'")
    if not HARDENED <= path[2] <= UINT32_MAX:
        raise ValueError("the account index must be hardened")
    if path[3] not in (0, 1) or path[4] >= HARDENED:
        raise ValueError("change must be 0/1 and address index unhardened")
    return path


def key_derivation_message(alg_name: str, path: tuple[int, ...], epoch: int) -> bytes:
    """Exact §18.12 domain message; epoch zero preserves the old derivation."""
    if not isinstance(alg_name, str) or not alg_name or "/" in alg_name:
        raise ValueError("algorithm name must be nonempty ASCII without slash")
    try:
        name = alg_name.encode("ascii")
    except UnicodeEncodeError as exc:
        raise ValueError("algorithm name must be ASCII") from exc
    _uint(epoch, UINT32_MAX, "epoch")
    encoded_path = b"".join(struct.pack(">I", index) for index in validate_path(path))
    message = b"PQ-MIGRATE-v1/" + name + b"/" + encoded_path
    return message if epoch == 0 else message + b"/" + struct.pack(">I", epoch)


def derive_epoch_seed(seed64: bytes, alg_name: str, path: tuple[int, ...], epoch: int) -> bytes:
    if not isinstance(seed64, bytes) or len(seed64) != 64:
        raise ValueError("seed64 must contain exactly 64 bytes")
    return hmac.digest(seed64, key_derivation_message(alg_name, path, epoch), "sha512")[:32]


def local_seed_identity(seed64: bytes) -> str:
    """Stable private local identifier, independent of chain, account and algorithm.

    Never put this identifier in transactions, telemetry or public recovery data.
    The caller may instead use an existing stable wallet seed identity, but must
    reuse it for the same seed across all chains. Do not key identity by address.
    """
    if not isinstance(seed64, bytes) or len(seed64) != 64:
        raise ValueError("seed64 must contain exactly 64 bytes")
    return hmac.digest(seed64, b"PQ-MIGRATE/local-wallet-security-scope/v1", "sha256").hex()


def _hex(value: str, size: int, name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be hexadecimal")
    text = value.removeprefix("0x").lower()
    try:
        decoded = bytes.fromhex(text)
    except ValueError as exc:
        raise ValueError(f"invalid {name}") from exc
    if len(text) != size * 2 or len(decoded) != size:
        raise ValueError(f"{name} must contain {size} bytes")
    return text


@dataclass(frozen=True)
class DerivationScope:
    # A stable local identifier for the SAME seed, never a raw secret. The caller
    # must use one identity across networks and accounts backed by that seed.
    seed_identity: str
    path: tuple[int, int, int, int, int]

    def __post_init__(self) -> None:
        if not isinstance(self.seed_identity, str) or not self.seed_identity:
            raise ValueError("a stable local seed identity is required")
        object.__setattr__(self, "path", validate_path(self.path))

    @property
    def key(self) -> str:
        payload = json.dumps([self.seed_identity, self.path], separators=(",", ":"))
        return hashlib.sha256(payload.encode()).hexdigest()


@dataclass(frozen=True)
class CanonicalState:
    """Rule 1's reading of `a` at one identified canonical block B.

    Rule 10 (b): `status` is one of the four modes of l. 97 and is validated with
    `activated`, the commitment, the nonce and the code it implies (l. 104, l. 110).
    Rule 10 (c): the inputs of check 5 are part of the bound state, so the component
    evaluates the state gate itself (check5_gate). `timestamp`, `override_window`
    and `enrolled_at` are None when they were not read at B; `fork_time` is None
    while no release schedules T (l. 61), never as a default for "not read".
    """
    chain_id: int
    genesis_hash: str
    legacy_address: str
    block_hash: str
    migration_nonce: int
    status: str = "LEGACY"
    activated: bool = False
    commitment: bytes | None = None
    alg_name: str = "ML-DSA-44"
    alg_id: int = 1
    timestamp: int | None = None
    fork_time: int | None = None
    override_window: int | None = None
    enrolled_at: int | None = None
    code_kind: str | None = None  # None: EMPTY, or PQ_MARKER when activated
    protocol_time: int | None = None  # Authenticated T0; required for the v1.31 gate.
    legacy_seed_proof_from_t0: bool = False  # False preserves historical profiles.

    def __post_init__(self) -> None:
        _uint(self.chain_id, (1 << 256) - 1, "chain ID")
        _uint(self.migration_nonce, UINT64_MAX, "migration nonce")
        _uint(self.alg_id, 255, "algorithm ID")
        if not isinstance(self.alg_name, str) or not self.alg_name or "/" in self.alg_name:
            raise ValueError("algorithm name must be nonempty ASCII without slash")
        try:
            self.alg_name.encode("ascii")
        except UnicodeEncodeError as exc:
            raise ValueError("algorithm name must be ASCII") from exc
        for field, size in (("genesis_hash", 32), ("legacy_address", 20), ("block_hash", 32)):
            object.__setattr__(self, field, _hex(getattr(self, field), size, field))
        if self.commitment is not None and (not isinstance(self.commitment, bytes) or len(self.commitment) != 32):
            raise ValueError("commitment must contain exactly 32 bytes")
        if type(self.activated) is not bool:
            raise ValueError("activated must be boolean")
        if type(self.legacy_seed_proof_from_t0) is not bool:
            raise ValueError("legacy seed-proof configuration must be boolean")
        for field in ("timestamp", "fork_time", "override_window", "enrolled_at", "protocol_time"):
            if getattr(self, field) is not None:
                _uint(getattr(self, field), UINT64_MAX, field)
        # Rule 10 (b) with 31.2 rule 1: a mode outside l. 97 is invalid, never a default.
        if self.status not in MODES:
            raise ValueError("invalid account mode metadata")
        if self.code_kind is not None and self.code_kind not in CODE_KINDS:
            raise ValueError("invalid account code metadata")
        code = self.effective_code_kind
        if self.status == "LEGACY":
            # Both registry slots of a LEGACY account are zero (l. 104).
            if (self.activated or self.commitment is not None or self.migration_nonce != 0
                    or self.enrolled_at not in (None, 0) or code == "PQ_MARKER"):
                raise ValueError("a LEGACY state has zero registry slots and no PQ marker")
        else:
            if self.commitment is None or self.migration_nonce == 0:
                raise ValueError("a PQ mode has a commitment and a nonzero migration nonce")
            # A PQ account's code is empty or its own marker (l. 110, l. 194, l. 275).
            if code not in ("EMPTY", "PQ_MARKER") or (code == "PQ_MARKER") != self.activated:
                raise ValueError("a PQ account's code is empty or its activated marker")
            if self.status == "PQ_NATIVE" and (not self.activated or self.enrolled_at not in (None, 0)):
                raise ValueError("PQ_NATIVE is activated from creation, with enrolled_at 0")

    @property
    def effective_code_kind(self) -> str:
        if self.code_kind is not None:
            return self.code_kind
        return "PQ_MARKER" if self.activated else "EMPTY"

    @property
    def cache_key(self) -> str:
        return f"{self.chain_id}:{self.genesis_hash}:{self.legacy_address}"

    @property
    def anchor(self) -> str:
        # Include every policy-relevant state field; changed same-block inputs
        # cannot reuse a recovered key either. The check-5 inputs are included.
        values = [self.cache_key, self.block_hash, self.migration_nonce, self.status,
                  self.activated, None if self.commitment is None else self.commitment.hex(),
                  self.alg_name, self.alg_id, self.timestamp, self.fork_time,
                  self.override_window, self.enrolled_at, self.effective_code_kind,
                  self.protocol_time, self.legacy_seed_proof_from_t0]
        return hashlib.sha256(json.dumps(values, separators=(",", ":")).encode()).hexdigest()

    @property
    def is_frozen(self) -> bool | None:
        """is_frozen(a) of l. 111 at B; None when B's state lacks the timestamp."""
        if self.status != "LEGACY" or self.effective_code_kind == "OTHER" or self.fork_time is None:
            return False
        if self.timestamp is None:
            return None
        return self.timestamp >= self.fork_time


def check5_gate(state: CanonicalState) -> tuple[str | None, str]:
    """Spec section 3.2 check 5 at B, in the order of section 14.14 (l. 1159-1161).

    Rule 10 (c). Returns (gate, reason). gate is PRE_T_LEGACY, FROZEN, OVERRIDE or RECOMMIT when
    one is open at B's header timestamp, else None with the check-5 code, or with
    STATE_GATE_UNEVALUATED when B's state lacks an input that this mode needs.
    An unscheduled T leaves deadline(a) infinite, so the override gate is open
    (l. 61, l. 112). Inclusion comes later than B, and a gate that closes before it
    fails at the chain's own check 5.
    """
    if not isinstance(state, CanonicalState):
        raise ValueError("canonical state required")
    if state.legacy_seed_proof_from_t0 and state.protocol_time is None:
        return None, "STATE_GATE_UNEVALUATED"
    if state.protocol_time is not None:
        if state.timestamp is None:
            return None, "STATE_GATE_UNEVALUATED"
        if state.timestamp < state.protocol_time:
            return None, "FORK_NOT_ACTIVE"
    if state.status in ("PQ_BY_PROOF", "PQ_NATIVE"):
        if state.status == "PQ_BY_PROOF" and state.effective_code_kind == "EMPTY":
            return "RECOMMIT", "RECOMMIT_GATE_OPEN"
        return None, "ALREADY_MIGRATED"
    if state.status == "PQ_BY_ENROLL":
        if state.fork_time is None:
            return "OVERRIDE", "OVERRIDE_GATE_OPEN"
        if state.timestamp is None or state.enrolled_at is None or state.override_window is None:
            return None, "STATE_GATE_UNEVALUATED"
        deadline = max(state.enrolled_at, state.fork_time) + state.override_window  # unbounded integer
        if state.timestamp < deadline:
            return "OVERRIDE", "OVERRIDE_GATE_OPEN"
        return None, "OVERRIDE_WINDOW_CLOSED"
    if state.effective_code_kind not in ("EMPTY", "DELEGATION"):
        return None, "NOT_AN_EOA"
    if state.fork_time is None and not state.legacy_seed_proof_from_t0:
        return None, "FORK_NOT_ACTIVE"
    if state.timestamp is None:
        return None, "STATE_GATE_UNEVALUATED"
    if state.fork_time is not None and state.timestamp >= state.fork_time:
        return "FROZEN", "FROZEN_GATE_OPEN"
    if state.legacy_seed_proof_from_t0:
        return "PRE_T_LEGACY", "PRE_T_LEGACY_GATE_OPEN"
    return None, "FORK_NOT_ACTIVE"


@dataclass(frozen=True)
class CurrentKey:
    # This is a trusted in-process value returned by scan_current_key, not a
    # signed attestation or an untrusted serialization format. Applications must
    # not deserialize attacker-supplied CurrentKey values as verified recovery.
    scope_key: str
    state_anchor: str
    epoch: int
    commitment: bytes

    def matches(self, scope: DerivationScope, state: CanonicalState) -> bool:
        return (self.scope_key == scope.key and self.state_anchor == state.anchor
                and type(self.epoch) is int and 0 <= self.epoch <= UINT32_MAX
                and self.epoch < state.migration_nonce and self.commitment == state.commitment)

    def above_bound(self, scope: DerivationScope, state: CanonicalState) -> bool:
        """(31.2 rules 4-5): the current key of this state found only by MATCH_ABOVE_BOUND, its epoch at or above
        the state's migration_nonce (above U = migration_nonce - 1). Such a key is used only for the range repair of
        rule 5: the e - migration_nonce + 1 same-key writes of rule 8 (a), offered before any new selection."""
        return (self.scope_key == scope.key and self.state_anchor == state.anchor
                and type(self.epoch) is int and state.migration_nonce <= self.epoch <= UINT32_MAX
                and self.commitment == state.commitment)


@dataclass(frozen=True)
class ScanCursor:
    scope_key: str
    state_anchor: str
    next_epoch: int


@dataclass(frozen=True)
class ScanResult:
    status: str
    current_key: CurrentKey | None
    next_cursor: ScanCursor | None
    attempts_total: int
    upper_epoch: int


def scan_current_key(scope: DerivationScope, state: CanonicalState,
                     derive_commit: Callable[[int], bytes], *, max_attempts: int = 4096,
                     cursor: ScanCursor | None = None) -> ScanResult:
    """Search authenticated current commitment, never equating a budget with exhaustion.

    derive_commit must implement the selected registered algorithm's exact public
    key commitment for this scope. A cursor belongs to one immutable state anchor.
    Rule 10 (b): a LEGACY account gives NO_COMMITMENT with nothing derived, and a
    PQ_NATIVE account is not scanned (31.2 rule 4).
    """
    _uint(max_attempts, UINT64_MAX, "scan budget")
    if max_attempts == 0:
        raise ValueError("scan budget must be positive")
    upper = min(state.migration_nonce - 1, UINT32_MAX)
    start = 0
    if cursor is not None:
        if cursor.scope_key != scope.key or cursor.state_anchor != state.anchor:
            raise ValueError("scan cursor is stale or belongs to another scope")
        _uint(cursor.next_epoch, UINT32_MAX + 1, "scan cursor")
        start = cursor.next_epoch
    if state.status == "LEGACY":
        return ScanResult("NO_COMMITMENT", None, None, 0, upper)
    if state.status == "PQ_NATIVE":
        return ScanResult("NOT_SCANNED_PQ_NATIVE", None, None, 0, upper)
    if start > upper + 1:
        raise ValueError("scan cursor exceeds the state-derived range")
    stop = min(start + max_attempts, upper + 1)
    for epoch in range(start, stop):
        commitment = derive_commit(epoch)
        if not isinstance(commitment, bytes) or len(commitment) != 32:
            raise ValueError("derive_commit must return a 32-byte commitment")
        if hmac.compare_digest(commitment, state.commitment):
            key = CurrentKey(scope.key, state.anchor, epoch, commitment)
            return ScanResult("MATCH", key, None, epoch + 1, upper)
    if stop <= upper:
        return ScanResult("INCOMPLETE", None, ScanCursor(scope.key, state.anchor, stop), stop, upper)
    return ScanResult("NO_MATCH_WITHIN_BOUND", None, None, stop, upper)


def scan_above_bound(scope: DerivationScope, state: CanonicalState,
                     derive_commit: Callable[[int], bytes], *, owner_request: bool,
                     max_attempts: int = 4096, cursor: ScanCursor | None = None) -> ScanResult:
    """The recovery aid of 31.2 rule 4 above U, only on the owner's explicit request.

    It tests e = U + 1, ..., 2^32 - 1 in increasing order. A match is
    MATCH_ABOVE_BOUND and does not change U: its CurrentKey lies outside U, so
    CurrentKey.matches is False and the adapter refuses to use it until the range
    repair of 31.2 rule 5 has landed. attempts_total counts epochs from 0, as if the
    in-bound scan had run first (vector WE-2 (ii): MATCH_ABOVE_BOUND e = 2 "at the
    third"). No log is read.
    """
    if owner_request is not True:
        raise ValueError("the above-bound aid runs only on the owner's explicit request")
    _uint(max_attempts, UINT64_MAX, "scan budget")
    if max_attempts == 0:
        raise ValueError("scan budget must be positive")
    upper = min(state.migration_nonce - 1, UINT32_MAX)
    if state.status == "LEGACY":
        return ScanResult("NO_COMMITMENT", None, None, 0, upper)
    if state.status == "PQ_NATIVE":
        return ScanResult("NOT_SCANNED_PQ_NATIVE", None, None, 0, upper)
    start = upper + 1
    if cursor is not None:
        if cursor.scope_key != scope.key or cursor.state_anchor != state.anchor:
            raise ValueError("scan cursor is stale or belongs to another scope")
        _uint(cursor.next_epoch, UINT32_MAX + 1, "scan cursor")
        if cursor.next_epoch < start:
            raise ValueError("an in-bound cursor cannot continue the above-bound aid")
        start = cursor.next_epoch
    stop = min(start + max_attempts, UINT32_MAX + 1)
    for epoch in range(start, stop):
        commitment = derive_commit(epoch)
        if not isinstance(commitment, bytes) or len(commitment) != 32:
            raise ValueError("derive_commit must return a 32-byte commitment")
        if hmac.compare_digest(commitment, state.commitment):
            key = CurrentKey(scope.key, state.anchor, epoch, commitment)
            return ScanResult("MATCH_ABOVE_BOUND", key, None, epoch + 1, upper)
    if stop <= UINT32_MAX:
        return ScanResult("INCOMPLETE", None, ScanCursor(scope.key, state.anchor, stop), stop, upper)
    return ScanResult("NO_MATCH_ABOVE_BOUND", None, None, stop, upper)


@dataclass(frozen=True)
class SecurityKnowledge:
    """The optional advisory record of 31.2 rule 7: known exposed epochs only.

    Rule 10 (a): there is no completeness status (UNKNOWN or COMPLETE) and no
    backup promotion. An empty record blocks nothing (rule 6, D-1). revision counts
    local mutations; it is not a completeness assessment.
    """
    compromised_epochs: frozenset[int]
    revision: int


class MetadataError(RuntimeError):
    """Unreadable or invalid metadata fails closed; it must not reset the ledger."""


@contextmanager
def _locked(path: Path) -> Iterator[None]:
    # OS locks disappear on process exit. An abandoned lock file is harmless.
    handle = open(path, "a+b")
    try:
        handle.seek(0, os.SEEK_END)
        if handle.tell() == 0:
            handle.write(b"\0")
            handle.flush()
        handle.seek(0)
        if os.name == "nt":
            import msvcrt
            deadline = time.monotonic() + 10
            while True:
                try:
                    msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
                    break
                except OSError:
                    if time.monotonic() >= deadline:
                        raise MetadataError("metadata lock timed out")
                    time.sleep(0.02)
        else:
            import fcntl
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            handle.seek(0)
            if os.name == "nt":
                msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
    finally:
        handle.close()


def _atomic_json(path: Path, document: dict) -> None:
    fd, temporary = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as handle:
            json.dump(document, handle, sort_keys=True, indent=2)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
        if os.name != "nt":
            directory = os.open(path.parent, os.O_RDONLY)
            try:
                os.fsync(directory)
            finally:
                os.close(directory)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def _validate_compromises(compromises: dict) -> None:
    for epoch, reason in compromises.items():
        if not isinstance(epoch, str) or str(int(epoch)) != epoch:
            raise ValueError("noncanonical epoch")
        _uint(int(epoch), UINT32_MAX, "ledger epoch")
        if not isinstance(reason, str) or not reason:
            raise ValueError("missing compromise reason")


class WalletEpochStore:
    """Separate the advisory compromise record from the disposable canonical cache.

    31.2 rules 6-7 (D-1): the record is optional and advisory. A mnemonic restore
    without it is a first use and needs no acknowledgement or second backup; the
    record only adds known exposed epochs, and nothing removes one. Rule 10 (a):
    the completeness status (UNKNOWN or COMPLETE) and its backup promotion of
    a501bcc0 are not adopted, so this store has no initialize_new_wallet and no
    mark_knowledge_unknown. An older record file may
    carry its legacy "knowledge" field; it is accepted, ignored and dropped on the
    next write. This store detects corruption but has no trusted monotonic
    hardware: a restored old backup can hide newer leak records (31.2 residual
    risk 5).
    """

    def __init__(self, directory: str | Path):
        self.directory = Path(directory)
        self.directory.mkdir(parents=True, exist_ok=True)
        self.security_path = self.directory / "security.json"
        self.cache_path = self.directory / "canonical-cache.json"
        self.lock_path = self.directory / "metadata.lock"

    @staticmethod
    def _read(path: Path, *, security: bool) -> dict:
        if not path.exists():
            return {"schema": 1, "scopes": {}}
        try:
            document = json.loads(path.read_text(encoding="utf-8"))
            if document.get("schema") != 1 or not isinstance(document.get("scopes"), dict):
                raise ValueError("unexpected schema")
            for scope_key, record in document["scopes"].items():
                _hex(scope_key, 32, "scope key")
                if not isinstance(record, dict):
                    raise ValueError("bad scope record")
                if security:
                    if "knowledge" in record and record["knowledge"] not in ("COMPLETE", "UNKNOWN"):
                        raise ValueError("bad legacy knowledge field")
                    if not isinstance(record.get("compromises"), dict):
                        raise ValueError("bad compromise ledger")
                    _uint(record.get("revision"), UINT64_MAX, "security revision")
                    _validate_compromises(record["compromises"])
            return document
        except (OSError, ValueError, TypeError, AttributeError) as exc:
            raise MetadataError(f"invalid metadata: {path.name}") from exc

    def security(self, scope: DerivationScope) -> SecurityKnowledge:
        with _locked(self.lock_path):
            record = self._read(self.security_path, security=True)["scopes"].get(scope.key)
            if record is None:
                return SecurityKnowledge(frozenset(), 0)
            return SecurityKnowledge(frozenset(map(int, record["compromises"])), record["revision"])

    @staticmethod
    def _advance_revision(record: dict) -> None:
        if record["revision"] == UINT64_MAX:
            raise MetadataError("security revision exhausted; mutation refused")
        record["revision"] += 1

    def _record_for(self, document: dict, scope: DerivationScope) -> dict:
        record = document["scopes"].setdefault(scope.key, {"compromises": {}, "revision": 0})
        record.pop("knowledge", None)  # Not adopted (rule 10 (a)); never written again.
        return record

    def mark_compromised(self, scope: DerivationScope, epoch: int, reason: str) -> None:
        _uint(epoch, UINT32_MAX, "compromised epoch")
        if not isinstance(reason, str) or not reason:
            raise ValueError("a compromise reason is required")
        with _locked(self.lock_path):
            document = self._read(self.security_path, security=True)
            record = self._record_for(document, scope)
            # Union-only: a second report cannot erase the first reason or epoch.
            record["compromises"].setdefault(str(epoch), reason)
            self._advance_revision(record)
            _atomic_json(self.security_path, document)

    def export_security_backup(self, scope: DerivationScope) -> dict:
        """Export data only, unencrypted: 31.2 rule 7 (d) / rule 10 (h) stay open.

        The application must encrypt, authenticate and version every backup.
        """
        with _locked(self.lock_path):
            record = self._read(self.security_path, security=True)["scopes"].get(scope.key)
            if record is None:
                record = {"compromises": {}, "revision": 0}
            return {"schema": 1, "scope_key": scope.key,
                    "compromises": dict(record["compromises"]), "revision": record["revision"]}

    def import_security_backup(self, scope: DerivationScope, backup: dict, *,
                               authenticated: bool) -> SecurityKnowledge:
        """Union an externally authenticated backup; never delete local records.

        `authenticated` is the caller's attestation, not a check performed here. A
        backup's revision never replaces the local one, and a legacy "knowledge"
        field promotes nothing (rule 10 (a): only the union of records is kept).
        """
        if authenticated is not True:
            raise MetadataError("backup authentication is required")
        if (not isinstance(backup, dict) or backup.get("schema") != 1
                or backup.get("scope_key") != scope.key
                or backup.get("knowledge", "UNKNOWN") not in ("UNKNOWN", "COMPLETE")
                or not isinstance(backup.get("compromises"), dict)):
            raise MetadataError("invalid security backup")
        try:
            _uint(backup.get("revision"), UINT64_MAX, "backup revision")
            _validate_compromises(backup["compromises"])
        except (ValueError, TypeError) as exc:
            raise MetadataError("invalid security backup") from exc
        with _locked(self.lock_path):
            document = self._read(self.security_path, security=True)
            record = self._record_for(document, scope)
            for epoch, reason in backup["compromises"].items():
                record["compromises"].setdefault(epoch, reason)
            self._advance_revision(record)
            _atomic_json(self.security_path, document)
            return SecurityKnowledge(frozenset(map(int, record["compromises"])), record["revision"])

    def sync_canonical(self, scope: DerivationScope, state: CanonicalState,
                       verified_key: CurrentKey | None = None, *, above_bound: CurrentKey | None = None) -> dict:
        if verified_key is not None and not verified_key.matches(scope, state):
            raise ValueError("current key was not verified against this canonical state")
        if above_bound is not None and not above_bound.above_bound(scope, state):
            raise ValueError("above-bound key was not found against this canonical state")
        with _locked(self.lock_path):
            document = self._read(self.cache_path, security=False)
            records = document["scopes"].setdefault(scope.key, {})
            previous = records.get(state.cache_key)
            same_anchor = previous is not None and previous.get("anchor") == state.anchor
            current_epoch = verified_key.epoch if verified_key is not None else (
                previous.get("current_epoch") if same_anchor else None)
            record = {"anchor": state.anchor, "block_hash": state.block_hash,
                      "migration_nonce": state.migration_nonce, "current_epoch": current_epoch,
                      # e_high is explicitly invalidated; logs are not a selection authority.
                      "e_high": None, "next_candidate_epoch": state.migration_nonce}
            # (31.2 rule 5): a key that the above-bound aid found is a fact of the seed (that commitment is the
            # key of that epoch on this path and algorithm), kept across blocks so that the repair is offered before any
            # new selection until it has landed (above_bound_key); the cache stays disposable, and a lost record only
            # means that the owner runs the above-bound aid again (rule 5: only that aid finds the key meanwhile).
            known = {} if previous is None else dict(previous.get("above_bound") or {})
            if above_bound is not None:
                known[above_bound.commitment.hex()] = above_bound.epoch
            if known:
                record["above_bound"] = known
            records[state.cache_key] = record
            _atomic_json(self.cache_path, document)
            return record.copy()

    def above_bound_key(self, scope: DerivationScope, state: CanonicalState) -> CurrentKey | None:
        """(31.2 rule 5): the current key of `state` as an earlier above-bound scan found it, where its epoch is
        still at or above the state's migration_nonce (the repair has not landed); None otherwise."""
        if state.commitment is None:
            return None
        with _locked(self.lock_path):
            record = self._read(self.cache_path, security=False)["scopes"].get(scope.key, {}).get(state.cache_key)
        epoch = (record or {}).get("above_bound", {}).get(state.commitment.hex())
        if type(epoch) is not int or not state.migration_nonce <= epoch <= UINT32_MAX:
            return None
        return CurrentKey(scope.key, state.anchor, epoch, state.commitment)


@dataclass(frozen=True)
class Selection:
    status: str
    epoch: int | None
    reason: str
    requires_new_authorization: bool = True
    # (31.2 rule 10 (d), rule 8 (a)): the forms of the same-key step that the bound state admits
    # (SAME_KEY_STEP_FORMS), in the order of rule 8 (a); empty unless a same-key step is offered.
    steps: tuple = ()
    # (31.2 rule 5): for OFFER_RANGE_REPAIR, the e - migration_nonce + 1 same-key writes still due.
    repair_steps: int | None = None


# (31.2 rule 8 (a), l. 8972-8975; rule 10 (d)): the four forms of the same-key step.
STEP_0x7E_RECOMMIT = "0x7E_RECOMMIT_THROUGH_THE_RECOMMIT_GATE"                  # PQ_BY_PROOF, code empty (l. 263)
STEP_0x7E_OVERRIDE = "0x7E_SAME_KEY_EARLY_FINALISATION_THROUGH_THE_OVERRIDE_GATE"  # own enrolled key (l. 262, l. 327)
STEP_ROTATE = "0x7C_ROTATE_TO_THE_CURRENT_KEY"                                  # binding-final and activated (ROT-D2)
STEP_ACTIVATING_ROTATE = "ACTIVATING_0x7C_CARRYING_THE_ROTATE_TO_THE_CURRENT_KEY"  # 14.4 rule 6, 14.8 item 9
SAME_KEY_STEP_FORMS = (STEP_0x7E_RECOMMIT, STEP_0x7E_OVERRIDE, STEP_ROTATE, STEP_ACTIVATING_ROTATE)
WRITE_STEP_FORMS = (STEP_0x7E_RECOMMIT, STEP_0x7E_OVERRIDE)
ROTATE_STEP_FORMS = (STEP_ROTATE, STEP_ACTIVATING_ROTATE)


def binding_final(state: CanonicalState) -> bool | None:
    """final(a) of l. 113 at B: PQ_BY_PROOF and activated, PQ_NATIVE, or PQ_BY_ENROLL past its window.

    None where B's state lacks an input that the PQ_BY_ENROLL case needs (check5_gate's
    STATE_GATE_UNEVALUATED). An unscheduled T leaves deadline(a) infinite (l. 61, l. 112).
    """
    if state.status == "PQ_NATIVE":
        return True
    if state.status == "PQ_BY_PROOF":
        return state.activated
    if state.status == "PQ_BY_ENROLL":
        gate, reason = check5_gate(state)
        if reason == "STATE_GATE_UNEVALUATED":
            return None
        return gate is None and reason == "OVERRIDE_WINDOW_CLOSED"
    return False


def same_key_step_forms(state: CanonicalState) -> tuple:
    """(31.2 rule 10 (d)): the forms of the same-key step of 31.2 rule 8 (a) that B's state admits.

    - a 0x7e that re-commits the current commitment through the re-commit gate (PQ_BY_PROOF with code
      empty, l. 263);
    - for the owner's own seed-derived enrolled key, the same 0x7e through the override gate
      (override_open, l. 262; the same-key early finalisation of l. 327): the caller's CurrentKey, a
      commitment-matching scan of this seed, is what makes the enrolled key the owner's own;
    - for an account that is binding-final and activated, a rotate to the current key with pop_sig by
      that key (vector ROT-D2, l. 5252);
    - for a PQ_BY_PROOF account that is not activated, or a binding-final PQ_BY_ENROLL one that is not,
      an activating 0x7c that carries that rotate (14.4 rule 6, 14.8 item 9).
    PQ_NATIVE is excluded from selection and scan (rule 10 (b)); LEGACY has no current key (rule 8 (b)).
    """
    if state.status not in ("PQ_BY_ENROLL", "PQ_BY_PROOF"):
        return ()
    gate, _ = check5_gate(state)
    final = binding_final(state)
    forms = []
    if gate == "RECOMMIT":
        forms.append(STEP_0x7E_RECOMMIT)
    if gate == "OVERRIDE":
        forms.append(STEP_0x7E_OVERRIDE)
    if final is True and state.activated:
        forms.append(STEP_ROTATE)
    elif not state.activated and (state.status == "PQ_BY_PROOF" or final is True):
        forms.append(STEP_ACTIVATING_ROTATE)
    return tuple(forms)


def select_new_key_epoch(scope: DerivationScope, state: CanonicalState,
                         store: WalletEpochStore, *, current_key: CurrentKey | None = None) -> Selection:
    """Select e=m or report a known exclusion; a missing record is not a gate.

    D-1 permits mnemonic-only recovery, and every known compromised epoch is still
    excluded from automatic selection. Rule 10 (b): rules 2 and 4 do not apply to
    a PQ_NATIVE account (NOT_APPLICABLE). Rule 10 (c): the same-key offer needs a
    state gate (or, for a rotate, final(a)) evaluated from the bound state. No signing,
    recommit, counter increment or blacklist skip occurs here.

    (31.2 rule 10 (d), rule 8 (a)): with e = m recorded and a verified current key whose
    epoch is not recorded, the same-key step is offered in every form that B's state admits
    (`steps`, same_key_step_forms): OFFER_SAME_KEY_RECOMMIT where a 0x7e form exists (the re-commit
    gate, or the override gate of the owner's own enrolled key, l. 327), OFFER_SAME_KEY_ROTATE where
    only a rotate to the current key exists (binding-final, activated or not).

    (31.2 rule 5, l. 8957; rule 10 (d)): a current key that the scan finds only by
    MATCH_ABOVE_BOUND at an epoch e (`current_key` from scan_above_bound, or the cache's record of an earlier one, kept
    until the repair lands) gets OFFER_RANGE_REPAIR before any new selection, whether or not the epoch at the current
    nonce is recorded: the e - migration_nonce + 1 same-key writes of rule 8 (a) (`repair_steps`), in the forms that B
    admits (`steps`), after which the key lies inside U. A selection at a nonce m <= e would give the current key
    itself, or an epoch below e from which a later selection reaches e again (l. 8957). Where e itself is recorded,
    31.2 rule 7 (b) applies instead (32.2 rule 4 (c)): the selection proceeds as for any recorded current key.
    """
    if state.status == "PQ_NATIVE":
        return Selection("NOT_APPLICABLE", None, "PQ_NATIVE")
    above = current_key if isinstance(current_key, CurrentKey) and current_key.above_bound(scope, state) else None
    store.sync_canonical(scope, state, None if above is not None else current_key, above_bound=above)
    if above is None:
        above = store.above_bound_key(scope, state)
    security = store.security(scope)
    if above is not None and above.epoch not in security.compromised_epochs:
        forms = same_key_step_forms(state)
        if not forms:
            return Selection("BLOCKED", None, "RANGE_REPAIR_UNAVAILABLE")
        return Selection("OFFER_RANGE_REPAIR", above.epoch, "CURRENT_KEY_ABOVE_U_SAME_KEY_REPAIR_BEFORE_ANY_NEW_SELECTION",
                         steps=forms, repair_steps=above.epoch - state.migration_nonce + 1)
    epoch = state.migration_nonce
    if epoch > UINT32_MAX:
        return Selection("BLOCKED", None, "EPOCH_EXHAUSTED")
    if epoch not in security.compromised_epochs:
        return Selection("SELECTED", epoch, "CANONICAL_PRESTATE_NONCE")
    if (current_key is not None and current_key.matches(scope, state)
            and current_key.epoch not in security.compromised_epochs
            and state.migration_nonce < UINT32_MAX):
        forms = same_key_step_forms(state)
        if STEP_0x7E_RECOMMIT in forms:
            return Selection("OFFER_SAME_KEY_RECOMMIT", current_key.epoch,
                             "CANDIDATE_COMPROMISED_EXPLICIT_SAFE_RECOMMIT_AVAILABLE", steps=forms)
        if STEP_0x7E_OVERRIDE in forms:
            return Selection("OFFER_SAME_KEY_RECOMMIT", current_key.epoch,
                             "CANDIDATE_COMPROMISED_SAME_KEY_EARLY_FINALISATION_AVAILABLE", steps=forms)
        if forms:
            return Selection("OFFER_SAME_KEY_ROTATE", current_key.epoch,
                             "CANDIDATE_COMPROMISED_SAME_KEY_ROTATE_AVAILABLE", steps=forms)
    return Selection("BLOCKED", None, "EPOCH_COMPROMISED")


def requires_new_authorization(old_nonce: int, old_commitment: bytes,
                               new_nonce: int, new_commitment: bytes) -> bool:
    """A different target commitment or nonce invalidates the old proof/PI binding.

    This helper covers these two fields only; every other PI field must also be
    checked by the transaction builder. Fresh prover randomness remains required.
    """
    _uint(old_nonce, UINT64_MAX, "old nonce")
    _uint(new_nonce, UINT64_MAX, "new nonce")
    if len(old_commitment) != 32 or len(new_commitment) != 32:
        raise ValueError("commitments must contain exactly 32 bytes")
    return old_nonce != new_nonce or not hmac.compare_digest(old_commitment, new_commitment)


@dataclass(frozen=True)
class KeyUseDecision:
    allowed: bool
    reason: str


def revalidate_key_use(scope: DerivationScope, state: CanonicalState,
                       store: WalletEpochStore, current_key: CurrentKey, *, for_range_repair: bool = False) -> KeyUseDecision:
    """Fresh activation/signing gate on the epoch record; recovery alone does not authorize use.

    The application must serialize this check with signing and compromise-event
    processing in its single wallet process, and re-fetch canonical state first.
    A previous ALLOWED/SELECTED result is not a durable capability. This API does
    not implement cross-process signing coordination or authenticate RPC state.
    It reads the epoch record only; the adapter's signers also consult the
    authorization tracker's commitment-level exposures first (D-1, wallet.py).
    (31.2 rule 5): with for_range_repair, a key that only MATCH_ABOVE_BOUND finds is accepted too, for the
    same-key writes of the range repair only.
    """
    above = (for_range_repair is True and isinstance(current_key, CurrentKey)
             and current_key.above_bound(scope, state))
    if not isinstance(current_key, CurrentKey) or not (current_key.matches(scope, state) or above):
        return KeyUseDecision(False, "STALE_OR_UNVERIFIED_CURRENT_KEY")
    store.sync_canonical(scope, state, None if above else current_key, above_bound=current_key if above else None)
    security = store.security(scope)
    if current_key.epoch in security.compromised_epochs:
        return KeyUseDecision(False, "CURRENT_KEY_COMPROMISED")
    return KeyUseDecision(True, "CURRENT_KEY_VERIFIED_AND_NOT_DENIED")
