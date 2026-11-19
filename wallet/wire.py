"""Public-test carrier encoding and crypto helper transport."""
import hashlib
import subprocess

class Worker:
    def __init__(self, path):
        self.proc = subprocess.Popen([str(path)], stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                     text=True, bufsize=1)

    def text(self, op, *args):
        self.proc.stdin.write(" ".join([op, *[(x.hex() or "-") for x in args]]) + "\n")
        self.proc.stdin.flush()
        result = self.proc.stdout.readline().strip()
        if not result:
            raise RuntimeError(self.proc.stderr.read())
        return result

    def __call__(self, op, *args):
        return bytes.fromhex(self.text(op, *args))

    def close(self):
        self.proc.stdin.close()
        assert self.proc.wait(timeout=10) == 0

def rlp(value):
    """Small independent encoder; no geth or previous protocol adapter imported."""
    if isinstance(value, int):
        assert value >= 0
        value = value.to_bytes((value.bit_length() + 7) // 8, "big")
    if isinstance(value, (list, tuple)):
        payload, offset = b"".join(rlp(v) for v in value), 0xC0
    else:
        assert isinstance(value, bytes)
        if len(value) == 1 and value[0] < 0x80:
            return value
        payload, offset = value, 0x80
    if len(payload) < 56:
        return bytes([offset + len(payload)]) + payload
    size = len(payload).to_bytes((len(payload).bit_length() + 7) // 8, "big")
    return bytes([offset + 55 + len(size)]) + size + payload

def signed_pq(cr, config, sender, key, nonce, value, reveal):
    pk, seed = bytes.fromhex(key["public_key"]), bytes.fromhex(key["public_test_seed"])
    tx = [config["chain_id"], sender, nonce, config["max_priority_fee_per_gas"],
          config["max_fee_per_gas"], config["pq_transaction_gas_limit"],
          bytes.fromhex(config["recipient"]), value, b"", [], 1, [pk] if reveal else [], b""]
    preimage = b"\x7c" + rlp(tx)
    digest, ctx = cr("hash", preimage), b"ETH-PQ-TX/v1"
    message = ctx + digest
    tx[12] = cr("sign", seed, message, ctx)
    assert cr.text("verify", pk, message, ctx, tx[12]) == "true"
    raw = b"\x7c" + rlp(tx)
    variable = tx[8] + tx[12] + (pk if reveal else b"")
    return raw, {"type": 0x7C, "sender": sender.hex(), "nonce": nonce, "value": value,
                 "recipient": config["recipient"], "reveals_pk": reveal,
                 "preimage": preimage.hex(), "digest": digest.hex(), "ctx": ctx.hex(),
                 "message": message.hex(), "signature": tx[12].hex(),
                 "signature_verified": True, "raw_hash": cr("hash", raw).hex(),
                 "raw_sha256": hashlib.sha256(raw).hexdigest(), "raw_bytes": len(raw),
                 "calldata_bytes": len(variable), "calldata_zero_bytes": variable.count(0),
                 "calldata_nonzero_bytes": len(variable) - variable.count(0)}
