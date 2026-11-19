"""Pure schedule/hash checks for the synthetic live request-deadline regression."""
import hashlib

REQUEST_TARGETS = {"7002": "0x00000961ef480eb55e80d19ad83579a64c007002",
                   "7251": "0x0000bbddc7ce488642fb579f8b00f3a590007251"}


def boundary_schedule(genesis_time, fork_time, window):
    # A is validator zero of three, proposing once every three 12-second slots.
    deadline = fork_time + window
    if window < 612 or window % 12 or (deadline - genesis_time) % 36:
        raise ValueError("request deadline must be an A proposer slot with at least a 612-second window")
    return [("before", deadline - 36, 0), ("at", deadline, 1), ("after", deadline + 36, 1)]


def request_hash(bodies):
    """EIP-7685 hash of the nonempty request types, in increasing type order."""
    if not set(bodies).issubset(REQUEST_TARGETS):
        raise ValueError("unknown request type")
    parts = []
    for kind, type_byte in (("7002", 1), ("7251", 2)):
        if bodies.get(kind):
            parts.append(hashlib.sha256(bytes([type_byte]) + bodies[kind]).digest())
    return "0x" + hashlib.sha256(b"".join(parts)).hexdigest()


def check_boundary_pair(phase, deadline, timestamp, receipts, block, source, payloads):
    expected = {"before": (deadline - 36, 0), "at": (deadline, 1), "after": (deadline + 36, 1)}
    if phase not in expected or timestamp != expected[phase][0]:
        raise ValueError("canonical inclusion missed the requested deadline boundary")
    if set(receipts) != set(REQUEST_TARGETS):
        raise ValueError("both request types must be included in the boundary block")
    status = expected[phase][1]
    bodies = {}
    for kind, receipt in receipts.items():
        if receipt["blockHash"] != block["hash"] or int(receipt["status"], 16) != status:
            raise ValueError("boundary receipt block/status mismatch")
        logs = [row for row in receipt["logs"] if row["address"].lower() == REQUEST_TARGETS[kind]]
        if not status:
            if logs:
                raise ValueError("blocked request emitted a queue log")
            continue
        if len(logs) != 1:
            raise ValueError("accepted request must emit exactly one queue log")
        body = bytes.fromhex(logs[0]["data"].removeprefix("0x"))
        if body != bytes.fromhex(source.removeprefix("0x")) + payloads[kind]:
            raise ValueError("request source or payload mismatch")
        bodies[kind] = body
    expected_hash = request_hash(bodies)
    if block["requestsHash"] != expected_hash:
        raise ValueError("combined canonical requestsHash mismatch")
    return {"phase": phase, "deadline": deadline, "canonicalTimestamp": timestamp,
            "expectedStatus": status, "requestsHash": expected_hash, "source": source}
