"""Pure N1 checkpoint rules shared by the collector and the two-phase lab."""

SLOT = 12
UINT64_MAX = 2**64 - 1


def switch_timeline(genesis, phase0_slots, delta, t_after_t0, min_lead):
    values = (genesis, phase0_slots, delta, t_after_t0, min_lead)
    if any(type(v) is not int for v in values) or genesis < 0:
        raise ValueError("timeline fields must be nonnegative integers")
    # Five registration groups, their finalization, and a deliberately unfinalized tail.
    if phase0_slots < 18 or min_lead < 30 or delta < min_lead + 30 or t_after_t0 <= 0:
        raise ValueError("insufficient registration/checkpoint/startup interval")
    halt = genesis + phase0_slots * SLOT
    deadline = halt + delta
    end = deadline + t_after_t0
    if end > UINT64_MAX:
        raise ValueError("timeline exceeds uint64")
    return {"elGenesis": genesis, "halt": halt, "dReg": deadline, "S": deadline,
            "T0": deadline, "T": end}


def resolve_registrations(snapshot, registrations):
    """Exclude every conflicting index; duplicate identical tuples count once.

    Validation (including BLS) happens before this function. Invalid registrations
    cannot add a tuple or turn an otherwise included validator into a conflict.
    """
    results, included = [], []
    for index in sorted(snapshot):
        mine = [r for r in registrations if r.get("index") == index]
        valid = [r for r in mine if r["valid"]]
        key = lambda r: (r["message"]["lean_attestation_pubkey"], r["message"]["lean_proposal_pubkey"])
        tuples = sorted({key(r) for r in valid})
        item = {"index": index, "registrations": [r["seq"] for r in mine],
                "valid": [r["seq"] for r in valid],
                "invalid": {str(r["seq"]): r["reason"] for r in mine if not r["valid"]}}
        if len(tuples) == 1:
            item.update(result="included", attestation=tuples[0][0], proposal=tuples[0][1])
            included.append(item)
        elif len(tuples) > 1:
            item.update(result="excluded", reason="conflict", path="late path (rule 5)",
                        tuples=[{"attestation": t[0], "proposal": t[1],
                                 "seqs": [r["seq"] for r in valid if key(r) == t]} for t in tuples])
        elif (credential := bytes.fromhex(snapshot[index]["withdrawalCredentials"].removeprefix("0x"))[0]) not in (1, 2):
            item.update(result="excluded", reason="withdrawal-credentials-0x%02x" % credential, rule="6 (a)")
        else:
            item.update(result="excluded", reason="missed")
        results.append(item)
    unknown = [r["seq"] for r in registrations if "unknown-index" in r["reasons"]]
    return results, included, unknown


def execution_invariants(before, after):
    """Checkpoint state and clients stay fixed while latest head may advance."""
    stable = ("gethBinarySHA256", "elGenesisFileSHA256", "genesisBlock", "gethPids", "bckBlock", "balancesAtBck")
    checks = {field: before[field] == after[field] for field in stable}
    checks["clientsAlive"] = bool(after["gethAlive"]) and all(after["gethAlive"].values())
    old, new = before["registrySlots0to2"], after["registrySlots0to2"]
    checks["registry"] = bool(old) and old.keys() == new.keys() and all(
        new[node]["atBck"] == old[node]["atBck"] and
        new[node]["latest"] == old[node]["atBck"] for node in old)
    return checks
