"""Observe enrollment logs on the local research chain; never sign or change key state.

The caller supplies its own enrollment transaction hashes. A missing hash means
"not recorded by this wallet", not a claim that an attack has been proved.
The observer trusts its local, consensus-validating node, as the demo wallet does.
"""
import json
import os
from pathlib import Path
import time

TOPIC = '0x8ebb3372700da67933964c68aed4af31f4d179ffa18054e781fdfdc5b36067f8'
REGISTRY = '0x0000000000000000000000000000000000000800'


def hex_bytes(value, size):
    if not isinstance(value, str) or not value.startswith('0x'):
        raise ValueError('expected hex DATA')
    data = bytes.fromhex(value[2:])
    if len(data) != size:
        raise ValueError('wrong DATA size')
    return '0x' + data.hex()


class Watch:
    def __init__(self, rpc, address, own_transactions=(), start=0, state=None):
        self.rpc = rpc
        self.address = hex_bytes(address, 20)
        self.own = {hex_bytes(x, 32) for x in own_transactions}
        if start < 0:
            raise ValueError('negative starting block')
        genesis = rpc('eth_getBlockByNumber', ['0x0', False])
        identity = {'chainId': rpc('eth_chainId', []), 'genesis': genesis['hash'],
                    'address': self.address, 'registry': REGISTRY, 'fromBlock': start}
        if int(identity['chainId'], 16) != 13378:
            raise ValueError('this observer is restricted to local chain 13378')
        self.state = {'schema': 1, 'identity': identity, 'blocks': []} if state is None else state
        if self.state.get('schema') != 1 or self.state.get('identity') != identity:
            raise ValueError('observer state belongs to another chain, address or coverage range')
        self.start = start

    def poll(self, stop=None):
        out = []
        blocks = self.state['blocks']
        # Retain observations when a block is removed. This observer does not
        # roll back the wallet's independent exposure/key-generation ledger.
        while blocks:
            old = blocks[-1]
            current = self.rpc('eth_getBlockByNumber', [hex(old['number']), False])
            if current and current['hash'] == old['hash']:
                break
            for event in old['events']:
                out.append({**event, 'kind': 'ENROLLMENT_REMOVED', 'removed': True,
                            'message': 'Enrollment block was reorganized out; no wallet key was made reusable.'})
            blocks.pop()
        head = self.rpc('eth_getBlockByNumber', ['latest', False])
        end = int(head['number'], 16)
        if stop is not None:
            end = min(end, stop)
        begin = blocks[-1]['number'] + 1 if blocks else self.start
        for number in range(begin, min(end + 1, begin + 256)):
            block = self.rpc('eth_getBlockByNumber', [hex(number), False])
            if block is None or (blocks and block['parentHash'] != blocks[-1]['hash']):
                break  # Retry the new canonical branch on the next poll.
            account_topic = '0x' + '00' * 12 + self.address[2:]
            logs = self.rpc('eth_getLogs', [{'blockHash': block['hash'], 'address': REGISTRY,
                                            'topics': [TOPIC, account_topic]}])
            events = []
            for log in sorted(logs, key=lambda x: int(x['logIndex'], 16)):
                if (log.get('removed') or log['blockHash'] != block['hash']
                        or int(log['blockNumber'], 16) != number
                        or log['address'].lower() != REGISTRY
                        or [x.lower() for x in log['topics']] != [TOPIC, account_topic]):
                    raise ValueError('enrollment log identity mismatch')
                data = bytes.fromhex(log['data'][2:])
                if len(data) != 96 or any(data[:31]) or any(data[64:88]):
                    raise ValueError('noncanonical enrollment event')
                enrolled_at = int.from_bytes(data[64:], 'big')
                if enrolled_at != int(block['timestamp'], 16):
                    raise ValueError('enrollment timestamp differs from its block')
                tx = hex_bytes(log['transactionHash'], 32)
                known = tx in self.own
                events.append({'kind': 'KNOWN_ENROLLMENT' if known else 'UNRECOGNIZED_ENROLLMENT',
                    'address': self.address, 'transactionHash': tx, 'blockHash': block['hash'],
                    'blockNumber': number, 'logIndex': int(log['logIndex'], 16), 'removed': False,
                    'algId': data[31], 'pqPkCommit': '0x' + data[32:64].hex(), 'enrolledAt': enrolled_at,
                    'finality': 'canonical-observation; finality not asserted',
                    'message': 'Enrollment matches the supplied local record.' if known else
                    'Enrollment was not recorded by this wallet. Check the commitment and recovery window.'})
            # Do not commit a cursor or print a new alert from a block that was
            # replaced during the request. RPC failures likewise leave it pending.
            again = self.rpc('eth_getBlockByNumber', [hex(number), False])
            if again is None or again['hash'] != block['hash']:
                break
            blocks.append({'number': number, 'hash': block['hash'], 'events': events})
            out.extend(events)
        return out


def run(query, rpc_url, address, own_transactions, start, state_path, once, interval):
    if interval < .1:
        raise ValueError('poll interval must be at least 0.1 seconds')
    state_path = Path(state_path)
    state = json.loads(state_path.read_text()) if state_path.exists() else None
    watch = Watch(lambda m, p: query(rpc_url, m, p), address, own_transactions, start, state)
    print(json.dumps({'kind': 'WATCH_COVERAGE', **watch.state['identity'],
                      'scope': 'local public-test observer; does not sign or update key exposure state'}), flush=True)
    target = int(watch.rpc('eth_blockNumber', []), 16) if once else None
    while True:
        before = [(b['number'], b['hash']) for b in watch.state['blocks']]
        events = watch.poll(target)
        # At-least-once delivery: flush observations BEFORE advancing the durable
        # cursor. A crash between output and rename can repeat an event, but
        # cannot silently consume an event that was never output. Consumers may
        # deduplicate by (blockHash, transactionHash, logIndex, removed).
        for event in events:
            print(json.dumps(event), flush=True)
        state_path.parent.mkdir(parents=True, exist_ok=True)
        temp = state_path.with_name(state_path.name + '.tmp')
        with temp.open('w') as f:
            json.dump(watch.state, f, sort_keys=True); f.write('\n'); f.flush(); os.fsync(f.fileno())
        os.replace(temp, state_path)
        if once:
            blocks = watch.state['blocks']
            scanned = blocks[-1]['number'] if blocks else start - 1
            if scanned >= target or target < start:
                print(json.dumps({'kind': 'WATCH_CAUGHT_UP', 'throughBlock': scanned,
                                  'requestedHead': target}), flush=True)
                return
            if before == [(b['number'], b['hash']) for b in blocks]:
                raise RuntimeError('canonical scan did not progress; retry with the saved cursor')
            continue
        time.sleep(interval)
