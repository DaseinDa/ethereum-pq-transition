"""Local RPC model tests. Real-chain coverage is recorded separately."""
import contextlib
import copy
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from enrollment_watch import REGISTRY, TOPIC, Watch, run

OWNER = '0x' + '11' * 20
TX = '0x' + 'ab' * 32


class Chain:
    def __init__(self, length=3):
        self.blocks = []
        self.logs = {}
        self.calls = []
        for number in range(length):
            self.blocks.append({'number': hex(number), 'hash': '0x' + f'{number + 1:064x}',
                'parentHash': self.blocks[-1]['hash'] if self.blocks else '0x' + '00' * 32,
                'timestamp': hex(1000 + number)})
        self.enroll(1)

    def enroll(self, number, tx=TX):
        b = self.blocks[number]
        self.logs[b['hash']] = [{'address': REGISTRY, 'topics': [TOPIC, '0x' + '00' * 12 + OWNER[2:]],
            'transactionHash': tx, 'blockNumber': b['number'], 'blockHash': b['hash'],
            'logIndex': '0x0', 'data': '0x' + ((1).to_bytes(32, 'big') + bytes([0x42]) * 32
                + int(b['timestamp'], 16).to_bytes(32, 'big')).hex()}]

    def rpc(self, method, params):
        self.calls.append((method, copy.deepcopy(params)))
        if method == 'eth_chainId':
            return '0x3442'
        if method == 'eth_blockNumber':
            return hex(len(self.blocks) - 1)
        if method == 'eth_getBlockByNumber':
            number = len(self.blocks) - 1 if params[0] == 'latest' else int(params[0], 16)
            return copy.deepcopy(self.blocks[number]) if number < len(self.blocks) else None
        if method == 'eth_getLogs':
            assert params[0]['address'] == REGISTRY
            assert params[0]['topics'] == [TOPIC, '0x' + '00' * 12 + OWNER[2:]]
            return copy.deepcopy(self.logs.get(params[0]['blockHash'], []))
        raise AssertionError(method)


class ObserverTests(unittest.TestCase):
    def test_unknown_enrollment(self):
        c = Chain(); events = Watch(c.rpc, OWNER).poll()
        self.assertEqual([e['kind'] for e in events], ['UNRECOGNIZED_ENROLLMENT'])
        self.assertEqual(events[0]['pqPkCommit'], '0x' + '42' * 32)
        self.assertEqual(events[0]['enrolledAt'], 1001)

    def test_known_enrollment(self):
        self.assertEqual(Watch(Chain().rpc, OWNER, [TX]).poll()[0]['kind'], 'KNOWN_ENROLLMENT')

    def test_restart_does_not_repeat(self):
        c = Chain(); w = Watch(c.rpc, OWNER); self.assertEqual(len(w.poll()), 1)
        resumed = Watch(c.rpc, OWNER, state=json.loads(json.dumps(w.state)))
        self.assertEqual(resumed.poll(), [])

    def test_reorg_removal_and_replacement(self):
        c = Chain(); w = Watch(c.rpc, OWNER); w.poll()
        c.blocks[1]['hash'] = '0x' + 'cd' * 32
        c.blocks[2]['parentHash'] = c.blocks[1]['hash']; c.blocks[2]['hash'] = '0x' + 'de' * 32
        c.enroll(1, '0x' + 'ef' * 32)
        events = w.poll()
        self.assertEqual([e['kind'] for e in events], ['ENROLLMENT_REMOVED', 'UNRECOGNIZED_ENROLLMENT'])
        self.assertTrue(events[0]['removed'])

    def test_state_cannot_cross_genesis(self):
        c = Chain(); w = Watch(c.rpc, OWNER); w.poll(); c.blocks[0]['hash'] = '0x' + 'ff' * 32
        with self.assertRaisesRegex(ValueError, 'another chain'):
            Watch(c.rpc, OWNER, state=w.state)

    def test_empty_saved_object_is_not_a_new_cursor(self):
        with self.assertRaises(ValueError): Watch(Chain().rpc, OWNER, state={})

    def test_state_cannot_cross_owner_or_coverage(self):
        c = Chain(); state = Watch(c.rpc, OWNER).state
        with self.assertRaises(ValueError): Watch(c.rpc, '0x' + '22' * 20, state=state)
        with self.assertRaises(ValueError): Watch(c.rpc, OWNER, start=1, state=state)

    def test_mainnet_rejected(self):
        c = Chain()
        with self.assertRaisesRegex(ValueError, 'restricted'):
            Watch(lambda m, p: '0x1' if m == 'eth_chainId' else c.rpc(m, p), OWNER)

    def test_wrong_event_identity(self):
        c = Chain(); c.logs[c.blocks[1]['hash']][0]['blockHash'] = '0x' + 'ff' * 32
        with self.assertRaisesRegex(ValueError, 'identity mismatch'): Watch(c.rpc, OWNER).poll()

    def test_noncanonical_event(self):
        c = Chain(); log = c.logs[c.blocks[1]['hash']][0]; log['data'] += '00'
        with self.assertRaisesRegex(ValueError, 'noncanonical'): Watch(c.rpc, OWNER).poll()

    def test_event_timestamp(self):
        c = Chain(); log = c.logs[c.blocks[1]['hash']][0]
        log['data'] = log['data'][:-64] + (999).to_bytes(32, 'big').hex()
        with self.assertRaisesRegex(ValueError, 'timestamp'): Watch(c.rpc, OWNER).poll()

    def test_block_changes_during_log_read(self):
        c = Chain()
        def rpc(m, p):
            result = c.rpc(m, p)
            if m == 'eth_getLogs' and p[0]['blockHash'] == c.blocks[1]['hash']:
                c.blocks[1]['hash'] = '0x' + 'fe' * 32
            return result
        w = Watch(rpc, OWNER)
        self.assertEqual(w.poll(), []); self.assertEqual(w.state['blocks'][-1]['number'], 0)

    def test_once_catches_up_across_pages(self):
        c = Chain(600)
        with tempfile.TemporaryDirectory() as temp, contextlib.redirect_stdout(io.StringIO()) as out:
            path = Path(temp) / 'cursor.json'
            run(lambda u, m, p: c.rpc(m, p), 'local', OWNER, [], 0, path, True, .1)
            self.assertEqual(json.loads(path.read_text())['blocks'][-1]['number'], 599)
            events = [json.loads(line) for line in out.getvalue().splitlines()]
            self.assertEqual(events[-1]['kind'], 'WATCH_CAUGHT_UP')
            self.assertEqual(sum(e['kind'] == 'UNRECOGNIZED_ENROLLMENT' for e in events), 1)

    def test_failed_output_does_not_consume_alert(self):
        c = Chain()
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'cursor.json'
            def printing(text, **kwargs):
                if json.loads(text)['kind'] == 'UNRECOGNIZED_ENROLLMENT': raise BrokenPipeError()
            with patch('builtins.print', side_effect=printing), self.assertRaises(BrokenPipeError):
                run(lambda u, m, p: c.rpc(m, p), 'local', OWNER, [], 0, path, True, .1)
            self.assertFalse(path.exists())


if __name__ == '__main__':
    unittest.main()
