// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.28;

/// N1 lab registry (probe). Application code in genesis: stores BLS-authorized
/// leanXMSS registrations before D_reg. It verifies no signature; the checkpoint
/// tool verifies each one against the out-of-band validator snapshot.
contract N1Registry {
    uint64 internal dReg;   // slot 0, written by the genesis alloc
    bytes32 internal acc;   // slot 1, hash chain over accepted payloads
    uint64 internal count;  // slot 2
    uint256 private constant LEN = 312; // SSZ SignedN1Registration

    event Registered(uint64 indexed seq, uint64 indexed validatorIndex, bytes32 accAfter, bytes payload);

    fallback() external {
        require(block.timestamp < dReg, "N1: after D_reg");
        require(msg.data.length == LEN, "N1: length");
        uint64 vi;
        for (uint256 i = 0; i < 8; i++) {
            vi |= uint64(uint8(msg.data[8 + i])) << uint64(8 * i);
        }
        bytes32 a = keccak256(abi.encodePacked(acc, keccak256(msg.data)));
        acc = a;
        emit Registered(count, vi, a, msg.data);
        count += 1;
    }
}
