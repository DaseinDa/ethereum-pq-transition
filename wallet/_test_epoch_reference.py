"""Retained-high-watermark policy counterexample used only by regression tests.

This intentionally obsolete selection rule is not a wallet authority. Production
selection is wallet_epochs.select_new_key_epoch, which uses the canonical state.
"""
from __future__ import annotations

from wallet_epochs import CanonicalState, UINT32_MAX, _uint


def v118_selection_epoch(state: CanonicalState, *, e_high: int | None,
                         knows_no_seed_key_committed: bool = False) -> int:
    """v1.18: epoch 0 when the wallet knows that no seed-derived key was committed;
    otherwise e_high + 1 with e_high "the highest epoch the account has committed",
    read from local metadata; without e_high the fallback e = migration_nonce(a)."""
    if not isinstance(state, CanonicalState):
        raise ValueError("canonical state required")
    if knows_no_seed_key_committed:
        return 0
    if e_high is not None:
        _uint(e_high, UINT32_MAX - 1, "retained e_high")
        return e_high + 1
    return state.migration_nonce
