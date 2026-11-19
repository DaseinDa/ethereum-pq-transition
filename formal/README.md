# Formal models

| Folder | Model | Tool |
|---|---|---|
| `account-inductive/` | One account's authority record as an inductive invariant over unbounded integers | Apalache 0.62.4 |

These checks need Java and Apalache, which the offline build does not include. The run of record is kept beside
each model. `tests/test_formal_record.py` ties each record to its model without running Java.
