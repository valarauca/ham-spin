# History

This package was split out of `valarauca/ham_pairings` for COD-257, without rewriting history.

## Source

- Repository `valarauca/ham_pairings`, branch `main`, commit 25936b8
  (`25936b818b5a6c04097c1dd188d8aab63d52460f`, 2026-11-26).
- Every file below was taken unchanged from that commit and keeps its path.

| Path here | Path in ham_pairings (main 25936b8) |
|---|---|
| `core/Pairing/Basic.lean` | `core/Pairing/Basic.lean` |
| `clifford/` (Lean sources, `basic_spin.md`, `sketch.md`, `check_clifford.py`) | `clifford/` |
| `spin/` | `spin/` |
| `lean-toolchain`, `.gitignore` | `lean-toolchain`, `.gitignore` |

The blobs are identical, so `git hash-object <path>` here equals `git rev-parse 25936b8:<path>` in
ham_pairings. The earlier history of a file is read in ham_pairings, for example

    git log --follow 25936b8 -- clifford/Clifford/Contraction.lean

Commits on `main` up to 25936b8 that touched these paths are 23c122b, d6b896d, d845c3e, 9463165
and 33b3edc.

## New in this package

- `lakefile.toml` declares the libraries `PairingBasic` (srcDir `core`, root `Pairing.Basic`),
  `Clifford` (srcDir `clifford`) and `Spin` (srcDir `spin`).
- `lake-manifest.json` pins the same mathlib `v4.35.0` revision as ham_pairings main 25936b8.
- `AxiomCheck.lean` holds the 68 endpoints of ham_pairings `AxiomCheck.lean` (main 25936b8)
  whose declarations live in this package. The remaining endpoints stay in ham_pairings.

Module names and declaration names are unchanged. The module `Pairing.Basic` lives here, and
ham_pairings keeps the modules `Pairing` and `Pairing.RoundRobin` in its `Pairing` library.
