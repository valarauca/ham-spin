# History

This package was split out of `valarauca/ham_pairings` for COD-257, without rewriting history.

## Source

- Repository `valarauca/ham_pairings`, branch `main`, commit 25936b8
  (`25936b818b5a6c04097c1dd188d8aab63d52460f`, 2026-11-26).
- Every file below was taken unchanged from that commit and keeps its path.

| Path here | Path in ham_pairings (main 25936b8) |
|---|---|
| `core/Pairing.lean` | `core/Pairing.lean` |
| `core/Pairing/Basic.lean` | `core/Pairing/Basic.lean` |
| `core/Pairing/RoundRobin.lean` | `core/Pairing/RoundRobin.lean` |
| `clifford/` (Lean sources, `basic_spin.md`, `sketch.md`, `check_clifford.py`) | `clifford/` |
| `spin/` | `spin/` |
| `lean-toolchain`, `.gitignore` | `lean-toolchain`, `.gitignore` |

The blobs are identical, so `git hash-object <path>` here equals `git rev-parse 25936b8:<path>` in
ham_pairings. The earlier history of a file is read in ham_pairings, for example

    git log --follow 25936b8 -- clifford/Clifford/Contraction.lean

Commits on `main` up to 25936b8 that touched these paths are 23c122b, d6b896d, d845c3e, 9463165,
d06f72c and 33b3edc.

## New in this package

- `lakefile.toml` declares the libraries `Pairing` (srcDir `core`), `Clifford` (srcDir `clifford`)
  and `Spin` (srcDir `spin`).
- `lake-manifest.json` pins the same mathlib `v4.35.0` revision as ham_pairings main 25936b8.
- `AxiomCheck.lean` holds the 74 endpoints of ham_pairings `AxiomCheck.lean` (main 25936b8)
  whose declarations live in this package. The remaining 876 stay in ham_pairings.

Module names and declaration names are unchanged. Every `Pairing.*`, `Clifford.*` and `Spin.*`
module lives here, so ham_pairings has no module under those roots.

`core/Pairing.lean` and `core/Pairing/RoundRobin.lean` were added in a second commit. The first
commit (aa5a395) kept them in ham_pairings, which broke `lake env lean` there, because Lean looks
up every `Pairing.*` module in the first search-path directory that has a `Pairing` folder.

## Renames

Changes made for the risky items of `REVIEW.md` (ham_pairings main 7168bcb) on branch
`spin-risky`, in commits c44c5e4 (module moves), ced0a26 (general vertex type) and fc2bff3
(removals). "Last old form" is the last commit with the old name, location or statement, so
`git show <commit>:<path>` shows it. All names are in namespace `Pairing`, and `PM` abbreviates
`PerfectMatching`.

### Moved modules (declaration names unchanged)

| old | new | commit | last old form |
|---|---|---|---|
| `Clifford.Contraction` | `Pairing.Contraction` (`core/Pairing/Contraction.lean`) | c44c5e4 | `ca8c6cf:clifford/Clifford/Contraction.lean` |
| ham_pairings `Repair.CycleCount` | `Pairing.Union` (`core/Pairing/Union.lean`) | c44c5e4 | ham_pairings `7168bcb:repair/Repair/CycleCount.lean` |

`Clifford.Contraction` stays as a module that only imports `Pairing.Contraction`, so
`import Clifford.Contraction` keeps working.

`Pairing.Union` is a copy of the ham_pairings file, with `PM.cycleCount`, `PM.cycleCount_pos`,
`PM.ham_iff_cycleCount_eq_one`, `PM.cycleCount_comm`, `PM.cycleCount_of_isEmpty`,
`PM.mate_eq_comm`, `PM.Rest`, `PM.contractFn` and its lemmas, `PM.contractAt`,
`PM.componentMap`, `PM.cycleCount_le_contractAt`, `PM.cycleCount_le_contractAt_add_one`,
`PM.contractAt_injOn_eq`, `PM.contractAt_injOn_ne`, `PM.card_rest` and
`PM.sum_pow_cycleCount_le`. Until ham_pairings drops its copy, no module may import both. Only
the `Pairing` root imports `Pairing.Union`, and ham_pairings main imports neither that root nor
`Pairing.Union`.

### Removed

None of these is used or cited in ham-spin, ham_pairings main or `organize-archive/results/`, and
none was an `AxiomCheck.lean` endpoint. Removed in fc2bff3.

| name | finding | last old form |
|---|---|---|
| `PM.raise` | U5 | `ca8c6cf:clifford/Clifford/LocalFactor.lean:23` |
| `PM.raise_w` | U5 | `ca8c6cf:clifford/Clifford/LocalFactor.lean:34` |
| `PM.raise_lower_w` | U5 | `ca8c6cf:clifford/Clifford/LocalFactor.lean:42` |
| `PM.lower_raise_w` | U5 | `ca8c6cf:clifford/Clifford/LocalFactor.lean:50` |
| `PM.raise_mem_adjoin` | U5 | `ca8c6cf:clifford/Clifford/LocalFactor.lean:73` |
| `PM.mem_symmDiff_single` | U6 | `ca8c6cf:clifford/Clifford/Frame.lean:107` |
| `PM.symmDiff_single_erase_comm` | U6 | `ca8c6cf:clifford/Clifford/Frame.lean:112` |
| `PM.frameF_sq` | U6 | `ca8c6cf:clifford/Clifford/Frame.lean:141` |
| `PM.frame_commute` | U6 | `ca8c6cf:clifford/Clifford/Frame.lean:160` |
| `PM.frameE_commute` | U6 | `ca8c6cf:clifford/Clifford/Frame.lean:178` |
| `PM.ι_ones_commute` | U6 | `ca8c6cf:clifford/Clifford/ConceptualForm.lean:56` |
| `PM.ι_ones_sq` | U6 | `ca8c6cf:clifford/Clifford/ConceptualForm.lean:75` |
| `PM.ΓU_anticomm` | U6 | `ca8c6cf:clifford/Clifford/Action.lean:121` |
| `PM.last_mem_erase_castSucc` | U6 | `ca8c6cf:clifford/Clifford/MaasModel.lean:145` |
| `RoundRobin.mem_block` | U6 | `ca8c6cf:core/Pairing/RoundRobin.lean:125` |
| `restrictHom_apply` | U6 | `ca8c6cf:spin/Spin/Existence.lean:82` |
| `AntiComm.sub_right` | U6 | `ca8c6cf:spin/Spin/JSystem.lean:40` |
| `redHom_stildeCl_t` | U6 | `ca8c6cf:spin/Spin/Reduction.lean:105` |
| `redHom_stildeCl_z` | U6 | `ca8c6cf:spin/Spin/Reduction.lean:109` |
| `schurHom_z` | U6 | `ca8c6cf:spin/Spin/SchurForm.lean:145` |

Kept although the review lists them. `PM.symmDiff_single_of_notMem` (U5) is used in
`Assembly.lean` and `Spin/Char2Modules.lean`. `H_comm` (U6) is used by `PM.hamForm_comm` in
`BasisFree.lean`, which the review did not read.

### Deprecated (kept, cited)

| name | finding | cited by | commit |
|---|---|---|---|
| `PM.eq_zero_of_ρW_threeCycle_fixed` | U7 | ham_pairings `TODO.md` (main 7168bcb) | fc2bff3 |
| `PM.ρW_threeCycle_ne_smul_one` | U7 | ham_pairings `TODO.md` (main 7168bcb) | fc2bff3 |

### General vertex type (Fin forms keep their names)

Finding O25. For any `V` with `Fintype.card V = 2 * n`, added in ced0a26.

| `Fin (2 * n)` form | general form | location |
|---|---|---|
| `PM.cknUpperBound` | `PM.cknUpperBound_of_card` | `clifford/Clifford/BasisFree.lean` |
| `PM.nontrivial_W` | `PM.nontrivial_W_of_card` | `clifford/Clifford/Irreducible.lean` |
| `PM.adjoin_ρW_eq_top` | `PM.adjoin_ρW_eq_top_of_card` | `clifford/Clifford/Irreducible.lean` |
| `PM.preserves_of_invariant` | `PM.preserves_of_invariant_of_card` | `clifford/Clifford/Irreducible.lean` |
| `PM.invariant_eq_bot_or_top` | `PM.invariant_eq_bot_or_top_of_card` | `clifford/Clifford/Irreducible.lean` |

`nontrivial_W`, `preserves_of_invariant` and `invariant_eq_bot_or_top` are now corollaries of
the general forms. `cknUpperBound` and `adjoin_ρW_eq_top` stay the base of the transport along
`wCongr`. `finrank_W_eq` and `rank_H_eq` already had `finrank_W_eq_of_card` and
`rank_H_eq_of_card`.

### AxiomCheck

117 endpoints at ca8c6cf, 124 after. No endpoint was removed. Added are the four cycle-count
endpoints that ham_pairings lists (`PM.ham_iff_cycleCount_eq_one`,
`PM.cycleCount_le_contractAt`, `PM.cycleCount_le_contractAt_add_one`,
`PM.sum_pow_cycleCount_le`) and `cknUpperBound_of_card`, `adjoin_ρW_eq_top_of_card` and
`invariant_eq_bot_or_top_of_card`.
