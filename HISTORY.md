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

## Affine maps and the automorphism group (COD-259, branch `agl`)

Moved from ham_pairings main d1cda40 in c1941cf, with every module-level declaration name and
namespace unchanged. The AGL instance of the polar section was added in 7f4fd9b. "Last old form"
is in ham_pairings, so `git show d1cda40:<path>` there shows it. `RRC` abbreviates
`RoundRobin.Canonical`, and all names are in namespace `Pairing`.

### Moved modules

| old module (ham_pairings) | new module | last old form |
|---|---|---|
| `Repair.Automorphism` | `Pairing.Automorphism` (`core/Pairing/Automorphism.lean`) | `d1cda40:repair/Repair/Automorphism.lean` |

ham_pairings keeps `Repair.Automorphism` as a module that imports `Pairing.Automorphism` and
`Repair.FactorCap.Tail`, its old import, so `import Repair.Automorphism` keeps working. The
declarations are moved unchanged. The file differs from the old one only in its imports
(`Mathlib.LinearAlgebra.AffineSpace.AffineEquiv` and `Pairing.Affine` in place of
`Repair.FactorCap.Tail`), two additions to the module docstring, and the definition of
`FactorCap.gadget` before `RoundRobin.Canonical`.

### Moved declarations (same full name)

| name | old location (ham_pairings) | new location | last old form |
|---|---|---|---|
| `RRC.shift`, `RRC.shift_none`, `RRC.shift_some`, `RRC.shift_inv_none`, `RRC.shift_inv_some`, `RRC.shift_smul_factor` | `suppression/Suppression/HamCount.lean` | `core/Pairing/Affine.lean` | `d1cda40:suppression/Suppression/HamCount.lean:40` to `:66` |
| `RRC.scale`, `RRC.scale_none`, `RRC.scale_some`, `RRC.scale_inv_none`, `RRC.scale_inv_some`, `RRC.scale_smul_factor`, `RRC.scale_mate_factor`, `RRC.affine_smul_factor`, `RRC.isZeroState_affine_smul_iff` | `repair/Repair/FactorCap/Scale.lean` | `core/Pairing/Affine.lean` | `d1cda40:repair/Repair/FactorCap/Scale.lean:26` to `:73`, `:90` |
| `RRC.two_mul_natCast_self`, `RRC.natCast_injOn` | `repair/Repair/ZeroState.lean` | `core/Pairing/Affine.lean` | `d1cda40:repair/Repair/ZeroState.lean:94`, `:103` |
| `FactorCap.gadget` | `repair/Repair/FactorCap/Tail.lean` | `core/Pairing/Automorphism.lean` | `d1cda40:repair/Repair/FactorCap/Tail.lean:49` |
| `RRC.IsAut` and its `DecidablePred` instance, `RRC.IsAut.exists_perm`, `RRC.autGroup`, `RRC.mem_autGroup`, `RRC.mate_smul_eq`, `RRC.isAut_shift`, `RRC.isAut_affine`, `RRC.edgeLabel`, `RRC.mate_edgeLabel`, `RRC.edgeLabel_eq`, `RRC.mate_ne_mate`, `RRC.edgeLabel_smul`, `RRC.localSq`, `RRC.IsMedial`, `RRC.IsMedial.of_hom`, `RRC.localSq_smul`, `RRC.localSq_none`, `RRC.isMedial_localSq_none`, `RRC.localSq_zero`, `RRC.natCast_ne`, `RRC.not_isMedial_localSq_zero`, `RRC.IsAut.apply_none`, `RRC.IsAut.exists_affine`, `RRC.isAut_iff`, `RRC.affine_inj`, `RRC.autEquiv`, `RRC.card_autGroup`, `RRC.affinePerm`, `RRC.affinePerm_some`, `RRC.affinePerm_injective`, `RRC.affineEquiv_apply`, `RRC.range_affinePerm`, `RRC.autGroupMulEquiv`, `RRC.gadgetFlip`, `RRC.gadgetFlip_some`, `RRC.stab_gadget`, `RRC.autGroup_two`, `RRC.card_autGroup_two`, `RRC.card_autGroup_three`, `RRC.isAut_three_moebius` | `repair/Repair/Automorphism.lean` | `core/Pairing/Automorphism.lean` | `d1cda40:repair/Repair/Automorphism.lean:41` to `:506` |

`Suppression.HamCount`, `Repair.FactorCap.Scale`, `Repair.ZeroState` and `Repair.FactorCap.Tail`
stay in ham_pairings without these declarations and import `Pairing.Affine` or
`Pairing.Automorphism`. `RRC.ham_factor_of_isUnit_sub` stays in `Repair.FactorCap.Scale`, since it
uses `RRC.ham_factor_one` of `Suppression.HamCount`.

### New

| name | statement | location | commit |
|---|---|---|---|
| `RRC.affine_mem_fpSpanStab` | `shift m b * scale m a ∈ fpSpanStab (factor m)` | `clifford/Clifford/PolarSectionAGL.lean` | 7f4fd9b |
| `RRC.rrSpan_map_and_isZeroState_affine_smul` | `v ↦ a v + b` fixes `R_rr` under `ρW` and the zero set | `clifford/Clifford/PolarSectionAGL.lean` | 7f4fd9b |
| `RRC.autGroup_le_fpSpanStab` | `autGroup m ≤ fpSpanStab (factor m)` | `clifford/Clifford/PolarSectionAGL.lean` | 7f4fd9b |
| `RRC.rrSpan_map_and_isZeroState_autGroupMulEquiv` | for `4 ≤ m`, `autGroupMulEquiv hm g` fixes `R_rr` under `ρW` and the zero set | `clifford/Clifford/PolarSectionAGL.lean` | 7f4fd9b |

### AxiomCheck

124 endpoints at fd082bf, 143 after c1941cf and 147 after 7f4fd9b. The 19 moved from ham_pairings
`AxiomCheck.lean` (main d1cda40) are `RRC.shift_smul_factor`, `RRC.scale_smul_factor`,
`RRC.isZeroState_affine_smul_iff` and the 16 automorphism endpoints from `RRC.isAut_affine` to
`RRC.isAut_three_moebius`. The 4 new ones are the theorems above.

ham_pairings drops its copies in 760cd71 on branch `agl-main` and records them in its
`historic_references.md`.

## Reachability closure helpers (COD-266 stage 3, branch `spin-shrink`)

From fe1f6bf. The walk induction "a set closed under the edges holds each component it meets" was
proved separately in `core/Pairing/Contraction.lean` (twice, private), in the proof of
`PM.not_ham_of_closed`, and in four places in ham_pairings (inventory entry 25 of
`organize-archive/results/walk-engine-inventory.md`, d13fb2c). It now lives once in
`core/Pairing/Basic.lean`.

### New

| name | statement | location |
|---|---|---|
| `mem_of_reachable_of_forall_adj` | a set closed under the edges of `G` holds every vertex reachable from one of its vertices | `core/Pairing/Basic.lean` |
| `reachable_map_of_forall_adj` | a map sending edges to reachable pairs preserves reachability | `core/Pairing/Basic.lean` |
| `PM.mem_of_reachable_of_mate_mem` | a set closed under `X` and `Y` holds the component of `X ∪ Y` of each of its vertices | `core/Pairing/Basic.lean` |

### Same statement, new proof

| name | now proved from | last old proof |
|---|---|---|
| `PM.not_ham_of_closed` | `PM.mem_of_reachable_of_mate_mem` | `fe1f6bf:core/Pairing/Basic.lean:123` |
| `PM.not_ham_glue` | `PM.not_ham_of_closed` | `fe1f6bf:core/Pairing/Contraction.lean:297` |
| `PM.reachable_of_reachable_contractAt` | `reachable_map_of_forall_adj` | `fe1f6bf:core/Pairing/Union.lean:202` |

### Removed (private)

`reachable_map_of_adj` and `mem_of_reachable` of `core/Pairing/Contraction.lean`
(`fe1f6bf:core/Pairing/Contraction.lean:29`, `:37`). Use the two new lemmas.

### AxiomCheck

179 endpoints, 174 on `[propext, Classical.choice, Quot.sound]` and 5 on fewer axioms. None was
removed.
