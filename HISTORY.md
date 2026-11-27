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

## Three-cycle presentation, archive Conjecture 13.2 (COD-275, branch `spin-pres`)

From 5ecf8a5. The upper-bound half of the CKN proof (`clifford/Clifford/Dimension.lean`, section
`Upper`) and the edge relations R1 to R4 used only `1 + τ + τ² = 0`. They are now proved once for
any `IsThreeCycleRep` in namespace `PM.ThreeCycleRep`, and the `W` statements are specializations.
The presented module `Q V = 𝔽₂^𝓜 ⧸ R_3` is a second instance, which gives `Q V ≃ W V` and
`ker Θ = R_3`. The mathematics is Proposition A and Corollary A1 of
`results/presentation-consequences-contra.md` and Theorem A and Corollary A2 of
`results/presentation-consequences-extend.md` (organize-archive 3ba2201). Background is
`results/switch-patterns-extend.md` Theorem 2.1 (3293188).

### New

| name | statement | location |
|---|---|---|
| `PM.IsThreeCycleRep` | `1 + ρ(τ) + ρ(τ)² = 0` for every three-cycle `τ` | `clifford/Clifford/EdgeRelations.lean` |
| `PM.ThreeCycleRep.Γ`, `.Γ_comm`, `.Γ_mul_self`, `.Γ_mul_comm_of_disjoint`, `.Γ_conj`, `.end_add_self` | `Γ_ij = ρ((i j))` and the group relations on any representation | `clifford/Clifford/EdgeRelations.lean` |
| `PM.ThreeCycleRep.Γ_anticomm_of_adj`, `.Γ_add_Γ_add_Γ`, `.Γ_eq_add` | R3 and R4 on any `IsThreeCycleRep` | `clifford/Clifford/EdgeRelations.lean` |
| `PM.isThreeCycleRep_ρW` | `W V` is a three-cycle representation (T1) | `clifford/Clifford/EdgeRelations.lean` |
| `PM.ThreeCycleRep.wv`, `.wv_empty`, `.ρ_sigma_wv`, `.wv_insert` | `w_S = σ_S e` and the gap swaps on it | `clifford/Clifford/Dimension.lean` |
| `PM.ThreeCycleRep.B`, `.Γ_gap`, `.B_mul_sigma`, `.B_wv`, `.wspan`, `.wv_mem`, `.pres_adj`, `.pres_Γ`, `.pres_ρ`, `.span_wv_eq_top` | section `Upper` for any `IsThreeCycleRep` with a generator fixed by the block swaps | `clifford/Clifford/Dimension.lean` |
| `PM.ThreeCycleRep.finrank_le` | such a module on `Fin (2n)` has `dim ≤ 2^(n-1)` | `clifford/Clifford/Dimension.lean` |
| `PM.w_eq_wv`, `PM.Wspan_eq_wspan` | `w_S` and `Wspan` are the generic ones at `e = r_{P0}` | `clifford/Clifford/Dimension.lean` |
| `PM.isThreeCycle_permCongr`, `PM.permCongr_swap` | relabelling keeps three-cycles and transpositions | `clifford/Clifford/Presentation.lean` |
| `PM.finrank_le_of_isThreeCycleRep` | `|V| = 2n`, generator fixed by the edges of one matching, gives `dim ≤ 2^(n-1)` | `clifford/Clifford/Presentation.lean` |
| `PM.δ`, `PM.ρ_δ`, `PM.sum_smul_δ` | the basis vectors `e_P` of `𝔽₂^𝓜` | `clifford/Clifford/Presentation.lean` |
| `PM.R3`, `PM.orbitSum_mem_R3`, `PM.R3_le_comap` | `R_3`, the span of the orbit sums `e_P + e_{τP} + e_{τ²P}` | `clifford/Clifford/Presentation.lean` |
| `PM.Q`, `PM.ρQ`, `PM.ρQ_mk`, `PM.isThreeCycleRep_ρQ`, `PM.span_orbit_mk_δ` | `Q V = 𝔽₂^𝓜 ⧸ R_3` with its `S_V` action | `clifford/Clifford/Presentation.lean` |
| `PM.finrank_Q_le`, `PM.finrank_Q_eq` | `dim Q V ≤ 2^(n-1)`, and `= 2^(n-1)` for `n ≥ 1` | `clifford/Clifford/Presentation.lean` |
| `PM.Θ`, `PM.Θ_δ`, `PM.R3_le_ker_Θ`, `PM.Θ_surjective`, `PM.Θ_ρ` | the row map `e_P ↦ r_P` | `clifford/Clifford/Presentation.lean` |
| `PM.ΘQ`, `PM.ΘQ_mk`, `PM.ΘQ_ρQ`, `PM.ΘQ_surjective`, `PM.ΘQ_bijective`, `PM.ΘQEquiv`, `PM.ΘQEquiv_mk_δ` | the induced `S_V`-map `Q V → W V` is bijective | `clifford/Clifford/Presentation.lean` |
| `PM.ker_Θ_eq_R3` | Conjecture 13.2, `ker Θ = R_3` for `|V| = 2n`, `n ≥ 1` | `clifford/Clifford/Presentation.lean` |
| `PM.rowW_eq_sum`, `PM.mk_δ_eq_sum` | `r_P = ∑_S H[P, X_{G∖S}] w_S`, and the normal form `e_P ≡ ∑_S H[P, X_{G∖S}] e_{X_S}` mod `R_3` | `clifford/Clifford/Presentation.lean` |
| `PM.firstBlocks`, `PM.mem_matchingStar_firstBlocks` | `E_j`, the first `j` edges of `P0`, and `x ∈ L_{E_j}` iff the block swaps `a < j` fix `x` | `clifford/Clifford/MatchingStarDim.lean` |
| `PM.completions`, `PM.mem_completions`, `PM.card_completions` | the gap sets with no gap below `j`, `2^(n-1-j)` of them | `clifford/Clifford/MatchingStarDim.lean` |
| `PM.w_mem_matchingStar_firstBlocks`, `PM.lower_eq_zero_of_mem`, `PM.repr_eq_zero_of_mem` | completion rows lie in `L_{E_j}`, and the lowering operators cut out the rest | `clifford/Clifford/MatchingStarDim.lean` |
| `PM.matchingStar_firstBlocks_eq_span`, `PM.finrank_matchingStar_firstBlocks` | `L_{E_j} = span{w_S : S ∈ completions j}` and `dim L_{E_j} = 2^(n-1-j)` (extend Corollary A4) | `clifford/Clifford/MatchingStarDim.lean` |
| `PM.card_filter_lt_mate` | a perfect matching of `Fin (2n)` has `n` edges `v < M v` | `clifford/Clifford/Corollaries.lean` |

### Same statement, new proof

Each is now a specialization of its `PM.ThreeCycleRep` namesake.

| name | last old proof |
|---|---|
| `PM.end_add_self` | `5ecf8a5:clifford/Clifford/EdgeRelations.lean:22` |
| `PM.Γ_comm` | `5ecf8a5:clifford/Clifford/EdgeRelations.lean:29` |
| `PM.Γ_mul_self` | `5ecf8a5:clifford/Clifford/EdgeRelations.lean:33` |
| `PM.Γ_mul_comm_of_disjoint` | `5ecf8a5:clifford/Clifford/EdgeRelations.lean:37` |
| `PM.Γ_anticomm_of_adj` | `5ecf8a5:clifford/Clifford/EdgeRelations.lean:47` |
| `PM.Γ_conj` | `5ecf8a5:clifford/Clifford/EdgeRelations.lean:65` |
| `PM.Γ_add_Γ_add_Γ` | `5ecf8a5:clifford/Clifford/EdgeRelations.lean:70` |
| `PM.Γ_eq_add` | `5ecf8a5:clifford/Clifford/EdgeRelations.lean:81` |
| `PM.w_insert` | `5ecf8a5:clifford/Clifford/Dimension.lean:178` |
| `PM.B_mul_sigma` | `5ecf8a5:clifford/Clifford/Dimension.lean:224` |
| `PM.B_w` | `5ecf8a5:clifford/Clifford/Dimension.lean:259` |
| `PM.pres_adj` | `5ecf8a5:clifford/Clifford/Dimension.lean:307` |
| `PM.pres_Γ` | `5ecf8a5:clifford/Clifford/Dimension.lean:324` |
| `PM.pres_ρW` | `5ecf8a5:clifford/Clifford/Dimension.lean:357` |
| `PM.span_w_eq_top` | `5ecf8a5:clifford/Clifford/Dimension.lean:375` |

`PM.sum_Γ_matching` (C3) is now proved from `Γ(𝟙) r_{P0} = n r_{P0}` and the spanning rows, without
T4 (`adjoin_ρW_eq_top`), `wBasis` or `eq_smul_one_of_commute_rankOne`, following the compiled
prototype `scripts/presentation-consequences-c-c3.lean` (organize-archive 3ba2201). Its last old
proof is `4dbb915:clifford/Clifford/Corollaries.lean:150`. `eq_smul_one_of_commute_rankOne`,
`qfun_ones` and `f2_mul_self` keep their statements but have no users left in ham-spin.

### Moved (private)

`pres_of_gen` (`5ecf8a5:clifford/Clifford/Dimension.lean:292`) is now `PM.ThreeCycleRep.pres_of_gen`.

### AxiomCheck

193 endpoints, 188 on `[propext, Classical.choice, Quot.sound]` and 5 on fewer axioms. The 14 new
ones are `isThreeCycleRep_ρW`, `ThreeCycleRep.finrank_le`, `finrank_le_of_isThreeCycleRep`,
`isThreeCycleRep_ρQ`, `finrank_Q_le`, `finrank_Q_eq`, `ΘQ_ρQ`, `ΘQ_bijective`, `ΘQEquiv`,
`ker_Θ_eq_R3`, `rowW_eq_sum`, `mk_δ_eq_sum`, `matchingStar_firstBlocks_eq_span` and
`finrank_matchingStar_firstBlocks`. None was removed.

## Temperley–Lieb and Brauer forms of the presentation (COD-278, branch `spin-tl`)

From 5ecf8a5, merged with 11916af. Theorems B.1, B.2, C.1 to C.4 of
`results/presentation-consequences-extend.md` §3.1 and §3.2, with items 8 to 14 of
`results/presentation-consequences-factcheck-extend.md` (organize-archive 3ba2201). The crossing
`s_i = 1 + e_i` at `δ = -2` is from `results/tl-jantzen-extend.md` (b21b41a). Mathlib v4.35.0
has no Temperley–Lieb or Brauer algebra, so `TL_N(δ)` is built here as a `RingCon.Quotient` of a
free algebra, like Mathlib's `CliffordAlgebra`. B.3 is not formalized. It needs the
`TL_2n(0)`-module structure on `Δ = 𝔽₂^𝓜 ⧸ R_4`, that is the braid relation for cap-cups, which is
not in the package.

### New

| name | statement | location |
|---|---|---|
| `TL`, `TL.Rel`, `TL.ringCon`, `TL.mk`, `TL.e`, `TL.mk_rel` | `TL_N(δ)` over a commutative ring, generators `e_i`, `i < N - 1` | `clifford/Clifford/TemperleyLieb.lean` |
| `TL.e_mul_self`, `TL.e_mul_e_mul_e`, `TL.e_mul_e_comm` | the Temperley–Lieb relations | `clifford/Clifford/TemperleyLieb.lean` |
| `TL.lift`, `TL.lift_e`, `TL.hom_ext` | the universal property | `clifford/Clifford/TemperleyLieb.lean` |
| `jw`, `jw_comm`, `mul_jw`, `jw_mul`, `jw_mul_self`, `map_jw` | the Jones–Wenzl element `1 - (δ/(δ²-1))(x + y) + (1/(δ²-1))(xy + yx)` and its algebra | `clifford/Clifford/TemperleyLieb.lean` |
| `TL.e_mul_jw`, `TL.jw_mul_e`, `TL.e_mul_jw'`, `TL.jw_mul_e'`, `TL.jw_e_mul_self` | B.1 on adjacent generators of any `TL_N(δ)` | `clifford/Clifford/TemperleyLieb.lean` |
| `TL.f3`, `TL.e_mul_f3_and`, `TL.f3_mul_self` | B.1, `e_i f_3 = f_3 e_i = 0` and `f_3² = f_3` in `TL_3(δ)` for `δ² - 1` a unit | `clifford/Clifford/TemperleyLieb.lean` |
| `one_add_mul_add_mul_eq_three_smul_jw`, `TL.one_add_s_mul_s_add_s_mul_s` | B.1, `1 + s_1 s_2 + s_2 s_1 = 3 f_3` at `δ = -2` when `3` is a unit | `clifford/Clifford/TemperleyLieb.lean` |
| `jw_zero_F₂`, `TL.f3_F₂` | B.1, `f_3 = 1 + e_1 e_2 + e_2 e_1` over `𝔽₂` at `δ = 0` | `clifford/Clifford/TemperleyLieb.lean` |
| `TL.JWRel`, `TLJW`, `TLJW.mk`, `TLJW.mk_jw`, `TLJW.mk_surjective`, `TLJW.lift`, `TLJW.lift_mk`, `TLJW.ebar`, `TLJW.hom_ext` | `TL_2n(0) ⧸ ⟨f_3^(i)⟩` over `𝔽₂`, all translates as generators | `clifford/Clifford/TemperleyLieb.lean` |
| `TLJW.clToTLJW`, `TLJW.tlToCl`, `TLJW.tlJWToCl` | the maps `ι(v_{t,t+1}) ↦ 1 + ē_t` (from `reduceHom`) and `e_t ↦ 1 + ι(v_{t,t+1})` | `clifford/Clifford/TemperleyLieb.lean` |
| `TLJW.jwQuotEquivCl`, `TLJW.jwQuotEquivCl_ebar`, `TLJW.jwQuotEquivCl_symm_ι` | B.2, `TL_2n(0) ⧸ ⟨f_3^(i)⟩ ≃ₐ Cl(U_n, q)` | `clifford/Clifford/TemperleyLieb.lean` |
| `one_add_mul_mul_one_add_of_comm_F₂`, `conj_one_add_F₂`, `TL.s`, `TL.e_mul_self_zero`, `TL.s_mul_self`, `TL.s_mul_e_mul_s`, `TL.s_mul_s_mul_e_mul_s_mul_s`, `TL.conj_one_add_mul_add_mul` | conjugation by the crossings `s_i = 1 + e_i` in `TL_N(0)` over `𝔽₂` | `clifford/Clifford/TemperleyLieb.lean` |
| `TL.jw_succ_eq`, `TL.map_jw_eq_zero`, `TLJW.liftOfF3`, `TLJW.liftOfF3_mk` | `f_3^(k+1) = w f_3^(k) w⁻¹`, so `⟨f_3⟩` contains every translate and `TLJW n` is `TL_2n(0) ⧸ ⟨f_3⟩` | `clifford/Clifford/TemperleyLieb.lean` |
| `PM.brauerPairing`, `PM.H_eq_coeff_X_pow`, `PM.coeff_one_brauerPairing` | C.1, `H(x, y)` is the `δ¹` coefficient of `∑ x_P y_Q δ^{c(P ∪ Q)}` | `clifford/Clifford/Brauer.lean` |
| `PM.offPair`, `PM.cup`, `PM.cupFun`, `PM.glue_cup`, `PM.capFun`, `PM.boundary`, `PM.contract_cup`, `PM.hasClosedCycle_cup_iff` | `Q ∪ {ab}`, `∂_ab F`, and their relation to `glue` and `contract` | `clifford/Clifford/Brauer.lean` |
| `PM.H_cup` | C.2 on matchings, `H[Q ∪ ab, F] = [ab ∉ F] H[Q, ∂_ab F]` for `V ∖ {a, b}` nonempty | `clifford/Clifford/Brauer.lean` |
| `PM.cupLin`, `PM.capLin`, `PM.capVec`, `PM.hamForm_δ`, `PM.hamForm_cupLin` | C.2, the cap is the `H`-adjoint of the cup | `clifford/Clifford/Brauer.lean` |
| `PM.fourSum`, `PM.R4`, `PM.isThreeCycle_four`, `PM.R4_le_R3` | `R_4`, spanned by four-point orbit sums, lies in `R_3` | `clifford/Clifford/Brauer.lean` |
| `PM.cup_boundary`, `PM.fourSum_eq`, `PM.cupLin_capLin_add_mem_R4`, `PM.mk_cupLin_capLin` | C.4, cap-cup on `{a, b}` is `1 + (a b)` modulo `R_4` | `clifford/Clifford/Brauer.lean` |
| `PM.cup_smul`, `PM.cupLin_R3_le`, `PM.coe_Θ`, `PM.mem_R3_iff`, `PM.capLin_R3_le`, `PM.congrLin`, `PM.congrLin_R3_le` | C.3, cups, caps (`|V| = 2n`, `n ≥ 2`) and bijections preserve `R_3`; `R_3` is the radical of `H` | `clifford/Clifford/Brauer.lean` |
| `PM.cupQ`, `PM.capQ`, `PM.congrQ`, `PM.cupQ_mk`, `PM.capQ_mk`, `PM.cupQ_capQ` | C.3 and C.4 on `Q V = 𝔽₂^𝓜 ⧸ R_3` | `clifford/Clifford/Brauer.lean` |

C.2 needs `V ∖ {a, b}` nonempty. At `|V| = 2` it is false (fact check item 13), and `H_cup` uses
`H_glue_of_hasClosedCycle`, which needs a nonempty complement.

### AxiomCheck

213 endpoints, 208 on `[propext, Classical.choice, Quot.sound]` and 5 on fewer axioms. The 20 new
ones are `TL.e_mul_f3_and`, `TL.f3_mul_self`, `TL.one_add_s_mul_s_add_s_mul_s`, `TL.f3_F₂`,
`TLJW.jwQuotEquivCl`, `TLJW.jwQuotEquivCl_ebar`, `TLJW.jwQuotEquivCl_symm_ι`, `TL.jw_succ_eq`,
`TL.map_jw_eq_zero`, `TLJW.liftOfF3`,
`coeff_one_brauerPairing`, `H_cup`, `hamForm_cupLin`, `R4_le_R3`, `cupLin_capLin_add_mem_R4`,
`mk_cupLin_capLin`, `cupLin_R3_le`, `capLin_R3_le`, `congrLin_R3_le` and `cupQ_capQ`. None was
removed.

## Theorem B.3, `W_n ≅ Δ_2n(0) ⧸ ⟨f_3⟩ Δ_2n(0)` (COD-278, branch `spin-b3`)

From 59ff171. Theorem B.3 of `results/presentation-consequences-extend.md` §3.1, verified in item
10 of `results/presentation-consequences-factcheck-extend.md` (organize-archive 3ba2201).
`Δ V = 𝔽₂^𝓜 ⧸ R_4` is the four-switch quotient. The missing local lemma is the vanishing of the
`S_3` sum on three points modulo `R_4`. It is proved from `cap_ab (b c) cup_ab = 1` and C.4, with no
finite check. The Jantzen identification `M̄² = rad H_n` (`results/tl-jantzen-extend.md` Theorem 3,
b21b41a) is not formalized.

### New

| name | statement | location |
|---|---|---|
| `PM.swap_smul_cup_mate_left`, `PM.boundary_swap_smul_cup`, `PM.capLin_ρ_swap_cupLin` | `cap_ab ∘ (b c) ∘ cup_ab = 1` for `c ∉ {a, b}` | `clifford/Clifford/TLAction.lean` |
| `PM.smul_smul_eq_conj_smul`, `PM.ρ_fourSum`, `PM.R4_le_comap` | `R_4` is `S_V`-stable | `clifford/Clifford/TLAction.lean` |
| `PM.sym3_mem_R4`, `PM.sum_sym3_δ_mem_R4` | the local lemma, `∑_{σ ∈ Sym{a,b,c}} e_{σP} ∈ R_4` | `clifford/Clifford/TLAction.lean` |
| `PM.Δ`, `PM.ρΔ`, `PM.ρΔ_mk`, `PM.ρΔ_swap_mul_self`, `PM.ρΔ_sym3`, `PM.one_add_mul_mul_one_add_of_sym3`, `PM.one_add_ρΔ_braid` | `Δ V = 𝔽₂^𝓜 ⧸ R_4`, its `S_V` action and the local lemma on it | `clifford/Clifford/TLAction.lean` |
| `PM.one_add_mul_self_F₂`, `PM.adjSwap_commute`, `PM.one_add_ρΔ_adjSwap_braid`, `PM.tlAct`, `PM.tlAct_e`, `PM.tlAct_one_add_e` | `TL_2n(0)` acts on `Δ_2n(0)` by `e_i ↦ 1 + (i, i+1)` | `clifford/Clifford/TLAction.lean` |
| `PM.closure_adjSwap`, `PM.le_comap_tlAct` | adjacent transpositions generate `S_m`; a submodule stable under them is `TL_2n(0)`-stable | `clifford/Clifford/TLAction.lean` |
| `PM.f3TL`, `PM.τ₀`, `PM.isThreeCycle_τ₀`, `PM.τ₀_sq`, `PM.tlAct_f3`, `PM.tlAct_f3_mk` | `f_3` acts on `Δ_2n(0)` as `1 + τ₀ + τ₀²`, `τ₀ = (0 1)(1 2)` | `clifford/Clifford/TLAction.lean` |
| `PM.f3Delta`, `PM.f3Delta_le_comap_tlAct`, `PM.f3Delta_le_comap_ρΔ` | `⟨f_3⟩ Δ_2n(0)`, stable under `TL_2n(0)` and `S_2n` | `clifford/Clifford/TLAction.lean` |
| `PM.R3Δ`, `PM.R3Δ_le_comap`, `PM.mk_mem_R3Δ_iff`, `PM.orbit_mem_R3` | the image `R_3 ⧸ R_4` of `R_3` in `Δ V` | `clifford/Clifford/TLAction.lean` |
| `PM.f3Delta_le_R3Δ`, `PM.R3Δ_le_f3Delta`, `PM.f3Delta_eq` | `⟨f_3⟩ Δ_2n(0) = R_3 ⧸ R_4` for `n ≥ 2` | `clifford/Clifford/TLAction.lean` |
| `PM.deltaQuotEquivW`, `PM.deltaQuotEquivW_mk`, `PM.deltaQuotEquivW_ρ` | B.3, `Δ_2n(0) ⧸ ⟨f_3⟩ Δ_2n(0) ≃ W_n`, `S_2n`-equivariant, `[e_P] ↦ r_P` | `clifford/Clifford/TLAction.lean` |
| `PM.mk_mem_f3Delta_iff` | `[x] ∈ ⟨f_3⟩ Δ_2n(0)` iff `x` is in the radical of `H` | `clifford/Clifford/TLAction.lean` |

### AxiomCheck

224 endpoints, 219 on `[propext, Classical.choice, Quot.sound]` and 5 on fewer axioms. The 11 new
ones are `capLin_ρ_swap_cupLin`, `R4_le_comap`, `sym3_mem_R4`, `sum_sym3_δ_mem_R4`, `ρΔ_sym3`,
`tlAct`, `tlAct_f3`, `f3Delta_eq`, `deltaQuotEquivW`, `deltaQuotEquivW_ρ` and
`mk_mem_f3Delta_iff`. None was removed.

## The Hamiltonian-pair quadratic form and the parity theorem (COD-293, branch `spin-q`)

From e88ff2d. The form `Q(u) = ⟨ABu, BAu⟩` with `A = 1 + Γ_vx`, `B = 1 + Γ_vy` is the elementary
construction of `results/parity-apps-contra.md` §1, verified in
`results/parity-apps-factcheck-contra.md` (organize-archive d6e5620). It formalizes Theorem A part 1
and Corollary B of `results/outside-applications-extend.md` §§1–2 and Theorem Q of
`results/p1f-spin-extend.md` §1.2 (d6e5620), without `ker Θ = R_3`. The vanishing `Q(φ(P)) = 0`
is proved by one edge of `P` that misses `v, x, y`, in place of the contra's four-case check.
S_2m-invariance, Witt index and plus type (Theorem A parts 2 to 4) are not formalized.

### New

| name | statement | location |
|---|---|---|
| `PM.fpForm_Γ_left`, `PM.one_add_Γ_mul_self`, `PM.fpForm_one_add_Γ_left` | `Γ_e` and `1 + Γ_e` are self-adjoint, `(1 + Γ_e)² = 0` | `clifford/Clifford/QuadraticForm.lean` |
| `PM.quadT`, `PM.quadS`, `PM.fpForm_quadT_left`, `PM.fpForm_quadS_left`, `PM.quadT_mul_quadS`, `PM.quadS_mul_quadT`, `PM.quadT_add_quadS` | `AB` and `BA` are adjoint, `AB · BA = BA · AB = 0`, `AB + BA = 1` | `clifford/Clifford/QuadraticForm.lean` |
| `PM.hamQuad`, `PM.hamQuad_apply`, `PM.polar_hamQuad`, `PM.polarBilin_hamQuad`, `PM.quadraticForm_add_of_polarBilin`, `PM.hamQuad_add` | (i) `Q(u) = ⟨ABu, BAu⟩` has polar form `fpForm` | `clifford/Clifford/QuadraticForm.lean` |
| `PM.hamQuad_rowW` | (ii) `Q(φ(P)) = 0` for `\|V\| ≥ 7` | `clifford/Clifford/QuadraticForm.lean` |
| `PM.quadraticForm_eq_of_polarBilin`, `PM.existsUnique_quadraticForm`, `PM.hamQuad_eq` | the form is unique, exists for `\|V\| = 2m`, `m ≥ 4`, and does not depend on `(v, x, y)` | `clifford/Clifford/QuadraticForm.lean` |
| `PM.quadraticForm_sum_rowW`, `PM.hamQuad_sum_rowW` | (iii) `Q(Σ_{i ∈ s} φ(F_i)) = #{i < j : Ham F_i F_j}` mod 2 | `clifford/Clifford/QuadraticForm.lean` |
| `PM.coe_sum_rowW_apply`, `PM.sum_rowW_ne_zero_of_odd`, `PM.exists_odd_ham_of_odd`, `PM.even_hamPairs_of_sum_rowW_eq_zero` | Corollary B.1 and B.3 | `clifford/Clifford/QuadraticForm.lean` |

### AxiomCheck

234 endpoints, 229 on `[propext, Classical.choice, Quot.sound]` and 5 on fewer axioms. The 10 new
ones are `quadT_add_quadS`, `polarBilin_hamQuad`, `hamQuad_rowW`, `existsUnique_quadraticForm`,
`hamQuad_eq`, `quadraticForm_sum_rowW`, `hamQuad_sum_rowW`, `sum_rowW_ne_zero_of_odd`,
`exists_odd_ham_of_odd` and `even_hamPairs_of_sum_rowW_eq_zero`. None was removed.

## Pure spinors and the self-dual code dictionary (COD-297, branch `spin-dict`)

From 87df892. Theorems 1 and 2 of `results/spinor-hull-extend.md` (organize-archive b47b504), and
Theorem 1.1 and Corollary 1.2 of `results/spinor-codes.md` (d846b99), split into layers as in
`results/spinor-codes-factcheck.md` (4e3fe2d) §6. No quotient type is built. The space is
`U × 𝔽₂` with `q̃(x, λ) = q(x) + λ`, and `kE = 𝟙 + nε` spans the kernel of the map to
`Ũ_n = (U ⊕ 𝔽₂ε) ⧸ ⟨𝟙 + nε⟩`. Every maximal totally singular subspace contains `kE`, so dimensions
in `Ũ_n` are one less than here. Theorem 2 is proved without the Fock basis: `𝔽₂[Γ̃(M')]ψ` is
`S_V`-stable, hence all of `W` by `invariant_eq_bot_or_top_of_card`, and `𝔽₂[Γ̃(M')]` acts on
`⟨ψ', ·⟩` by scalars. `Ann(M_P) = ⟨φ(P)⟩` then follows from Theorem 2, not from Lemma 1.1 of
`results/zero-span-extend.md`. Not formalized: the count `∏(2^i + 1)`, the dual polar distance
clause of Theorem 1.1.5, the affine-cube generator `M_(A,R)` of Theorem 1.1.4, and the `s mod 4`
remark.

### New

| name | statement | location |
|---|---|---|
| `PM.dotForm`, `PM.dotForm_nondegenerate`, `PM.IsSelfOrth`, `PM.IsSelfDual` | codes `C ≤ 𝔽₂^V`, `C^⊥` | `clifford/Clifford/SelfDualCode.lean` |
| `PM.IsSelfDual.le_U`, `PM.IsSelfDual.one_mem`, `PM.IsSelfDual.finrank_eq` | spinor-codes Theorem 1.1.1, `dim C = n` | `clifford/Clifford/SelfDualCode.lean` |
| `PM.pairCode`, `PM.isSelfDual_pairCode`, `PM.span_v_mate` | `i₂(P)` is self-dual and spanned by the `v_e`, `e ∈ P` | `clifford/Clifford/SelfDualCode.lean` |
| `PM.qE`, `PM.polar_qE`, `PM.epsE`, `PM.kE`, `PM.IsTotSing`, `PM.finrank_U`, `PM.mem_span_kE_of_polar` | `U ⊕ 𝔽₂ε` and `q̃`; `Ũ_n` is nondegenerate of dimension `2n - 1` | `clifford/Clifford/SelfDualCode.lean` |
| `PM.liftCode`, `PM.codeOf`, `PM.finrank_le_of_isTotSing`, `PM.kE_mem_of_maximal`, `PM.maximal_isTotSing_iff` | `M_C`; Witt index `n - 1` | `clifford/Clifford/SelfDualCode.lean` |
| `PM.selfDualEquiv`, `PM.maximal_liftCode_pairCode` | spinor-codes Theorem 1.1.2; `M_P` is maximal | `clifford/Clifford/SelfDualCode.lean` |
| `PM.finrank_liftCode_inf`, `PM.liftCode_inf_le_span_kE_iff`, `PM.sup_eq_U_of_inf_le` | `dim(M_C ∩ M_C') = dim(C ∩ C')` here, opposition in code form | `clifford/Clifford/SelfDualCode.lean` |
| `PM.gammaE`, `PM.gammaE_mul_self`, `PM.gammaE_anticomm`, `PM.gammaE_indep`, `PM.cliffordRepE` | `Γ̃(x + λε) = Γ(x) + λI` is a Clifford map | `clifford/Clifford/PureSpinor.lean` |
| `PM.map_even_cliffordRepE`, `PM.cliffordRepE_surjective` | the even Clifford algebra maps onto `End(W)` | `clifford/Clifford/PureSpinor.lean` |
| `PM.gammaE_kE`, `PM.gammaL_one` | `Γ̃(𝟙 + nε) = 0`; `Γ(𝟙) = nI` for any `V` | `clifford/Clifford/PureSpinor.lean` |
| `PM.annE`, `PM.nullE`, `PM.IsPureSpinor`, `PM.isTotSing_nullE`, `PM.finrank_nullE_le` | `Ann(M)`, `N′(v)`, pure spinors; `N′(v)` is totally singular | `clifford/Clifford/PureSpinor.lean` |
| `PM.fpForm_gammaE_left`, `PM.rowW_mem_annE`, `PM.annE_ne_bot` | `Γ̃(z)` is self-adjoint; `φ(P) ∈ Ann(M_P)`; `Ann(M) ≠ 0` | `clifford/Clifford/PureSpinor.lean` |
| `PM.fpForm_eq_zero_of_mem_inf`, `PM.eq_zero_of_fpForm_eq_zero` | the two cases of Theorem 2 | `clifford/Clifford/PureSpinor.lean` |
| `PM.finrank_annE`, `PM.psiE`, `PM.eq_psiE`, `PM.annE_eq_span_psiE`, `PM.fpForm_psiE_eq_one_iff` | Theorem 2: `Ann(M) = ⟨ψ_M⟩`, `⟨ψ_M, ψ_M'⟩ = 1` iff `M ∩ M' = 0` | `clifford/Clifford/PureSpinor.lean` |
| `PM.nullE_psiE`, `PM.isPureSpinor_iff`, `PM.annE_liftCode_pairCode`, `PM.nullE_rowW`, `PM.isPureSpinor_rowW` | Theorem 1 parts 3 and 4 | `clifford/Clifford/PureSpinor.lean` |
| `PM.annE_liftCode_pairCode_eq_matchingStar`, `PM.matchingStar_edgeSet_eq_span`, `PM.finrank_matchingStar_edgeSet` | `L_P = ⟨φ(P)⟩` for every `P` and `V` | `clifford/Clifford/PureSpinor.lean` |
| `PM.psiCode`, `PM.pureSpinorEquiv`, `PM.psiCode_pairCode`, `PM.fpForm_psiCode_eq_one_iff` | spinor-codes Theorem 1.1 parts 3, 4 and 6 | `clifford/Clifford/PureSpinor.lean` |
| `PM.psiCode_apply_eq_one_iff`, `PM.psiCode_mem_orthogonal_fpSpan_iff` | spinor-codes Corollary 1.2 and its survivor form | `clifford/Clifford/PureSpinor.lean` |

### AxiomCheck

284 endpoints, 279 on `[propext, Classical.choice, Quot.sound]` and 5 on fewer axioms. The 50 new
ones are `dotForm_nondegenerate`, `IsSelfDual.le_U`, `IsSelfDual.one_mem`, `IsSelfDual.finrank_eq`,
`isSelfDual_pairCode`, `finrank_U`, `sup_eq_U_of_inf_le`, `polar_qE`, `qE_epsE`, `polar_epsE`,
`mem_span_kE_of_polar`, `finrank_le_of_isTotSing`, `kE_mem_of_maximal`, `maximal_isTotSing_iff`,
`selfDualEquiv`, `maximal_liftCode_pairCode`, `finrank_liftCode_inf`,
`liftCode_inf_le_span_kE_iff`, `gammaE_mul_self`, `gammaE_anticomm`, `gammaE_indep`,
`cliffordRepE`, `cliffordRepE_ι`, `map_even_cliffordRepE`, `cliffordRepE_surjective`,
`fpForm_gammaE_left`, `gammaE_kE`, `gammaL_one`, `rowW_mem_annE`, `isTotSing_nullE`,
`finrank_nullE_le`, `annE_ne_bot`, `fpForm_eq_zero_of_mem_inf`, `eq_zero_of_fpForm_eq_zero`,
`finrank_annE`, `annE_eq_span_psiE`, `fpForm_psiE_eq_one_iff`, `nullE_psiE`, `isPureSpinor_iff`,
`annE_liftCode_pairCode`, `nullE_rowW`, `isPureSpinor_rowW`,
`annE_liftCode_pairCode_eq_matchingStar`, `matchingStar_edgeSet_eq_span`,
`finrank_matchingStar_edgeSet`, `pureSpinorEquiv`, `psiCode_pairCode`,
`fpForm_psiCode_eq_one_iff`, `psiCode_apply_eq_one_iff` and `psiCode_mem_orthogonal_fpSpan_iff`.
None was removed.

## Cameron's theorem for abelian groups of odd order (COD-299, branch `spin-audit`)

From cfe1b55. Lemma 1, Lemma 2(b) and Theorem 3 of `results/audit-manuscript-extend.md` §4.1
(organize-archive 313d6ea). `GK(A)` is built for every finite additive commutative group `A` of odd
order, on `Option A` with `none = ∞`, in the new module `Pairing.AbelianAutomorphism`
(`core/Pairing/AbelianAutomorphism.lean`), namespace `GK`. Oddness is the instance
`Fact (Odd (Nat.card A))`. The `ℤ/n` development of `Pairing.Automorphism` is unchanged, and
`GK.factor_zmod` identifies the two families at `A = ℤ/(2m - 1)`.

The non-mediality witness is the corrected Lemma 2(b) of the source, not the audit's computation:
for `a ≠ 0` and `b ∉ {0, a, -a, a/2, 2a}` the two sides are `a + 2b` and `3a + b`.

### New

| name | statement | location |
|---|---|---|
| `GK.twoEquiv`, `GK.half` and their lemmas | `x ↦ 2x` as an additive automorphism of `A`, and its inverse | `core/Pairing/AbelianAutomorphism.lean` |
| `GK.mateFn`, `GK.factor`, `GK.factor_injective` | `F_c` pairs `∞` with `c` and `x ≠ c` with `2c - x` | `core/Pairing/AbelianAutomorphism.lean` |
| `GK.IsAut`, `GK.autGroup`, `GK.IsAut.exists_perm`, `GK.mate_smul_eq` | the automorphisms of `GK(A)` | `core/Pairing/AbelianAutomorphism.lean` |
| `GK.affPerm`, `GK.affPerm_smul_factor`, `GK.isAut_affPerm`, `GK.affPerm_inj` | `x ↦ α x + b` sends `F_c` to `F_(α c + b)` and determines `(α, b)` | `core/Pairing/AbelianAutomorphism.lean` |
| `GK.edgeLabel`, `GK.localSq`, `GK.localSq_smul` | the operation `∘_v`, carried to `∘_(σ v)` by an automorphism | `core/Pairing/AbelianAutomorphism.lean` |
| `GK.localSq_none`, `GK.isMedial_localSq_none` | Lemma 1(1), `c ∘_∞ d = (c + d)/2` is medial | `core/Pairing/AbelianAutomorphism.lean` |
| `GK.localSq_zero`, `GK.localSq_zero_left`, `GK.localSq_zero_right` | Lemma 1(2) and 1(3), `c ∘₀ d = c + d` and `0 ∘₀ d = d ∘₀ 0 = 2d` | `core/Pairing/AbelianAutomorphism.lean` |
| `GK.not_isMedial_localSq_zero` | Lemma 2(b), `∘₀` is not medial for `|A| ≥ 7` | `core/Pairing/AbelianAutomorphism.lean` |
| `GK.IsAut.apply_none`, `GK.IsAut.exists_affPerm`, `GK.isAut_iff` | Theorem 3, `Aut(GK(A)) = {x ↦ α x + b}` for `|A| ≥ 7` | `core/Pairing/AbelianAutomorphism.lean` |
| `GK.autEquiv`, `GK.card_autGroup` | `Aut(A) × A ≃ Aut(GK(A))` and `|Aut(GK(A))| = |A| |Aut(A)|` | `core/Pairing/AbelianAutomorphism.lean` |
| `GK.affinePerm`, `GK.range_affinePerm`, `GK.autGroupMulEquiv` | `Hol(A) = (A ≃ᵃ[ℤ] A) ≃* Aut(GK(A))` for `|A| ≥ 7` | `core/Pairing/AbelianAutomorphism.lean` |
| `GK.fact_odd_card_zmod`, `GK.factor_zmod`, `GK.isAut_zmod_iff` | at `A = ℤ/(2m - 1)`, `GK(A)` is the round-robin family | `core/Pairing/AbelianAutomorphism.lean` |

`core/Pairing.lean` imports the new module.

### AxiomCheck

284 endpoints at cfe1b55, 306 after. The 22 new ones are the `GK.*` lines at the end of
`AxiomCheck.lean`. 300 endpoints are on `[propext, Classical.choice, Quot.sound]` and 6 on fewer
(`GK.affPerm_inj` is on `[propext, Quot.sound]`). None was removed.
