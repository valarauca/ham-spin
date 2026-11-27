import Clifford.BasisFree
import Clifford.EdgeRelations
import Pairing.RoundRobin
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Basic.Real.Basic

/-!
# Zero states as a polar section (COD-259)

Let `F : ι → 𝓜(V)` be any family of perfect matchings. `P` is a zero state for `F`
(`IsZeroState`, ham-spin 0360f0d) when no `P ∪ F_t` is one cycle. This file reads that condition
in the CKN fingerprint module `W V` (`W`, `rowW`, ham-spin 0360f0d), where `φ(P) = r_P`.

Source: archive Proposition 14.1 ("Hamiltonian Matching Modular Spin-Web Checkpoint" §14, splitter
`old-personal-chatgpt` doc 01a1e1b7-1d50-770b-bb1e-667b6b2bd4d3), stated there for the round-robin
family. Here it is proved for every family, and the round-robin case is a corollary.

* `hamFormRad` : the Hamiltonicity form `B` (`hamForm`, ham-spin 0360f0d) on `𝔽₂^𝓜 ⧸ rad B`.
  `fpForm` : the same form on `W V`, carried along `quotRadEquiv` (ham-spin 0360f0d), with
  `fpForm_rowW : ⟨r_P, r_Q⟩ = H[P, Q]` and `fpForm_rowW_right : ⟨f, r_Q⟩ = f(Q)`.
  `fpForm_nondegenerate`, `fpForm_comm`, `fpForm_ρW` : it is nondegenerate, symmetric and
  `S_V`-invariant.
* `fpSpan F = R(F) = span{φ(F_t)}`. `isZeroState_iff_rowW_mem_orthogonal` : `P` is a zero state iff
  `φ(P) ∈ R(F)^⊥` (Proposition 14.1). `image_rowW_zeroStates` : `φ(Z(F)) = Φ ∩ R(F)^⊥` with
  `Φ = range φ`. `isZeroState_iff_mk_mem_orthogonal_rad` : the same in the basis-free model.
* `fpSpan_smul`, `orthogonal_fpSpan_smul` : `R(σ F) = σ R(F)` and `R(σ F)^⊥ = σ R(F)^⊥`.
  `fpSpanStab F` : the permutations preserving `R(F)`. `isZeroState_smul_iff_of_mem_fpSpanStab` :
  they preserve the zero set. `mem_fpSpanStab_of_perm` : a permutation that permutes the factors
  lies in `fpSpanStab F`.
* `zeroStates_eq_iUnion_orbit` : the zero set is a union of orbits of any subgroup of
  `fpSpanStab F`, and `card_zeroStates_eq_sum_card_orbit` : `|Z(F)|` is the sum of the orbit sizes.
  `card_zeroStates_eq_card_orthogonal` : `|Z(F)| = |{P : φ(P) ∈ R(F)^⊥}|`, so the zero-state
  density is `q = |{P : φ(P) ∈ R^⊥}| / |𝓜|` (`zeroDensity_eq`).
* `edgeStar e = L_e = ker(1 + Γ_e)` and `matchingStar E = L_E = ⋂_{e ∈ E} L_e`.
  `rowW_mem_edgeStar_iff` : `φ(P) ∈ L_e` iff `e ∈ P`. `rowW_injective` : `φ` is injective.
  `isZeroState_and_subset_iff` : the zero states containing `E` are the orbit points in
  `R(F)^⊥ ∩ L_E`.
* `RoundRobin.Canonical` : `rrSpan m = R_rr`, the round-robin corollaries, and
  `zeroCount_eq_card_orthogonal` : `Z_m = |{P : φ(P) ∈ R_rr^⊥}|`.
-/

namespace Pairing.PerfectMatching

open Equiv

variable {V : Type*} [Fintype V] [DecidableEq V]

section Form

/-- The Hamiltonicity form `B` (`hamForm`, ham-spin 0360f0d) descended to `𝔽₂^𝓜 ⧸ rad B`. -/
def hamFormRad :
    LinearMap.BilinForm F₂ ((PerfectMatching V → F₂) ⧸ LinearMap.ker (hamForm (V := V))) :=
  hamForm.liftQ₂ _ _ le_rfl fun x hx ↦ LinearMap.mem_ker.mpr (LinearMap.ext fun y ↦ by
    rw [LinearMap.flip_apply, hamForm_comm, LinearMap.mem_ker.mp hx])

/-- `hamFormRad [x] [y] = B(x, y)`, for `hamForm` at ham-spin 0360f0d. -/
theorem hamFormRad_mk (x y : PerfectMatching V → F₂) :
    hamFormRad (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = hamForm x y :=
  rfl

/-- The fingerprint pairing on the CKN module `W V`, transported from `hamFormRad` along
`quotRadEquiv` (ham-spin 0360f0d). It is the nondegenerate form of archive Proposition 14.1
(`old-personal-chatgpt` doc 01a1e1b7-1d50-770b-bb1e-667b6b2bd4d3). -/
noncomputable def fpForm : LinearMap.BilinForm F₂ (W V) :=
  hamFormRad.compl₁₂ (quotRadEquiv (V := V)).symm.toLinearMap quotRadEquiv.symm.toLinearMap

/-- `quotRadEquiv` (ham-spin 0360f0d) is an isometry from `hamFormRad` to `fpForm`. -/
theorem fpForm_quotRadEquiv (x y : (PerfectMatching V → F₂) ⧸ LinearMap.ker (hamForm (V := V))) :
    fpForm (quotRadEquiv x) (quotRadEquiv y) = hamFormRad x y := by
  simp [fpForm]

/-- `⟨φ(P), φ(Q)⟩ = H[P, Q]`, for the fingerprints `rowW` and the CKN matrix `H`
(ham-spin 0360f0d). -/
theorem fpForm_rowW (P Q : PerfectMatching V) : fpForm (rowW P) (rowW Q) = H P Q := by
  rw [← quotRadEquiv_single, ← quotRadEquiv_single, fpForm_quotRadEquiv, hamFormRad_mk,
    hamForm_single, H_apply]

/-- Pairing with a fingerprint evaluates, `⟨f, φ(Q)⟩ = f(Q)` for `f ∈ W V` (`rowW`, ham-spin
0360f0d). -/
theorem fpForm_rowW_right (f : W V) (Q : PerfectMatching V) :
    fpForm f (rowW Q) = (f : PerfectMatching V → F₂) Q := by
  obtain ⟨x, rfl⟩ := quotRadEquiv.surjective f
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← quotRadEquiv_single, fpForm_quotRadEquiv, hamFormRad_mk, hamForm_apply,
    coe_quotRadEquiv_mk, dotProduct_single, mul_one]

/-- The fingerprint pairing is symmetric, as `hamForm` is (`hamForm_comm`, ham-spin 0360f0d). -/
theorem fpForm_comm (f g : W V) : fpForm f g = fpForm g f := by
  obtain ⟨x, rfl⟩ := quotRadEquiv.surjective f
  obtain ⟨y, rfl⟩ := quotRadEquiv.surjective g
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [fpForm_quotRadEquiv, fpForm_quotRadEquiv, hamFormRad_mk, hamFormRad_mk, hamForm_comm]

/-- The fingerprint pairing on `W V` (`W`, ham-spin 0360f0d) is nondegenerate: `f` pairs to zero
with every `φ(Q)` only if `f = 0`. -/
theorem fpForm_nondegenerate : (fpForm (V := V)).Nondegenerate := by
  have hR : LinearMap.SeparatingRight (fpForm (V := V)) := by
    intro g hg
    apply Subtype.ext
    funext Q
    rw [← fpForm_rowW_right, fpForm_comm, hg]
    rfl
  exact ⟨fun f hf ↦ hR f fun x ↦ (fpForm_comm x f).trans (hf x), hR⟩

/-- The fingerprint pairing is `S_V`-invariant under `ρW` (ham-spin 0360f0d). -/
theorem fpForm_ρW (σ : Perm V) (f g : W V) : fpForm (ρW σ f) (ρW σ g) = fpForm f g := by
  have h : (fpForm (ρW σ f)).comp (ρW σ) = fpForm f := by
    refine LinearMap.ext_on_range span_rowW fun Q ↦ ?_
    rw [LinearMap.comp_apply, ρW_rowW, fpForm_rowW_right, fpForm_rowW_right, ρW_apply_coe,
      ρ_apply, inv_smul_smul]
  exact LinearMap.congr_fun h g

end Form

section Polar

variable {ι : Type*}

private theorem mem_orthogonal_span_range_iff {M : Type*} [AddCommGroup M] [Module F₂ M]
    (B : LinearMap.BilinForm F₂ M) (v : ι → M) (x : M) :
    x ∈ B.orthogonal (Submodule.span F₂ (Set.range v)) ↔ ∀ t, B (v t) x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  refine ⟨fun h t ↦ h _ (Submodule.subset_span ⟨t, rfl⟩), fun h y hy ↦ ?_⟩
  have hle : Submodule.span F₂ (Set.range v) ≤ LinearMap.ker (B.flip x) := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact LinearMap.mem_ker.mpr (h t)
  exact LinearMap.mem_ker.mp (hle hy)

private theorem ite_ham_eq_zero_iff (P Q : PerfectMatching V) :
    (if Ham Q P then (1 : F₂) else 0) = 0 ↔ ¬Ham P Q := by
  by_cases h : Ham P Q
  · simp [h, (ham_comm P Q).1 h]
  · have h' : ¬Ham Q P := fun h' ↦ h ((ham_comm Q P).1 h')
    simp [h, h']

/-- The fingerprint span `R(F) = span{φ(F_t)}` of a family of matchings, in the CKN module `W V`
(`rowW`, ham-spin 0360f0d). For the round-robin family it is `R_rr` of archive Proposition 14.1. -/
def fpSpan (F : ι → PerfectMatching V) : Submodule F₂ (W V) :=
  Submodule.span F₂ (Set.range fun t ↦ rowW (F t))

/-- `R(F)^⊥` is the set of `f ∈ W V` vanishing at every `F_t` (`W`, ham-spin 0360f0d). -/
theorem mem_orthogonal_fpSpan_iff (F : ι → PerfectMatching V) (f : W V) :
    f ∈ fpForm.orthogonal (fpSpan F) ↔ ∀ t, (f : PerfectMatching V → F₂) (F t) = 0 := by
  rw [fpSpan, mem_orthogonal_span_range_iff]
  exact forall_congr' fun t ↦ by rw [fpForm_comm, fpForm_rowW_right]

/-- Polar section, archive Proposition 14.1 (`old-personal-chatgpt` doc
01a1e1b7-1d50-770b-bb1e-667b6b2bd4d3, §14), for any family `F`: `P` is a zero state
(`IsZeroState`, ham-spin 0360f0d) iff `φ(P) ∈ R(F)^⊥` under the fingerprint pairing. -/
theorem isZeroState_iff_rowW_mem_orthogonal (F : ι → PerfectMatching V) (P : PerfectMatching V) :
    IsZeroState F P ↔ rowW P ∈ fpForm.orthogonal (fpSpan F) := by
  rw [fpSpan, mem_orthogonal_span_range_iff]
  exact forall_congr' fun t ↦ by rw [fpForm_rowW, H_apply, ite_ham_eq_zero_iff]

/-- Archive Proposition 14.1 in image form (`old-personal-chatgpt` doc
01a1e1b7-1d50-770b-bb1e-667b6b2bd4d3): `φ(Z(F)) = Φ ∩ R(F)^⊥`, where `Φ` is the set of
fingerprints `rowW` (ham-spin 0360f0d). -/
theorem image_rowW_zeroStates (F : ι → PerfectMatching V) :
    rowW '' {P | IsZeroState F P} =
      Set.range rowW ∩ (fpForm.orthogonal (fpSpan F) : Set (W V)) := by
  ext f
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨⟨P, rfl⟩, (isZeroState_iff_rowW_mem_orthogonal F P).1 hP⟩
  · rintro ⟨⟨P, rfl⟩, hf⟩
    exact ⟨P, (isZeroState_iff_rowW_mem_orthogonal F P).2 hf, rfl⟩

/-- `R(F)` in the basis-free model, `span{[F_t]}` in `𝔽₂^𝓜 ⧸ rad B` (`hamForm`, ham-spin
0360f0d). -/
def radSpan (F : ι → PerfectMatching V) :
    Submodule F₂ ((PerfectMatching V → F₂) ⧸ LinearMap.ker (hamForm (V := V))) :=
  Submodule.span F₂ (Set.range fun t ↦ Submodule.Quotient.mk (Pi.single (F t) 1))

/-- `quotRadEquiv` (ham-spin 0360f0d) carries the basis-free span `radSpan F` onto `R(F)`. -/
theorem map_quotRadEquiv_radSpan (F : ι → PerfectMatching V) :
    (radSpan F).map (quotRadEquiv (V := V) : _ →ₗ[F₂] W V) = fpSpan F := by
  rw [radSpan, Submodule.map_span, ← Set.range_comp]
  exact congrArg _ (congrArg Set.range (funext fun t ↦ quotRadEquiv_single (F t)))

/-- Archive Proposition 14.1 (`old-personal-chatgpt` doc 01a1e1b7-1d50-770b-bb1e-667b6b2bd4d3) in
the basis-free model: `P` is a zero state iff its class lies in `radSpan F ^⊥` for the Hamiltonicity
form on `𝔽₂^𝓜 ⧸ rad B` (`hamForm`, `IsZeroState`, ham-spin 0360f0d). -/
theorem isZeroState_iff_mk_mem_orthogonal_rad (F : ι → PerfectMatching V) (P : PerfectMatching V) :
    IsZeroState F P ↔
      Submodule.Quotient.mk (Pi.single P 1) ∈ hamFormRad.orthogonal (radSpan F) := by
  rw [radSpan, mem_orthogonal_span_range_iff]
  exact forall_congr' fun t ↦ by rw [hamFormRad_mk, hamForm_single, ite_ham_eq_zero_iff]

/-- `dim R(F) ≤ |ι|` for the fingerprint span in `W V` (`W`, ham-spin 0360f0d). -/
theorem finrank_fpSpan_le [Fintype ι] (F : ι → PerfectMatching V) :
    Module.finrank F₂ (fpSpan F) ≤ Fintype.card ι :=
  finrank_range_le_card _

/-- `dim R(F) + dim R(F)^⊥ = 2^(n-1)` for `|V| = 2n ≥ 2`, as the fingerprint pairing is
nondegenerate on `W V` of dimension `2^(n-1)` (`finrank_W_eq_of_card`, ham-spin 0360f0d). -/
theorem finrank_fpSpan_add_finrank_orthogonal (F : ι → PerfectMatching V) {n : ℕ}
    (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) :
    Module.finrank F₂ (fpSpan F) + Module.finrank F₂ (fpForm.orthogonal (fpSpan F)) =
      2 ^ (n - 1) := by
  have hker : LinearMap.ker (fpForm (V := V)) = ⊥ :=
    LinearMap.ker_eq_bot'.mpr fun f hf ↦ fpForm_nondegenerate.1 f fun g ↦ LinearMap.congr_fun hf g
  rw [LinearMap.BilinForm.finrank_add_finrank_orthogonal', finrank_W_eq_of_card hV hn, hker,
    inf_bot_eq, finrank_bot, add_zero]

end Polar

section Equivariance

variable {ι : Type*}

private theorem map_ρW_eq_comap (σ : Perm V) (N : Submodule F₂ (W V)) :
    N.map (ρW σ) = N.comap (ρW σ⁻¹) := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [Submodule.mem_comap, Representation.inv_self_apply]
    exact hg
  · intro hf
    exact ⟨ρW σ⁻¹ f, hf, Representation.self_inv_apply _ _ _⟩

/-- `R(σ F) = σ R(F)` under `ρW` (ham-spin 0360f0d), since `ρW σ φ(P) = φ(σ P)`. -/
theorem fpSpan_smul (σ : Perm V) (F : ι → PerfectMatching V) :
    fpSpan (fun t ↦ σ • F t) = (fpSpan F).map (ρW σ) := by
  rw [fpSpan, fpSpan, Submodule.map_span, ← Set.range_comp]
  exact congrArg _ (congrArg Set.range (funext fun t ↦ (ρW_rowW σ (F t)).symm))

/-- `R(σ F)^⊥ = σ R(F)^⊥` under `ρW` (ham-spin 0360f0d), so the zero set is `S_V`-equivariant. -/
theorem orthogonal_fpSpan_smul (σ : Perm V) (F : ι → PerfectMatching V) :
    fpForm.orthogonal (fpSpan fun t ↦ σ • F t) = (fpForm.orthogonal (fpSpan F)).map (ρW σ) := by
  rw [map_ρW_eq_comap]
  ext f
  rw [Submodule.mem_comap, mem_orthogonal_fpSpan_iff, mem_orthogonal_fpSpan_iff]
  exact forall_congr' fun t ↦ by rw [ρW_apply_coe, ρ_apply, inv_inv]

/-- The permutations whose action `ρW` (ham-spin 0360f0d) preserves `R(F)`. For the round-robin
family it contains `Aut(𝓕) ≅ AGL(1, ℤ/n)` (`RoundRobin.Canonical.autGroup`, ham_pairings main
81fccb6), by `mem_fpSpanStab_of_perm`. -/
def fpSpanStab (F : ι → PerfectMatching V) : Subgroup (Perm V) where
  carrier := {σ | (fpSpan F).map (ρW σ) = fpSpan F}
  mul_mem' {σ τ} hσ hτ := by
    change (fpSpan F).map (ρW (σ * τ)) = fpSpan F
    rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp, hτ, hσ]
  one_mem' := by
    change (fpSpan F).map (ρW 1) = fpSpan F
    rw [map_one]
    exact Submodule.map_id _
  inv_mem' {σ} hσ := by
    change (fpSpan F).map (ρW σ⁻¹) = fpSpan F
    change (fpSpan F).map (ρW σ) = fpSpan F at hσ
    conv_lhs => rw [← hσ, ← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul,
      inv_mul_cancel, map_one]
    exact Submodule.map_id _

/-- Membership in `fpSpanStab F` is `σ R(F) = R(F)` under `ρW` (ham-spin 0360f0d). -/
theorem mem_fpSpanStab {F : ι → PerfectMatching V} {σ : Perm V} :
    σ ∈ fpSpanStab F ↔ (fpSpan F).map (ρW σ) = fpSpan F :=
  Iff.rfl

/-- A permutation that permutes the members of `F`, `σ • F_t = F_{π t}`, preserves `R(F)`. For
the round-robin family `π` comes from `RoundRobin.Canonical.IsAut.exists_perm` (ham_pairings main
81fccb6). -/
theorem mem_fpSpanStab_of_perm {F : ι → PerfectMatching V} {σ : Perm V} (π : ι ≃ ι)
    (h : ∀ t, σ • F t = F (π t)) : σ ∈ fpSpanStab F := by
  rw [mem_fpSpanStab, ← fpSpan_smul, fpSpan, fpSpan]
  simp only [h]
  exact congrArg _ (π.surjective.range_comp fun t ↦ rowW (F t))

/-- Every `σ` preserving `R(F)` preserves `R(F)^⊥`, under `ρW` (ham-spin 0360f0d). -/
theorem map_orthogonal_of_mem_fpSpanStab {F : ι → PerfectMatching V} {σ : Perm V}
    (hσ : σ ∈ fpSpanStab F) :
    (fpForm.orthogonal (fpSpan F)).map (ρW σ) = fpForm.orthogonal (fpSpan F) := by
  rw [← orthogonal_fpSpan_smul, fpSpan_smul, hσ]

/-- Every `σ` preserving `R(F)` preserves the zero set (`IsZeroState`, ham-spin 0360f0d). This is
the spin form of the equivariance in archive Proposition 14.1. -/
theorem isZeroState_smul_iff_of_mem_fpSpanStab {F : ι → PerfectMatching V} {σ : Perm V}
    (hσ : σ ∈ fpSpanStab F) (P : PerfectMatching V) :
    IsZeroState F (σ • P) ↔ IsZeroState F P := by
  have hO := map_orthogonal_of_mem_fpSpanStab hσ
  rw [map_ρW_eq_comap] at hO
  rw [isZeroState_iff_rowW_mem_orthogonal, isZeroState_iff_rowW_mem_orthogonal, ← ρW_rowW]
  conv_lhs => rw [← hO]
  rw [Submodule.mem_comap, Representation.inv_self_apply]

omit [Fintype V] [DecidableEq V] in
/-- A permutation that permutes the members of `F` preserves the zero set (`IsZeroState`,
`ham_smul`, ham-spin 0360f0d). For finite `V` this is also `isZeroState_smul_iff_of_mem_fpSpanStab`
applied to `mem_fpSpanStab_of_perm`. -/
theorem isZeroState_smul_iff_of_perm {F : ι → PerfectMatching V} {σ : Perm V} (π : ι ≃ ι)
    (h : ∀ t, σ • F t = F (π t)) (P : PerfectMatching V) :
    IsZeroState F (σ • P) ↔ IsZeroState F P := by
  refine ⟨fun hP t ht ↦ hP (π t) ?_, fun hP t ht ↦ hP (π.symm t) ?_⟩
  · rwa [← h, ham_smul]
  · rwa [← ham_smul σ, h, π.apply_symm_apply]

end Equivariance

section Orbits

variable {ι : Type*}

/-- The zero set (`IsZeroState`, ham-spin 0360f0d) is a union of orbits of any group `G` that
preserves `R(F)`. -/
theorem zeroStates_eq_iUnion_orbit {F : ι → PerfectMatching V} {G : Subgroup (Perm V)}
    (hG : G ≤ fpSpanStab F) :
    {P | IsZeroState F P} = ⋃ P ∈ {P | IsZeroState F P}, MulAction.orbit G P := by
  ext Q
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  refine ⟨fun hQ ↦ ⟨Q, hQ, MulAction.mem_orbit_self Q⟩, ?_⟩
  rintro ⟨P, hP, g, rfl⟩
  exact (isZeroState_smul_iff_of_mem_fpSpanStab (hG g.2) P).2 hP

/-- A group `G` preserving `R(F)` acts on the zero states (`IsZeroState`, ham-spin 0360f0d). -/
instance zeroStateAction (F : ι → PerfectMatching V) :
    MulAction (fpSpanStab F) {P // IsZeroState F P} where
  smul g P := ⟨(g : Perm V) • P.1, (isZeroState_smul_iff_of_mem_fpSpanStab g.2 P.1).2 P.2⟩
  one_smul P := Subtype.ext (one_smul _ P.1)
  mul_smul g h P := Subtype.ext (mul_smul (g : Perm V) (h : Perm V) P.1)

/-- The action of `fpSpanStab F` on zero states is the action on matchings (`IsZeroState`, ham-spin
0360f0d). -/
@[simp]
theorem coe_zeroState_smul {F : ι → PerfectMatching V} (g : fpSpanStab F)
    (P : {P // IsZeroState F P}) : ((g • P : {P // IsZeroState F P}) : PerfectMatching V) =
      (g : Perm V) • (P : PerfectMatching V) :=
  rfl

/-- Orbit decomposition: the number of zero states (`IsZeroState`, ham-spin 0360f0d) is the sum,
over the orbits of the stabilizer of `R(F)` on the zero set, of their sizes. -/
theorem card_zeroStates_eq_sum_card_orbit (F : ι → PerfectMatching V) :
    Nat.card {P // IsZeroState F P} =
      ∑ᶠ ω : MulAction.orbitRel.Quotient (fpSpanStab F) {P // IsZeroState F P},
        Nat.card (MulAction.orbit (fpSpanStab F) ω.out) := by
  classical
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits (fpSpanStab F) {P // IsZeroState F P}),
    Nat.card_sigma, finsum_eq_sum_of_fintype]

/-- The zero states (`IsZeroState`, ham-spin 0360f0d) are counted in spin form,
`|Z(F)| = |{P : φ(P) ∈ R(F)^⊥}|`. -/
theorem card_zeroStates_eq_card_orthogonal (F : ι → PerfectMatching V) :
    Nat.card {P // IsZeroState F P} =
      Nat.card {P : PerfectMatching V // rowW P ∈ fpForm.orthogonal (fpSpan F)} :=
  Nat.card_congr (Equiv.subtypeEquivRight (isZeroState_iff_rowW_mem_orthogonal F))

/-- The zero-state density in spin form: for `|V| = 2n`,
`q = |{P : φ(P) ∈ R(F)^⊥}| / (2n - 1)!!` (`card_eq_doubleFactorial`, ham-spin 0360f0d). -/
theorem zeroDensity_eq (F : ι → PerfectMatching V) {n : ℕ} (hV : Fintype.card V = 2 * n) :
    (Nat.card {P // IsZeroState F P} : ℝ) / Nat.card (PerfectMatching V) =
      (Nat.card {P : PerfectMatching V // rowW P ∈ fpForm.orthogonal (fpSpan F)} : ℝ) /
        Nat.doubleFactorial (2 * n - 1) := by
  rw [card_zeroStates_eq_card_orthogonal, Nat.card_eq_fintype_card (α := PerfectMatching V),
    card_eq_doubleFactorial hV]

end Orbits

section Star

private theorem add_self_W (x : W V) : x + x = 0 := by
  rw [← two_smul F₂ x, show (2 : F₂) = 0 by decide, zero_smul]

/-- The edge-star space `L_e = ker(1 + Γ_e)` of an edge `e = ij`, the vectors of `W V` fixed by
`Γ_{ij} = ρW((i j))` (`Γ`, ham-spin 0360f0d). Archive Theorem 7.2 (`old-personal-chatgpt` doc
01a1e1b7-1d50-770b-bb1e-667b6b2bd4d3). -/
def edgeStar (e : Sym2 V) : Submodule F₂ (W V) :=
  Sym2.lift ⟨fun i j ↦ LinearMap.ker (1 + Γ i j), fun i j ↦ by dsimp only; rw [Γ_comm]⟩ e

/-- `L_{ij} = ker(1 + Γ_{ij})`, for `Γ` at ham-spin 0360f0d. -/
@[simp]
theorem edgeStar_mk (i j : V) : edgeStar s(i, j) = LinearMap.ker (1 + Γ i j) :=
  rfl

/-- `x ∈ L_{ij}` iff `Γ_{ij} x = x`, for `Γ` at ham-spin 0360f0d. -/
theorem mem_edgeStar_mk {i j : V} {x : W V} : x ∈ edgeStar s(i, j) ↔ Γ i j x = x := by
  rw [edgeStar_mk, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply]
  constructor
  · intro h
    calc Γ i j x = (x + Γ i j x) + x := by rw [add_comm x, add_assoc, add_self_W, add_zero]
      _ = x := by rw [h, zero_add]
  · intro h
    rw [h, add_self_W]

/-- Fingerprints are nonzero: `φ(P) ≠ 0` when `|V| = 2n ≥ 2`, since the `S_V`-orbit of `φ(P)`
spans `W V` and `dim W V = 2^(n-1)` (`finrank_W_eq_of_card`, `span_rowW`, ham-spin 0360f0d). -/
theorem rowW_ne_zero {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (P : PerfectMatching V) :
    rowW P ≠ 0 := by
  intro h0
  have htop : (⊤ : Submodule F₂ (W V)) = ⊥ := by
    rw [← span_rowW, Submodule.span_eq_bot]
    rintro _ ⟨Q, rfl⟩
    obtain ⟨σ, rfl⟩ := exists_smul_eq hV P Q
    rw [← ρW_rowW, h0, map_zero]
  have hfin := finrank_W_eq_of_card hV hn
  rw [← finrank_top, htop, finrank_bot] at hfin
  exact (pow_pos two_pos _).ne hfin

/-- `φ(P) ∈ L_{ij}` iff `ij` is an edge of `P`, for `i ≠ j` and `|V| = 2n ≥ 2`. The reverse
direction uses the anticommutation `{Γ_{ij}, Γ_{ik}} = 1` of adjacent edges
(`Γ_anticomm_of_adj`, ham-spin 0360f0d) and `rowW_ne_zero`. -/
theorem rowW_mem_edgeStar_mk_iff {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n)
    (P : PerfectMatching V) {i j : V} (hij : i ≠ j) :
    rowW P ∈ edgeStar s(i, j) ↔ P.mate i = j := by
  have hfix : ∀ {a b : V}, P.mate a = b → Γ a b (rowW P) = rowW P := by
    rintro a _ rfl
    rw [Γ, ρW_rowW, swap_mate_smul]
  rw [mem_edgeStar_mk]
  refine ⟨fun h ↦ ?_, hfix⟩
  by_contra hk
  have hik : i ≠ P.mate i := (P.mate_ne i).symm
  have hanti := LinearMap.congr_fun (Γ_anticomm_of_adj hij.symm hik (Ne.symm hk)) (rowW P)
  rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, hfix rfl, Γ_comm j i, h,
    hfix rfl, Module.End.one_apply, add_self_W] at hanti
  exact rowW_ne_zero hV hn P hanti.symm

/-- `φ(P) ∈ L_e` iff `e ∈ P`, for a non-diagonal `e` and `|V| = 2n ≥ 2` (`rowW`, ham-spin
0360f0d). Archive Theorem 7.2 (`old-personal-chatgpt` doc 01a1e1b7-1d50-770b-bb1e-667b6b2bd4d3),
orbit-point form. -/
theorem rowW_mem_edgeStar_iff {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n)
    (P : PerfectMatching V) {e : Sym2 V} (he : ¬e.IsDiag) :
    rowW P ∈ edgeStar e ↔ e ∈ P.toGraph.edgeSet := by
  induction e using Sym2.ind with
  | _ i j =>
    rw [SimpleGraph.mem_edgeSet, toGraph_adj]
    exact rowW_mem_edgeStar_mk_iff hV hn P (fun h ↦ he (Sym2.mk_isDiag_iff.mpr h))

/-- The fingerprint map `P ↦ φ(P) = r_P` (`rowW`, ham-spin 0360f0d) is injective when
`|V| = 2n ≥ 2`. -/
theorem rowW_injective {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) :
    Function.Injective (rowW (V := V)) := by
  intro P Q h
  ext i
  have hQ : rowW Q ∈ edgeStar s(i, Q.mate i) :=
    (rowW_mem_edgeStar_mk_iff hV hn Q (Q.mate_ne i).symm).2 rfl
  rw [← h] at hQ
  exact (rowW_mem_edgeStar_mk_iff hV hn P (Q.mate_ne i).symm).1 hQ

/-- The matching-star space `L_E = ⋂_{e ∈ E} L_e` of a set `E` of edges, in `W V` (`W`, ham-spin
0360f0d). Archive Theorem 7.2 (`old-personal-chatgpt` doc 01a1e1b7-1d50-770b-bb1e-667b6b2bd4d3). -/
def matchingStar (E : Set (Sym2 V)) : Submodule F₂ (W V) :=
  ⨅ e ∈ E, edgeStar e

/-- `x ∈ L_E` iff `x ∈ L_e` for every `e ∈ E` (`W`, ham-spin 0360f0d). -/
theorem mem_matchingStar {E : Set (Sym2 V)} {x : W V} :
    x ∈ matchingStar E ↔ ∀ e ∈ E, x ∈ edgeStar e := by
  simp only [matchingStar, Submodule.mem_iInf]

/-- `φ(P) ∈ L_E` iff `E ⊆ P`, for a set `E` of non-diagonal edges and `|V| = 2n ≥ 2` (`rowW`,
ham-spin 0360f0d). -/
theorem rowW_mem_matchingStar_iff {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n)
    (P : PerfectMatching V) {E : Set (Sym2 V)} (hE : ∀ e ∈ E, ¬e.IsDiag) :
    rowW P ∈ matchingStar E ↔ E ⊆ P.toGraph.edgeSet := by
  rw [mem_matchingStar]
  exact forall₂_congr fun e he ↦ rowW_mem_edgeStar_iff hV hn P (hE e he)

/-- Matching-star refinement of archive Proposition 14.1 (`old-personal-chatgpt` doc
01a1e1b7-1d50-770b-bb1e-667b6b2bd4d3): the zero states (`IsZeroState`, ham-spin 0360f0d)
containing `E` are the matchings `P` with `φ(P) ∈ R(F)^⊥ ∩ L_E`. -/
theorem isZeroState_and_subset_iff {ι : Type*} (F : ι → PerfectMatching V) {n : ℕ}
    (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (P : PerfectMatching V) {E : Set (Sym2 V)}
    (hE : ∀ e ∈ E, ¬e.IsDiag) :
    IsZeroState F P ∧ E ⊆ P.toGraph.edgeSet ↔
      rowW P ∈ fpForm.orthogonal (fpSpan F) ⊓ matchingStar E := by
  rw [Submodule.mem_inf, isZeroState_iff_rowW_mem_orthogonal, rowW_mem_matchingStar_iff hV hn P hE]

/-- Image form of the matching-star refinement: `φ({P ∈ Z(F) : E ⊆ P}) = Φ ∩ R(F)^⊥ ∩ L_E`, with
`Φ = range φ` (`rowW`, `IsZeroState`, ham-spin 0360f0d). -/
theorem image_rowW_zeroStates_subset {ι : Type*} (F : ι → PerfectMatching V) {n : ℕ}
    (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) {E : Set (Sym2 V)} (hE : ∀ e ∈ E, ¬e.IsDiag) :
    rowW '' {P | IsZeroState F P ∧ E ⊆ P.toGraph.edgeSet} =
      Set.range rowW ∩ ((fpForm.orthogonal (fpSpan F) ⊓ matchingStar E : Submodule F₂ (W V)) :
        Set (W V)) := by
  ext f
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨⟨P, rfl⟩, (isZeroState_and_subset_iff F hV hn P hE).1 hP⟩
  · rintro ⟨⟨P, rfl⟩, hf⟩
    exact ⟨P, (isZeroState_and_subset_iff F hV hn P hE).2 hf, rfl⟩

end Star

end Pairing.PerfectMatching

namespace Pairing.RoundRobin.Canonical

open Equiv PerfectMatching

variable {m : ℕ} [NeZero m]

/-- `R_rr = span{φ(F_t)}`, the fingerprint span of the canonical round-robin factors `factor m`
(ham-spin 0360f0d), as in archive Proposition 14.1 (`old-personal-chatgpt` doc
01a1e1b7-1d50-770b-bb1e-667b6b2bd4d3). -/
abbrev rrSpan (m : ℕ) [NeZero m] : Submodule F₂ (W (Vertex m)) :=
  fpSpan (factor m)

/-- Archive Proposition 14.1 for the canonical round-robin factors (`old-personal-chatgpt` doc
01a1e1b7-1d50-770b-bb1e-667b6b2bd4d3): `P` is a zero state iff `φ(P) ∈ R_rr^⊥` (`factor`,
`IsZeroState`, ham-spin 0360f0d). -/
theorem isZeroState_iff_mem_orthogonal_rrSpan (P : PerfectMatching (Vertex m)) :
    IsZeroState (factor m) P ↔ rowW P ∈ fpForm.orthogonal (rrSpan m) :=
  isZeroState_iff_rowW_mem_orthogonal _ P

/-- A permutation of `V_m` that permutes the canonical factors, `σ • F_t = F_{π t}`, preserves
`R_rr` and the zero states. This covers `Aut(𝓕) ≅ AGL(1, ℤ/(2m-1))` through
`RoundRobin.Canonical.IsAut.exists_perm` (ham_pairings main 81fccb6); `factor` at ham-spin
0360f0d. -/
theorem rrSpan_map_and_isZeroState_smul_of_perm {σ : Perm (Vertex m)}
    (π : ZMod (2 * m - 1) ≃ ZMod (2 * m - 1)) (h : ∀ t, σ • factor m t = factor m (π t)) :
    (rrSpan m).map (ρW σ) = rrSpan m ∧
      ∀ P, IsZeroState (factor m) (σ • P) ↔ IsZeroState (factor m) P :=
  ⟨mem_fpSpanStab_of_perm π h, isZeroState_smul_iff_of_perm π h⟩

/-- `dim R_rr ≤ 2m - 1` and `dim R_rr + dim R_rr^⊥ = 2^(m-1)`, in `W V_m` (`W`, `factor`, ham-spin
0360f0d). -/
theorem finrank_rrSpan :
    Module.finrank F₂ (rrSpan m) ≤ 2 * m - 1 ∧
      Module.finrank F₂ (rrSpan m) + Module.finrank F₂ (fpForm.orthogonal (rrSpan m)) =
        2 ^ (m - 1) := by
  refine ⟨?_, finrank_fpSpan_add_finrank_orthogonal _ (card_vertex m) (NeZero.one_le)⟩
  simpa [ZMod.card] using finrank_fpSpan_le (factor m)

/-- `Z_m = |{P : φ(P) ∈ R_rr^⊥}|`, for `zeroCount` at ham-spin 0360f0d. -/
theorem zeroCount_eq_card_orthogonal :
    zeroCount m =
      Nat.card {P : PerfectMatching (Vertex m) // rowW P ∈ fpForm.orthogonal (rrSpan m)} := by
  rw [zeroCount, ← Nat.card_eq_fintype_card, card_zeroStates_eq_card_orthogonal]

/-- The round-robin zero-state density in spin form,
`q_m = Z_m / (2m - 1)!! = |{P : φ(P) ∈ R_rr^⊥}| / (2m - 1)!!` (`zeroCount`, ham-spin 0360f0d). -/
theorem zeroCount_div_eq :
    (zeroCount m : ℝ) / Nat.doubleFactorial (2 * m - 1) =
      (Nat.card {P : PerfectMatching (Vertex m) // rowW P ∈ fpForm.orthogonal (rrSpan m)} : ℝ) /
        Nat.doubleFactorial (2 * m - 1) := by
  rw [zeroCount_eq_card_orthogonal]

end Pairing.RoundRobin.Canonical
