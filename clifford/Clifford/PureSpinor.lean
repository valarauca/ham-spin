import Clifford.SelfDualCode
import Clifford.ConceptualForm
import Clifford.Irreducible
import Clifford.QuadraticForm
import Mathlib.LinearAlgebra.CliffordAlgebra.Even

/-!
# Pure spinors of `Ũ_n` and the opposition criterion (COD-297)

Let `|V| = 2n` with `n ≥ 1`. This file formalizes Theorems 1 and 2 of
`results/spinor-hull-extend.md` (organize-archive b47b504), and Theorem 1.1 and Corollary 1.2 of
`results/spinor-codes.md` (d846b99), on the CKN module `W V` with the fingerprint pairing
`fpForm` and `φ(P) = rowW P` (ham-spin 87df892). Layer A (no spin module) is
`Clifford.SelfDualCode`, whose module docstring states the design: no quotient type, the space is
`U V × 𝔽₂` with `kE = 𝟙 + nε`, and dimensions in `Ũ_n` are one less than here.

`Γ` is computed with a base vertex `o` (`gammaL`, `ΓU`, ham-spin 87df892). `gammaE_indep` shows
that `Γ̃` does not depend on `o`, so neither do `annE`, `nullE`, `psiE` and `IsPureSpinor`.

## Theorem 1 of spinor-hull-extend

* `gammaE o (x + λε) = Γ(x) + λI`. `gammaE_mul_self` and `gammaE_anticomm` : `Γ̃` is a Clifford
  map, so `cliffordRepE : Cl(U ⊕ 𝔽₂ε, q̃) → End(W)`. `gammaE_kE` : `Γ̃(𝟙 + nε) = 0`, so it
  descends to `Ũ_n`. `gammaL_one` : `Γ(𝟙) = n I` for any `V`, which generalizes
  `cliffordRep_ι_ones`. `map_even_cliffordRepE` : the even Clifford algebra already maps onto
  `End(W)`, so `W` is simple over it, in Burnside's form. The nondegeneracy and Witt index of
  part 1 are `mem_span_kE_of_polar` and `maximal_isTotSing_iff` in `Clifford.SelfDualCode`.
* `nullE o v = N′(v)` and `annE o M = Ann(M)`. `isTotSing_nullE` : `N′(v)` is totally singular for
  `v ≠ 0`, so `finrank_nullE_le` : `dim N′(v) ≤ n` here, `n - 1` in `Ũ_n` (part 4).
  `IsPureSpinor o n v` : `v ≠ 0` and `dim N′(v) = n` here, that is `n - 1` in `Ũ_n`, which is the
  definition of `PS_s` in §2 of the source.
* `maximal_liftCode_pairCode` (`Clifford.SelfDualCode`) and `annE_liftCode_pairCode` : `M_P` is
  maximal totally singular and `Ann(M_P) = ⟨φ(P)⟩` (part 3). `nullE_rowW` : `N′(φ(P)) = M_P`, and
  `isPureSpinor_rowW` : `φ(P)` is pure (part 4).
* `annE_liftCode_pairCode_eq_matchingStar`, `matchingStar_edgeSet_eq_span` and
  `finrank_matchingStar_edgeSet` : `Ann(M_P) = L_P`, so `L_P = ⟨φ(P)⟩` for every perfect matching
  of every `V`. This extends `finrank_matchingStar_firstBlocks` at `j = n`
  (`Clifford.MatchingStarDim`) from `P0` on `Fin (2n)` to any `P`.

## Theorem 2 of spinor-hull-extend

* `fpForm_gammaE_left` : `Γ̃(z)` is self-adjoint. `annE_ne_bot` : commuting square-zero operators
  have a common null vector, so `Ann(M) ≠ 0`.
* `fpForm_eq_zero_of_mem_inf` : the non-opposite case, `⟨Ann(M), Ann(M')⟩ = 0` when
  `M ∩ M' ≠ 0` in `Ũ_n`.
* `eq_zero_of_fpForm_eq_zero` : the opposite case. If `M ∩ M' = 0` in `Ũ_n`, `0 ≠ ψ ∈ Ann(M)` and
  `ψ' ∈ Ann(M')` with `⟨ψ', ψ⟩ = 0`, then `ψ' = 0`. The proof differs from the source's Fock basis.
  `F = 𝔽₂[Γ̃(M')] ψ` is stable under `Γ̃(M')`, under `Γ̃(M)` (the commutator with `Γ̃(z)` is a
  derivation of `𝔽₂[Γ̃(M')]`), and under `ε`. As `M + M' + ⟨ε⟩` is everything
  (`sup_eq_U_of_inf_le`), `F` is `S_V`-stable, so `F = W` by irreducibility
  (`invariant_eq_bot_or_top_of_card`, in place of the simplicity step). Every element of
  `𝔽₂[Γ̃(M')]` acts on the covector `⟨ψ', ·⟩` by a scalar, so `⟨ψ', W⟩ = 0`.
* `finrank_annE` : part 1, `dim Ann(M) = 1` for every maximal `M`. A nonzero `ψ' ∈ Ann(M)` pairs to
  `1` with some fingerprint `φ(Q)`, so `M` is opposite `M_Q`, and pairing with `φ(Q)` is injective
  on `Ann(M)`. `psiE o M = ψ_M` is its nonzero vector, `annE_eq_span_psiE`, `eq_psiE`.
* `fpForm_psiE_eq_one_iff` : part 2, `⟨ψ_M, ψ_M'⟩ = 1` iff `M ∩ M' = 0` in `Ũ_n`.
* `nullE_psiE`, `isPureSpinor_iff` : `N′(ψ_M) = M`, and the pure spinors are the `ψ_M`.

## Theorem 1.1 and Corollary 1.2 of spinor-codes

* `psiCode o C = ψ_C = ψ_(M_C)`. `pureSpinorEquiv` : `C ↦ ψ_C` is a bijection from self-dual codes
  of length `2n` onto the pure spinors, with inverse `v ↦ codeOf N′(v)` (part 3, without the count
  `|PS_s| = σ_(s-1)`). `psiCode_pairCode` : `ψ_(i₂(P)) = φ(P)` (part 4). `fpForm_psiCode_eq_one_iff`
  : `⟨ψ_C, ψ_C'⟩ = 1` iff `C ∩ C' = ⟨𝟙⟩` (part 6). Part 2 is `selfDualEquiv` and the intersection
  formula of part 5 is `finrank_liftCode_inf`, both in `Clifford.SelfDualCode`.
* `psiCode_apply_eq_one_iff` : Corollary 1.2, `ψ_C(Q) = ⟨ψ_C, φ(Q)⟩ = 1` iff no word of `C` other
  than `0` and `𝟙` is a union of `Q`-edges. `psiCode_mem_orthogonal_fpSpan_iff` : its survivor
  form, `ψ_C ∈ R(F)^⊥` iff every `F_t` closes some word of `C` other than `0` and `𝟙`.
-/

namespace Pairing.PerfectMatching

open Module Equiv

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem f2_cases' (a : F₂) : a = 0 ∨ a = 1 := by
  revert a
  decide

private theorem f2_mul_self'' (a : F₂) : a * a = a := by
  revert a
  decide

private theorem mul_self_add_central {R : Type*} [Ring R] (h2 : ∀ x : R, x + x = 0) {A a : R}
    (ha : Commute a A) : (A + a) * (A + a) = A * A + a * a := by
  have e : (A + a) * (A + a) = A * A + a * a + (a * A + A * a) := by noncomm_ring
  rw [e, ← ha.eq, h2, add_zero]

private theorem anticomm_add_central {R : Type*} [Ring R] (h2 : ∀ x : R, x + x = 0)
    {A B a b : R} (ha : ∀ x, Commute a x) (hb : ∀ x, Commute b x) :
    (A + a) * (B + b) + (B + b) * (A + a) = A * B + B * A := by
  have e : (A + a) * (B + b) + (B + b) * (A + a) =
      A * B + B * A + (a * B + B * a) + (A * b + b * A) + (a * b + b * a) := by noncomm_ring
  rw [e, ← (ha B).eq, h2, (hb A).eq, h2, (ha b).eq, h2, add_zero, add_zero, add_zero]

private theorem eq_of_add_eq_zero_F₂ {M : Type*} [AddCommGroup M] [Module F₂ M] {a b : M}
    (h : a + b = 0) : a = b :=
  calc a = a + (b + b) := by rw [add_self_F₂, add_zero]
    _ = b := by rw [← add_assoc, h, zero_add]

section Clifford

/-- `Γ̃(x + λε) = Γ(x) + λI` on `W` (`ΓU`, ham-spin 87df892; Theorem 1 of
`results/spinor-hull-extend.md`, organize-archive b47b504). -/
def gammaE (o : V) : U V × F₂ →ₗ[F₂] Module.End F₂ (W V) :=
  ΓU o ∘ₗ LinearMap.fst F₂ (U V) F₂ + (LinearMap.snd F₂ (U V) F₂).smulRight 1

theorem gammaE_apply (o : V) (z : U V × F₂) : gammaE o z = ΓU o z.1 + z.2 • 1 :=
  rfl

theorem gammaE_inl (o : V) (x : U V) : gammaE o (x, 0) = ΓU o x := by
  rw [gammaE_apply, zero_smul, add_zero]

/-- `ε` acts as the identity. -/
theorem gammaE_epsE (o : V) : gammaE o (epsE V) = 1 := by
  rw [gammaE_apply, epsE, map_zero, one_smul, zero_add]

/-- `Γ̃` does not depend on the base vertex, by `ΓU_unique` (ham-spin 87df892). -/
theorem gammaE_indep (o o' : V) : gammaE o = gammaE o' := by
  have h : ΓU o = ΓU o' := ΓU_unique o' (ΓU o) fun i j hij ↦ by
    rw [ΓU_apply]
    exact gammaL_v o hij
  refine LinearMap.ext fun z ↦ ?_
  rw [gammaE_apply, gammaE_apply, h]

private theorem commute_smul_one (c : F₂) (x : Module.End F₂ (W V)) : Commute (c • 1) x :=
  (Commute.one_left x).smul_left c

/-- `Γ̃(z)² = q̃(z) I` (Theorem 1.2 of `results/spinor-hull-extend.md`, organize-archive
b47b504). -/
theorem gammaE_mul_self (o : V) (z : U V × F₂) : gammaE o z * gammaE o z = qE V z • 1 := by
  rw [gammaE_apply]
  refine (mul_self_add_central (R := Module.End F₂ (W V)) end_add_self
    (commute_smul_one z.2 (ΓU o z.1))).trans ?_
  rw [ΓU_sq, smul_mul_smul_comm, one_mul, f2_mul_self'', qForm_apply, qE_apply, add_smul]

/-- `{Γ̃(z), Γ̃(w)} = B̃(z, w) I` (Theorem 1.2 of `results/spinor-hull-extend.md`, organize-archive
b47b504). -/
theorem gammaE_anticomm (o : V) (z w : U V × F₂) :
    gammaE o z * gammaE o w + gammaE o w * gammaE o z = QuadraticMap.polar (qE V) z w • 1 := by
  rw [gammaE_apply, gammaE_apply]
  refine (anticomm_add_central (R := Module.End F₂ (W V)) end_add_self (commute_smul_one z.2)
    (commute_smul_one w.2)).trans ?_
  rw [ΓU_apply, ΓU_apply, gammaL_anticomm o z.1.2 w.1.2, polar_qE]

/-- The Clifford action `Cl(U ⊕ 𝔽₂ε, q̃) → End(W)` of Theorem 1.2 of
`results/spinor-hull-extend.md` (organize-archive b47b504). -/
def cliffordRepE (o : V) : CliffordAlgebra (qE V) →ₐ[F₂] Module.End F₂ (W V) :=
  CliffordAlgebra.lift (qE V)
    ⟨gammaE o, fun z ↦ by rw [gammaE_mul_self, Algebra.algebraMap_eq_smul_one]⟩

theorem cliffordRepE_ι (o : V) (z : U V × F₂) :
    cliffordRepE o (CliffordAlgebra.ι (qE V) z) = gammaE o z :=
  CliffordAlgebra.lift_ι_apply _ _ _

/-- `G_j` is self-adjoint for the fingerprint pairing (`G`, `fpForm_Γ_left`, ham-spin 87df892). -/
theorem fpForm_G_left (o j : V) (f g : W V) : fpForm (G o j f) g = fpForm f (G o j g) := by
  unfold G
  split_ifs
  · simp
  · exact fpForm_Γ_left o j f g

/-- `Γ(x)` is self-adjoint for the fingerprint pairing (`gammaL`, `fpForm`, ham-spin 87df892). -/
theorem fpForm_gammaL_left (o : V) (x : V → F₂) (f g : W V) :
    fpForm (gammaL o x f) g = fpForm f (gammaL o x g) := by
  simp only [gammaL_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    fpForm_G_left]

/-- `Γ̃(z)` is self-adjoint for the fingerprint pairing (`fpForm`, ham-spin 87df892), as in the
proof of Theorem 2 of `results/spinor-hull-extend.md` (organize-archive b47b504). -/
theorem fpForm_gammaE_left (o : V) (z : U V × F₂) (f g : W V) :
    fpForm (gammaE o z f) g = fpForm f (gammaE o z g) := by
  rw [gammaE_apply, LinearMap.add_apply, LinearMap.add_apply, ΓU_apply, map_add,
    LinearMap.add_apply, map_add, fpForm_gammaL_left, LinearMap.smul_apply, LinearMap.smul_apply,
    Module.End.one_apply, Module.End.one_apply, map_smul, map_smul, LinearMap.smul_apply]

private theorem ρW_mem_of_Γ_mem (S : Subalgebra F₂ (Module.End F₂ (W V)))
    (h : ∀ i j : V, i ≠ j → Γ i j ∈ S) (σ : Perm V) : ρW σ ∈ S := by
  have hσ : σ ∈ Submonoid.closure {τ : Perm V | τ.IsSwap} := by
    rw [Perm.mclosure_isSwap]
    exact Submonoid.mem_top σ
  induction hσ using Submonoid.closure_induction with
  | mem τ hτ =>
    obtain ⟨i, j, hij, rfl⟩ := hτ
    exact h i j hij
  | one =>
    rw [map_one]
    exact S.one_mem
  | mul τ τ' _ _ h1 h2 =>
    rw [map_mul]
    exact S.mul_mem h1 h2

private theorem ρW_mapsTo {F : Submodule F₂ (W V)} (h : ∀ i j : V, i ≠ j → ∀ w ∈ F, Γ i j w ∈ F)
    (σ : Perm V) : ∀ w ∈ F, ρW σ w ∈ F := by
  have hσ : σ ∈ Submonoid.closure {τ : Perm V | τ.IsSwap} := by
    rw [Perm.mclosure_isSwap]
    exact Submonoid.mem_top σ
  induction hσ using Submonoid.closure_induction with
  | mem τ hτ =>
    obtain ⟨i, j, hij, rfl⟩ := hτ
    exact h i j hij
  | one =>
    intro w hw
    rw [map_one, Module.End.one_apply]
    exact hw
  | mul τ τ' _ _ h1 h2 =>
    intro w hw
    rw [map_mul, Module.End.mul_apply]
    exact h1 _ (h2 w hw)

/-- `W` is simple over the even Clifford algebra of `Ũ_n` (Theorem 1.2 of
`results/spinor-hull-extend.md`, organize-archive b47b504), in Burnside's form: the even part
`Cl⁰(U ⊕ 𝔽₂ε, q̃)` maps onto `End(W)`. Since `ε` acts as `1`, `Γ̃(z) = Γ̃(z) Γ̃(ε)` is even, and the
`Γ_{ij}` generate `End(W)` (`adjoin_ρW_eq_top_of_card`, ham-spin 87df892). -/
theorem map_even_cliffordRepE {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V) :
    (CliffordAlgebra.even (qE V)).map (cliffordRepE o) = ⊤ := by
  have hΓ : ∀ i j : V, i ≠ j → Γ i j ∈ (CliffordAlgebra.even (qE V)).map (cliffordRepE o) := by
    intro i j hij
    have hx : CliffordAlgebra.ι (qE V) (⟨v i j, v_mem i j⟩, 0) * CliffordAlgebra.ι (qE V) (epsE V)
        ∈ CliffordAlgebra.even (qE V) := by
      rw [← Subalgebra.mem_toSubmodule, CliffordAlgebra.even_toSubmodule]
      exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero _ _ _
    refine Subalgebra.mem_map.mpr ⟨_, hx, ?_⟩
    rw [map_mul, cliffordRepE_ι, cliffordRepE_ι, gammaE_epsE, mul_one, gammaE_inl, ΓU_apply]
    exact gammaL_v o hij
  rw [eq_top_iff, ← adjoin_ρW_eq_top_of_card hV hn, Algebra.adjoin_le_iff]
  rintro _ ⟨σ, rfl⟩
  exact ρW_mem_of_Γ_mem _ hΓ σ

/-- The Clifford action of `Ũ_n` on `W` is onto `End(W)` (`cliffordRep_surjective`, ham-spin
87df892, for `Γ̃`). -/
theorem cliffordRepE_surjective {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V) :
    Function.Surjective (cliffordRepE o) := by
  intro f
  have hf : f ∈ (CliffordAlgebra.even (qE V)).map (cliffordRepE o) := by
    rw [map_even_cliffordRepE hV hn o]
    exact Algebra.mem_top
  obtain ⟨x, _, hx⟩ := hf
  exact ⟨x, hx⟩

end Clifford

section Annihilator

variable {M M' : Submodule F₂ (U V × F₂)}

/-- `Ann(M) = {v ∈ W : Γ̃(z) v = 0 for z ∈ M}` (Theorem 1.3 of `results/spinor-hull-extend.md`,
organize-archive b47b504). -/
def annE (o : V) (M : Submodule F₂ (U V × F₂)) : Submodule F₂ (W V) :=
  ⨅ z ∈ M, LinearMap.ker (gammaE o z)

theorem mem_annE {o : V} {f : W V} : f ∈ annE o M ↔ ∀ z ∈ M, gammaE o z f = 0 := by
  simp [annE]

/-- `N′(v) = {z : Γ̃(z) v = 0}` (Theorem 1.4 of `results/spinor-hull-extend.md`, organize-archive
b47b504), here in `U ⊕ 𝔽₂ε`, where it always contains `kE` (`kE_mem_nullE`). -/
def nullE (o : V) (f : W V) : Submodule F₂ (U V × F₂) :=
  LinearMap.ker ((gammaE o).flip f)

theorem mem_nullE {o : V} {f : W V} {z : U V × F₂} : z ∈ nullE o f ↔ gammaE o z f = 0 :=
  Iff.rfl

theorem le_nullE_iff {o : V} {f : W V} : M ≤ nullE o f ↔ f ∈ annE o M := by
  rw [mem_annE]
  exact ⟨fun h z hz ↦ h hz, fun h z hz ↦ h z hz⟩

/-- `Ann(span S) = ⋂_{z ∈ S} ker Γ̃(z)`. -/
theorem mem_annE_span {o : V} {S : Set (U V × F₂)} {f : W V} :
    f ∈ annE o (Submodule.span F₂ S) ↔ ∀ z ∈ S, gammaE o z f = 0 := by
  rw [← le_nullE_iff, Submodule.span_le]
  exact Iff.rfl

/-- `Γ̃(v_{i, P i} + ε) φ(P) = 0`, since `Γ_{i, P i}` fixes `φ(P)` (`rowW`, ham-spin 87df892). -/
theorem gammaE_v_mate_rowW (o : V) (P : PerfectMatching V) (i : V) :
    gammaE o (⟨v i (P.mate i), v_mem _ _⟩, 1) (rowW P) = 0 := by
  change gammaL o (v i (P.mate i)) (rowW P) + (1 : F₂) • rowW P = 0
  rw [gammaL_v o (P.mate_ne i).symm, one_smul, Γ, ρW_rowW, swap_mate_smul, add_self_F₂]

/-- `M_P = span{v_e + ε : e ∈ P}` (proof of Theorem 1.3 of `results/spinor-hull-extend.md`,
organize-archive b47b504). -/
theorem liftCode_pairCode_eq_span (P : PerfectMatching V) :
    liftCode (pairCode P) =
      Submodule.span F₂ (Set.range fun i ↦ ((⟨v i (P.mate i), v_mem _ _⟩, 1) : U V × F₂)) := by
  set N := Submodule.span F₂ (Set.range fun i ↦ ((⟨v i (P.mate i), v_mem _ _⟩, 1) : U V × F₂))
  have hsd := isSelfDual_pairCode P
  have hle : N ≤ liftCode (pairCode P) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine (mem_liftCode hsd.isSelfOrth).mpr ⟨v_mate_mem_pairCode P i, ?_⟩
    rw [qE_apply]
    change qfun (v i (P.mate i)) + 1 = 0
    rw [qfun_v (P.mate_ne i).symm]
    rfl
  have hcode : codeOf N = pairCode P := by
    rw [codeOf, Submodule.map_span, ← Set.range_comp, ← span_v_mate]
    rfl
  rw [← hcode]
  exact liftCode_codeOf ((isTotSing_liftCode hsd.isSelfOrth).mono hle)

/-- `φ(P) ∈ Ann(M_P)` (Theorem 1.3 of `results/spinor-hull-extend.md`, organize-archive
b47b504). -/
theorem rowW_mem_annE (o : V) (P : PerfectMatching V) :
    rowW P ∈ annE o (liftCode (pairCode P)) := by
  rw [liftCode_pairCode_eq_span, mem_annE_span]
  rintro _ ⟨i, rfl⟩
  exact gammaE_v_mate_rowW o P i

/-- `Ann(M_P) = L_P`, the matching star of the edges of `P` (`matchingStar`, ham-spin 87df892). -/
theorem annE_liftCode_pairCode_eq_matchingStar (o : V) (P : PerfectMatching V) :
    annE o (liftCode (pairCode P)) = matchingStar P.toGraph.edgeSet := by
  ext f
  rw [liftCode_pairCode_eq_span, mem_annE_span, mem_matchingStar]
  constructor
  · intro h e he
    induction e using Sym2.ind with
    | _ i j =>
      rw [SimpleGraph.mem_edgeSet, toGraph_adj] at he
      subst he
      have h1 : gammaL o (v i (P.mate i)) f + (1 : F₂) • f = 0 := h _ ⟨i, rfl⟩
      rw [gammaL_v o (P.mate_ne i).symm, one_smul] at h1
      exact mem_edgeStar_mk.mpr (eq_of_add_eq_zero_F₂ h1)
  · rintro h _ ⟨i, rfl⟩
    have h1 := mem_edgeStar_mk.mp (h s(i, P.mate i) (by rw [SimpleGraph.mem_edgeSet, toGraph_adj]))
    change gammaL o (v i (P.mate i)) f + (1 : F₂) • f = 0
    rw [gammaL_v o (P.mate_ne i).symm, h1, one_smul, add_self_F₂]

variable {n : ℕ}

/-- `Γ̃(𝟙 + nε) = 0` (Theorem 1.2 of `results/spinor-hull-extend.md`, organize-archive b47b504), so
`Γ̃` descends to `Ũ_n`. Proved on the fingerprints, as `kE ∈ M_P` for every `P`. -/
theorem gammaE_kE (hV : Fintype.card V = 2 * n) (o : V) : gammaE o (kE hV) = 0 := by
  refine LinearMap.ext_on_range span_rowW fun P ↦ ?_
  have hk : kE hV ∈ liftCode (pairCode P) :=
    (mem_liftCode (isSelfDual_pairCode P).isSelfOrth).mpr ⟨one_mem_pairCode P, qE_kE hV⟩
  rw [mem_annE.mp (rowW_mem_annE o P) _ hk, LinearMap.zero_apply]

/-- `Γ(𝟙) = n I` on `W V` for `|V| = 2n`, for any vertex type (`gammaL`, ham-spin 87df892). This
generalizes `cliffordRep_ι_ones` from `Fin (2 * n)`. -/
theorem gammaL_one (hV : Fintype.card V = 2 * n) (o : V) :
    gammaL o (1 : V → F₂) = (n : F₂) • 1 := by
  have h := gammaE_kE hV o
  change gammaL o 1 + (n : F₂) • 1 = 0 at h
  exact eq_of_add_eq_zero_F₂ h

theorem kE_mem_nullE (hV : Fintype.card V = 2 * n) (o : V) (f : W V) : kE hV ∈ nullE o f := by
  rw [mem_nullE, gammaE_kE, LinearMap.zero_apply]

/-- Theorem 1.4 of `results/spinor-hull-extend.md` (organize-archive b47b504): `N′(v)` is totally
singular for `v ≠ 0`, because `q̃(z) v = Γ̃(z)² v`. -/
theorem isTotSing_nullE (o : V) {f : W V} (hf : f ≠ 0) : IsTotSing (nullE o f) := fun z hz ↦ by
  have h := LinearMap.congr_fun (gammaE_mul_self o z) f
  rw [Module.End.mul_apply, mem_nullE.mp hz, map_zero, LinearMap.smul_apply,
    Module.End.one_apply] at h
  rcases f2_cases' (qE V z) with h0 | h1
  · exact h0
  · rw [h1, one_smul] at h
    exact absurd h.symm hf

/-- Theorem 1.4 of `results/spinor-hull-extend.md` (organize-archive b47b504): `dim N′(v) ≤ n` in
`U ⊕ 𝔽₂ε`, that is `dim N′(v) ≤ n - 1` in `Ũ_n`. -/
theorem finrank_nullE_le (hV : Fintype.card V = 2 * n) (o : V) {f : W V} (hf : f ≠ 0) :
    finrank F₂ (nullE o f) ≤ n :=
  finrank_le_of_isTotSing hV (isTotSing_nullE o hf)

/-- A pure spinor of `Ũ_n` (§2 of `results/spinor-hull-extend.md`, organize-archive b47b504):
`v ≠ 0` with `dim N′(v) = n` in `U ⊕ 𝔽₂ε`, that is `dim N′(v) = n - 1` in `Ũ_n`. -/
def IsPureSpinor (o : V) (n : ℕ) (f : W V) : Prop :=
  f ≠ 0 ∧ finrank F₂ (nullE o f) = n

/-- For a pure spinor `v`, `N′(v)` is maximal totally singular. -/
theorem maximal_nullE (hV : Fintype.card V = 2 * n) {o : V} {f : W V} (hf : IsPureSpinor o n f) :
    Maximal IsTotSing (nullE o f) :=
  (maximal_isTotSing_iff hV).mpr ⟨isTotSing_nullE o hf.1, hf.2⟩

/-- Commuting square-zero operators on a nonzero `𝔽₂`-space have a common null vector. -/
theorem exists_ne_zero_forall_eq_zero {E : Type*} [AddCommGroup E] [Module F₂ E] [Nontrivial E]
    (S : Finset (Module.End F₂ E)) (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hsq : ∀ a ∈ S, a * a = 0) : ∃ x : E, x ≠ 0 ∧ ∀ a ∈ S, a x = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact ⟨x, hx, by simp⟩
  | insert a S ha ih =>
    obtain ⟨x, hx, hxS⟩ := ih
      (fun b hb c hc ↦ hcomm b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc))
      (fun b hb ↦ hsq b (Finset.mem_insert_of_mem hb))
    by_cases hax : a x = 0
    · refine ⟨x, hx, fun b hb ↦ ?_⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hax
      · exact hxS b hb
    · refine ⟨a x, hax, fun b hb ↦ ?_⟩
      rcases Finset.mem_insert.mp hb with rfl | hb'
      · rw [← Module.End.mul_apply, hsq b (Finset.mem_insert_self _ _), LinearMap.zero_apply]
      · rw [← Module.End.mul_apply, hcomm b hb a (Finset.mem_insert_self _ _),
          Module.End.mul_apply, hxS b hb', map_zero]

/-- `Ann(M) ≠ 0` for a totally singular `M`: the `Γ̃(z)`, `z ∈ M`, commute and square to zero
(proof of Theorem 2.1 of `results/spinor-hull-extend.md`, organize-archive b47b504). -/
theorem annE_ne_bot (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V) (hM : IsTotSing M) :
    annE o M ≠ ⊥ := by
  classical
  have := nontrivial_W_of_card hV hn
  set S := (M : Set (U V × F₂)).toFinite.toFinset.image (gammaE o) with hS
  have memS : ∀ {T}, T ∈ S ↔ ∃ z ∈ M, gammaE o z = T := by
    intro T
    simp [hS]
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    obtain ⟨z, hz, rfl⟩ := memS.mp ha
    obtain ⟨w, hw, rfl⟩ := memS.mp hb
    have h := gammaE_anticomm o z w
    rw [hM.polar_eq_zero hz hw, zero_smul] at h
    exact eq_of_add_eq_zero_F₂ h
  have hsq : ∀ a ∈ S, a * a = 0 := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := memS.mp ha
    rw [gammaE_mul_self, hM z hz, zero_smul]
  obtain ⟨x, hx, hxS⟩ := exists_ne_zero_forall_eq_zero S hcomm hsq
  intro hbot
  have hxM : x ∈ annE o M := mem_annE.mpr fun z hz ↦ hxS _ (memS.mpr ⟨z, hz, rfl⟩)
  rw [hbot] at hxM
  exact hx ((Submodule.mem_bot F₂).mp hxM)

end Annihilator

section Opposition

variable {M M' : Submodule F₂ (U V × F₂)} {n : ℕ}

/-- Theorem 2.2 of `results/spinor-hull-extend.md` (organize-archive b47b504), the non-opposite
case: if `M ∩ M'` has a vector outside `⟨kE⟩`, that is `M ∩ M' ≠ 0` in `Ũ_n`, then
`⟨Ann(M), Ann(M')⟩ = 0` for the fingerprint pairing (`fpForm`, ham-spin 87df892). -/
theorem fpForm_eq_zero_of_mem_inf (hV : Fintype.card V = 2 * n) (o : V) (hM : IsTotSing M)
    {x : U V × F₂} (hx : x ∈ M ⊓ M') (hxk : x ∉ F₂ ∙ kE hV) {f g : W V} (hf : f ∈ annE o M)
    (hg : g ∈ annE o M') : fpForm f g = 0 := by
  obtain ⟨y, hy⟩ : ∃ y, QuadraticMap.polar (qE V) x y = 1 := by
    by_contra h
    simp only [not_exists] at h
    exact hxk (mem_span_kE_of_polar hV (fun y ↦ (f2_cases' _).resolve_right (h y))
      (hM x (Submodule.mem_inf.mp hx).1))
  have hfx : gammaE o x f = 0 := mem_annE.mp hf x (Submodule.mem_inf.mp hx).1
  have hgx : gammaE o x g = 0 := mem_annE.mp hg x (Submodule.mem_inf.mp hx).2
  have h := congrArg (fun T : Module.End F₂ (W V) ↦ fpForm (T f) g) (gammaE_anticomm o x y)
  simp only [hy, one_smul, Module.End.one_apply, LinearMap.add_apply, Module.End.mul_apply, hfx,
    map_zero, add_zero] at h
  rw [fpForm_gammaE_left, hgx, map_zero] at h
  exact h.symm

/-- Theorem 2 of `results/spinor-hull-extend.md` (organize-archive b47b504), the opposite case.
Let `M, M'` be maximal totally singular with `M ∩ M' = 0` in `Ũ_n`, `0 ≠ ψ ∈ Ann(M)` and
`ψ' ∈ Ann(M')`. If `⟨ψ', ψ⟩ = 0` then `ψ' = 0`. In place of the Fock basis, `𝔽₂[Γ̃(M')] ψ` is shown
to be `S_V`-stable, hence all of `W` (`invariant_eq_bot_or_top_of_card`, ham-spin 87df892), and
`𝔽₂[Γ̃(M')]` acts on `⟨ψ', ·⟩` by scalars. -/
theorem eq_zero_of_fpForm_eq_zero (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V)
    (hM : Maximal IsTotSing M) (hM' : Maximal IsTotSing M') (hopp : M ⊓ M' ≤ F₂ ∙ kE hV)
    {ψ : W V} (hψ : ψ ∈ annE o M) (hψ0 : ψ ≠ 0) {ψ' : W V} (hψ' : ψ' ∈ annE o M')
    (h : fpForm ψ' ψ = 0) : ψ' = 0 := by
  set A := Algebra.adjoin F₂ (gammaE o '' (M' : Set (U V × F₂))) with hA
  set F : Submodule F₂ (W V) := (Subalgebra.toSubmodule A).map (LinearMap.applyₗ ψ) with hF
  have memF : ∀ {w}, w ∈ F ↔ ∃ T ∈ A, T ψ = w := by
    intro w
    simp [hF]
  have hψF : ψ ∈ F := memF.mpr ⟨1, A.one_mem, rfl⟩
  have hM'F : ∀ z ∈ M', ∀ w ∈ F, gammaE o z w ∈ F := by
    intro z hz w hw
    obtain ⟨T, hT, rfl⟩ := memF.mp hw
    exact memF.mpr ⟨gammaE o z * T, A.mul_mem (Algebra.subset_adjoin ⟨z, hz, rfl⟩) hT, rfl⟩
  have hD : ∀ z ∈ M, ∀ T ∈ A, gammaE o z * T + T * gammaE o z ∈ A := by
    intro z hz T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨z', hz', rfl⟩ := hT
      rw [gammaE_anticomm, ← Algebra.algebraMap_eq_smul_one]
      exact A.algebraMap_mem _
    | algebraMap c =>
      rw [Algebra.commutes, end_add_self]
      exact A.zero_mem
    | add T T' _ _ h1 h2 =>
      have e : gammaE o z * (T + T') + (T + T') * gammaE o z =
          (gammaE o z * T + T * gammaE o z) + (gammaE o z * T' + T' * gammaE o z) := by
        noncomm_ring
      rw [e]
      exact A.add_mem h1 h2
    | mul T T' hT hT' h1 h2 =>
      have e : (gammaE o z * T + T * gammaE o z) * T' + T * (gammaE o z * T' + T' * gammaE o z) =
          gammaE o z * (T * T') + T * T' * gammaE o z +
            (T * gammaE o z * T' + T * gammaE o z * T') := by
        noncomm_ring
      rw [end_add_self, add_zero] at e
      rw [← e]
      exact A.add_mem (A.mul_mem h1 hT') (A.mul_mem hT h2)
  have hMF : ∀ z ∈ M, ∀ w ∈ F, gammaE o z w ∈ F := by
    intro z hz w hw
    obtain ⟨T, hT, rfl⟩ := memF.mp hw
    refine memF.mpr ⟨_, hD z hz T hT, ?_⟩
    rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, mem_annE.mp hψ z hz,
      map_zero, add_zero]
  have hC := isSelfDual_codeOf hV hM
  have hC' := isSelfDual_codeOf hV hM'
  have hopp' : codeOf M ⊓ codeOf M' ≤ F₂ ∙ (1 : V → F₂) := by
    rw [← liftCode_inf_le_span_kE_iff hV hC.isSelfOrth hC'.isSelfOrth, liftCode_codeOf hM.1,
      liftCode_codeOf hM'.1]
    exact hopp
  have hUF : ∀ x : U V, ∀ w ∈ F, ΓU o x w ∈ F := by
    intro x w hw
    have hx : (x : V → F₂) ∈ codeOf M ⊔ codeOf M' := by
      rw [sup_eq_U_of_inf_le hC hC' hopp']
      exact x.2
    obtain ⟨_, ⟨z, hz, rfl⟩, _, ⟨z', hz', rfl⟩, hcc⟩ := Submodule.mem_sup.mp hx
    have e : ((x, 0) : U V × F₂) = z + z' + (z.2 + z'.2) • epsE V := by
      refine Prod.ext (Subtype.ext ?_) ?_
      · simp only [Prod.fst_add, Prod.smul_fst, epsE, smul_zero, add_zero, Submodule.coe_add]
        exact hcc.symm
      · simp only [Prod.snd_add, Prod.smul_snd, epsE, smul_eq_mul, mul_one]
        rw [add_self_F₂]
    have e2 : ΓU o x = gammaE o z + gammaE o z' + (z.2 + z'.2) • 1 := by
      rw [← gammaE_inl, e, map_add, map_add, map_smul, gammaE_epsE]
    rw [e2, LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact F.add_mem (F.add_mem (hMF z hz w hw) (hM'F z' hz' w hw)) (F.smul_mem _ hw)
  have hΓF : ∀ i j : V, i ≠ j → ∀ w ∈ F, Γ i j w ∈ F := fun i j hij w hw ↦ by
    have h1 := hUF ⟨v i j, v_mem i j⟩ w hw
    rwa [ΓU_apply, gammaL_v o hij] at h1
  have hFtop : F = ⊤ := by
    refine (invariant_eq_bot_or_top_of_card hV hn F (ρW_mapsTo hΓF)).resolve_left fun hb ↦ hψ0 ?_
    rw [hb] at hψF
    exact (Submodule.mem_bot F₂).mp hψF
  have heig : ∀ T ∈ A, ∃ c : F₂, ∀ w, fpForm ψ' (T w) = c * fpForm ψ' w := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨z', hz', rfl⟩ := hT
      refine ⟨0, fun w ↦ ?_⟩
      rw [← fpForm_gammaE_left, mem_annE.mp hψ' z' hz', map_zero, LinearMap.zero_apply, zero_mul]
    | algebraMap c =>
      refine ⟨c, fun w ↦ ?_⟩
      rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, map_smul,
        smul_eq_mul]
    | add T T' _ _ h1 h2 =>
      obtain ⟨c, hc⟩ := h1
      obtain ⟨c', hc'⟩ := h2
      exact ⟨c + c', fun w ↦ by rw [LinearMap.add_apply, map_add, hc, hc', add_mul]⟩
    | mul T T' _ _ h1 h2 =>
      obtain ⟨c, hc⟩ := h1
      obtain ⟨c', hc'⟩ := h2
      exact ⟨c * c', fun w ↦ by rw [Module.End.mul_apply, hc, hc', mul_assoc]⟩
  refine fpForm_nondegenerate.1 ψ' fun w ↦ ?_
  have hw : w ∈ F := hFtop ▸ Submodule.mem_top
  obtain ⟨T, hT, rfl⟩ := memF.mp hw
  obtain ⟨c, hc⟩ := heig T hT
  rw [hc, h, mul_zero]

/-- For a maximal totally singular `M` there is a fingerprint `φ(Q)` such that pairing with it is
injective on `Ann(M)`: `M` is opposite `M_Q`, by `fpForm_eq_zero_of_mem_inf`, and
`eq_zero_of_fpForm_eq_zero` applies (`rowW`, ham-spin 87df892). -/
theorem exists_rowW_pairing_injective (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V)
    (hM : Maximal IsTotSing M) :
    ∃ Q : PerfectMatching V, ∀ f ∈ annE o M, fpForm f (rowW Q) = 0 → f = 0 := by
  obtain ⟨ψ', hψ', hψ'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (annE_ne_bot hV hn o hM.1)
  obtain ⟨Q, hQ⟩ : ∃ Q, fpForm ψ' (rowW Q) ≠ 0 := by
    by_contra hc
    simp only [ne_eq, not_exists, not_not] at hc
    have h0 : fpForm ψ' = 0 := LinearMap.ext_on_range span_rowW fun Q ↦ hc Q
    exact hψ'0 (fpForm_nondegenerate.1 ψ' fun g ↦ by rw [h0, LinearMap.zero_apply])
  have hMQ := maximal_liftCode_pairCode hV Q
  have hopp : liftCode (pairCode Q) ⊓ M ≤ F₂ ∙ kE hV := by
    intro x hx
    by_contra hxk
    exact hQ (by rw [fpForm_comm]; exact
      fpForm_eq_zero_of_mem_inf hV o hMQ.1 hx hxk (rowW_mem_annE o Q) hψ')
  exact ⟨Q, fun f hf h0 ↦ eq_zero_of_fpForm_eq_zero hV hn o hMQ hM hopp (rowW_mem_annE o Q)
    (rowW_ne_zero hV hn Q) hf h0⟩

/-- Theorem 2.1 of `results/spinor-hull-extend.md` (organize-archive b47b504): `Ann(M)` is
one-dimensional for every maximal totally singular `M`. -/
theorem finrank_annE (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V)
    (hM : Maximal IsTotSing M) : finrank F₂ (annE o M) = 1 := by
  have hne := annE_ne_bot hV hn o hM.1
  obtain ⟨Q, hQ⟩ := exists_rowW_pairing_injective hV hn o hM
  have hinj : Function.Injective ((fpForm.flip (rowW Q)).domRestrict (annE o M)) :=
    (injective_iff_map_eq_zero _).mpr fun m hm ↦ Subtype.ext (hQ m m.2 hm)
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_self] at h1
  have h2 : finrank F₂ (annE o M) ≠ 0 := fun h0 ↦ hne (Submodule.finrank_eq_zero.mp h0)
  omega

/-- Over `𝔽₂`, `Ann(M)` has exactly one nonzero vector for a maximal totally singular `M`. -/
theorem eq_of_mem_annE (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V)
    (hM : Maximal IsTotSing M) {f g : W V} (hf : f ∈ annE o M) (hf0 : f ≠ 0) (hg : g ∈ annE o M)
    (hg0 : g ≠ 0) : f = g := by
  obtain ⟨Q, hQ⟩ := exists_rowW_pairing_injective hV hn o hM
  have h1 : fpForm f (rowW Q) = 1 := (f2_cases' _).resolve_left fun h ↦ hf0 (hQ f hf h)
  have h2 : fpForm g (rowW Q) = 1 := (f2_cases' _).resolve_left fun h ↦ hg0 (hQ g hg h)
  refine eq_of_add_eq_zero_F₂ (hQ _ ((annE o M).add_mem hf hg) ?_)
  rw [map_add, LinearMap.add_apply, h1, h2]
  rfl

/-- `ψ_M`, a nonzero vector of `Ann(M)` when there is one. For maximal `M` it spans `Ann(M)` and
is unique over `𝔽₂` (Theorem 2.1 of `results/spinor-hull-extend.md`, organize-archive
b47b504). -/
noncomputable def psiE (o : V) (M : Submodule F₂ (U V × F₂)) : W V :=
  Classical.epsilon fun f ↦ f ∈ annE o M ∧ f ≠ 0

/-- `0 ≠ ψ_M ∈ Ann(M)` for a totally singular `M`. -/
theorem psiE_spec (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V) (hM : IsTotSing M) :
    psiE o M ∈ annE o M ∧ psiE o M ≠ 0 :=
  Classical.epsilon_spec (Submodule.exists_mem_ne_zero_of_ne_bot (annE_ne_bot hV hn o hM))

/-- Over `𝔽₂`, the nonzero vector of `Ann(M)` is unique: it is `ψ_M`. -/
theorem eq_psiE (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V) (hM : Maximal IsTotSing M)
    {f : W V} (hf : f ∈ annE o M) (hf0 : f ≠ 0) : f = psiE o M :=
  eq_of_mem_annE hV hn o hM hf hf0 (psiE_spec hV hn o hM.1).1 (psiE_spec hV hn o hM.1).2

/-- Theorem 2.1 of `results/spinor-hull-extend.md` (organize-archive b47b504):
`Ann(M) = ⟨ψ_M⟩`. -/
theorem annE_eq_span_psiE (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V)
    (hM : Maximal IsTotSing M) : annE o M = F₂ ∙ psiE o M := by
  refine le_antisymm (fun f hf ↦ ?_)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr (psiE_spec hV hn o hM.1).1)
  by_cases hf0 : f = 0
  · rw [hf0]
    exact zero_mem _
  · rw [eq_psiE hV hn o hM hf hf0]
    exact Submodule.mem_span_singleton_self _

/-- Theorem 2.2 of `results/spinor-hull-extend.md` (organize-archive b47b504), the opposition
criterion: `⟨ψ_M, ψ_M'⟩ = 1` iff `M ∩ M' = 0` in `Ũ_n`, that is `M ⊓ M' ≤ ⟨kE⟩` in
`U ⊕ 𝔽₂ε` (`fpForm`, ham-spin 87df892). -/
theorem fpForm_psiE_eq_one_iff (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V)
    (hM : Maximal IsTotSing M) (hM' : Maximal IsTotSing M') :
    fpForm (psiE o M) (psiE o M') = 1 ↔ M ⊓ M' ≤ F₂ ∙ kE hV := by
  obtain ⟨hψ, hψ0⟩ := psiE_spec hV hn o hM.1
  obtain ⟨hψ', hψ'0⟩ := psiE_spec hV hn o hM'.1
  constructor
  · intro h x hx
    by_contra hxk
    rw [fpForm_eq_zero_of_mem_inf hV o hM.1 hx hxk hψ hψ'] at h
    exact zero_ne_one h
  · intro hopp
    rcases f2_cases' (fpForm (psiE o M) (psiE o M')) with h0 | h1
    · exact absurd (eq_zero_of_fpForm_eq_zero hV hn o hM hM' hopp hψ hψ0 hψ'
        (by rw [fpForm_comm]; exact h0)) hψ'0
    · exact h1

/-- `N′(ψ_M) = M` for a maximal totally singular `M` (§2 of `results/spinor-hull-extend.md`,
organize-archive b47b504). -/
theorem nullE_psiE (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V)
    (hM : Maximal IsTotSing M) : nullE o (psiE o M) = M := by
  obtain ⟨hψ, hψ0⟩ := psiE_spec hV hn o hM.1
  have hle : M ≤ nullE o (psiE o M) := le_nullE_iff.mpr hψ
  exact (hM.2 (isTotSing_nullE o hψ0) hle).antisymm hle

/-- `ψ_M` is a pure spinor (§2 of `results/spinor-hull-extend.md`, organize-archive b47b504). -/
theorem isPureSpinor_psiE (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V)
    (hM : Maximal IsTotSing M) : IsPureSpinor o n (psiE o M) :=
  ⟨(psiE_spec hV hn o hM.1).2, by
    rw [nullE_psiE hV hn o hM]
    exact ((maximal_isTotSing_iff hV).mp hM).2⟩

/-- A pure spinor `v` is `ψ_(N′(v))`. -/
theorem psiE_nullE (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) {o : V} {f : W V}
    (hf : IsPureSpinor o n f) : psiE o (nullE o f) = f :=
  (eq_psiE hV hn o (maximal_nullE hV hf) (le_nullE_iff.mp le_rfl) hf.1).symm

/-- The pure spinors are exactly the `ψ_M`, `M` maximal totally singular (§2 of
`results/spinor-hull-extend.md`, organize-archive b47b504). -/
theorem isPureSpinor_iff (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V) (f : W V) :
    IsPureSpinor o n f ↔ ∃ M, Maximal IsTotSing M ∧ psiE o M = f :=
  ⟨fun hf ↦ ⟨nullE o f, maximal_nullE hV hf, psiE_nullE hV hn hf⟩,
    fun ⟨_, hM, hf⟩ ↦ hf ▸ isPureSpinor_psiE hV hn o hM⟩

/-- Theorem 1.3 of `results/spinor-hull-extend.md` (organize-archive b47b504):
`Ann(M_P) = ⟨φ(P)⟩` (`rowW`, ham-spin 87df892). -/
theorem annE_liftCode_pairCode (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V)
    (P : PerfectMatching V) : annE o (liftCode (pairCode P)) = F₂ ∙ rowW P := by
  rw [annE_eq_span_psiE hV hn o (maximal_liftCode_pairCode hV P),
    ← eq_psiE hV hn o (maximal_liftCode_pairCode hV P) (rowW_mem_annE o P) (rowW_ne_zero hV hn P)]

/-- Theorem 1.4 of `results/spinor-hull-extend.md` (organize-archive b47b504):
`N′(φ(P)) = M_P` (`rowW`, ham-spin 87df892). -/
theorem nullE_rowW (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V) (P : PerfectMatching V) :
    nullE o (rowW P) = liftCode (pairCode P) := by
  rw [eq_psiE hV hn o (maximal_liftCode_pairCode hV P) (rowW_mem_annE o P) (rowW_ne_zero hV hn P),
    nullE_psiE hV hn o (maximal_liftCode_pairCode hV P)]

/-- Theorem 1 of `results/spinor-hull-extend.md` (organize-archive b47b504): every fingerprint
`φ(P)` is a pure spinor of `Ũ_n`, for odd and even `n` (`rowW`, ham-spin 87df892). -/
theorem isPureSpinor_rowW (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V)
    (P : PerfectMatching V) : IsPureSpinor o n (rowW P) := by
  rw [eq_psiE hV hn o (maximal_liftCode_pairCode hV P) (rowW_mem_annE o P) (rowW_ne_zero hV hn P)]
  exact isPureSpinor_psiE hV hn o (maximal_liftCode_pairCode hV P)

/-- `L_P = ⟨φ(P)⟩` for every perfect matching `P` of every `V` with `|V| = 2n ≥ 2`
(`matchingStar`, `rowW`, ham-spin 87df892). For `P0` on `Fin (2 * n)` this is
`finrank_matchingStar_firstBlocks` at `j = n`. -/
theorem matchingStar_edgeSet_eq_span (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n)
    (P : PerfectMatching V) : matchingStar P.toGraph.edgeSet = F₂ ∙ rowW P := by
  obtain ⟨o⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  rw [← annE_liftCode_pairCode_eq_matchingStar o P, annE_liftCode_pairCode hV hn o P]

/-- `dim L_P = 1` for every perfect matching `P` (`matchingStar`, ham-spin 87df892). -/
theorem finrank_matchingStar_edgeSet (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n)
    (P : PerfectMatching V) : finrank F₂ (matchingStar P.toGraph.edgeSet) = 1 := by
  rw [matchingStar_edgeSet_eq_span hV hn P, finrank_span_singleton (rowW_ne_zero hV hn P)]

end Opposition

end Pairing.PerfectMatching
