import Clifford.Assembly
import Clifford.BasisFree

/-!
# C2 / T4. Absolute irreducibility (sketch §6)

* `adjoin_ρW_eq_top` : `ρ(𝔽₂ S_{2n}) = End_{𝔽₂}(W_n)`. This is Burnside's form of absolute
  irreducibility, and it survives every extension of scalars.
* `invariant_eq_bot_or_top` : every `S_{2n}`-invariant subspace of `W_n` is `0` or `W_n`.
* `nontrivial_W` and `finrank_W_eq` (COD-103) : `W_n ≠ 0` and `dim W_n = 2^(n-1)`.
* `nontrivial_W_of_card`, `adjoin_ρW_eq_top_of_card`, `preserves_of_invariant_of_card` and
  `invariant_eq_bot_or_top_of_card` : the same for any vertex type `V` with `|V| = 2n`. The first
  two are transported along `wCongr`, and the `Fin (2 * n)` forms of the last two are their
  corollaries.

The rank of `H` enters only through `finrank_W_eq`, which is proved, so no `[EXT]` input remains.
-/

namespace Pairing.PerfectMatching

open Equiv

variable (n : ℕ)

theorem frameAlg_le_adjoin :
    frameAlg n ≤ Algebra.adjoin F₂ (Set.range (ρW (V := Fin (2 * n)))) := by
  apply Algebra.adjoin_le
  rintro x (⟨k, rfl⟩ | ⟨k, rfl⟩)
  · exact Subalgebra.sum_mem _ fun a _ ↦ Algebra.subset_adjoin ⟨_, rfl⟩
  · exact Algebra.subset_adjoin ⟨_, rfl⟩

/-- T4. `ρ(𝔽₂ S_{2n}) = End(W_n)`. -/
theorem adjoin_ρW_eq_top (hn : 1 ≤ n) :
    Algebra.adjoin F₂ (Set.range (ρW (V := Fin (2 * n)))) = ⊤ :=
  top_le_iff.mp (adjoin_frame_eq_top n hn ▸ frameAlg_le_adjoin n)

section Card

variable {V : Type*} [Fintype V] [DecidableEq V] {n}

/-- `W V ≠ 0` for any vertex type with `|V| = 2n` and `n ≥ 1`, from `finrank_W_eq_of_card`. -/
theorem nontrivial_W_of_card (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) : Nontrivial (W V) :=
  Module.nontrivial_of_finrank_pos (R := F₂) (by rw [finrank_W_eq_of_card hV hn]; positivity)

/-- T4 for any vertex type with `|V| = 2n` and `n ≥ 1`, `ρ(𝔽₂ S_V) = End(W V)`. Conjugation by
`wCongr` carries `ρ(𝔽₂ S_{2n})` onto `ρ(𝔽₂ S_V)`, so this is `adjoin_ρW_eq_top` transported. -/
theorem adjoin_ρW_eq_top_of_card (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) :
    Algebra.adjoin F₂ (Set.range (ρW (V := V))) = ⊤ := by
  set e := (Fintype.equivFinOfCardEq hV).symm
  set φ : Module.End F₂ (W (Fin (2 * n))) →ₐ[F₂] Module.End F₂ (W V) :=
    ((wCongr e).conjAlgEquiv F₂).toAlgHom
  have h : Set.range (ρW (V := V)) = φ '' Set.range (ρW (V := Fin (2 * n))) := by
    rw [← Set.range_comp, ← e.permCongr.surjective.range_comp]
    congr 1
  rw [h, Algebra.adjoin_image, adjoin_ρW_eq_top n hn, Algebra.map_top, AlgHom.range_eq_top]
  exact ((wCongr e).conjAlgEquiv F₂).surjective

/-- Every endomorphism of `W V` is a polynomial in the `ρ(σ)`, so it preserves any
`S_V`-invariant subspace. -/
theorem preserves_of_invariant_of_card (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n)
    (M : Submodule F₂ (W V)) (hM : ∀ σ : Perm V, ∀ x ∈ M, ρW σ x ∈ M)
    (f : Module.End F₂ (W V)) : ∀ x ∈ M, f x ∈ M := by
  have hf : f ∈ Algebra.adjoin F₂ (Set.range (ρW (V := V))) := by
    rw [adjoin_ρW_eq_top_of_card hV hn]
    exact Algebra.mem_top
  induction hf using Algebra.adjoin_induction with
  | mem g hg =>
    obtain ⟨σ, rfl⟩ := hg
    exact hM σ
  | algebraMap c =>
    intro x hx
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact M.smul_mem c hx
  | add f g _ _ hf hg =>
    intro x hx
    rw [LinearMap.add_apply]
    exact add_mem (hf x hx) (hg x hx)
  | mul f g _ _ hf hg =>
    intro x hx
    rw [Module.End.mul_apply]
    exact hf _ (hg x hx)

/-- `W V` is irreducible for any vertex type with `|V| = 2n` and `n ≥ 1`. -/
theorem invariant_eq_bot_or_top_of_card (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n)
    (M : Submodule F₂ (W V)) (hM : ∀ σ : Perm V, ∀ x ∈ M, ρW σ x ∈ M) : M = ⊥ ∨ M = ⊤ := by
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual F₂ (W V), φ m ≠ 0 := by
    by_contra! h
    exact hm0 ((Module.forall_dual_apply_eq_zero_iff F₂ m).mp h)
  rw [eq_top_iff]
  intro x _
  have hx := preserves_of_invariant_of_card hV hn M hM ((φ m)⁻¹ • φ.smulRight x) m hm
  rwa [LinearMap.smul_apply, LinearMap.smulRight_apply, smul_smul, inv_mul_cancel₀ hφ,
    one_smul] at hx

end Card

theorem nontrivial_W (hn : 1 ≤ n) : Nontrivial (W (Fin (2 * n))) :=
  nontrivial_W_of_card (Fintype.card_fin _) hn

/-- Every endomorphism of `W_n` is a polynomial in the `ρ(σ)`, so it preserves any
`S_{2n}`-invariant subspace. -/
theorem preserves_of_invariant (hn : 1 ≤ n) (M : Submodule F₂ (W (Fin (2 * n))))
    (hM : ∀ σ : Perm (Fin (2 * n)), ∀ x ∈ M, ρW σ x ∈ M) (f : Module.End F₂ (W (Fin (2 * n)))) :
    ∀ x ∈ M, f x ∈ M :=
  preserves_of_invariant_of_card (Fintype.card_fin _) hn M hM f

/-- `W_n` is irreducible. -/
theorem invariant_eq_bot_or_top (hn : 1 ≤ n) (M : Submodule F₂ (W (Fin (2 * n))))
    (hM : ∀ σ : Perm (Fin (2 * n)), ∀ x ∈ M, ρW σ x ∈ M) : M = ⊥ ∨ M = ⊤ :=
  invariant_eq_bot_or_top_of_card (Fintype.card_fin _) hn M hM

end Pairing.PerfectMatching
