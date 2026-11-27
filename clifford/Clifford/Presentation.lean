import Clifford.BasisFree

/-!
# Conjecture 13.2, the three-cycle presentation `W_n = 𝔽₂[𝓜_n] ⧸ R_3` (COD-275)

`R_3 ⊆ 𝔽₂^𝓜` is spanned by the orbit sums `e_P + e_{τP} + e_{τ²P}` over three-cycles `τ`, and
`Q V = 𝔽₂^𝓜 ⧸ R_3`. The row map `Θ : e_P ↦ r_P` kills `R_3` by T1 (`sum_H_isThreeCycle`), so it
factors through `Q V`. The upper-bound half of the CKN proof (`ThreeCycleRep.finrank_le` in
`Clifford.Dimension`) runs on `Q V` and gives `dim Q V ≤ 2^(n-1)`. With the CKN rank
`finrank_W_eq_of_card` the induced map `Q V → W V` is an isomorphism, so `ker Θ = R_3`.

This is Proposition A with Corollary A1 of `results/presentation-consequences-contra.md` and
Theorem A with Corollary A2 of `results/presentation-consequences-extend.md` (organize-archive
3ba2201). It needs no Clifford simplicity or Frobenius reciprocity, unlike the routes of
`results/switch-patterns-extend.md` Theorem 2.1 (3293188).

* `finrank_le_of_isThreeCycleRep` : a three-cycle representation of `S_V`, `|V| = 2n`, generated
  by a vector fixed by the edges of one matching has dimension at most `2^(n-1)`.
* `R3`, `Q`, `ρQ`, `isThreeCycleRep_ρQ` : the presented module and its `S_V` action.
* `Θ`, `R3_le_ker_Θ`, `ΘQ`, `ΘQ_ρQ` : the row map and its equivariant factorization through `Q V`.
* `finrank_Q_le`, `finrank_Q_eq` : `dim Q V = 2^(n-1)`.
* `ΘQ_bijective`, `ΘQEquiv` : `Q V ≃ W V`.
* `ker_Θ_eq_R3` : Conjecture 13.2, `ker Θ = R_3`.
* `mk_δ_eq_sum` : the normal form `e_P ≡ ∑_S H[P, X_{G∖S}] e_{X_S} (mod R_3)`.
-/

namespace Pairing.PerfectMatching

open Equiv

section Transport

variable {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']

/-- Relabelling along `f : V ≃ V'` keeps three-cycles. -/
theorem isThreeCycle_permCongr (f : V ≃ V') {τ : Perm V} (hτ : τ.IsThreeCycle) :
    (f.permCongr τ).IsThreeCycle := by
  rw [← card_support_eq_three_iff] at hτ ⊢
  have h : (f.permCongr τ).support = τ.support.map f.toEmbedding := by
    ext x
    simp [Perm.mem_support, ← f.eq_symm_apply]
  rw [h, Finset.card_map, hτ]

omit [Fintype V] [Fintype V'] in
/-- Relabelling a transposition along `f : V ≃ V'`. -/
theorem permCongr_swap (f : V ≃ V') (x y : V) : f.permCongr (swap x y) = swap (f x) (f y) := by
  ext v
  simp only [permCongr_apply, swap_apply_def, symm_apply_eq]
  split_ifs <;> simp_all

variable {M : Type*} [AddCommGroup M] [Module F₂ M]

/-- The upper bound of `results/presentation-consequences-contra.md` Proposition A
(organize-archive 3ba2201) on any vertex type. If `|V| = 2n`, `1 + τ + τ² = 0` for every
three-cycle `τ`, and `M` is spanned by the orbit of a vector `e` fixed by the edges of a matching
`P`, then `dim M ≤ 2^(n-1)`. Transported from `ThreeCycleRep.finrank_le`. -/
theorem finrank_le_of_isThreeCycleRep {n : ℕ} (hV : Fintype.card V = 2 * n)
    {ρM : Representation F₂ (Perm V) M} (h3 : IsThreeCycleRep ρM) (P : PerfectMatching V) {e : M}
    (he : ∀ v, ρM (swap v (P.mate v)) e = e)
    (hgen : Submodule.span F₂ (Set.range fun σ ↦ ρM σ e) = ⊤) :
    Module.finrank F₂ M ≤ 2 ^ (n - 1) := by
  set f₀ := Fintype.equivFinOfCardEq hV
  obtain ⟨c, hc⟩ := exists_smul_eq (n := n) (by simp) (congr f₀ P) (P0 n)
  set f : V ≃ Fin (2 * n) := f₀.trans c
  have hf : congr f P = P0 n := by
    rw [← hc]
    ext v
    simp [f, smul_mate, Perm.inv_def]
  let ρ' : Representation F₂ (Perm (Fin (2 * n))) M := ρM.comp f.symm.permCongrHom.toMonoidHom
  refine ThreeCycleRep.finrank_le n (ρM := ρ') (e := e) ?_ ?_ ?_
  · exact fun τ hτ ↦ h3 (isThreeCycle_permCongr f.symm hτ)
  · intro a
    change ρM (f.symm.permCongr (swap (blockLo n a) (blockHi n a))) e = e
    have hm : f.symm (blockHi n a) = P.mate (f.symm (blockLo n a)) := by
      rw [← P0_mate_blockLo, ← hf, congr_mate, symm_apply_apply]
    rw [permCongr_swap, hm]
    exact he _
  · rw [eq_top_iff, ← hgen, Submodule.span_le]
    rintro _ ⟨σ, rfl⟩
    refine Submodule.subset_span ⟨f.permCongr σ, ?_⟩
    change ρM (f.symm.permCongr (f.permCongr σ)) e = ρM σ e
    rw [← permCongr_symm, symm_apply_apply]

end Transport

section Presentation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The basis vector `e_P` of `𝔽₂^𝓜`. -/
def δ (P : PerfectMatching V) : PerfectMatching V → F₂ :=
  Pi.single P 1

/-- `σ e_P = e_{σP}`. -/
theorem ρ_δ (σ : Perm V) (P : PerfectMatching V) : ρ σ (δ P) = δ (σ • P) := by
  funext Q
  simp only [ρ_apply, δ, Pi.single_apply, inv_smul_eq_iff]

/-- `f = ∑_P f(P) e_P`. -/
theorem sum_smul_δ (f : PerfectMatching V → F₂) : ∑ P, f P • δ P = f := by
  funext Q
  simp [δ, Pi.single_apply]

variable (V) in
/-- `R_3`, the span of the three-cycle orbit sums `e_P + e_{τP} + e_{τ²P}`
(`results/presentation-consequences-extend.md` §0, organize-archive 3ba2201). -/
def R3 : Submodule F₂ (PerfectMatching V → F₂) :=
  Submodule.span F₂ {f | ∃ P : PerfectMatching V, ∃ τ : Perm V, τ.IsThreeCycle ∧
    f = δ P + δ (τ • P) + δ (τ ^ 2 • P)}

/-- An orbit sum lies in `R_3`. -/
theorem orbitSum_mem_R3 (P : PerfectMatching V) {τ : Perm V} (hτ : τ.IsThreeCycle) :
    δ P + δ (τ • P) + δ (τ ^ 2 • P) ∈ R3 V :=
  Submodule.subset_span ⟨P, τ, hτ, rfl⟩

/-- `R_3` is `S_V`-stable, since conjugates of three-cycles are three-cycles. -/
theorem R3_le_comap (σ : Perm V) : R3 V ≤ (R3 V).comap (ρ σ) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨P, τ, hτ, rfl⟩
  have hτ' : (σ * τ * σ⁻¹).IsThreeCycle := by
    unfold Perm.IsThreeCycle
    rw [Perm.cycleType_conj]
    exact hτ
  have e1 : σ • τ • P = (σ * τ * σ⁻¹) • σ • P := by simp [mul_smul]
  have e2 : σ • τ ^ 2 • P = (σ * τ * σ⁻¹) ^ 2 • σ • P := by simp [pow_two, mul_smul]
  change ρ σ _ ∈ R3 V
  rw [map_add, map_add, ρ_δ, ρ_δ, ρ_δ, e1, e2]
  exact orbitSum_mem_R3 _ hτ'

variable (V) in
/-- `Q V = 𝔽₂[𝓜] ⧸ R_3`, the three-cycle presentation of archive Conjecture 13.2
(`results/presentation-consequences-contra.md` §1, organize-archive 3ba2201). -/
abbrev Q : Type _ :=
  (PerfectMatching V → F₂) ⧸ R3 V

variable (V) in
/-- The action of `S_V` on `Q V`, induced from `ρ`. -/
def ρQ : Representation F₂ (Perm V) (Q V) :=
  ρ.quotient (R3 V) R3_le_comap

/-- `ρQ` on classes. -/
theorem ρQ_mk (σ : Perm V) (f : PerfectMatching V → F₂) :
    ρQ V σ (Submodule.Quotient.mk f) = Submodule.Quotient.mk (ρ σ f) :=
  rfl

/-- `1 + τ + τ² = 0` on `Q V` for every three-cycle `τ`, by definition of `R_3`. -/
theorem isThreeCycleRep_ρQ : IsThreeCycleRep (ρQ V) := by
  intro τ hτ
  refine LinearMap.ext fun x ↦ ?_
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    have hf : f + ρ τ f + ρ τ (ρ τ f) ∈ R3 V := by
      rw [← sum_smul_δ f]
      simp only [map_sum, map_smul, ← Finset.sum_add_distrib, ← smul_add]
      refine Submodule.sum_mem _ fun P _ ↦ Submodule.smul_mem _ _ ?_
      rw [ρ_δ, ρ_δ, smul_smul, ← pow_two]
      exact orbitSum_mem_R3 P hτ
    simp only [LinearMap.add_apply, Module.End.one_apply, pow_two, Module.End.mul_apply, ρQ_mk,
      LinearMap.zero_apply]
    rw [← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_add, Submodule.Quotient.mk_eq_zero]
    exact hf

/-- `Q V` is spanned by the `S_V`-orbit of the class of `e_P`, for any matching `P`. -/
theorem span_orbit_mk_δ {n : ℕ} (hV : Fintype.card V = 2 * n) (P : PerfectMatching V) :
    Submodule.span F₂ (Set.range fun σ ↦ ρQ V σ (Submodule.Quotient.mk (δ P))) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    rw [← sum_smul_δ f]
    change (R3 V).mkQ _ ∈ _
    rw [map_sum]
    refine Submodule.sum_mem _ fun R _ ↦ ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    obtain ⟨c, rfl⟩ := exists_smul_eq hV P R
    exact ⟨c, by simp only [ρQ_mk, ρ_δ, Submodule.mkQ_apply]⟩

/-- The upper bound on the presented module, `dim Q V ≤ 2^(n-1)` when `|V| = 2n`
(`results/presentation-consequences-contra.md` Corollary A1 step 1, organize-archive 3ba2201). -/
theorem finrank_Q_le {n : ℕ} (hV : Fintype.card V = 2 * n) :
    Module.finrank F₂ (Q V) ≤ 2 ^ (n - 1) := by
  have P := congr (Fintype.equivFinOfCardEq hV).symm (P0 n)
  refine finrank_le_of_isThreeCycleRep hV isThreeCycleRep_ρQ P (fun v ↦ ?_) (span_orbit_mk_δ hV P)
  rw [ρQ_mk, ρ_δ, swap_mate_smul]

/-- The row map `Θ : 𝔽₂[𝓜] → W`, `e_P ↦ r_P`. -/
def Θ : (PerfectMatching V → F₂) →ₗ[F₂] W V :=
  Fintype.linearCombination F₂ (rowW (V := V))

/-- `Θ e_P = r_P`. -/
theorem Θ_δ (P : PerfectMatching V) : Θ (δ P) = rowW P := by
  rw [Θ, δ, Fintype.linearCombination_apply_single, one_smul]

/-- `Θ` kills `R_3`, by T1 (`row_sum_isThreeCycle`). -/
theorem R3_le_ker_Θ : R3 V ≤ LinearMap.ker (Θ (V := V)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨P, τ, hτ, rfl⟩
  change Θ _ = 0
  rw [map_add, map_add, Θ_δ, Θ_δ, Θ_δ]
  exact Subtype.ext (row_sum_isThreeCycle hτ P)

/-- `Θ` is onto `W`. -/
theorem Θ_surjective : Function.Surjective (Θ (V := V)) := by
  rw [← LinearMap.range_eq_top, Θ, Fintype.range_linearCombination, span_rowW]

/-- The induced map `Q V → W V`, the class of `e_P` going to `r_P`. -/
def ΘQ : Q V →ₗ[F₂] W V :=
  (R3 V).liftQ Θ R3_le_ker_Θ

/-- `ΘQ` on classes. -/
theorem ΘQ_mk (f : PerfectMatching V → F₂) : ΘQ (Submodule.Quotient.mk f : Q V) = Θ f :=
  rfl

/-- `Θ` is `S_V`-equivariant. -/
theorem Θ_ρ (σ : Perm V) (f : PerfectMatching V → F₂) : Θ (ρ σ f) = ρW σ (Θ f) := by
  rw [← sum_smul_δ f]
  simp only [map_sum, map_smul, ρ_δ, Θ_δ, ρW_rowW]

/-- `ΘQ` is `S_V`-equivariant. -/
theorem ΘQ_ρQ (σ : Perm V) (x : Q V) : ΘQ (ρQ V σ x) = ρW σ (ΘQ x) := by
  induction x using Submodule.Quotient.induction_on with
  | H f => rw [ρQ_mk, ΘQ_mk, ΘQ_mk, Θ_ρ]

/-- `ΘQ` is onto `W`. -/
theorem ΘQ_surjective : Function.Surjective (ΘQ (V := V)) := by
  intro y
  obtain ⟨f, rfl⟩ := Θ_surjective y
  exact ⟨Submodule.Quotient.mk f, rfl⟩

/-- `dim Q V = 2^(n-1)` for `|V| = 2n`, `n ≥ 1`: the upper bound `finrank_Q_le` against the CKN
rank `finrank_W_eq_of_card` through the surjection `ΘQ`. -/
theorem finrank_Q_eq {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) :
    Module.finrank F₂ (Q V) = 2 ^ (n - 1) := by
  refine le_antisymm (finrank_Q_le hV) ?_
  have h := LinearMap.finrank_range_le (ΘQ (V := V))
  rwa [LinearMap.range_eq_top.mpr ΘQ_surjective, finrank_top, finrank_W_eq_of_card hV hn] at h

/-- The induced map `Q V → W V` is bijective for `|V| = 2n`, `n ≥ 1`
(`results/presentation-consequences-contra.md` Corollary A1, organize-archive 3ba2201). -/
theorem ΘQ_bijective {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) :
    Function.Bijective (ΘQ (V := V)) := by
  refine ⟨?_, ΘQ_surjective⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr ΘQ_surjective
  rw [finrank_Q_eq hV hn, finrank_W_eq_of_card hV hn]

/-- `Q V ≃ W V`, the three-cycle presentation of `W_n` (archive Conjecture 13.2,
`results/presentation-consequences-extend.md` Corollary A2, organize-archive 3ba2201). -/
noncomputable def ΘQEquiv {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) : Q V ≃ₗ[F₂] W V :=
  LinearEquiv.ofBijective ΘQ (ΘQ_bijective hV hn)

/-- `ΘQEquiv` sends the class of `e_P` to `r_P`. -/
theorem ΘQEquiv_mk_δ {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (P : PerfectMatching V) :
    ΘQEquiv hV hn (Submodule.Quotient.mk (δ P)) = rowW P :=
  Θ_δ P

/-- Archive Conjecture 13.2: for `|V| = 2n`, `n ≥ 1`, the kernel of `e_P ↦ r_P` is `R_3`
(`results/presentation-consequences-contra.md` Corollary A1 and
`results/presentation-consequences-extend.md` Corollary A2, organize-archive 3ba2201; previously
through Clifford simplicity in `results/switch-patterns-extend.md` Theorem 2.1, 3293188). -/
theorem ker_Θ_eq_R3 {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) :
    LinearMap.ker (Θ (V := V)) = R3 V := by
  refine le_antisymm (fun x hx ↦ ?_) R3_le_ker_Θ
  have hx' : ΘQ (Submodule.Quotient.mk x : Q V) = ΘQ 0 := by
    rw [map_zero]
    exact hx
  exact (Submodule.Quotient.mk_eq_zero _).mp ((ΘQ_bijective hV hn).1 hx')

end Presentation

section NormalForm

variable (n : ℕ)

/-- The coordinates of a row in the basis `wBasis`, `r_P = ∑_S H[P, X_{G∖S}] w_S`. This is CKN's
factorization (arXiv:1211.1506, §3.1), read off the Gram identity `H_X`. -/
theorem rowW_eq_sum (hn : 1 ≤ n) (P : PerfectMatching (Fin (2 * n))) :
    rowW P = ∑ S, H P (X n Sᶜ) • w n S := by
  have key : ∀ S, (wBasis n hn).repr (rowW P) S = H P (X n Sᶜ) := by
    intro S
    have h := congrArg (fun f : W (Fin (2 * n)) ↦ (f : PerfectMatching (Fin (2 * n)) → F₂) (X n Sᶜ))
      ((wBasis n hn).sum_repr (rowW P))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      wBasis_apply, w, coe_rowW, H_X n hn, symmDiff_compl_eq_univ, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    exact h
  conv_lhs => rw [← (wBasis n hn).sum_repr (rowW P)]
  simp only [key, wBasis_apply]

/-- The normal form modulo `R_3`, `e_P ≡ ∑_S H[P, X_{G∖S}] e_{X_S}`
(`results/presentation-consequences-extend.md` Corollary A2, organize-archive 3ba2201). -/
theorem mk_δ_eq_sum (hn : 1 ≤ n) (P : PerfectMatching (Fin (2 * n))) :
    (Submodule.Quotient.mk (δ P) : Q (Fin (2 * n))) =
      ∑ S, H P (X n Sᶜ) • Submodule.Quotient.mk (δ (X n S)) := by
  apply (ΘQ_bijective (V := Fin (2 * n)) (by simp) hn).1
  simp only [map_sum, map_smul, ΘQ_mk, Θ_δ]
  exact rowW_eq_sum n hn P

end NormalForm

end Pairing.PerfectMatching
