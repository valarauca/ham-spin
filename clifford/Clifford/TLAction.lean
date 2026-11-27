import Clifford.TemperleyLieb
import Clifford.Brauer
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Theorem B.3, `W_n ≅ Δ_2n(0) ⧸ ⟨f_3⟩ Δ_2n(0)` (COD-278)

Theorem B.3 of `results/presentation-consequences-extend.md` §3.1 (organize-archive 3ba2201),
verified in item 10 of `results/presentation-consequences-factcheck-extend.md` (3ba2201).
`Δ V = 𝔽₂[𝓜] ⧸ R_4` is the four-switch quotient, with `R4` from `Clifford/Brauer.lean`
(ham-spin 59ff171).

* The local lemma. `sym3_mem_R4` : for three points `a, b, c`, `∑_{σ ∈ Sym{a,b,c}} σ x ∈ R_4`,
  and `sum_sym3_δ_mem_R4` is its form `∑_σ e_{σP} ∈ R_4` on a matching `P`. The proof is
  `cap_ab (b c) cup_ab = 1` (`capLin_ρ_swap_cupLin`) together with Theorem C.4,
  `cup_ab cap_ab = 1 + (a b)` modulo `R_4` (`cupLin_capLin_add_mem_R4`).
* `ρΔ` : `S_V` acts on `Δ V`, since `R_4` is `S_V`-stable (`R4_le_comap`). `ρΔ_sym3` is the
  local lemma on `Δ V`.
* `tlAct n` : `TL_2n(0)` acts on `Δ_2n(0)` by `e_i ↦ 1 + (i, i+1)`. The relation
  `e_i e_(i±1) e_i = e_i` is the local lemma, and `e_i² = 0` and far commutation are automatic.
* `f3TL n hn` is `f_3` on the strands `0, 1, 2` of `TL_2n(0)`, and `tlAct_f3` : it acts as the
  three-cycle orbit sum `1 + τ₀ + τ₀²` with `τ₀ = (0 1)(1 2)`.
* `f3Delta n hn` is `⟨f_3⟩ Δ_2n(0)`, the span of `a x` over `a` in the two-sided ideal of `f_3`.
  `f3Delta_eq` : it is the image of `R_3` in `Δ_2n(0)`.
* **Theorem B.3.** `deltaQuotEquivW` : `Δ_2n(0) ⧸ ⟨f_3⟩ Δ_2n(0) ≃ W_n`, sending the class of
  `e_P` to the row `r_P` (`deltaQuotEquivW_mk`), and it is `S_2n`-equivariant
  (`deltaQuotEquivW_ρ`). `mk_mem_f3Delta_iff` : `⟨f_3⟩ Δ_2n(0)` is the radical of `H` on
  `Δ_2n(0)`, the part `rad H_n = ⟨f_3⟩ Δ_2n(0)` of B.3. The Jantzen identification
  `M̄² = rad H_n` (`results/tl-jantzen-extend.md` Theorem 3, b21b41a) is not formalized here.
-/

namespace Pairing.PerfectMatching

open Equiv

variable {V : Type*} [Fintype V] [DecidableEq V]

section Local

variable {a b c : V}

/-- `(b c)(Q ∪ ab)` sends `a` to `c`. -/
theorem swap_smul_cup_mate_left (hab : a ≠ b) (hca : c ≠ a) (Q : PerfectMatching (offPair a b)) :
    (swap b c • cup hab Q).mate a = c := by
  rw [smul_mate, swap_inv, swap_apply_of_ne_of_ne hab (Ne.symm hca), cup_mate, cupFun_left,
    swap_apply_left]

/-- `∂_ab ((b c)(Q ∪ ab)) = Q` for `c ∉ {a, b}`: the cap on `{a, b}` joins `c` back to `Q(c)`. -/
theorem boundary_swap_smul_cup (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (Q : PerfectMatching (offPair a b)) : boundary hab (swap b c • cup hab Q) = Q := by
  have hc : c ∈ offPair a b := mem_offPair.mpr ⟨hca, hcb⟩
  have hF : ∀ v, (swap b c • cup hab Q).mate v = swap b c (cupFun a b Q (swap b c v)) := fun v ↦ by
    rw [smul_mate, swap_inv, cup_mate]
  have hfix : ∀ w : offPair a b, (w : V) ≠ c → swap b c w = w := fun w hw ↦
    swap_apply_of_ne_of_ne (mem_offPair.mp w.2).2 hw
  ext x
  rw [boundary_mate]
  have hxa := (mem_offPair.mp x.2).1
  have hxb := (mem_offPair.mp x.2).2
  by_cases hxc : (x : V) = c
  · have hx : x = ⟨c, hc⟩ := Subtype.ext hxc
    have h1 : (swap b c • cup hab Q).mate x = a := by
      rw [hF, hxc, swap_apply_right, cupFun_right hab, swap_apply_of_ne_of_ne hab (Ne.symm hca)]
    have hQc : (Q.mate ⟨c, hc⟩ : V) ≠ c := fun h ↦ Q.mate_ne ⟨c, hc⟩ (Subtype.ext h)
    rw [capFun_of_eq_left _ h1, hF, swap_apply_left, cupFun_of_mem Q hc, hfix _ hQc, hx]
  · have hx : swap b c x = x := swap_apply_of_ne_of_ne hxb hxc
    by_cases hQx : (Q.mate x : V) = c
    · have h2 : (swap b c • cup hab Q).mate x = b := by
        rw [hF, hx, cupFun_of_mem Q x.2, hQx, swap_apply_right]
      rw [capFun_of_eq_right hab _ h2, swap_smul_cup_mate_left hab hca, hQx]
    · have h3 : (swap b c • cup hab Q).mate x = Q.mate x := by
        rw [hF, hx, cupFun_of_mem Q x.2, hfix _ hQx]
      rw [capFun_of_ne _ (by rw [h3]; exact (mem_offPair.mp (Q.mate x).2).1)
        (by rw [h3]; exact (mem_offPair.mp (Q.mate x).2).2), h3]

/-- `cap_ab ∘ (b c) ∘ cup_ab = 1` on `𝔽₂[𝓜(V ∖ {a, b})]` for `c ∉ {a, b}`. -/
theorem capLin_ρ_swap_cupLin (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (y : PerfectMatching (offPair a b) → F₂) : capLin hab (ρ (swap b c) (cupLin hab y)) = y := by
  rw [← sum_smul_δ y]
  simp only [map_sum, map_smul, cupLin_δ, ρ_δ, capLin_δ, capVec,
    swap_smul_cup_mate_left hab hca, hcb, ite_false, boundary_swap_smul_cup hab hca hcb]

omit [Fintype V] [DecidableEq V] in
/-- `σ (τ X) = (σ τ σ⁻¹)(σ X)`. -/
theorem smul_smul_eq_conj_smul (σ τ : Perm V) (X : PerfectMatching V) :
    σ • τ • X = (σ * τ * σ⁻¹) • σ • X := by
  rw [← mul_smul, ← mul_smul, inv_mul_cancel_right]

/-- `σ` carries the four-point orbit sum of `X` at `a, c` to that of `σ X` at `σ a, σ c`. -/
theorem ρ_fourSum (σ : Perm V) (X : PerfectMatching V) (a c : V) :
    ρ σ (fourSum X a c) = fourSum (σ • X) (σ a) (σ c) := by
  have hτ : swap (σ a) ((σ • X).mate (σ a)) * swap (σ a) (σ c) =
      σ * (swap a (X.mate a) * swap a c) * σ⁻¹ := by
    rw [smul_mate, Perm.coe_inv, symm_apply_apply, swap_apply_apply, swap_apply_apply]
    group
  rw [fourSum, fourSum, hτ, map_add, map_add, ρ_δ, ρ_δ, ρ_δ, smul_smul_eq_conj_smul,
    smul_smul_eq_conj_smul σ (_ ^ 2), conj_pow]

/-- `R_4` is `S_V`-stable. -/
theorem R4_le_comap (σ : Perm V) : R4 V ≤ (R4 V).comap (ρ σ) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨X, a, c, hca, hcX, rfl⟩
  change ρ σ _ ∈ R4 V
  rw [ρ_fourSum]
  refine Submodule.subset_span ⟨σ • X, σ a, σ c, σ.injective.ne hca, ?_, rfl⟩
  rw [smul_mate, Perm.coe_inv, symm_apply_apply]
  exact σ.injective.ne hcX

/-- **The local lemma of Theorem B.3.** For three points `a, b, c` of `V`,
`∑_{σ ∈ Sym{a,b,c}} σ x ∈ R_4` for every `x ∈ 𝔽₂[𝓜]`, where `Sym{a,b,c}` is
`1, (a b), (b c), (a b)(b c), (b c)(a b), (a b)(b c)(a b)`. On a basis vector this is
`∑_σ e_{σP} ∈ R_4` (`sum_sym3_δ_mem_R4`), the relation `e_i e_(i±1) e_i = e_i` of `TL_2n(0)` on
`Δ_2n(0) = 𝔽₂[𝓜] ⧸ R_4` that Theorem B.3 of `results/presentation-consequences-extend.md` §3.1
(organize-archive 3ba2201) uses for the action `e_i ↦ 1 + s_i`.

Proof. Write `t = (a b)`, `u = (b c)` and `N = cup_ab cap_ab`. Then
`Sym{a,b,c} = (1 + u + t u)(1 + t)`, and `(1 + t) x ≡ N x` modulo `R_4` (Theorem C.4,
`cupLin_capLin_add_mem_R4`). With `w = u N x`, `(1 + t) w ≡ cup_ab (cap_ab u cup_ab) cap_ab x
= N x`, since `cap_ab u cup_ab = 1` (`capLin_ρ_swap_cupLin`). So the sum is
`N x + (1 + t) w ≡ N x + N x = 0`, using that `R_4` is `S_V`-stable (`R4_le_comap`). This
replaces a finite check on `Fin 6`. -/
theorem sym3_mem_R4 (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (x : PerfectMatching V → F₂) :
    x + ρ (swap a b) x + ρ (swap b c) x + ρ (swap a b * swap b c) x +
      ρ (swap b c * swap a b) x + ρ (swap a b * swap b c * swap a b) x ∈ R4 V := by
  have hA := cupLin_capLin_add_mem_R4 hab x
  have hB := cupLin_capLin_add_mem_R4 hab (ρ (swap b c) (cupLin hab (capLin hab x)))
  rw [capLin_ρ_swap_cupLin hab hca hcb] at hB
  simp only [map_mul, Module.End.mul_apply]
  set y := cupLin hab (capLin hab x)
  set t := ρ (swap a b)
  set u := ρ (swap b c)
  have key : y + x + t x + u (y + x + t x) + t (u (y + x + t x)) + (y + u y + t (u y)) =
      x + t x + u x + t (u x) + u (t x) + t (u (t x)) +
        ((y + u y + t (u y)) + (y + u y + t (u y))) := by
    simp only [map_add]
    abel
  rw [add_self_F₂, add_zero] at key
  rw [← key]
  exact add_mem (add_mem (add_mem hA (R4_le_comap _ hA)) (R4_le_comap _ (R4_le_comap _ hA))) hB

/-- **The local lemma on a matching.** For three points `a, b, c` and any perfect matching `P`,
`∑_{σ ∈ Sym{a,b,c}} e_{σP} ∈ R_4` (`results/presentation-consequences-extend.md` Theorem B.3,
organize-archive 3ba2201). -/
theorem sum_sym3_δ_mem_R4 (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (P : PerfectMatching V) :
    δ P + δ (swap a b • P) + δ (swap b c • P) + δ ((swap a b * swap b c) • P) +
      δ ((swap b c * swap a b) • P) + δ ((swap a b * swap b c * swap a b) • P) ∈ R4 V := by
  have h := sym3_mem_R4 hab hca hcb (δ P)
  simp only [ρ_δ] at h
  exact h

end Local

section Quotient

variable (V) in
/-- `Δ V = 𝔽₂[𝓜] ⧸ R_4`, the four-switch quotient. On `V = Fin (2n)` it is the cell module
`Δ_2n(0) = S^(n,n)` with no through-strands (`results/presentation-consequences-extend.md`
Theorem B.3, organize-archive 3ba2201). -/
abbrev Δ : Type _ :=
  (PerfectMatching V → F₂) ⧸ R4 V

variable (V) in
/-- The action of `S_V` on `Δ V`, induced from `ρ`. -/
def ρΔ : Representation F₂ (Perm V) (Δ V) :=
  ρ.quotient (R4 V) R4_le_comap

/-- `ρΔ` on classes. -/
theorem ρΔ_mk (σ : Perm V) (f : PerfectMatching V → F₂) :
    ρΔ V σ (Submodule.Quotient.mk f) = Submodule.Quotient.mk (ρ σ f) :=
  rfl

/-- `ρΔ σ` squares to `1` for a transposition. -/
theorem ρΔ_swap_mul_self (a b : V) : ρΔ V (swap a b) * ρΔ V (swap a b) = 1 := by
  rw [← map_mul, swap_mul_self, map_one]

variable {a b c : V}

/-- The local lemma on `Δ V`: `∑_{σ ∈ Sym{a,b,c}} σ = 0` as an operator. -/
theorem ρΔ_sym3 (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    1 + ρΔ V (swap a b) + ρΔ V (swap b c) + ρΔ V (swap a b) * ρΔ V (swap b c) +
      ρΔ V (swap b c) * ρΔ V (swap a b) + ρΔ V (swap a b) * ρΔ V (swap b c) * ρΔ V (swap a b) =
      0 := by
  refine LinearMap.ext fun y ↦ ?_
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    have h := sym3_mem_R4 hab hca hcb x
    simp only [map_mul, Module.End.mul_apply] at h
    simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply, ρΔ_mk,
      LinearMap.zero_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.mk_eq_zero]
    exact h

/-- The `δ = 0` Temperley–Lieb braid relation `(1 + x)(1 + y)(1 + x) = 1 + x` from `x² = 1` and
the vanishing of the `S_3` sum `1 + x + y + x y + y x + x y x`. -/
theorem one_add_mul_mul_one_add_of_sym3 {A : Type*} [Ring A] {x y : A} (hx : x * x = 1)
    (h : 1 + x + y + x * y + y * x + x * y * x = 0) : (1 + x) * (1 + y) * (1 + x) = 1 + x := by
  calc (1 + x) * (1 + y) * (1 + x) = (1 + x + y + x * y + y * x + x * y * x) + (x + x * x) := by
        noncomm_ring
    _ = 1 + x := by rw [h, hx, zero_add, add_comm]

/-- `e_t e_u e_t = e_t` on `Δ V` for `e = 1 + ρΔ`, `t = (a b)` and `u = (b c)`. -/
theorem one_add_ρΔ_braid (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    (1 + ρΔ V (swap a b)) * (1 + ρΔ V (swap b c)) * (1 + ρΔ V (swap a b)) = 1 + ρΔ V (swap a b) :=
  one_add_mul_mul_one_add_of_sym3 (ρΔ_swap_mul_self a b) (ρΔ_sym3 hab hca hcb)

end Quotient

section Action

variable (n : ℕ)

/-- `(1 + g)² = 0` in characteristic `2` when `g² = 1`. -/
theorem one_add_mul_self_F₂ {A : Type*} [Ring A] [Algebra F₂ A] {g : A} (hg : g * g = 1) :
    (1 + g) * (1 + g) = 0 := by
  calc (1 + g) * (1 + g) = (1 + g * g) + (g + g) := by noncomm_ring
    _ = 0 := by rw [hg, add_self_F₂, add_self_F₂, add_zero]

/-- The adjacent transpositions `(i, i+1)` and `(j, j+1)` commute for `i + 2 ≤ j`. -/
theorem adjSwap_commute {i j : Fin (2 * n - 1)} (h : (i : ℕ) + 2 ≤ j) :
    Commute (Stilde.adjSwap (m := 2 * n) i) (Stilde.adjSwap j) := by
  refine (Perm.disjoint_swap_swap ?_).commute
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    not_false_eq_true, and_true, Fin.ext_iff]
  omega

/-- The braid relation for adjacent generators `e_i`, `e_j` of `TL_2n(0)` on `Δ_2n(0)`. -/
theorem one_add_ρΔ_adjSwap_braid {i j : Fin (2 * n - 1)} (h : (j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1) :
    (1 + ρΔ _ (Stilde.adjSwap i)) * (1 + ρΔ _ (Stilde.adjSwap j)) * (1 + ρΔ _ (Stilde.adjSwap i)) =
      1 + ρΔ (Fin (2 * n)) (Stilde.adjSwap i) := by
  rcases h with h | h
  · have e1 : Stilde.adjSwap (m := 2 * n) i = swap ⟨i, by omega⟩ ⟨j, by omega⟩ := by
      rw [Stilde.adjSwap]
      congr 2
      omega
    rw [e1, Stilde.adjSwap]
    exact one_add_ρΔ_braid (Fin.ne_of_val_ne (by simp; omega)) (Fin.ne_of_val_ne (by simp; omega))
      (Fin.ne_of_val_ne (by simp))
  · have e1 : Stilde.adjSwap (m := 2 * n) i = swap ⟨i + 1, by omega⟩ ⟨i, by omega⟩ := by
      rw [Stilde.adjSwap, swap_comm]
    have e2 : Stilde.adjSwap (m := 2 * n) j = swap ⟨i, by omega⟩ ⟨j, by omega⟩ := by
      rw [Stilde.adjSwap, swap_comm]
      congr 2
      omega
    rw [e1, e2]
    exact one_add_ρΔ_braid (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp; omega))
      (Fin.ne_of_val_ne (by simp; omega))

/-- **The action of `TL_2n(0)` on `Δ_2n(0)`.** `e_i ↦ 1 + (i, i+1)`, so `s_i = 1 + e_i` acts as
the transposition (`results/presentation-consequences-extend.md` Theorem B.3, organize-archive
3ba2201, after `results/tl-jantzen-extend.md` Theorem 1(c), b21b41a). The relation
`e_i e_(i±1) e_i = e_i` is the local lemma `sym3_mem_R4`. -/
noncomputable def tlAct : TL F₂ (2 * n) 0 →ₐ[F₂] Module.End F₂ (Δ (Fin (2 * n))) :=
  TL.lift (fun i ↦ 1 + ρΔ _ (Stilde.adjSwap i))
    (fun i ↦ by
      rw [zero_smul, Stilde.adjSwap]
      exact one_add_mul_self_F₂ (ρΔ_swap_mul_self _ _))
    (fun _ _ h ↦ one_add_ρΔ_adjSwap_braid n h)
    (fun i j h ↦ by
      have hc : ρΔ _ (Stilde.adjSwap i) * ρΔ (Fin (2 * n)) (Stilde.adjSwap j) =
          ρΔ _ (Stilde.adjSwap j) * ρΔ _ (Stilde.adjSwap i) := by
        rw [← map_mul, ← map_mul, (adjSwap_commute n h).eq]
      simp only [add_mul, mul_add, one_mul, mul_one, hc]
      abel)

/-- `tlAct` sends `e_i` to `1 + (i, i+1)`. -/
theorem tlAct_e (i : Fin (2 * n - 1)) :
    tlAct n (TL.e F₂ (2 * n) 0 i) = 1 + ρΔ _ (Stilde.adjSwap i) :=
  TL.lift_e _ _ _ _ i

/-- `s_i = 1 + e_i` acts as the transposition `(i, i+1)`. -/
theorem tlAct_one_add_e (i : Fin (2 * n - 1)) :
    tlAct n (1 + TL.e F₂ (2 * n) 0 i) = ρΔ _ (Stilde.adjSwap i) := by
  rw [map_add, map_one, tlAct_e, one_add_one_add_F₂]

/-- The adjacent transpositions generate `S_m` for `m ≥ 1`. -/
theorem closure_adjSwap {m : ℕ} (hm : 1 ≤ m) :
    Submonoid.closure (Set.range (Stilde.adjSwap (m := m))) = ⊤ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine top_unique ?_
  rw [← Perm.mclosure_swap_castSucc_succ k]
  refine Submonoid.closure_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, by omega⟩, rfl⟩

/-- A submodule of `Δ_2n(0)` stable under the adjacent transpositions is stable under
`TL_2n(0)`. -/
theorem le_comap_tlAct {S : Submodule F₂ (Δ (Fin (2 * n)))}
    (hS : ∀ i, S ≤ S.comap (ρΔ _ (Stilde.adjSwap i))) (c : TL F₂ (2 * n) 0) :
    S ≤ S.comap (tlAct n c) := by
  have hmk : Function.Surjective (TL.mk F₂ (2 * n) 0) := RingCon.mkₐ_surjective _
  obtain ⟨c, rfl⟩ := hmk c
  induction c using FreeAlgebra.induction with
  | grade0 r =>
    intro y hy
    rw [Submodule.mem_comap, AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply]
    exact S.smul_mem r hy
  | grade1 i =>
    intro y hy
    rw [Submodule.mem_comap]
    change tlAct n (TL.e F₂ (2 * n) 0 i) y ∈ S
    rw [tlAct_e, LinearMap.add_apply, Module.End.one_apply]
    exact S.add_mem hy (hS i hy)
  | mul a b ha hb =>
    intro y hy
    rw [Submodule.mem_comap, map_mul, map_mul, Module.End.mul_apply]
    exact ha (hb hy)
  | add a b ha hb =>
    intro y hy
    rw [Submodule.mem_comap, map_add, map_add, LinearMap.add_apply]
    exact S.add_mem (ha hy) (hb hy)

end Action

section Ideal

variable (n : ℕ) (hn : 2 ≤ n)

include hn in
/-- `f_3` on the strands `0, 1, 2` of `TL_2n(0)` over `𝔽₂`, `f_3 = 1 + e_0 e_1 + e_1 e_0` by
`jw_zero_F₂` (`results/presentation-consequences-extend.md` Theorem B.1, organize-archive
3ba2201). -/
noncomputable def f3TL : TL F₂ (2 * n) 0 :=
  jw (0 : F₂) (TL.e F₂ (2 * n) 0 ⟨0, by omega⟩) (TL.e F₂ (2 * n) 0 ⟨1, by omega⟩)

include hn in
/-- The three-cycle `τ₀ = (0 1)(1 2)` of `Fin (2n)`. -/
def τ₀ : Perm (Fin (2 * n)) :=
  Stilde.adjSwap (m := 2 * n) ⟨0, by omega⟩ * Stilde.adjSwap ⟨1, by omega⟩

/-- `τ₀` is a three-cycle. -/
theorem isThreeCycle_τ₀ : (τ₀ n hn).IsThreeCycle := by
  rw [τ₀, Stilde.adjSwap, Stilde.adjSwap, swap_comm]
  exact Perm.isThreeCycle_swap_mul_swap_same (Fin.ne_of_val_ne (by simp))
    (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))

/-- `τ₀² = (1 2)(0 1)`. -/
theorem τ₀_sq : τ₀ n hn ^ 2 = Stilde.adjSwap (m := 2 * n) ⟨1, by omega⟩ *
    Stilde.adjSwap ⟨0, by omega⟩ := by
  have h3 : τ₀ n hn ^ 3 = 1 := by
    rw [← (isThreeCycle_τ₀ n hn).orderOf, pow_orderOf_eq_one]
  have hinv : τ₀ n hn ^ 2 = (τ₀ n hn)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h3)
  rw [hinv, τ₀, mul_inv_rev, Stilde.adjSwap, Stilde.adjSwap, swap_inv, swap_inv]

/-- **`f_3` is the three-cycle orbit sum.** On `Δ_2n(0)`, `f_3` acts as `1 + τ₀ + τ₀²`, the
three-cycle element `1 + s_1 s_2 + s_2 s_1` of Theorem B.1 over `𝔽₂`. -/
theorem tlAct_f3 :
    tlAct n (f3TL n hn) = 1 + (ρΔ _ (τ₀ n hn) + ρΔ _ (τ₀ n hn ^ 2)) := by
  rw [f3TL, map_jw, tlAct_e, tlAct_e, jw_zero_F₂, add_assoc, one_add_mul_one_add_add_F₂, τ₀_sq,
    τ₀, map_mul, map_mul]

/-- `f_3` on a class, `[x] ↦ [x + τ₀ x + τ₀² x]`. -/
theorem tlAct_f3_mk (x : PerfectMatching (Fin (2 * n)) → F₂) :
    tlAct n (f3TL n hn) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (x + ρ (τ₀ n hn) x + ρ (τ₀ n hn ^ 2) x) := by
  rw [tlAct_f3, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, ρΔ_mk, ρΔ_mk,
    ← add_assoc, Submodule.Quotient.mk_add, Submodule.Quotient.mk_add]

/-- `⟨f_3⟩ Δ_2n(0)`, the span of `a x` over `a` in the two-sided ideal of `TL_2n(0)` generated by
`f_3` and `x ∈ Δ_2n(0)` (`results/presentation-consequences-extend.md` Theorem B.3,
organize-archive 3ba2201). -/
def f3Delta : Submodule F₂ (Δ (Fin (2 * n))) :=
  Submodule.span F₂ {z | ∃ a ∈ TwoSidedIdeal.span {f3TL n hn}, ∃ x, z = tlAct n a x}

/-- `⟨f_3⟩ Δ_2n(0)` is stable under `TL_2n(0)`. -/
theorem f3Delta_le_comap_tlAct (c : TL F₂ (2 * n) 0) :
    f3Delta n hn ≤ (f3Delta n hn).comap (tlAct n c) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, ha, x, rfl⟩
  change tlAct n c (tlAct n a x) ∈ f3Delta n hn
  exact Submodule.subset_span ⟨c * a, TwoSidedIdeal.mul_mem_left _ c a ha, x,
    by rw [map_mul, Module.End.mul_apply]⟩

/-- `⟨f_3⟩ Δ_2n(0)` is `S_2n`-stable, since `s_i = 1 + e_i` acts as `(i, i+1)` and these
generate `S_2n`. -/
theorem f3Delta_le_comap_ρΔ (σ : Perm (Fin (2 * n))) :
    f3Delta n hn ≤ (f3Delta n hn).comap (ρΔ _ σ) := by
  have hσ : σ ∈ Submonoid.closure (Set.range (Stilde.adjSwap (m := 2 * n))) := by
    rw [closure_adjSwap (by omega)]
    exact Submonoid.mem_top σ
  induction hσ using Submonoid.closure_induction with
  | mem s hs =>
    obtain ⟨i, rfl⟩ := hs
    rw [← tlAct_one_add_e]
    exact f3Delta_le_comap_tlAct n hn _
  | one =>
    intro y hy
    rwa [Submodule.mem_comap, map_one, Module.End.one_apply]
  | mul s t _ _ hs ht =>
    intro y hy
    rw [Submodule.mem_comap, map_mul, Module.End.mul_apply]
    exact hs (ht hy)

end Ideal

section Image

variable (V) in
/-- The image `R_3 ⧸ R_4` of `R_3` in `Δ V = 𝔽₂[𝓜] ⧸ R_4`. -/
def R3Δ : Submodule F₂ (Δ V) :=
  (R3 V).map (R4 V).mkQ

/-- `R_3 ⧸ R_4` is `S_V`-stable. -/
theorem R3Δ_le_comap (σ : Perm V) : R3Δ V ≤ (R3Δ V).comap (ρΔ V σ) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Submodule.mem_comap]
  exact Submodule.mem_map.mpr ⟨ρ σ x, R3_le_comap σ hx, rfl⟩

/-- `[x] ∈ R_3 ⧸ R_4` iff `x ∈ R_3`, as `R_4 ⊆ R_3`. -/
theorem mk_mem_R3Δ_iff (x : PerfectMatching V → F₂) :
    (Submodule.Quotient.mk x : Δ V) ∈ R3Δ V ↔ x ∈ R3 V := by
  rw [R3Δ, ← Submodule.mkQ_apply, ← Submodule.mem_comap, Submodule.comap_map_mkQ,
    sup_eq_right.mpr R4_le_R3]

/-- `x + τ x + τ² x ∈ R_3` for every three-cycle `τ`. -/
theorem orbit_mem_R3 {τ : Perm V} (hτ : τ.IsThreeCycle) (x : PerfectMatching V → F₂) :
    x + ρ τ x + ρ (τ ^ 2) x ∈ R3 V := by
  have h := LinearMap.congr_fun (isThreeCycleRep_ρQ hτ) (Submodule.Quotient.mk x)
  rw [← map_pow] at h
  simp only [LinearMap.add_apply, Module.End.one_apply, ρQ_mk, LinearMap.zero_apply,
    ← Submodule.Quotient.mk_add, Submodule.Quotient.mk_eq_zero] at h
  exact h

variable (n : ℕ) (hn : 2 ≤ n)

/-- `⟨f_3⟩ Δ_2n(0) ⊆ R_3 ⧸ R_4`: `f_3` acts as a three-cycle orbit sum, and `R_3 ⧸ R_4` is
stable under `TL_2n(0)`. -/
theorem f3Delta_le_R3Δ : f3Delta n hn ≤ R3Δ (Fin (2 * n)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, ha, x, rfl⟩
  induction ha using TwoSidedIdeal.span_induction generalizing x with
  | mem a h =>
    rw [Set.mem_singleton_iff] at h
    subst h
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [SetLike.mem_coe, tlAct_f3_mk, mk_mem_R3Δ_iff]
      exact orbit_mem_R3 (isThreeCycle_τ₀ n hn) x
  | zero =>
    rw [map_zero, LinearMap.zero_apply]
    exact zero_mem _
  | add a b _ _ iha ihb =>
    rw [map_add, LinearMap.add_apply]
    exact add_mem (iha x) (ihb x)
  | neg a _ ih =>
    rw [map_neg, LinearMap.neg_apply]
    exact neg_mem (ih x)
  | left_absorb c a _ ih =>
    rw [map_mul, Module.End.mul_apply]
    exact le_comap_tlAct n (fun i ↦ R3Δ_le_comap _) c (ih x)
  | right_absorb c a _ ih =>
    rw [map_mul, Module.End.mul_apply]
    exact ih _

/-- `R_3 ⧸ R_4 ⊆ ⟨f_3⟩ Δ_2n(0)`: every three-cycle is conjugate to `τ₀`, and `⟨f_3⟩ Δ_2n(0)` is
`S_2n`-stable. -/
theorem R3Δ_le_f3Delta : R3Δ (Fin (2 * n)) ≤ f3Delta n hn := by
  rw [R3Δ, R3, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨P, τ, hτ, rfl⟩, rfl⟩
  obtain ⟨σ, rfl⟩ := isConj_iff.mp
    (Perm.isConj_iff_cycleType_eq.mpr ((isThreeCycle_τ₀ n hn).trans hτ.symm))
  have e : ρ σ (δ (σ⁻¹ • P) + ρ (τ₀ n hn) (δ (σ⁻¹ • P)) + ρ (τ₀ n hn ^ 2) (δ (σ⁻¹ • P))) =
      δ P + δ ((σ * τ₀ n hn * σ⁻¹) • P) + δ ((σ * τ₀ n hn * σ⁻¹) ^ 2 • P) := by
    simp only [map_add, ρ_δ]
    rw [smul_smul_eq_conj_smul σ (τ₀ n hn), smul_smul_eq_conj_smul σ (τ₀ n hn ^ 2), smul_inv_smul,
      conj_pow]
  have key : (R4 _).mkQ (δ P + δ ((σ * τ₀ n hn * σ⁻¹) • P) + δ ((σ * τ₀ n hn * σ⁻¹) ^ 2 • P)) =
      ρΔ _ σ (tlAct n (f3TL n hn) (Submodule.Quotient.mk (δ (σ⁻¹ • P)))) := by
    rw [tlAct_f3_mk, ρΔ_mk, e, Submodule.mkQ_apply]
  rw [SetLike.mem_coe, key]
  exact f3Delta_le_comap_ρΔ n hn σ
    (Submodule.subset_span ⟨f3TL n hn, TwoSidedIdeal.subset_span rfl, _, rfl⟩)

/-- **`⟨f_3⟩ Δ_2n(0) = R_3 ⧸ R_4`.** The image of the two-sided ideal `⟨f_3⟩` of `TL_2n(0)`
applied to `Δ_2n(0) = 𝔽₂[𝓜] ⧸ R_4` is the image of `R_3`
(`results/presentation-consequences-extend.md` Theorem B.3 proof, organize-archive 3ba2201). -/
theorem f3Delta_eq : f3Delta n hn = R3Δ (Fin (2 * n)) :=
  le_antisymm (f3Delta_le_R3Δ n hn) (R3Δ_le_f3Delta n hn)

/-- **Theorem B.3.** `W_n ≅ Δ_2n(0) ⧸ ⟨f_3⟩ Δ_2n(0)` for `n ≥ 2`, where
`Δ_2n(0) = 𝔽₂[𝓜] ⧸ R_4` (`results/presentation-consequences-extend.md` §3.1, organize-archive
3ba2201, verified in item 10 of `results/presentation-consequences-factcheck-extend.md`,
3ba2201). It is `f3Delta_eq`, the third isomorphism theorem with `R4_le_R3`, and `ΘQEquiv`. -/
noncomputable def deltaQuotEquivW : (Δ (Fin (2 * n)) ⧸ f3Delta n hn) ≃ₗ[F₂] W (Fin (2 * n)) :=
  (Submodule.quotEquivOfEq _ _ (f3Delta_eq n hn)).trans
    ((Submodule.quotientQuotientEquivQuotient (R4 _) (R3 _) R4_le_R3).trans
      (ΘQEquiv (Fintype.card_fin (2 * n)) (by omega)))

/-- `deltaQuotEquivW` sends the class of `x` to `Θ x`, so the class of `e_P` to the row `r_P`. -/
theorem deltaQuotEquivW_mk (x : PerfectMatching (Fin (2 * n)) → F₂) :
    deltaQuotEquivW n hn (Submodule.Quotient.mk (Submodule.Quotient.mk x)) = Θ x :=
  rfl

/-- `deltaQuotEquivW` is `S_2n`-equivariant, for the action on `Δ_2n(0) ⧸ ⟨f_3⟩ Δ_2n(0)`
induced from `ρΔ`. -/
theorem deltaQuotEquivW_ρ (σ : Perm (Fin (2 * n))) (y : Δ (Fin (2 * n)) ⧸ f3Delta n hn) :
    deltaQuotEquivW n hn ((ρΔ _).quotient _ (f3Delta_le_comap_ρΔ n hn) σ y) =
      ρW σ (deltaQuotEquivW n hn y) := by
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      change deltaQuotEquivW n hn (Submodule.Quotient.mk (Submodule.Quotient.mk (ρ σ x))) = _
      rw [deltaQuotEquivW_mk, deltaQuotEquivW_mk, Θ_ρ]

/-- **`⟨f_3⟩ Δ_2n(0)` is the radical of `H`.** `[x] ∈ ⟨f_3⟩ Δ_2n(0)` iff `H(x, y) = 0` for every
`y`, the statement `rad H_n = ⟨f_3⟩ Δ_2n(0)` of `results/presentation-consequences-extend.md`
Theorem B.3 (organize-archive 3ba2201) on `Δ_2n(0)`. -/
theorem mk_mem_f3Delta_iff (x : PerfectMatching (Fin (2 * n)) → F₂) :
    (Submodule.Quotient.mk x : Δ _) ∈ f3Delta n hn ↔ ∀ y, hamForm x y = 0 := by
  rw [f3Delta_eq, mk_mem_R3Δ_iff, mem_R3_iff (Fintype.card_fin (2 * n)) (by omega)]

end Image

end Pairing.PerfectMatching
