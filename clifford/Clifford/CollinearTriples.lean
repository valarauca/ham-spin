import Clifford.PureSpinor
import Clifford.ThreeCycle
import Pairing.InvolutionProduct

/-!
# Collinear triples of fingerprints (COD-299)

Theorem 3.2 of `results/audit-conjectures-extend.md` (organize-archive ad11c88), with the
correction of step 6 in `results/audit-conjectures-factcheck-extend.md` (ad11c88). Let `|V| = 2n`.
For distinct perfect matchings `P₁, P₂, P₃`, `φ(P₁) + φ(P₂) + φ(P₃) = 0` iff `{P₁, P₂, P₃}` is
one three-cycle orbit `{P, τP, τ²P}`. Here `φ(P) = rowW P` (ham-spin 87df892).

* `rowW_add_add_eq_zero_of_isThreeCycle` : the "if" half, from the three-cycle law
  `row_sum_isThreeCycle` (`Clifford.ThreeCycle`).
* Step 1. `pairCode_inf_le_of_rowW_eq_add` : `i₂(P₁) ∩ i₂(P₂) ⊆ i₂(P₃)`, since
  `M_(P₁) ∩ M_(P₂)` kills `φ(P₃)` and `N′(φ(P₃)) = M_(P₃)` (`nullE_rowW`).
  `mate_eq_of_rowW_eq_add` : a common edge of `P₁` and `P₂` is an edge of `P₃`.
* Lemma 3.1, in the form used by step 3. `le_finrank_nullE_inf_add_two` : if `φ(P₁) + φ(P₂)` is
  a fingerprint, then `dim(M_(P₁) ∩ M_(P₂)) ≥ n - 2` in `U ⊕ 𝔽₂ε`, that is the dual polar
  distance of `M_(P₁)` and `M_(P₂)` is at most `2`.
* `finrank_pairCode_inf_le_cycleCount` : `dim(i₂(P) ∩ i₂(Q)) ≤ κ(P ∪ Q)`, as a word in both codes
  is constant on each component of `P ∪ Q`. So `le_cycleCount_add_two` : step 3,
  `κ(P₁ ∪ P₂) ≥ n - 2`.
* `exists_isThreeCycle_of_rowW_add_add_eq_zero` and `rowW_add_add_eq_zero_iff` : Theorem 3.2.
  The bound of step 3 leaves one 4-cycle, one 6-cycle or two 4-cycles in `P₁ ∪ P₂` besides the
  common edges (`sum_card_reachable_le` counts components). For one cycle the three-cycle `τ` is
  written down (`smul_eq_of_block`), and `P₃ = τ² P₁` by injectivity of `φ` (`rowW_injective`).
  For two 4-cycles, step 1 fixes `P₃` (`block_mate_third`), so `P₂ = σ P₁` and `P₃ = σ² P₁` for
  `σ = τ_A τ_B`, and the three-cycle law gives `φ(τ_A P₁) = φ(τ_B P₁)`
  (`smul_eq_smul_of_rowW`), which is false. This replaces the test matching of step 6, whose
  corrected form is `Q′ = {15, 28, 36, 47}` in `results/audit-conjectures-factcheck-extend.md`
  (ad11c88).

Proposition 3.3 of the source (the 4-dimensional subspaces inside `Φ_n ∪ {0}`) is not formalized.
-/

namespace Pairing.PerfectMatching

open Module Equiv

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

/-- The "if" half of Theorem 3.2 of `results/audit-conjectures-extend.md` (organize-archive
ad11c88): a three-cycle orbit `P, τP, τ²P` has `φ(P) + φ(τP) + φ(τ²P) = 0` (`rowW`,
`row_sum_isThreeCycle`, ham-spin 87df892). -/
theorem rowW_add_add_eq_zero_of_isThreeCycle {τ : Perm V} (hτ : τ.IsThreeCycle)
    (P : PerfectMatching V) : rowW P + rowW (τ • P) + rowW (τ ^ 2 • P) = 0 :=
  Subtype.ext (row_sum_isThreeCycle hτ P)

private theorem f2_add_self (a : F₂) : a + a = 0 := by
  revert a
  decide

private theorem add_self_W (f : W V) : f + f = 0 :=
  Subtype.ext (funext fun _ ↦ f2_add_self _)

/-- `N′(f) ∩ N′(g) ≤ N′(f + g)`. -/
theorem nullE_inf_le_nullE_add (o : V) (f g : W V) : nullE o f ⊓ nullE o g ≤ nullE o (f + g) :=
  fun z hz ↦ by
    rw [mem_nullE, map_add, mem_nullE.mp hz.1, mem_nullE.mp hz.2, add_zero]

/-- Step 1 of Theorem 3.2 of `results/audit-conjectures-extend.md` (organize-archive ad11c88).
If `φ(P₃) = φ(P₁) + φ(P₂)`, then `i₂(P₁) ∩ i₂(P₂) ⊆ i₂(P₃)`: `M_(P₁) ∩ M_(P₂)` kills `φ(P₃)`,
and `N′(φ(P₃)) = M_(P₃)` (`nullE_rowW`, `pairCode`, `liftCode`, ham-spin 87df892). -/
theorem pairCode_inf_le_of_rowW_eq_add (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n)
    {P₁ P₂ P₃ : PerfectMatching V} (h : rowW P₃ = rowW P₁ + rowW P₂) :
    pairCode P₁ ⊓ pairCode P₂ ≤ pairCode P₃ := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨o⟩ := hne
  have hs : ∀ P : PerfectMatching V, IsSelfOrth (pairCode P) := fun P ↦
    (isSelfDual_pairCode P).isSelfOrth
  rw [← liftCode_le_liftCode_iff ((hs P₁).mono inf_le_left) (hs P₃), liftCode_inf (hs P₁) (hs P₂),
    ← nullE_rowW hV hn o, ← nullE_rowW hV hn o, ← nullE_rowW hV hn o, h]
  exact nullE_inf_le_nullE_add o _ _

/-- Step 1 of Theorem 3.2 of `results/audit-conjectures-extend.md` (organize-archive ad11c88),
edge form. If `φ(P₃) = φ(P₁) + φ(P₂)` and `P₁`, `P₂` share the edge at `u`, then `P₃` has it too
(`rowW`, ham-spin 87df892). -/
theorem mate_eq_of_rowW_eq_add (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n)
    {P₁ P₂ P₃ : PerfectMatching V} (h : rowW P₃ = rowW P₁ + rowW P₂) {u : V}
    (hu : P₁.mate u = P₂.mate u) : P₃.mate u = P₁.mate u := by
  have hx : v u (P₁.mate u) ∈ pairCode P₁ ⊓ pairCode P₂ :=
    ⟨v_mate_mem_pairCode P₁ u, by rw [hu]; exact v_mate_mem_pairCode P₂ u⟩
  have h3 := (mem_pairCode.mp (pairCode_inf_le_of_rowW_eq_add hV hn h hx)) u
  have hu1 : u ≠ P₁.mate u := (P₁.mate_ne u).symm
  by_contra hne
  have hu3 : P₃.mate u ≠ u := P₃.mate_ne u
  simp [v, hne, hu3, hu1] at h3

private theorem finrank_le_finrank_inf_ker_add_one {E : Type*} [AddCommGroup E] [Module F₂ E]
    [FiniteDimensional F₂ E] (M : Submodule F₂ E) (f : E →ₗ[F₂] F₂) :
    finrank F₂ M ≤ finrank F₂ ↥(M ⊓ LinearMap.ker f) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq M (LinearMap.ker f)
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 := Submodule.finrank_le (LinearMap.range f)
  have h4 := Submodule.finrank_le (M ⊔ LinearMap.ker f)
  rw [Module.finrank_self] at h3
  omega

/-- Lemma 3.1 of `results/audit-conjectures-extend.md` (organize-archive ad11c88), in the form
step 3 of Theorem 3.2 uses. If `φ(P₃) = φ(P₁) + φ(P₂)`, then `dim(M_(P₁) ∩ M_(P₂)) ≥ n - 2` in
`U ⊕ 𝔽₂ε`, with `M_(P) = N′(φ(P))` (`nullE`, `rowW`, ham-spin 87df892). For `z ∈ N′(φ(P₃))`,
`w = Γ̃(z)φ(P₁) = Γ̃(z)φ(P₂)` is killed by `(M_(P₁) ∩ z^⊥) + (M_(P₂) ∩ z^⊥)`. If some `w ≠ 0`,
`N′(w)` is totally singular, of dimension at most `n`. Otherwise `N′(φ(P₃)) ≤ M_(P₁) ∩ M_(P₂)`. -/
theorem le_finrank_nullE_inf_add_two (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) (o : V)
    {P₁ P₂ P₃ : PerfectMatching V} (h : rowW P₃ = rowW P₁ + rowW P₂) :
    n ≤ finrank F₂ ↥(nullE o (rowW P₁) ⊓ nullE o (rowW P₂)) + 2 := by
  have hd : ∀ P : PerfectMatching V, finrank F₂ (nullE o (rowW P)) = n := fun P ↦
    (isPureSpinor_rowW hV hn o P).2
  have h2 : rowW P₂ = rowW P₃ + rowW P₁ := by
    rw [h, add_comm (rowW P₁), add_assoc, add_self_W, add_zero]
  by_cases hall : ∀ z ∈ nullE o (rowW P₃), gammaE o z (rowW P₁) = 0
  · have hle : nullE o (rowW P₃) ≤ nullE o (rowW P₁) ⊓ nullE o (rowW P₂) := fun z hz ↦
      ⟨hall z hz, by
        change gammaE o z (rowW P₂) = 0
        rw [h2, map_add, mem_nullE.mp hz, hall z hz, add_zero]⟩
    have := Submodule.finrank_mono hle
    rw [hd P₃] at this
    omega
  · push Not at hall
    obtain ⟨z, hz, hw⟩ := hall
    have hw2 : gammaE o z (rowW P₂) = gammaE o z (rowW P₁) := by
      rw [h2, map_add, mem_nullE.mp hz, zero_add]
    let f : U V × F₂ →ₗ[F₂] F₂ := QuadraticMap.polarBilin (qE V) z
    have key : ∀ P : PerfectMatching V, gammaE o z (rowW P) = gammaE o z (rowW P₁) →
        nullE o (rowW P) ⊓ LinearMap.ker f ≤ nullE o (gammaE o z (rowW P₁)) := by
      intro P hP a ha
      have hac := LinearMap.congr_fun (gammaE_anticomm o a z) (rowW P)
      have ha0 : gammaE o a (rowW P) = 0 := ha.1
      have hpol : QuadraticMap.polar (qE V) a z = 0 := by
        rw [QuadraticMap.polar_comm]
        exact LinearMap.mem_ker.mp ha.2
      rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, hP, ha0, map_zero,
        add_zero, hpol, zero_smul, LinearMap.zero_apply] at hac
      exact hac
    have hS := sup_le (key P₁ rfl) (key P₂ hw2)
    have hSd := (Submodule.finrank_mono hS).trans (finrank_nullE_le hV o hw)
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (nullE o (rowW P₁) ⊓ LinearMap.ker f)
      (nullE o (rowW P₂) ⊓ LinearMap.ker f)
    have hinf : (nullE o (rowW P₁) ⊓ LinearMap.ker f) ⊓ (nullE o (rowW P₂) ⊓ LinearMap.ker f) ≤
        nullE o (rowW P₁) ⊓ nullE o (rowW P₂) :=
      inf_le_inf inf_le_left inf_le_left
    have hi := Submodule.finrank_mono hinf
    have h1 := finrank_le_finrank_inf_ker_add_one (nullE o (rowW P₁)) f
    have h2' := finrank_le_finrank_inf_ker_add_one (nullE o (rowW P₂)) f
    rw [hd] at h1 h2'
    omega

omit [Fintype V] [DecidableEq V] in
/-- `dim(i₂(P) ∩ i₂(Q)) ≤ κ(P ∪ Q)` (`pairCode`, ham-spin 87df892; `cycleCount`): a word that is a
union of `P`-edges and of `Q`-edges is constant on each component of `P ∪ Q`. -/
theorem finrank_pairCode_inf_le_cycleCount [Finite V] (P Q : PerfectMatching V) :
    finrank F₂ ↥(pairCode P ⊓ pairCode Q) ≤ cycleCount P Q := by
  let G := P.toGraph ⊔ Q.toGraph
  have : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let Φ : (G.ConnectedComponent → F₂) →ₗ[F₂] (V → F₂) :=
    LinearMap.funLeft F₂ F₂ G.connectedComponentMk
  have hle : pairCode P ⊓ pairCode Q ≤ LinearMap.range Φ := by
    intro x hx
    have hP := mem_pairCode.mp hx.1
    have hQ := mem_pairCode.mp hx.2
    have hconst : ∀ a b, G.Reachable a b → x a = x b := fun a b hab ↦
      (mem_of_reachable_of_forall_adj (D := {u | x u = x a}) (fun u w huw hu ↦ by
        rcases huw with h | h
        · rw [toGraph_adj] at h
          change x w = x a
          rw [← h, hP u]
          exact hu
        · rw [toGraph_adj] at h
          change x w = x a
          rw [← h, hQ u]
          exact hu) hab rfl).symm
    exact ⟨SimpleGraph.ConnectedComponent.lift x fun a b p _ ↦ hconst a b p.reachable, rfl⟩
  calc finrank F₂ ↥(pairCode P ⊓ pairCode Q) ≤ finrank F₂ (LinearMap.range Φ) :=
        Submodule.finrank_mono hle
    _ ≤ finrank F₂ (G.ConnectedComponent → F₂) := LinearMap.finrank_range_le Φ
    _ = cycleCount P Q := by
        rw [Module.finrank_fintype_fun_eq_card, cycleCount, Nat.card_eq_fintype_card]

/-- Step 3 of Theorem 3.2 of `results/audit-conjectures-extend.md` (organize-archive ad11c88). If
`φ(P₃) = φ(P₁) + φ(P₂)`, then `κ(P₁ ∪ P₂) ≥ n - 2` (`rowW`, ham-spin 87df892; `cycleCount`). -/
theorem le_cycleCount_add_two (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n)
    {P₁ P₂ P₃ : PerfectMatching V} (h : rowW P₃ = rowW P₁ + rowW P₂) :
    n ≤ cycleCount P₁ P₂ + 2 := by
  obtain ⟨o⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have h1 := le_finrank_nullE_inf_add_two hV hn o h
  rw [nullE_rowW hV hn o, nullE_rowW hV hn o, finrank_liftCode_inf
    (isSelfDual_pairCode P₁).isSelfOrth (isSelfDual_pairCode P₂).isSelfOrth] at h1
  have h2 := finrank_pairCode_inf_le_cycleCount P₁ P₂
  omega

section Classification

open Finset

private theorem eq_add_of_add_add_eq_zero {a b c : W V} (h : a + b + c = 0) : c = a + b :=
  calc c = c + (a + b + c) := by rw [h, add_zero]
    _ = a + b + (c + c) := by abel
    _ = a + b := by rw [add_self_W, add_zero]

private theorem eq_of_add_eq_zero_W {a b : W V} (h : a + b = 0) : a = b :=
  calc a = a + (b + b) := by rw [add_self_W, add_zero]
    _ = a + b + b := by abel
    _ = b := by rw [h, zero_add]

omit [Fintype V] [DecidableEq V] in
/-- `σ • P = Q` as soon as `σ (P x) = Q (σ x)` for every `x`. -/
theorem smul_eq_of_forall_mate {σ : Perm V} {P Q : PerfectMatching V}
    (h : ∀ x, σ (P.mate x) = Q.mate (σ x)) : σ • P = Q := by
  refine PerfectMatching.ext (Equiv.ext fun y ↦ ?_)
  rw [smul_mate, h, Perm.coe_inv, Equiv.apply_symm_apply]

omit [Fintype V] [DecidableEq V] in
private theorem smul_mate_apply_self (σ : Perm V) (P : PerfectMatching V) (y : V) :
    (σ • P).mate (σ y) = σ (P.mate y) := by
  rw [smul_mate, Perm.coe_inv, Equiv.symm_apply_apply]

omit [Fintype V] [DecidableEq V] in
private theorem conj_mate_mate {σ : Perm V} {P Q : PerfectMatching V} {y : V}
    (h : σ (P.mate y) = Q.mate (σ y)) : σ (P.mate (P.mate y)) = Q.mate (σ (P.mate y)) := by
  rw [mate_mate, h, mate_mate]

omit [Fintype V] in
private theorem swap_mul_swap_apply {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (swap a b * swap a c) a = c ∧ (swap a b * swap a c) c = b ∧ (swap a b * swap a c) b = a ∧
      ∀ y, y ≠ a → y ≠ b → y ≠ c → (swap a b * swap a c) y = y := by
  refine ⟨?_, ?_, ?_, fun y ha hb hc ↦ ?_⟩
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hac.symm hbc.symm]
  · rw [Perm.mul_apply, swap_apply_right, swap_apply_left]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab.symm hbc, swap_apply_right]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne ha hc, swap_apply_of_ne_of_ne ha hb]

omit [Fintype V] [DecidableEq V] in
private theorem ne_mate_of_sameCycle {P Q : PerfectMatching V} {v y z : V}
    (hy : (P.mate * Q.mate).SameCycle v y) (hz : (P.mate * Q.mate).SameCycle v z) :
    y ≠ P.mate z := fun h ↦ by
  rw [h] at hy
  exact not_sameCycle_mate_left P Q z (hz.symm.trans hy)

omit [Fintype V] [DecidableEq V] in
private theorem eq_or_eq_of_sameCycle_two [Finite V] {g : Perm V} {x y : V} (h2 : g (g x) = x)
    (hxy : g.SameCycle x y) : y = x ∨ y = g x := by
  obtain ⟨i, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction i with
  | zero => exact Or.inl rfl
  | succ i ih =>
    rw [pow_succ', Perm.mul_apply]
    rcases ih with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl h2

omit [Fintype V] [DecidableEq V] in
private theorem eq_or_eq_or_eq_of_sameCycle_three [Finite V] {g : Perm V} {x y : V}
    (h3 : g (g (g x)) = x) (hxy : g.SameCycle x y) : y = x ∨ y = g x ∨ y = g (g x) := by
  obtain ⟨i, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction i with
  | zero => exact Or.inl rfl
  | succ i ih =>
    rw [pow_succ', Perm.mul_apply]
    rcases ih with h | h | h <;> rw [h]
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl h3

omit [DecidableEq V] in
private theorem sum_card_reachable_le (P Q : PerfectMatching V) (T : Finset V)
    (hT : ∀ x ∈ T, ∀ y ∈ T, (P.toGraph ⊔ Q.toGraph).Reachable x y → x = y) :
    ∑ x ∈ T, Nat.card {y // (P.toGraph ⊔ Q.toGraph).Reachable x y} + 2 * cycleCount P Q ≤
      Fintype.card V + 2 * #T := by
  classical
  set G := P.toGraph ⊔ Q.toGraph
  have : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hfib : ∀ x, Nat.card {y // G.Reachable x y} =
      #{y | G.connectedComponentMk y = G.connectedComponentMk x} := fun x ↦ by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.ConnectedComponent.eq]
    exact ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩
  have hinj : Set.InjOn G.connectedComponentMk T := fun x hx y hy h ↦
    hT x hx y hy (SimpleGraph.ConnectedComponent.eq.mp h)
  have h1 : Fintype.card V = ∑ c, #{y | G.connectedComponentMk y = c} := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise fun _ _ ↦ Finset.mem_univ _
  rw [← Finset.sum_add_sum_compl (T.image G.connectedComponentMk), Finset.sum_image hinj] at h1
  have h2 : ∀ c ∈ (T.image G.connectedComponentMk)ᶜ,
      2 ≤ #{y | G.connectedComponentMk y = c} := by
    intro c _
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h y =>
      have hsub : ({y, P.mate y} : Finset V) ⊆
          ({z | G.connectedComponentMk z = G.connectedComponentMk y} : Finset V) := by
        intro z hz
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases hz with rfl | rfl
        · rfl
        · exact SimpleGraph.ConnectedComponent.eq.mpr (reachable_mate_left P Q y).symm
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair (P.mate_ne y).symm] at this
  have h3 := Finset.card_nsmul_le_sum _ _ 2 h2
  have h4 : #(T.image G.connectedComponentMk)ᶜ = Fintype.card G.ConnectedComponent - #T := by
    rw [Finset.card_compl, Finset.card_image_of_injOn hinj]
  have h5 : #T ≤ Fintype.card G.ConnectedComponent := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_univ _
  have h6 : cycleCount P Q = Fintype.card G.ConnectedComponent := by
    rw [cycleCount, Nat.card_eq_fintype_card]
  rw [Finset.sum_congr rfl fun x _ ↦ hfib x]
  rw [smul_eq_mul] at h3
  omega

omit [Fintype V] [DecidableEq V] in
private theorem two_mul_card_le_card_reachable [Finite V] (P Q : PerfectMatching V) (x : V)
    (S : Finset V) (hS : ∀ y ∈ S, (P.mate * Q.mate).SameCycle x y) :
    2 * #S ≤ Nat.card {y // (P.toGraph ⊔ Q.toGraph).Reachable x y} := by
  classical
  have := Fintype.ofFinite V
  rw [card_reachable_eq_two_mul]
  have : #S ≤ Nat.card {y // (P.mate * Q.mate).SameCycle x y} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact Finset.card_le_card fun y hy ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS y hy⟩
  omega

omit [Fintype V] [DecidableEq V] in
private theorem pow_three_of_card_reachable_le [Finite V] (P Q : PerfectMatching V) {x : V}
    (h6 : Nat.card {y // (P.toGraph ⊔ Q.toGraph).Reachable x y} ≤ 6)
    (h1 : (P.mate * Q.mate) x ≠ x) (h2 : (P.mate * Q.mate) ((P.mate * Q.mate) x) ≠ x) :
    (P.mate * Q.mate) ((P.mate * Q.mate) ((P.mate * Q.mate) x)) = x := by
  classical
  have := Fintype.ofFinite V
  set g := P.mate * Q.mate
  have hc := card_reachable_eq_two_mul P Q x
  rw [Nat.card_eq_fintype_card (α := {y // g.SameCycle x y}), Fintype.card_subtype] at hc
  have hS : ({x, g x, g (g x)} : Finset V) ⊆ ({y | g.SameCycle x y} : Finset V) := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hy with rfl | rfl | rfl
    · exact Perm.SameCycle.refl _ _
    · exact Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl _ _)
    · exact Perm.sameCycle_apply_right.mpr
        (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl _ _))
  have h3 : #({x, g x, g (g x)} : Finset V) = 3 :=
    Finset.card_eq_three.mpr ⟨_, _, _, h1.symm, h2.symm, fun h ↦ h1 (g.injective h).symm, rfl⟩
  have heq := Finset.eq_of_subset_of_card_le hS (by omega)
  have hmem : g (g (g x)) ∈ ({y | g.SameCycle x y} : Finset V) := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, Perm.sameCycle_apply_right.mpr (Perm.sameCycle_apply_right.mpr
      (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl _ _)))⟩
  rw [← heq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · exact h
  · exact absurd (g.injective h) h2
  · exact absurd (g.injective (g.injective h)) h1

omit [Fintype V] in
private theorem block_conj_one {P Q : PerfectMatching V} {w0 w1 w2 w3 : V}
    (h01 : P.mate w0 = w1) (h23 : P.mate w2 = w3) (h03 : Q.mate w0 = w3) (h21 : Q.mate w2 = w1)
    (d01 : w0 ≠ w1) (d02 : w0 ≠ w2) (d03 : w0 ≠ w3) (d12 : w1 ≠ w2) (d13 : w1 ≠ w3)
    (d23 : w2 ≠ w3) (y : V) (hy : y = w0 ∨ y = w1 ∨ y = w2 ∨ y = w3) :
    (swap w1 w2 * swap w1 w3) (P.mate y) = Q.mate ((swap w1 w2 * swap w1 w3) y) := by
  obtain ⟨t1, t3, t2, tfix⟩ := swap_mul_swap_apply d12 d13 d23
  have t0 := tfix w0 d01 d02 d03
  have e0 : (swap w1 w2 * swap w1 w3) (P.mate w0) = Q.mate ((swap w1 w2 * swap w1 w3) w0) := by
    rw [h01, t1, t0, h03]
  have e2 : (swap w1 w2 * swap w1 w3) (P.mate w2) = Q.mate ((swap w1 w2 * swap w1 w3) w2) := by
    rw [h23, t3, t2, Q.mate_eq_comm.mp h21]
  rcases hy with rfl | rfl | rfl | rfl
  · exact e0
  · have := conj_mate_mate e0
    rwa [h01] at this
  · exact e2
  · have := conj_mate_mate e2
    rwa [h23] at this

omit [Fintype V] in
private theorem block_conj_two {P Q : PerfectMatching V} {w0 w1 w2 w3 : V}
    (h03 : P.mate w0 = w3) (h12 : P.mate w1 = w2) (q02 : Q.mate w0 = w2) (q13 : Q.mate w1 = w3)
    (d01 : w0 ≠ w1) (d02 : w0 ≠ w2) (d03 : w0 ≠ w3) (d12 : w1 ≠ w2) (d13 : w1 ≠ w3)
    (d23 : w2 ≠ w3) (y : V) (hy : y = w0 ∨ y = w1 ∨ y = w2 ∨ y = w3) :
    (swap w1 w2 * swap w1 w3) (P.mate y) = Q.mate ((swap w1 w2 * swap w1 w3) y) := by
  obtain ⟨t1, t3, t2, tfix⟩ := swap_mul_swap_apply d12 d13 d23
  have t0 := tfix w0 d01 d02 d03
  have e0 : (swap w1 w2 * swap w1 w3) (P.mate w0) = Q.mate ((swap w1 w2 * swap w1 w3) w0) := by
    rw [h03, t3, t0, q02]
  have e1 : (swap w1 w2 * swap w1 w3) (P.mate w1) = Q.mate ((swap w1 w2 * swap w1 w3) w1) := by
    rw [h12, t2, t1, Q.mate_eq_comm.mp q13]
  rcases hy with rfl | rfl | rfl | rfl
  · exact e0
  · exact e1
  · have := conj_mate_mate e1
    rwa [h12] at this
  · have := conj_mate_mate e0
    rwa [h03] at this

omit [Fintype V] in
private theorem block_fix {P : PerfectMatching V} {w0 w1 w2 w3 : V}
    (hP : ∀ y, (y = w0 ∨ y = w1 ∨ y = w2 ∨ y = w3) →
      (P.mate y = w0 ∨ P.mate y = w1 ∨ P.mate y = w2 ∨ P.mate y = w3))
    (d12 : w1 ≠ w2) (d13 : w1 ≠ w3) (d23 : w2 ≠ w3) {y : V}
    (hy : ¬(y = w0 ∨ y = w1 ∨ y = w2 ∨ y = w3)) :
    (swap w1 w2 * swap w1 w3) y = y ∧ (swap w1 w2 * swap w1 w3) (P.mate y) = P.mate y := by
  obtain ⟨-, -, -, tfix⟩ := swap_mul_swap_apply d12 d13 d23
  have hPy : ¬(P.mate y = w0 ∨ P.mate y = w1 ∨ P.mate y = w2 ∨ P.mate y = w3) := fun h ↦
    hy (by simpa using hP _ h)
  push Not at hy hPy
  exact ⟨tfix y hy.2.1 hy.2.2.1 hy.2.2.2, tfix _ hPy.2.1 hPy.2.2.1 hPy.2.2.2⟩

omit [Fintype V] [DecidableEq V] in
private theorem block_closed {P : PerfectMatching V} {w0 w1 w2 w3 a b c d : V}
    (hab : P.mate a = b) (hcd : P.mate c = d)
    (hs : ∀ y, (y = w0 ∨ y = w1 ∨ y = w2 ∨ y = w3) ↔ (y = a ∨ y = b ∨ y = c ∨ y = d)) (y : V)
    (hy : y = w0 ∨ y = w1 ∨ y = w2 ∨ y = w3) :
    P.mate y = w0 ∨ P.mate y = w1 ∨ P.mate y = w2 ∨ P.mate y = w3 := by
  rw [hs] at hy ⊢
  have hba : P.mate b = a := P.mate_eq_comm.mp hab
  have hdc : P.mate d = c := P.mate_eq_comm.mp hcd
  rcases hy with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl hab)
  · exact Or.inl hba
  · exact Or.inr (Or.inr (Or.inr hcd))
  · exact Or.inr (Or.inr (Or.inl hdc))

omit [Fintype V] [DecidableEq V] in
private theorem smul_eq_of_block {P Q : PerfectMatching V} {τ : Perm V} (A : V → Prop)
    (hA : ∀ y, A y → τ (P.mate y) = Q.mate (τ y))
    (hout : ∀ y, ¬A y → τ y = y ∧ τ (P.mate y) = P.mate y ∧ P.mate y = Q.mate y) : τ • P = Q := by
  refine smul_eq_of_forall_mate fun y ↦ ?_
  by_cases hy : A y
  · exact hA y hy
  · obtain ⟨h1, h2, h3⟩ := hout y hy
    rw [h2, h1, h3]

omit [Fintype V] [DecidableEq V] in
private theorem smul_eq_of_two_blocks {P Q : PerfectMatching V} {τA τB : Perm V}
    (hc : τA * τB = τB * τA) (A B : V → Prop)
    (hA : ∀ y, A y → τA (P.mate y) = Q.mate (τA y))
    (hB : ∀ y, B y → τB (P.mate y) = Q.mate (τB y))
    (hAB : ∀ y, A y → τB y = y ∧ τB (P.mate y) = P.mate y)
    (hBA : ∀ y, B y → τA y = y ∧ τA (P.mate y) = P.mate y)
    (hout : ∀ y, ¬A y → ¬B y → τA y = y ∧ τB y = y ∧ τA (P.mate y) = P.mate y ∧
      τB (P.mate y) = P.mate y ∧ P.mate y = Q.mate y) :
    (τA * τB) • P = Q := by
  refine smul_eq_of_forall_mate fun y ↦ ?_
  by_cases hy : A y
  · obtain ⟨h1, h2⟩ := hAB y hy
    rw [Perm.mul_apply, Perm.mul_apply, h1, h2]
    exact hA y hy
  by_cases hy' : B y
  · obtain ⟨h1, h2⟩ := hBA y hy'
    rw [hc, Perm.mul_apply, Perm.mul_apply, h1, h2]
    exact hB y hy'
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hout y hy hy'
    rw [Perm.mul_apply, Perm.mul_apply, h4, h3, h2, h1, h5]

private theorem block_mate_third (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n)
    {P₁ P₂ P₃ : PerfectMatching V} (h3 : rowW P₃ = rowW P₁ + rowW P₂) {w0 w1 w2 w3 : V}
    (h01 : P₁.mate w0 = w1) (h23 : P₁.mate w2 = w3) (h03 : P₂.mate w0 = w3)
    (h21 : P₂.mate w2 = w1) (d02 : w0 ≠ w2) (d13 : w1 ≠ w3) :
    P₃.mate w0 = w2 ∧ P₃.mate w1 = w3 := by
  have h10 : P₁.mate w1 = w0 := P₁.mate_eq_comm.mp h01
  have h12 : P₂.mate w1 = w2 := P₂.mate_eq_comm.mp h21
  let S : Finset V := {w0, w1, w2, w3}
  have hmemS : ∀ y, y ∈ S ↔ (y = w0 ∨ y = w1 ∨ y = w2 ∨ y = w3) := fun y ↦ by
    simp [S]
  have hcl : ∀ P : PerfectMatching V, (∀ y, (y = w0 ∨ y = w1 ∨ y = w2 ∨ y = w3) →
      (P.mate y = w0 ∨ P.mate y = w1 ∨ P.mate y = w2 ∨ P.mate y = w3)) →
      (fun y ↦ if y ∈ S then (1 : F₂) else 0) ∈ pairCode P := by
    intro P hP
    rw [mem_pairCode]
    intro y
    by_cases hy : y ∈ S
    · have hPy : P.mate y ∈ S := (hmemS _).mpr (hP y ((hmemS y).mp hy))
      simp only [hy, hPy, ite_true]
    · have hPy : P.mate y ∉ S := fun h ↦ hy ((hmemS y).mpr (by
        simpa using hP _ ((hmemS _).mp h)))
      simp only [hy, hPy, ite_false]
  have hx := pairCode_inf_le_of_rowW_eq_add hV hn h3
    ⟨hcl P₁ (block_closed h01 h23 (fun y ↦ Iff.rfl)),
      hcl P₂ (block_closed h03 h21 (fun y ↦ by tauto))⟩
  have hmem : ∀ y, y ∈ S → P₃.mate y ∈ S := fun y hy ↦ by
    have := (mem_pairCode.mp hx) y
    by_contra hn'
    simp only [hn', hy, ite_true, ite_false] at this
    exact zero_ne_one this
  have h13 : rowW P₂ = rowW P₁ + rowW P₃ := by
    rw [h3, ← add_assoc, add_self_W, zero_add]
  have h23' : rowW P₁ = rowW P₂ + rowW P₃ := by
    rw [h3, add_comm (rowW P₁) (rowW P₂), ← add_assoc, add_self_W, zero_add]
  have hne1 : ∀ y, P₃.mate y = P₁.mate y → P₂.mate y = P₁.mate y := fun y hy ↦
    mate_eq_of_rowW_eq_add hV hn h13 hy.symm
  have hne2 : ∀ y, P₃.mate y = P₂.mate y → P₁.mate y = P₂.mate y := fun y hy ↦
    mate_eq_of_rowW_eq_add hV hn h23' hy.symm
  constructor
  · rcases (hmemS _).mp (hmem w0 ((hmemS _).mpr (Or.inl rfl))) with h | h | h | h
    · exact absurd h (P₃.mate_ne w0)
    · have := hne1 w0 (h.trans h01.symm)
      rw [h01, h03] at this
      exact absurd this d13.symm
    · exact h
    · have := hne2 w0 (h.trans h03.symm)
      rw [h01, h03] at this
      exact absurd this d13
  · rcases (hmemS _).mp (hmem w1 ((hmemS _).mpr (Or.inr (Or.inl rfl)))) with h | h | h | h
    · have := hne1 w1 (h.trans h10.symm)
      rw [h10, h12] at this
      exact absurd this d02.symm
    · exact absurd h (P₃.mate_ne w1)
    · have := hne2 w1 (h.trans h12.symm)
      rw [h10, h12] at this
      exact absurd this d02
    · exact h

private theorem smul_eq_smul_of_rowW (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n)
    {τA τB : Perm V} (hA : τA.IsThreeCycle) (hB : τB.IsThreeCycle) (hc : Commute τA τB)
    (P : PerfectMatching V)
    (h : rowW P + rowW ((τA * τB) • P) + rowW ((τA * τB) • (τA * τB) • P) = 0) :
    τA • P = τB • P := by
  apply rowW_injective hV hn
  have h3 := rowW_add_add_eq_zero_of_isThreeCycle hA (τB ^ 2 • P)
  have h4 := rowW_add_add_eq_zero_of_isThreeCycle hB P
  have h5 := rowW_add_add_eq_zero_of_isThreeCycle hB (τA • P)
  have e1 : τA ^ 2 • τB ^ 2 • P = (τA * τB) • (τA * τB) • P := by
    rw [smul_smul, smul_smul, ← pow_two, hc.mul_pow]
  have e2 : τB • τA • P = (τA * τB) • P := by
    rw [smul_smul, hc.eq]
  have e3 : τB ^ 2 • τA • P = τA • τB ^ 2 • P := by
    rw [smul_smul, smul_smul, (hc.symm.pow_left 2).eq]
  rw [e1] at h3
  rw [e2, e3] at h5
  have e : (rowW (τB ^ 2 • P) + rowW (τA • τB ^ 2 • P) + rowW ((τA * τB) • (τA * τB) • P)) +
      (rowW P + rowW (τB • P) + rowW (τB ^ 2 • P)) +
      (rowW (τA • P) + rowW ((τA * τB) • P) + rowW (τA • τB ^ 2 • P)) +
      (rowW P + rowW ((τA * τB) • P) + rowW ((τA * τB) • (τA * τB) • P)) =
      rowW (τA • P) + rowW (τB • P) + 2 • (rowW P + rowW (τB ^ 2 • P) +
        rowW ((τA * τB) • P) + rowW (τA • τB ^ 2 • P) + rowW ((τA * τB) • (τA * τB) • P)) := by
    abel
  rw [two_nsmul, add_self_W, h3, h4, h5, h] at e
  simp only [add_zero] at e
  exact eq_of_add_eq_zero_W e.symm

set_option hygiene false in
/-- `P₁ P₂` in the proof of `exists_isThreeCycle_of_rowW_add_add_eq_zero`. -/
local notation "𝔤" => P₁.mate * P₂.mate

set_option hygiene false in
/-- `P₁ ∪ P₂` in the proof of `exists_isThreeCycle_of_rowW_add_add_eq_zero`. -/
local notation "𝔾" => P₁.toGraph ⊔ P₂.toGraph

set_option hygiene false in
/-- The three-cycle of the first block, case of two blocks or one 4-cycle. -/
local notation "𝔱₁" => swap (P₁.mate v₀) (𝔤 v₀) * swap (P₁.mate v₀) (P₁.mate (𝔤 v₀))

set_option hygiene false in
/-- The three-cycle of the second block, case of two blocks. -/
local notation "𝔱₂" => swap (P₁.mate x) (𝔤 x) * swap (P₁.mate x) (P₁.mate (𝔤 x))

set_option hygiene false in
/-- The three-cycle of the 6-cycle case. -/
local notation "𝔱₃" => swap (P₁.mate v) (P₁.mate (𝔤 (𝔤 v))) * swap (P₁.mate v) (P₁.mate (𝔤 v))

/-- Theorem 3.2 of `results/audit-conjectures-extend.md` (organize-archive ad11c88), "only if"
half. If `P₁ ≠ P₂` and `φ(P₁) + φ(P₂) + φ(P₃) = 0` (`rowW`, ham-spin 87df892), then
`P₂ = τ P₁` and `P₃ = τ P₂` for a three-cycle `τ`. By step 3 (`le_cycleCount_add_two`),
`P₁ ∪ P₂` is a 4-cycle, a 6-cycle or two 4-cycles plus common edges. In the first two cases `τ`
is written down and `P₃ = τ² P₁` by injectivity of `φ`. The case of two 4-cycles (step 6) is
excluded by step 1 and the three-cycle law, in place of the test matching `Q′ = {15, 28, 36, 47}`
of `results/audit-conjectures-factcheck-extend.md` (ad11c88). -/
theorem exists_isThreeCycle_of_rowW_add_add_eq_zero (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n)
    {P₁ P₂ P₃ : PerfectMatching V} (h12 : P₁ ≠ P₂) (h : rowW P₁ + rowW P₂ + rowW P₃ = 0) :
    ∃ τ : Perm V, τ.IsThreeCycle ∧ P₂ = τ • P₁ ∧ P₃ = τ • P₂ := by
  have h3 := eq_add_of_add_add_eq_zero h
  suffices hτ : ∃ τ : Perm V, τ.IsThreeCycle ∧ τ • P₁ = P₂ by
    obtain ⟨τ, hτ, hτP⟩ := hτ
    refine ⟨τ, hτ, hτP.symm, rowW_injective hV hn ?_⟩
    have hlaw := rowW_add_add_eq_zero_of_isThreeCycle hτ P₁
    rw [pow_two, mul_smul, hτP] at hlaw
    exact h3.trans (eq_add_of_add_add_eq_zero hlaw).symm
  have hκ := le_cycleCount_add_two hV hn h3
  have hfix : ∀ x, 𝔤 x = x ↔ P₁.mate x = P₂.mate x := mate_mul_mate_apply_eq_self_iff P₁ P₂
  have hP₂ : ∀ x, P₂.mate x = P₁.mate (𝔤 x) := fun x ↦ by
    rw [Perm.mul_apply, mate_mate]
  have hcount : ∀ T : Finset V, (∀ x ∈ T, ∀ y ∈ T, (𝔾).Reachable x y → x = y) →
      ∑ x ∈ T, Nat.card {y // (𝔾).Reachable x y} ≤ 2 * #T + 4 := fun T hT ↦ by
    have := sum_card_reachable_le P₁ P₂ T hT
    omega
  have hsc1 : ∀ x, (𝔤).SameCycle x (𝔤 x) := fun x ↦
    Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl _ _)
  have hcomp4 : ∀ x, 𝔤 x ≠ x → 4 ≤ Nat.card {y // (𝔾).Reachable x y} := fun x hx ↦ by
    have := two_mul_card_le_card_reachable P₁ P₂ x {x, 𝔤 x} (by
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Perm.SameCycle.refl _ _
      · exact hsc1 _)
    rwa [Finset.card_pair hx.symm] at this
  have hreach : ∀ {x y : V}, (𝔤).SameCycle x y → (𝔾).Reachable x y := fun h ↦
    (reachable_iff_sameCycle P₁ P₂).mpr (Or.inl h)
  have hsum1 : ∀ x, Nat.card {y // (𝔾).Reachable x y} ≤ 6 := fun x ↦ by
    have := hcount {x} fun a ha b hb _ ↦
      (Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm
    rwa [Finset.sum_singleton, Finset.card_singleton] at this
  have hsum2 : ∀ x y, ¬(𝔾).Reachable x y →
      Nat.card {z // (𝔾).Reachable x z} + Nat.card {z // (𝔾).Reachable y z} ≤ 8 := fun x y hxy ↦ by
    have hne : x ≠ y := fun e ↦ hxy (by subst e; exact SimpleGraph.Reachable.rfl)
    have := hcount {x, y} (by
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact absurd hab hxy
      · exact absurd hab.symm hxy
      · rfl)
    rwa [Finset.sum_pair hne, Finset.card_pair hne] at this
  have hno3 : ∀ x y z, 𝔤 x ≠ x → 𝔤 y ≠ y → 𝔤 z ≠ z → ¬(𝔾).Reachable x y → ¬(𝔾).Reachable x z →
      ¬(𝔾).Reachable y z → False := by
    intro x y z hx hy hz hxy hxz hyz
    have nxy : x ≠ y := fun e ↦ hxy (by subst e; exact SimpleGraph.Reachable.rfl)
    have nxz : x ≠ z := fun e ↦ hxz (by subst e; exact SimpleGraph.Reachable.rfl)
    have nyz : y ≠ z := fun e ↦ hyz (by subst e; exact SimpleGraph.Reachable.rfl)
    have hT := hcount {x, y, z} (by
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first
        | rfl
        | exact absurd hab hxy
        | exact absurd hab.symm hxy
        | exact absurd hab hxz
        | exact absurd hab.symm hxz
        | exact absurd hab hyz
        | exact absurd hab.symm hyz)
    have hc3 : #({x, y, z} : Finset V) = 3 := Finset.card_eq_three.mpr ⟨x, y, z, nxy, nxz, nyz, rfl⟩
    have hle := Finset.card_nsmul_le_sum ({x, y, z} : Finset V)
      (fun w ↦ Nat.card {u // (𝔾).Reachable w u}) 4 (by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact hcomp4 _ hx
        · exact hcomp4 _ hy
        · exact hcomp4 _ hz)
    rw [hc3, smul_eq_mul] at hle
    rw [hc3] at hT
    omega
  obtain ⟨v₀, hv₀⟩ : ∃ v, P₁.mate v ≠ P₂.mate v := by
    by_contra hcon
    push Not at hcon
    exact h12 (PerfectMatching.ext (Equiv.ext hcon))
  by_cases hB : ∃ v, 𝔤 v ≠ v ∧ 𝔤 (𝔤 v) ≠ v
  · obtain ⟨v, hv1, hv2⟩ := hB
    have hv3 : 𝔤 (𝔤 (𝔤 v)) = v := pow_three_of_card_reachable_le P₁ P₂ (hsum1 v) hv1 hv2
    have hc6 : 6 ≤ Nat.card {y // (𝔾).Reachable v y} := by
      have := two_mul_card_le_card_reachable P₁ P₂ v {v, 𝔤 v, 𝔤 (𝔤 v)} (by
        intro y hy
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact Perm.SameCycle.refl _ _
        · exact hsc1 _
        · exact (hsc1 _).trans (hsc1 _))
      rwa [Finset.card_eq_three.mpr ⟨_, _, _, hv1.symm, hv2.symm,
        fun e ↦ hv1 (Equiv.injective _ e).symm, rfl⟩] at this
    have hD : ∀ x, P₁.mate x ≠ P₂.mate x → (x = v ∨ x = 𝔤 v ∨ x = 𝔤 (𝔤 v)) ∨
        (P₁.mate x = v ∨ P₁.mate x = 𝔤 v ∨ P₁.mate x = 𝔤 (𝔤 v)) := by
      intro x hx
      have hgx : 𝔤 x ≠ x := fun e ↦ hx ((hfix x).mp e)
      have hr : (𝔾).Reachable v x := by
        by_contra hnr
        have := hsum2 v x hnr
        have := hcomp4 x hgx
        omega
      rcases (reachable_iff_sameCycle P₁ P₂).mp hr with hs | hs
      · exact Or.inl (eq_or_eq_or_eq_of_sameCycle_three hv3 hs)
      · exact Or.inr (eq_or_eq_or_eq_of_sameCycle_three hv3 hs)
    have s0 : (𝔤).SameCycle v v := Perm.SameCycle.refl _ _
    have s2 : (𝔤).SameCycle v (𝔤 v) := hsc1 v
    have s4 : (𝔤).SameCycle v (𝔤 (𝔤 v)) := (hsc1 v).trans (hsc1 _)
    have d13 : P₁.mate v ≠ P₁.mate (𝔤 v) := fun e ↦ hv1 (P₁.mate.injective e).symm
    have d15 : P₁.mate v ≠ P₁.mate (𝔤 (𝔤 v)) := fun e ↦ hv2 (P₁.mate.injective e).symm
    have d35 : P₁.mate (𝔤 v) ≠ P₁.mate (𝔤 (𝔤 v)) := fun e ↦
      hv1 (Equiv.injective _ (P₁.mate.injective e)).symm
    obtain ⟨t1, t3, t5, tfix⟩ := swap_mul_swap_apply d15 d13 d35.symm
    have f0 := tfix v (ne_mate_of_sameCycle s0 s0) (ne_mate_of_sameCycle s0 s4)
      (ne_mate_of_sameCycle s0 s2)
    have f2 := tfix (𝔤 v) (ne_mate_of_sameCycle s2 s0) (ne_mate_of_sameCycle s2 s4)
      (ne_mate_of_sameCycle s2 s2)
    have f4 := tfix (𝔤 (𝔤 v)) (ne_mate_of_sameCycle s4 s0) (ne_mate_of_sameCycle s4 s4)
      (ne_mate_of_sameCycle s4 s2)
    have hE : ∀ y, (y = v ∨ y = 𝔤 v ∨ y = 𝔤 (𝔤 v)) → 𝔱₃ (P₁.mate y) = P₂.mate (𝔱₃ y) := by
      rintro y (rfl | rfl | rfl)
      · rw [t1, f0, hP₂]
      · rw [t3, f2, hP₂]
      · rw [t5, f4, hP₂, hv3]
    refine ⟨𝔱₃, Perm.isThreeCycle_swap_mul_swap_same d15 d13 d35.symm, ?_⟩
    refine smul_eq_of_block (fun y ↦ (y = v ∨ y = 𝔤 v ∨ y = 𝔤 (𝔤 v)) ∨
      (P₁.mate y = v ∨ P₁.mate y = 𝔤 v ∨ P₁.mate y = 𝔤 (𝔤 v))) ?_ ?_
    · rintro y (hy | hy)
      · exact hE y hy
      · have := conj_mate_mate (hE _ hy)
        simpa only [mate_mate] using this
    · intro y hy
      simp only [not_or] at hy
      obtain ⟨⟨a0, a2, a4⟩, ⟨b0, b2, b4⟩⟩ := hy
      refine ⟨tfix y ?_ ?_ ?_, tfix _ ?_ ?_ ?_, ?_⟩
      · exact fun e ↦ b0 (by rw [e, mate_mate])
      · exact fun e ↦ b4 (by rw [e, mate_mate])
      · exact fun e ↦ b2 (by rw [e, mate_mate])
      · exact fun e ↦ a0 (P₁.mate.injective e)
      · exact fun e ↦ a4 (P₁.mate.injective e)
      · exact fun e ↦ a2 (P₁.mate.injective e)
      · by_contra hne
        rcases hD y hne with h' | h'
        · rcases h' with h' | h' | h'
          · exact a0 h'
          · exact a2 h'
          · exact a4 h'
        · rcases h' with h' | h' | h'
          · exact b0 h'
          · exact b2 h'
          · exact b4 h'
  · push Not at hB
    have hgv₀ : 𝔤 v₀ ≠ v₀ := fun e ↦ hv₀ ((hfix v₀).mp e)
    have hv2 := hB v₀ hgv₀
    have hblock : ∀ w, 𝔤 (𝔤 w) = w → ∀ y, (𝔾).Reachable w y →
        (y = w ∨ y = P₁.mate w ∨ y = 𝔤 w ∨ y = P₁.mate (𝔤 w)) := by
      intro w hw y hy
      rcases (reachable_iff_sameCycle P₁ P₂).mp hy with hs | hs
      · rcases eq_or_eq_of_sameCycle_two hw hs with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
      · rcases eq_or_eq_of_sameCycle_two hw hs with h' | h'
        · exact Or.inr (Or.inl (P₁.mate_eq_comm.mp h').symm)
        · exact Or.inr (Or.inr (Or.inr (P₁.mate_eq_comm.mp h').symm))
    have hblockR : ∀ w y, (y = w ∨ y = P₁.mate w ∨ y = 𝔤 w ∨ y = P₁.mate (𝔤 w)) →
        (𝔾).Reachable w y := by
      rintro w y (rfl | rfl | rfl | rfl)
      · exact SimpleGraph.Reachable.rfl
      · exact reachable_mate_left P₁ P₂ w
      · exact hreach (hsc1 w)
      · exact (hreach (hsc1 w)).trans (reachable_mate_left P₁ P₂ _)
    have s0 : (𝔤).SameCycle v₀ v₀ := Perm.SameCycle.refl _ _
    have s2 : (𝔤).SameCycle v₀ (𝔤 v₀) := hsc1 v₀
    have d01 : v₀ ≠ P₁.mate v₀ := ne_mate_of_sameCycle s0 s0
    have d02 : v₀ ≠ 𝔤 v₀ := hgv₀.symm
    have d03 : v₀ ≠ P₁.mate (𝔤 v₀) := ne_mate_of_sameCycle s0 s2
    have d12 : P₁.mate v₀ ≠ 𝔤 v₀ := (ne_mate_of_sameCycle s2 s0).symm
    have d13 : P₁.mate v₀ ≠ P₁.mate (𝔤 v₀) := fun e ↦ hgv₀ (P₁.mate.injective e).symm
    have d23 : 𝔤 v₀ ≠ P₁.mate (𝔤 v₀) := ne_mate_of_sameCycle s2 s2
    have hP2v : P₂.mate v₀ = P₁.mate (𝔤 v₀) := hP₂ v₀
    have hP2g : P₂.mate (𝔤 v₀) = P₁.mate v₀ := by rw [hP₂, hv2]
    have hconj := block_conj_one (P := P₁) (Q := P₂) (w0 := v₀) (w1 := P₁.mate v₀)
      (w2 := 𝔤 v₀) (w3 := P₁.mate (𝔤 v₀)) rfl rfl hP2v hP2g d01 d02 d03 d12 d13 d23
    have hcl₁A := block_closed (P := P₁) (w0 := v₀) (w1 := P₁.mate v₀) (w2 := 𝔤 v₀)
      (w3 := P₁.mate (𝔤 v₀)) rfl rfl fun _ ↦ Iff.rfl
    by_cases hA1 : ∀ y, P₁.mate y ≠ P₂.mate y → (𝔾).Reachable v₀ y
    · refine ⟨𝔱₁, Perm.isThreeCycle_swap_mul_swap_same d12 d13 d23, ?_⟩
      refine smul_eq_of_block (fun y ↦ y = v₀ ∨ y = P₁.mate v₀ ∨ y = 𝔤 v₀ ∨
        y = P₁.mate (𝔤 v₀)) hconj ?_
      intro y hy
      obtain ⟨f1, f2⟩ := block_fix hcl₁A d12 d13 d23 hy
      refine ⟨f1, f2, ?_⟩
      by_contra hne
      exact hy (hblock v₀ hv2 y (hA1 y hne))
    · push Not at hA1
      obtain ⟨x, hx, hvx⟩ := hA1
      have hgx : 𝔤 x ≠ x := fun e ↦ hx ((hfix x).mp e)
      have hx2 := hB x hgx
      have r0 : (𝔤).SameCycle x x := Perm.SameCycle.refl _ _
      have r2 : (𝔤).SameCycle x (𝔤 x) := hsc1 x
      have e01 : x ≠ P₁.mate x := ne_mate_of_sameCycle r0 r0
      have e02 : x ≠ 𝔤 x := hgx.symm
      have e03 : x ≠ P₁.mate (𝔤 x) := ne_mate_of_sameCycle r0 r2
      have e12 : P₁.mate x ≠ 𝔤 x := (ne_mate_of_sameCycle r2 r0).symm
      have e13 : P₁.mate x ≠ P₁.mate (𝔤 x) := fun e ↦ hgx (P₁.mate.injective e).symm
      have e23 : 𝔤 x ≠ P₁.mate (𝔤 x) := ne_mate_of_sameCycle r2 r2
      have hQ2x : P₂.mate x = P₁.mate (𝔤 x) := hP₂ x
      have hQ2g : P₂.mate (𝔤 x) = P₁.mate x := by rw [hP₂, hx2]
      have hconjB := block_conj_one (P := P₁) (Q := P₂) (w0 := x) (w1 := P₁.mate x)
        (w2 := 𝔤 x) (w3 := P₁.mate (𝔤 x)) rfl rfl hQ2x hQ2g e01 e02 e03 e12 e13 e23
      have hcl₁B := block_closed (P := P₁) (w0 := x) (w1 := P₁.mate x) (w2 := 𝔤 x)
        (w3 := P₁.mate (𝔤 x)) rfl rfl fun _ ↦ Iff.rfl
      have hcl₂A := block_closed (P := P₂) (w0 := v₀) (w1 := P₁.mate v₀) (w2 := 𝔤 v₀)
        (w3 := P₁.mate (𝔤 v₀)) hP2v hP2g fun _ ↦ by tauto
      have hcl₂B := block_closed (P := P₂) (w0 := x) (w1 := P₁.mate x) (w2 := 𝔤 x)
        (w3 := P₁.mate (𝔤 x)) hQ2x hQ2g fun _ ↦ by tauto
      have hDAB : ∀ y, P₁.mate y ≠ P₂.mate y →
          (y = v₀ ∨ y = P₁.mate v₀ ∨ y = 𝔤 v₀ ∨ y = P₁.mate (𝔤 v₀)) ∨
            (y = x ∨ y = P₁.mate x ∨ y = 𝔤 x ∨ y = P₁.mate (𝔤 x)) := by
        intro y hy
        have hgy : 𝔤 y ≠ y := fun e ↦ hy ((hfix y).mp e)
        by_cases hvy : (𝔾).Reachable v₀ y
        · exact Or.inl (hblock v₀ hv2 y hvy)
        by_cases hxy : (𝔾).Reachable x y
        · exact Or.inr (hblock x hx2 y hxy)
        exact (hno3 v₀ x y hgv₀ hgx hgy hvx hvy hxy).elim
      have hcross : ∀ a b, (a = v₀ ∨ a = P₁.mate v₀ ∨ a = 𝔤 v₀ ∨ a = P₁.mate (𝔤 v₀)) →
          (b = x ∨ b = P₁.mate x ∨ b = 𝔤 x ∨ b = P₁.mate (𝔤 x)) → a ≠ b := fun a b ha hb e ↦
        hvx ((hblockR v₀ a ha).trans (by rw [e]; exact (hblockR x b hb).symm))
      obtain ⟨p0, p1⟩ := block_mate_third hV hn h3 (w0 := v₀) (w1 := P₁.mate v₀) (w2 := 𝔤 v₀)
        (w3 := P₁.mate (𝔤 v₀)) rfl rfl hP2v hP2g d02 d13
      obtain ⟨q0, q1⟩ := block_mate_third hV hn h3 (w0 := x) (w1 := P₁.mate x) (w2 := 𝔤 x)
        (w3 := P₁.mate (𝔤 x)) rfl rfl hQ2x hQ2g e02 e13
      have hP3out : ∀ y, P₁.mate y = P₂.mate y → P₃.mate y = P₁.mate y := fun y hy ↦
        mate_eq_of_rowW_eq_add hV hn h3 hy
      have hτA := Perm.isThreeCycle_swap_mul_swap_same d12 d13 d23
      have hτB := Perm.isThreeCycle_swap_mul_swap_same e12 e13 e23
      have hdisj : Perm.Disjoint 𝔱₁ 𝔱₂ := by
        intro y
        by_cases hy : y = v₀ ∨ y = P₁.mate v₀ ∨ y = 𝔤 v₀ ∨ y = P₁.mate (𝔤 v₀)
        · exact Or.inr (block_fix hcl₁B e12 e13 e23 (fun hb ↦ hcross y y hy hb rfl)).1
        · exact Or.inl (block_fix hcl₁A d12 d13 d23 hy).1
      have hc : Commute 𝔱₁ 𝔱₂ := hdisj.commute
      have hP2 : (𝔱₁ * 𝔱₂) • P₁ = P₂ := smul_eq_of_two_blocks hc.eq
        (fun y ↦ y = v₀ ∨ y = P₁.mate v₀ ∨ y = 𝔤 v₀ ∨ y = P₁.mate (𝔤 v₀))
        (fun y ↦ y = x ∨ y = P₁.mate x ∨ y = 𝔤 x ∨ y = P₁.mate (𝔤 x)) hconj hconjB
        (fun y hy ↦ block_fix hcl₁B e12 e13 e23 (fun hb ↦ hcross y y hy hb rfl))
        (fun y hy ↦ block_fix hcl₁A d12 d13 d23 (fun ha ↦ hcross y y ha hy rfl))
        (fun y hyA hyB ↦ by
          obtain ⟨f1, f2⟩ := block_fix hcl₁A d12 d13 d23 hyA
          obtain ⟨g1, g2⟩ := block_fix hcl₁B e12 e13 e23 hyB
          refine ⟨f1, g1, f2, g2, ?_⟩
          by_contra hne
          rcases hDAB y hne with h' | h'
          · exact hyA h'
          · exact hyB h')
      have hP3 : (𝔱₁ * 𝔱₂) • P₂ = P₃ := smul_eq_of_two_blocks hc.eq
        (fun y ↦ y = v₀ ∨ y = P₁.mate v₀ ∨ y = 𝔤 v₀ ∨ y = P₁.mate (𝔤 v₀))
        (fun y ↦ y = x ∨ y = P₁.mate x ∨ y = 𝔤 x ∨ y = P₁.mate (𝔤 x))
        (block_conj_two hP2v (P₂.mate_eq_comm.mp hP2g) p0 p1 d01 d02 d03 d12 d13 d23)
        (block_conj_two hQ2x (P₂.mate_eq_comm.mp hQ2g) q0 q1 e01 e02 e03 e12 e13 e23)
        (fun y hy ↦ block_fix hcl₂B e12 e13 e23 (fun hb ↦ hcross y y hy hb rfl))
        (fun y hy ↦ block_fix hcl₂A d12 d13 d23 (fun ha ↦ hcross y y ha hy rfl))
        (fun y hyA hyB ↦ by
          obtain ⟨f1, f2⟩ := block_fix hcl₂A d12 d13 d23 hyA
          obtain ⟨g1, g2⟩ := block_fix hcl₂B e12 e13 e23 hyB
          refine ⟨f1, g1, f2, g2, ?_⟩
          have hyD : P₁.mate y = P₂.mate y := by
            by_contra hne
            rcases hDAB y hne with h' | h'
            · exact hyA h'
            · exact hyB h'
          rw [← hyD, hP3out y hyD])
      have hrow : rowW P₁ + rowW ((𝔱₁ * 𝔱₂) • P₁) + rowW ((𝔱₁ * 𝔱₂) • (𝔱₁ * 𝔱₂) • P₁) = 0 := by
        rw [hP2, hP3]
        exact h
      have heq := smul_eq_smul_of_rowW hV hn hτA hτB hc P₁ hrow
      obtain ⟨t1A, -, -, tfixA⟩ := swap_mul_swap_apply d12 d13 d23
      have f0A := tfixA v₀ d01 d02 d03
      have f0B := block_fix hcl₁B e12 e13 e23 (y := v₀) (fun hb ↦ hcross v₀ v₀ (Or.inl rfl) hb rfl)
      have eA : (𝔱₁ • P₁).mate v₀ = P₁.mate (𝔤 v₀) := by
        have := smul_mate_apply_self 𝔱₁ P₁ v₀
        rw [f0A] at this
        rw [this, t1A]
      have eB : (𝔱₂ • P₁).mate v₀ = P₁.mate v₀ := by
        have := smul_mate_apply_self 𝔱₂ P₁ v₀
        rw [f0B.1] at this
        rw [this, f0B.2]
      have hv := congrArg (fun P : PerfectMatching V ↦ P.mate v₀) heq
      rw [eA, eB] at hv
      exact absurd (P₁.mate.injective hv) hgv₀

/-- **Theorem 3.2** of `results/audit-conjectures-extend.md` (organize-archive ad11c88), with
step 6 as corrected in `results/audit-conjectures-factcheck-extend.md` (ad11c88) and proved here
from the three-cycle law. Let `|V| = 2n ≥ 2` and `P₁ ≠ P₂`. Then
`φ(P₁) + φ(P₂) + φ(P₃) = 0` iff `P₂ = τ P₁` and `P₃ = τ P₂` for a three-cycle `τ`, that is iff
`{P₁, P₂, P₃}` is one three-cycle orbit `{P, τP, τ²P}` (`rowW`, ham-spin 87df892). -/
theorem rowW_add_add_eq_zero_iff (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n)
    {P₁ P₂ P₃ : PerfectMatching V} (h12 : P₁ ≠ P₂) :
    rowW P₁ + rowW P₂ + rowW P₃ = 0 ↔
      ∃ τ : Perm V, τ.IsThreeCycle ∧ P₂ = τ • P₁ ∧ P₃ = τ • P₂ := by
  refine ⟨exists_isThreeCycle_of_rowW_add_add_eq_zero hV hn h12, ?_⟩
  rintro ⟨τ, hτ, rfl, rfl⟩
  have := rowW_add_add_eq_zero_of_isThreeCycle hτ P₁
  rwa [pow_two, mul_smul] at this

end Classification

end Pairing.PerfectMatching
