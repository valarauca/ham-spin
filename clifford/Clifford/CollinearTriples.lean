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

end Pairing.PerfectMatching
