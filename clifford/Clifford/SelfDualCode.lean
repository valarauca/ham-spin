import Clifford.Descent
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Tactic.LinearCombination

/-!
# Self-dual codes and the extended space `U ⊕ 𝔽₂ε` (COD-297)

Let `|V| = 2n`. `U V ⊆ 𝔽₂^V` is the even-weight space with `q(x) = |supp x| / 2 mod 2` and
`b(x, y) = x · y` (`U`, `qfun`, `dot`, `qForm`, ham-spin 87df892). This file holds the part of
Theorem 1 of `results/spinor-hull-extend.md` (organize-archive b47b504) and of Theorem 1.1 of
`results/spinor-codes.md` (d846b99) that is plain `𝔽₂` linear algebra, layer A of
`results/spinor-codes-factcheck.md` (4e3fe2d) §6. The spin module enters in `Clifford.PureSpinor`.

## Design

The sources work in `Ũ_n = (U ⊕ 𝔽₂ε) ⧸ ⟨𝟙 + nε⟩` with `q(ε) = 1` and `B(ε, ·) = 0`. No quotient
type is built. The space is `U V × 𝔽₂` with `qE (x, λ) = q(x) + λ` (`qE`), and `kE = 𝟙 + nε`
(`kE`) spans the kernel of `U ⊕ 𝔽₂ε → Ũ_n`. As `kE` is singular and `B`-orthogonal to everything,
the totally singular subspaces of `Ũ_n` are the images of the totally singular subspaces of
`U V × 𝔽₂` that contain `kE`, and every maximal one contains `kE` (`kE_mem_of_maximal`). So the
maximal totally singular subspaces of the two spaces correspond, and every dimension in `Ũ_n` is
one less than here. "Witt index `n - 1`" reads `finrank M ≤ n`, with equality exactly for the
maximal `M` (`maximal_isTotSing_iff`), and "`M ∩ M' = 0` in `Ũ_n`" reads `M ⊓ M' ≤ 𝔽₂ ∙ kE`.

## Contents

* `dotForm`, `IsSelfOrth`, `IsSelfDual` : codes `C ≤ 𝔽₂^V` and `C^⊥`. `IsSelfDual.le_U` and
  `IsSelfDual.one_mem` : a self-dual code lies in `U` and contains `𝟙` (Theorem 1.1.1 of
  spinor-codes). `IsSelfDual.finrank_eq` : it has dimension `n`.
* `pairCode P = i₂(P)`, the words that are unions of `P`-edges. `isSelfDual_pairCode`.
* `qE`, `polar_qE`, `IsTotSing`, `kE`, `epsE`. `mem_span_kE_of_polar` : a singular vector in the
  `B`-radical is a multiple of `kE`, so `Ũ_n` is nondegenerate. `finrank_U` : `dim U = 2n - 1`.
* `liftCode C = M_C = {x + q(x)ε : x ∈ C}` and `codeOf M`, the projection of `M` to `𝔽₂^V`.
  `finrank_le_of_isTotSing` and `maximal_isTotSing_iff` : the Witt index statement.
* `selfDualEquiv` : `C ↦ M_C` is a bijection from self-dual codes onto the maximal totally
  singular subspaces (Theorem 1.1.2 of spinor-codes). `maximal_liftCode_pairCode` : `M_P` is
  maximal (Theorem 1.3 of spinor-hull-extend, first half).
* `finrank_liftCode_inf` : `dim(M_C ∩ M_C') = dim(C ∩ C')` here, that is `dim(C ∩ C') - 1` in
  `Ũ_n` (Theorem 1.1.5 of spinor-codes, first sentence). `liftCode_inf_le_span_kE_iff` :
  `M_C ∩ M_C' = 0` in `Ũ_n` iff `C ∩ C' ≤ ⟨𝟙⟩`. `sup_eq_U_of_inf_le` : then `C + C' = U`.
-/

namespace Pairing.PerfectMatching

open Module

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem f2_cases (a : F₂) : a = 0 ∨ a = 1 := by
  revert a
  decide

private theorem f2_mul_self' (a : F₂) : a * a = a := by
  revert a
  decide

section Code

variable (V) in
/-- The dot product `x · y` (`dot`, ham-spin 87df892) on `𝔽₂^V` as a bilinear form. -/
def dotForm : LinearMap.BilinForm F₂ (V → F₂) :=
  LinearMap.mk₂ F₂ dot
    (fun _ _ _ ↦ by simp [dot, add_mul, Finset.sum_add_distrib])
    (fun _ _ _ ↦ by simp [dot, Finset.mul_sum, mul_assoc])
    (fun _ _ _ ↦ by simp [dot, mul_add, Finset.sum_add_distrib])
    (fun _ _ _ ↦ by simp [dot, Finset.mul_sum, mul_left_comm])

omit [DecidableEq V] in
theorem dotForm_apply (x y : V → F₂) : dotForm V x y = dot x y :=
  rfl

omit [DecidableEq V] in
/-- `x · 𝟙 = ∑ x_i`. -/
theorem dot_one_left (x : V → F₂) : dot 1 x = ∑ i, x i := by
  simp [dot]

omit [DecidableEq V] in
/-- `x · x = ∑ x_i` over `𝔽₂`. -/
theorem dot_self (x : V → F₂) : dot x x = ∑ i, x i :=
  Finset.sum_congr rfl fun i _ ↦ f2_mul_self' (x i)

theorem dot_single (x : V → F₂) (i : V) : dot x (Pi.single i 1) = x i := by
  simp [dot, Pi.single_apply]

/-- `v_{ij} · y = y_i + y_j` (`v`, ham-spin 87df892). -/
theorem dot_v_left (i j : V) (y : V → F₂) : dot (v i j) y = y i + y j := by
  rw [dot_comm, v, ← dotForm_apply, map_add, dotForm_apply, dotForm_apply, dot_single, dot_single]

omit [DecidableEq V] in
theorem dotForm_isRefl : (dotForm V).IsRefl := fun x y h ↦ by
  rw [dotForm_apply, dot_comm]
  exact h

omit [DecidableEq V] in
/-- The dot product on `𝔽₂^V` is nondegenerate. -/
theorem dotForm_nondegenerate : (dotForm V).Nondegenerate := by
  classical
  have hL : ∀ x : V → F₂, (∀ y, dotForm V x y = 0) → x = 0 := fun x hx ↦
    funext fun i ↦ by
      rw [← dot_single x i]
      exact hx _
  exact ⟨hL, fun y hy ↦ hL y fun x ↦ by
    rw [dotForm_apply, dot_comm]
    exact hy x⟩

omit [DecidableEq V] in
/-- `y ∈ C^⊥` iff `x · y = 0` for every `x ∈ C`. -/
theorem mem_codeOrth {C : Submodule F₂ (V → F₂)} {y : V → F₂} :
    y ∈ (dotForm V).orthogonal C ↔ ∀ x ∈ C, dot x y = 0 :=
  LinearMap.BilinForm.mem_orthogonal_iff

omit [DecidableEq V] in
/-- `y ∈ (span S)^⊥` iff `x · y = 0` for every `x ∈ S`. -/
theorem mem_codeOrth_span {S : Set (V → F₂)} {y : V → F₂} :
    y ∈ (dotForm V).orthogonal (Submodule.span F₂ S) ↔ ∀ x ∈ S, dot x y = 0 := by
  rw [mem_codeOrth]
  refine ⟨fun h x hx ↦ h x (Submodule.subset_span hx), fun h x hx ↦ ?_⟩
  have hle : Submodule.span F₂ S ≤ LinearMap.ker ((dotForm V).flip y) :=
    Submodule.span_le.mpr fun x hx ↦ LinearMap.mem_ker.mpr (h x hx)
  exact LinearMap.mem_ker.mp (hle hx)

omit [DecidableEq V] in
/-- `dim C^⊥ = |V| - dim C`. -/
theorem finrank_codeOrth (C : Submodule F₂ (V → F₂)) :
    finrank F₂ ((dotForm V).orthogonal C) = Fintype.card V - finrank F₂ C := by
  classical
  rw [LinearMap.BilinForm.finrank_orthogonal dotForm_nondegenerate,
    Module.finrank_fintype_fun_eq_card]

omit [DecidableEq V] in
/-- `C^⊥⊥ = C`. -/
theorem codeOrth_codeOrth (C : Submodule F₂ (V → F₂)) :
    (dotForm V).orthogonal ((dotForm V).orthogonal C) = C :=
  LinearMap.BilinForm.orthogonal_orthogonal dotForm_nondegenerate dotForm_isRefl C

/-- A binary code `C ≤ 𝔽₂^V` is self-orthogonal when `C ≤ C^⊥` for the dot product. -/
def IsSelfOrth (C : Submodule F₂ (V → F₂)) : Prop :=
  C ≤ (dotForm V).orthogonal C

/-- A binary code is self-dual when `C^⊥ = C` (`results/spinor-codes.md` Theorem 1.1,
organize-archive d846b99). -/
def IsSelfDual (C : Submodule F₂ (V → F₂)) : Prop :=
  (dotForm V).orthogonal C = C

variable {C C' : Submodule F₂ (V → F₂)}

omit [DecidableEq V] in
theorem IsSelfDual.isSelfOrth (hC : IsSelfDual C) : IsSelfOrth C := by
  rw [IsSelfOrth, hC]

omit [DecidableEq V] in
theorem IsSelfOrth.mono (hC : IsSelfOrth C) (h : C' ≤ C) : IsSelfOrth C' :=
  le_trans h (le_trans hC (LinearMap.BilinForm.orthogonal_le h))

omit [DecidableEq V] in
/-- A self-orthogonal code has even weights, so it lies in `U` (`U`, ham-spin 87df892). -/
theorem IsSelfOrth.le_U (hC : IsSelfOrth C) : C ≤ U V := fun x hx ↦ by
  rw [mem_U, ← dot_self]
  exact mem_codeOrth.mp (hC hx) x hx

omit [DecidableEq V] in
/-- Theorem 1.1.1 of `results/spinor-codes.md` (organize-archive d846b99): a self-dual code lies in
`U` (`U`, ham-spin 87df892). -/
theorem IsSelfDual.le_U (hC : IsSelfDual C) : C ≤ U V :=
  hC.isSelfOrth.le_U

omit [DecidableEq V] in
/-- Theorem 1.1.1 of `results/spinor-codes.md` (organize-archive d846b99): a self-dual code
contains `𝟙`. -/
theorem IsSelfDual.one_mem (hC : IsSelfDual C) : (1 : V → F₂) ∈ C := by
  rw [← hC, mem_codeOrth]
  intro x hx
  rw [dot_comm, dot_one_left, ← mem_U]
  exact hC.le_U hx

variable {n : ℕ}

omit [DecidableEq V] in
/-- A self-orthogonal code of length `2n` has dimension at most `n`. -/
theorem finrank_le_of_isSelfOrth (hV : Fintype.card V = 2 * n) (hC : IsSelfOrth C) :
    finrank F₂ C ≤ n := by
  classical
  have h1 := Submodule.finrank_mono hC
  rw [finrank_codeOrth, hV] at h1
  omega

omit [DecidableEq V] in
/-- A self-dual code of length `2n` has dimension `n`. -/
theorem IsSelfDual.finrank_eq (hV : Fintype.card V = 2 * n) (hC : IsSelfDual C) :
    finrank F₂ C = n := by
  classical
  have h1 := finrank_codeOrth C
  rw [hC, hV] at h1
  omega

omit [DecidableEq V] in
/-- A self-orthogonal code of length `2n` and dimension `n` is self-dual. -/
theorem isSelfDual_of_finrank (hV : Fintype.card V = 2 * n) (hC : IsSelfOrth C)
    (h : finrank F₂ C = n) : IsSelfDual C := by
  classical
  refine (Submodule.eq_of_le_of_finrank_le hC ?_).symm
  rw [finrank_codeOrth, hV, h]
  omega

omit [DecidableEq V] in
/-- Adding an isotropic vector of `C^⊥` to a self-orthogonal code keeps it self-orthogonal. -/
theorem IsSelfOrth.sup_span (hC : IsSelfOrth C) {x : V → F₂}
    (hx : x ∈ (dotForm V).orthogonal C) (hxx : dot x x = 0) : IsSelfOrth (C ⊔ F₂ ∙ x) := by
  intro y hy
  rw [mem_codeOrth]
  intro z hz
  obtain ⟨c, hc, a, ha, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨d, hd, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.mp hb
  have h1 : dot d c = 0 := mem_codeOrth.mp (hC hc) d hd
  have h2 : dot d x = 0 := mem_codeOrth.mp hx d hd
  have h3 : dot x c = 0 := by
    rw [dot_comm]
    exact mem_codeOrth.mp hx c hc
  change dotForm V (d + β • x) (c + α • x) = 0
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, dotForm_apply, h1, h2,
    h3, hxx, smul_eq_mul, mul_zero, add_zero]

omit [DecidableEq V] in
/-- A self-orthogonal code of length `2n` and dimension below `n` lies in a larger one. -/
theorem exists_isSelfOrth_gt (hV : Fintype.card V = 2 * n) (hC : IsSelfOrth C)
    (h : finrank F₂ C < n) : ∃ C', IsSelfOrth C' ∧ C < C' := by
  classical
  by_cases h1 : (1 : V → F₂) ∈ C
  · have hlt : C < (dotForm V).orthogonal C := by
      refine lt_of_le_of_ne hC fun he ↦ ?_
      have h2 := finrank_codeOrth C
      rw [← he, hV] at h2
      omega
    obtain ⟨x, hx, hxC⟩ := IsConcreteLE.exists_of_lt hlt
    refine ⟨C ⊔ F₂ ∙ x, hC.sup_span hx ?_, lt_of_le_of_ne le_sup_left fun he ↦ hxC ?_⟩
    · rw [dot_self, ← dot_one_left]
      exact mem_codeOrth.mp hx 1 h1
    · rw [he]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  · refine ⟨C ⊔ F₂ ∙ (1 : V → F₂), hC.sup_span ?_ ?_,
      lt_of_le_of_ne le_sup_left fun he ↦ h1 ?_⟩
    · rw [mem_codeOrth]
      intro x hx
      rw [dot_comm, dot_one_left, ← mem_U]
      exact hC.le_U hx
    · rw [dot_one_left]
      simp only [Pi.one_apply, Finset.sum_const, Finset.card_univ, hV, nsmul_eq_mul, mul_one,
        Nat.cast_mul]
      rw [show ((2 : ℕ) : F₂) = 0 by decide, zero_mul]
    · rw [he]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

omit [DecidableEq V] in
theorem one_mem_U (hV : Fintype.card V = 2 * n) : (1 : V → F₂) ∈ U V := by
  rw [mem_U]
  simp only [Pi.one_apply, Finset.sum_const, Finset.card_univ, hV, nsmul_eq_mul, mul_one,
    Nat.cast_mul]
  rw [show ((2 : ℕ) : F₂) = 0 by decide, zero_mul]

omit [DecidableEq V] in
/-- `U = ⟨𝟙⟩^⊥` (`U`, ham-spin 87df892). -/
theorem U_eq_codeOrth : U V = (dotForm V).orthogonal (F₂ ∙ (1 : V → F₂)) := by
  ext x
  rw [mem_U, mem_codeOrth]
  constructor
  · intro hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    change dotForm V (a • 1) x = 0
    rw [map_smul, LinearMap.smul_apply, dotForm_apply, dot_one_left, hx, smul_zero]
  · intro h
    rw [← dot_one_left]
    exact h 1 (Submodule.mem_span_singleton_self 1)

omit [DecidableEq V] in
/-- `dim U = 2n - 1` (`U`, ham-spin 87df892). With `ε`, the space `U ⊕ 𝔽₂ε` has dimension `2n`,
and `Ũ_n` has dimension `2n - 1` (Theorem 1.1 of `results/spinor-hull-extend.md`, organize-archive
b47b504). -/
theorem finrank_U (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n) : finrank F₂ (U V) = 2 * n - 1 := by
  classical
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have h1 : (1 : V → F₂) ≠ 0 := fun h ↦ by
    obtain ⟨i⟩ := hne
    exact one_ne_zero (congrFun h i)
  rw [U_eq_codeOrth, finrank_codeOrth, finrank_span_singleton h1, hV]

omit [DecidableEq V] in
/-- Opposite self-dual codes span `U`: if `C ∩ C' ≤ ⟨𝟙⟩` then `C + C' = U` (`U`, ham-spin
87df892). -/
theorem sup_eq_U_of_inf_le (hC : IsSelfDual C) (hC' : IsSelfDual C')
    (h : C ⊓ C' ≤ F₂ ∙ (1 : V → F₂)) : C ⊔ C' = U V := by
  classical
  refine le_antisymm (sup_le hC.le_U hC'.le_U) ?_
  have h1 : (dotForm V).orthogonal (C ⊔ C') ≤ F₂ ∙ (1 : V → F₂) := by
    refine le_trans (le_inf ?_ ?_) h
    · conv_rhs => rw [← hC]
      exact LinearMap.BilinForm.orthogonal_le le_sup_left
    · conv_rhs => rw [← hC']
      exact LinearMap.BilinForm.orthogonal_le le_sup_right
  rw [U_eq_codeOrth, ← codeOrth_codeOrth (C ⊔ C')]
  exact LinearMap.BilinForm.orthogonal_le h1

omit [Fintype V] [DecidableEq V] in
/-- Over `𝔽₂`, `⟨𝟙⟩ = {0, 𝟙}`. -/
theorem mem_span_one_iff {x : V → F₂} : x ∈ F₂ ∙ (1 : V → F₂) ↔ x = 0 ∨ x = 1 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rcases f2_cases a with rfl | rfl
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr (one_smul _ _)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

end Code

section PairCode

/-- `i₂(P)`, the words of `𝔽₂^V` that are unions of edges of the perfect matching `P`, the
`P`-closed words of `results/spinor-codes.md` (organize-archive d846b99). -/
def pairCode (P : PerfectMatching V) : Submodule F₂ (V → F₂) where
  carrier := {x | ∀ i, x (P.mate i) = x i}
  add_mem' := fun {x y} (hx : ∀ i, x (P.mate i) = x i) (hy : ∀ i, y (P.mate i) = y i) i ↦ by
    rw [Pi.add_apply, Pi.add_apply, hx i, hy i]
  zero_mem' _ := rfl
  smul_mem' := fun c x (hx : ∀ i, x (P.mate i) = x i) i ↦ by
    rw [Pi.smul_apply, Pi.smul_apply, hx i]

omit [Fintype V] [DecidableEq V] in
theorem mem_pairCode {P : PerfectMatching V} {x : V → F₂} :
    x ∈ pairCode P ↔ ∀ i, x (P.mate i) = x i :=
  Iff.rfl

omit [Fintype V] [DecidableEq V] in
theorem one_mem_pairCode (P : PerfectMatching V) : (1 : V → F₂) ∈ pairCode P :=
  fun _ ↦ rfl

omit [Fintype V] in
/-- `v_{i, P i} ∈ i₂(P)` (`v`, ham-spin 87df892). -/
theorem v_mate_mem_pairCode (P : PerfectMatching V) (i : V) : v i (P.mate i) ∈ pairCode P := by
  intro k
  have e1 : (P.mate k = i) ↔ (k = P.mate i) :=
    ⟨fun h ↦ by rw [← h, mate_mate], fun h ↦ by rw [h, mate_mate]⟩
  have e2 : (P.mate k = P.mate i) ↔ (k = i) := P.mate.injective.eq_iff
  simp only [v, Pi.add_apply, Pi.single_apply, e1, e2]
  exact add_comm _ _

private theorem f2_add_eq_zero_iff (a b : F₂) : a + b = 0 ↔ b = a := by
  revert a b
  decide

omit [DecidableEq V] in
/-- `i₂(P)` is self-dual. -/
theorem isSelfDual_pairCode (P : PerfectMatching V) : IsSelfDual (pairCode P) := by
  classical
  refine le_antisymm (fun y hy i ↦ ?_) fun y hy ↦ mem_codeOrth.mpr fun x hx ↦ ?_
  · have h := mem_codeOrth.mp hy _ (v_mate_mem_pairCode P i)
    rwa [dot_v_left, f2_add_eq_zero_iff] at h
  · refine Finset.sum_ninvolution P.mate (fun j ↦ ?_) (fun j _ ↦ P.mate_ne j)
      (fun j ↦ Finset.mem_univ _) (fun j ↦ mate_mate P j)
    rw [hx j, hy j]
    exact CharTwo.add_self_eq_zero _

omit [Fintype V] in
/-- `i₂(P) = span{v_{i, P i}}` (`v`, ham-spin 87df892). -/
theorem span_v_mate [Finite V] (P : PerfectMatching V) :
    Submodule.span F₂ (Set.range fun i ↦ v i (P.mate i)) = pairCode P := by
  have := Fintype.ofFinite V
  have h : (dotForm V).orthogonal (Submodule.span F₂ (Set.range fun i ↦ v i (P.mate i))) =
      pairCode P := by
    ext y
    rw [mem_codeOrth_span, Set.forall_mem_range, mem_pairCode]
    exact forall_congr' fun i ↦ by rw [dot_v_left, f2_add_eq_zero_iff]
  rw [← codeOrth_codeOrth (Submodule.span F₂ _), h, isSelfDual_pairCode]

end PairCode

section Extended

variable (V) in
/-- `q̃(x + λε) = q(x) + λ` on `U ⊕ 𝔽₂ε = U V × 𝔽₂` (`qForm`, ham-spin 87df892; Theorem 1 of
`results/spinor-hull-extend.md`, organize-archive b47b504). -/
def qE : QuadraticForm F₂ (U V × F₂) :=
  (qForm V).prod QuadraticMap.sq

omit [DecidableEq V] in
theorem qE_apply (z : U V × F₂) : qE V z = qfun (z.1 : V → F₂) + z.2 := by
  rw [qE, QuadraticMap.prod_apply, QuadraticMap.sq_apply, qForm_apply, f2_mul_self']

omit [DecidableEq V] in
/-- The polar form of `q̃` is `B(x + λε, y + με) = x · y`, so `B(ε, ·) = 0`. -/
theorem polar_qE (z w : U V × F₂) :
    QuadraticMap.polar (qE V) z w = dot (z.1 : V → F₂) w.1 := by
  rw [QuadraticMap.polar, qE_apply, qE_apply, qE_apply, Prod.fst_add, Prod.snd_add,
    Submodule.coe_add, qfun_add z.1.2 w.1.2]
  ring

omit [DecidableEq V] in
theorem qE_add (z w : U V × F₂) :
    qE V (z + w) = qE V z + qE V w + QuadraticMap.polar (qE V) z w := by
  rw [QuadraticMap.polar]
  ring

variable (V) in
/-- `ε = 0 + 1ε`. -/
def epsE : U V × F₂ :=
  (0, 1)

omit [DecidableEq V] in
/-- `q(ε) = 1`. -/
theorem qE_epsE : qE V (epsE V) = 1 := by
  rw [qE_apply, epsE, ZeroMemClass.coe_zero, qfun_zero, zero_add]

omit [DecidableEq V] in
/-- `B(ε, ·) = 0`. -/
theorem polar_epsE (w : U V × F₂) : QuadraticMap.polar (qE V) (epsE V) w = 0 := by
  rw [polar_qE, epsE, ZeroMemClass.coe_zero]
  simp [dot]

/-- A subspace of `U ⊕ 𝔽₂ε` is totally singular when `q̃` vanishes on it (Theorem 1 of
`results/spinor-hull-extend.md`, organize-archive b47b504). -/
def IsTotSing (M : Submodule F₂ (U V × F₂)) : Prop :=
  ∀ z ∈ M, qE V z = 0

variable {M M' N : Submodule F₂ (U V × F₂)}

omit [DecidableEq V] in
theorem IsTotSing.mono (hM : IsTotSing M) (h : N ≤ M) : IsTotSing N :=
  fun z hz ↦ hM z (h hz)

omit [DecidableEq V] in
/-- On a totally singular subspace the polar form vanishes. -/
theorem IsTotSing.polar_eq_zero (hM : IsTotSing M) {z w : U V × F₂} (hz : z ∈ M) (hw : w ∈ M) :
    QuadraticMap.polar (qE V) z w = 0 := by
  rw [QuadraticMap.polar, hM _ (M.add_mem hz hw), hM z hz, hM w hw, sub_zero, sub_zero]

omit [DecidableEq V] in
theorem IsTotSing.dot_eq_zero (hM : IsTotSing M) {z w : U V × F₂} (hz : z ∈ M) (hw : w ∈ M) :
    dot (z.1 : V → F₂) w.1 = 0 := by
  rw [← polar_qE]
  exact hM.polar_eq_zero hz hw

omit [DecidableEq V] in
/-- Adding a singular vector orthogonal to a totally singular subspace keeps it totally
singular. -/
theorem IsTotSing.sup_span (hM : IsTotSing M) {z : U V × F₂} (hz : qE V z = 0)
    (hpol : ∀ m ∈ M, QuadraticMap.polar (qE V) m z = 0) : IsTotSing (M ⊔ F₂ ∙ z) := by
  intro y hy
  obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [qE_add, hM m hm, QuadraticMap.map_smul, hz, QuadraticMap.polar_smul_right, hpol m hm]
  simp

variable (V) in
/-- The projection `U ⊕ 𝔽₂ε → 𝔽₂^V`, `x + λε ↦ x`. -/
def projE : U V × F₂ →ₗ[F₂] V → F₂ :=
  (U V).subtype ∘ₗ LinearMap.fst F₂ (U V) F₂

omit [DecidableEq V] in
theorem projE_apply (z : U V × F₂) : projE V z = z.1 :=
  rfl

/-- The code of `M ≤ U ⊕ 𝔽₂ε`, its projection to `𝔽₂^V` (Theorem 1.1.2 of `results/spinor-codes.md`,
organize-archive d846b99). -/
def codeOf (M : Submodule F₂ (U V × F₂)) : Submodule F₂ (V → F₂) :=
  M.map (projE V)

/-- `M_C = {x + q(x)ε : x ∈ C}`, the span of the singular lifts of the words of `C`
(Theorem 1.1.2 of `results/spinor-codes.md`, organize-archive d846b99). For a self-orthogonal `C`
the span adds nothing (`mem_liftCode`). -/
def liftCode (C : Submodule F₂ (V → F₂)) : Submodule F₂ (U V × F₂) :=
  Submodule.span F₂ {z | (z.1 : V → F₂) ∈ C ∧ qE V z = 0}

variable {C C' D : Submodule F₂ (V → F₂)}

omit [DecidableEq V] in
/-- For a self-orthogonal `C`, `M_C` is exactly the set of singular lifts of the words of `C`. -/
theorem mem_liftCode (hC : IsSelfOrth C) {z : U V × F₂} :
    z ∈ liftCode C ↔ (z.1 : V → F₂) ∈ C ∧ qE V z = 0 := by
  refine ⟨fun hz ↦ ?_, fun hz ↦ Submodule.subset_span hz⟩
  let N : Submodule F₂ (U V × F₂) :=
    { carrier := {z | (z.1 : V → F₂) ∈ C ∧ qE V z = 0}
      add_mem' := fun {z w} (hz : (z.1 : V → F₂) ∈ C ∧ qE V z = 0)
          (hw : (w.1 : V → F₂) ∈ C ∧ qE V w = 0) ↦ by
        refine ⟨C.add_mem hz.1 hw.1, ?_⟩
        rw [qE_add, hz.2, hw.2, polar_qE, mem_codeOrth.mp (hC hw.1) _ hz.1, add_zero, add_zero]
      zero_mem' := ⟨C.zero_mem, QuadraticMap.map_zero _⟩
      smul_mem' := fun c z (hz : (z.1 : V → F₂) ∈ C ∧ qE V z = 0) ↦ by
        refine ⟨C.smul_mem c hz.1, ?_⟩
        rw [QuadraticMap.map_smul, hz.2, smul_zero] }
  exact (Submodule.span_le.mpr (fun z hz ↦ hz) : liftCode C ≤ N) hz

omit [DecidableEq V] in
theorem liftCode_mono (h : C ≤ C') : liftCode C ≤ liftCode C' :=
  Submodule.span_mono fun _ hz ↦ ⟨h hz.1, hz.2⟩

omit [DecidableEq V] in
theorem isTotSing_liftCode (hC : IsSelfOrth C) : IsTotSing (liftCode C) :=
  fun _ hz ↦ ((mem_liftCode hC).mp hz).2

omit [DecidableEq V] in
/-- The code of `M_C` is `C`. -/
theorem codeOf_liftCode (hC : IsSelfOrth C) : codeOf (liftCode C) = C := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ((mem_liftCode hC).mp hz).1
  · intro hx
    refine ⟨(⟨x, hC.le_U hx⟩, qfun x), (mem_liftCode hC).mpr ⟨hx, ?_⟩, rfl⟩
    rw [qE_apply]
    exact CharTwo.add_self_eq_zero _

omit [DecidableEq V] in
/-- A totally singular `M` is `M_C` for its code `C`. -/
theorem liftCode_codeOf (hM : IsTotSing M) : liftCode (codeOf M) = M := by
  refine le_antisymm (Submodule.span_le.mpr ?_) fun z hz ↦
    Submodule.subset_span ⟨⟨z, hz, rfl⟩, hM z hz⟩
  rintro z ⟨⟨w, hw, hwz⟩, hz⟩
  have h1 : w.1 = z.1 := Subtype.ext hwz
  have h2 : w.2 = z.2 := by
    have hq := hM w hw
    rw [qE_apply, h1] at hq
    rw [qE_apply] at hz
    linear_combination hq - hz
  have hwz' : w = z := Prod.ext h1 h2
  exact hwz' ▸ hw

omit [DecidableEq V] in
/-- The code of a totally singular subspace is self-orthogonal. -/
theorem isSelfOrth_codeOf (hM : IsTotSing M) : IsSelfOrth (codeOf M) := by
  rintro _ ⟨w, hw, rfl⟩
  rw [mem_codeOrth]
  rintro _ ⟨z, hz, rfl⟩
  exact hM.dot_eq_zero hz hw

omit [DecidableEq V] in
/-- The projection is injective on a totally singular subspace, since `ε` is not singular. -/
theorem IsTotSing.eq_zero_of_projE (hM : IsTotSing M) {z : U V × F₂} (hz : z ∈ M)
    (h : projE V z = 0) : z = 0 := by
  have h1 : z.1 = 0 := Subtype.ext h
  have hq := hM z hz
  rw [qE_apply, h1, ZeroMemClass.coe_zero, qfun_zero, zero_add] at hq
  exact Prod.ext h1 hq

omit [DecidableEq V] in
/-- `dim codeOf M = dim M` for a totally singular `M`. -/
theorem finrank_codeOf (hM : IsTotSing M) : finrank F₂ (codeOf M) = finrank F₂ M := by
  have hinj : Function.Injective ((projE V).domRestrict M) := by
    intro a b hab
    have h0 := hM.eq_zero_of_projE (M.sub_mem a.2 b.2)
      (by rw [map_sub]; exact sub_eq_zero.mpr hab)
    exact Subtype.ext (sub_eq_zero.mp h0)
  rw [codeOf, ← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj hinj

omit [DecidableEq V] in
/-- `dim M_C = dim C` for a self-orthogonal `C`. -/
theorem finrank_liftCode (hC : IsSelfOrth C) : finrank F₂ (liftCode C) = finrank F₂ C := by
  rw [← finrank_codeOf (isTotSing_liftCode hC), codeOf_liftCode hC]

variable {n : ℕ}

omit [DecidableEq V] in
/-- `q(𝟙) = n mod 2` for `|V| = 2n`. -/
theorem qfun_one (hV : Fintype.card V = 2 * n) : qfun (1 : V → F₂) = (n : F₂) := by
  have hs : supp (1 : V → F₂) = Finset.univ := by
    ext k
    simp [supp]
  rw [qfun, hs, Finset.card_univ, hV, Nat.mul_div_cancel_left n two_pos]

/-- `kE = 𝟙 + nε`, the vector whose span is the kernel of `U ⊕ 𝔽₂ε → Ũ_n` (Theorem 1 of
`results/spinor-hull-extend.md`, organize-archive b47b504). -/
def kE (hV : Fintype.card V = 2 * n) : U V × F₂ :=
  (⟨1, one_mem_U hV⟩, (n : F₂))

omit [DecidableEq V] in
/-- `q̃(𝟙 + nε) = 0`. -/
theorem qE_kE (hV : Fintype.card V = 2 * n) : qE V (kE hV) = 0 := by
  rw [qE_apply, kE]
  change qfun (1 : V → F₂) + (n : F₂) = 0
  rw [qfun_one hV]
  exact CharTwo.add_self_eq_zero _

omit [DecidableEq V] in
/-- `B(𝟙 + nε, ·) = 0`. -/
theorem polar_kE (hV : Fintype.card V = 2 * n) (w : U V × F₂) :
    QuadraticMap.polar (qE V) w (kE hV) = 0 := by
  rw [polar_qE, dot_comm]
  change dot 1 (w.1 : V → F₂) = 0
  rw [dot_one_left, ← mem_U]
  exact w.1.2

omit [DecidableEq V] in
/-- `Ũ_n` is nondegenerate (Theorem 1.1 of `results/spinor-hull-extend.md`, organize-archive
b47b504): a singular vector of `U ⊕ 𝔽₂ε` that is `B`-orthogonal to everything is a multiple of
`kE = 𝟙 + nε`. With `qE_epsE` and `polar_epsE`, the `B`-radical of `Ũ_n` is `⟨ε̄⟩` with
`q(ε̄) = 1`. -/
theorem mem_span_kE_of_polar (hV : Fintype.card V = 2 * n) {z : U V × F₂}
    (hpol : ∀ w, QuadraticMap.polar (qE V) z w = 0) (hq : qE V z = 0) : z ∈ F₂ ∙ kE hV := by
  classical
  have hconst : ∀ i j, (z.1 : V → F₂) i = (z.1 : V → F₂) j := fun i j ↦ by
    have h := hpol (⟨v i j, v_mem i j⟩, 0)
    rw [polar_qE, dot_comm, dot_v_left, f2_add_eq_zero_iff] at h
    exact h.symm
  rw [qE_apply] at hq
  by_cases h : ∃ i, (z.1 : V → F₂) i = 1
  · obtain ⟨i, hi⟩ := h
    have h1 : z.1 = ⟨1, one_mem_U hV⟩ := Subtype.ext (funext fun j ↦ (hconst j i).trans hi)
    have h2 : z.2 = n := by
      rw [h1] at hq
      change qfun (1 : V → F₂) + z.2 = 0 at hq
      rw [qfun_one hV] at hq
      exact (f2_add_eq_zero_iff _ _).mp hq
    have hz : z = kE hV := Prod.ext h1 h2
    rw [hz]
    exact Submodule.mem_span_singleton_self _
  · simp only [not_exists] at h
    have h1 : z.1 = 0 := Subtype.ext (funext fun j ↦ (f2_cases _).resolve_right (h j))
    rw [h1, ZeroMemClass.coe_zero, qfun_zero, zero_add] at hq
    have hz : z = 0 := Prod.ext h1 hq
    rw [hz]
    exact zero_mem _

omit [DecidableEq V] in
/-- Witt index (Theorem 1.1 of `results/spinor-hull-extend.md`, organize-archive b47b504): a
totally singular subspace of `U ⊕ 𝔽₂ε` has dimension at most `n`, so one of `Ũ_n` has dimension at
most `n - 1`. -/
theorem finrank_le_of_isTotSing (hV : Fintype.card V = 2 * n) (hM : IsTotSing M) :
    finrank F₂ M ≤ n := by
  classical
  rw [← finrank_codeOf hM]
  exact finrank_le_of_isSelfOrth hV (isSelfOrth_codeOf hM)

omit [DecidableEq V] in
/-- Every maximal totally singular subspace contains `kE = 𝟙 + nε`, so it is the preimage of a
maximal totally singular subspace of `Ũ_n` (Theorem 1 of `results/spinor-hull-extend.md`,
organize-archive b47b504). -/
theorem kE_mem_of_maximal (hV : Fintype.card V = 2 * n) (hM : Maximal IsTotSing M) :
    kE hV ∈ M :=
  hM.2 (hM.1.sup_span (qE_kE hV) fun m _ ↦ polar_kE hV m) le_sup_left
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))

omit [DecidableEq V] in
/-- The maximal totally singular subspaces of `U ⊕ 𝔽₂ε` are the totally singular ones of
dimension `n`, so the Witt index of `Ũ_n` is `n - 1` (Theorem 1.1 of
`results/spinor-hull-extend.md`, organize-archive b47b504). -/
theorem maximal_isTotSing_iff (hV : Fintype.card V = 2 * n) :
    Maximal IsTotSing M ↔ IsTotSing M ∧ finrank F₂ M = n := by
  classical
  constructor
  · intro hM
    refine ⟨hM.1, le_antisymm (finrank_le_of_isTotSing hV hM.1) (not_lt.mp fun hlt ↦ ?_)⟩
    have hC := isSelfOrth_codeOf hM.1
    obtain ⟨C', hC', hlt'⟩ := exists_isSelfOrth_gt hV hC (by rwa [finrank_codeOf hM.1])
    have hle : M ≤ liftCode C' := by
      conv_lhs => rw [← liftCode_codeOf hM.1]
      exact liftCode_mono hlt'.le
    have hge := hM.2 (isTotSing_liftCode hC') hle
    have h3 : C' ≤ codeOf M := by
      rw [← codeOf_liftCode hC']
      exact Submodule.map_mono hge
    exact hlt'.not_ge h3
  · rintro ⟨hM, hdim⟩
    refine ⟨hM, fun M' hM' hle ↦ (Submodule.eq_of_le_of_finrank_le hle ?_).ge⟩
    rw [hdim]
    exact finrank_le_of_isTotSing hV hM'

omit [DecidableEq V] in
/-- `M_C` is maximal totally singular for a self-dual `C` (Theorem 1.1.2 of
`results/spinor-codes.md`, organize-archive d846b99). -/
theorem maximal_liftCode (hV : Fintype.card V = 2 * n) (hC : IsSelfDual C) :
    Maximal IsTotSing (liftCode C) :=
  (maximal_isTotSing_iff hV).mpr
    ⟨isTotSing_liftCode hC.isSelfOrth, by rw [finrank_liftCode hC.isSelfOrth, hC.finrank_eq hV]⟩

omit [DecidableEq V] in
/-- The code of a maximal totally singular subspace is self-dual (Theorem 1.1.2 of
`results/spinor-codes.md`, organize-archive d846b99). -/
theorem isSelfDual_codeOf (hV : Fintype.card V = 2 * n) (hM : Maximal IsTotSing M) :
    IsSelfDual (codeOf M) := by
  classical
  refine isSelfDual_of_finrank hV (isSelfOrth_codeOf hM.1) ?_
  rw [finrank_codeOf hM.1]
  exact ((maximal_isTotSing_iff hV).mp hM).2

/-- Theorem 1.1.2 of `results/spinor-codes.md` (organize-archive d846b99): `C ↦ M_C` is a bijection
from the self-dual codes of length `2n` onto the maximal totally singular subspaces of
`U ⊕ 𝔽₂ε`, equivalently of `Ũ_n`, with inverse `M ↦ codeOf M`. -/
def selfDualEquiv (hV : Fintype.card V = 2 * n) :
    {C : Submodule F₂ (V → F₂) // IsSelfDual C} ≃
      {M : Submodule F₂ (U V × F₂) // Maximal IsTotSing M} where
  toFun C := ⟨liftCode C.1, maximal_liftCode hV C.2⟩
  invFun M := ⟨codeOf M.1, isSelfDual_codeOf hV M.2⟩
  left_inv C := Subtype.ext (codeOf_liftCode C.2.isSelfOrth)
  right_inv M := Subtype.ext (liftCode_codeOf M.2.1)

omit [DecidableEq V] in
/-- Theorem 1.3 of `results/spinor-hull-extend.md` (organize-archive b47b504), first half:
`M_P = {x + q(x)ε : x ∈ span P}` is maximal totally singular. -/
theorem maximal_liftCode_pairCode (hV : Fintype.card V = 2 * n) (P : PerfectMatching V) :
    Maximal IsTotSing (liftCode (pairCode P)) :=
  maximal_liftCode hV (isSelfDual_pairCode P)

omit [DecidableEq V] in
/-- `M_(C ∩ C') = M_C ∩ M_C'` for self-orthogonal codes. -/
theorem liftCode_inf (hC : IsSelfOrth C) (hC' : IsSelfOrth C') :
    liftCode (C ⊓ C') = liftCode C ⊓ liftCode C' := by
  ext z
  rw [Submodule.mem_inf, mem_liftCode (hC.mono inf_le_left), mem_liftCode hC, mem_liftCode hC',
    Submodule.mem_inf]
  tauto

omit [DecidableEq V] in
/-- Theorem 1.1.5 of `results/spinor-codes.md` (organize-archive d846b99), first sentence:
`dim(M_C ∩ M_C') = dim(C ∩ C')` in `U ⊕ 𝔽₂ε`. Both contain `kE`, so in `Ũ_n` this is
`dim(C ∩ C') - 1`. The dual polar distance `d = s - dim(C ∩ C')` is not formalized. -/
theorem finrank_liftCode_inf (hC : IsSelfOrth C) (hC' : IsSelfOrth C') :
    finrank F₂ ↥(liftCode C ⊓ liftCode C') = finrank F₂ ↥(C ⊓ C') := by
  rw [← liftCode_inf hC hC', finrank_liftCode (hC.mono inf_le_left)]

omit [DecidableEq V] in
theorem liftCode_le_liftCode_iff (hD : IsSelfOrth D) (hC : IsSelfOrth C) :
    liftCode D ≤ liftCode C ↔ D ≤ C := by
  refine ⟨fun h ↦ ?_, liftCode_mono⟩
  rw [← codeOf_liftCode hD, ← codeOf_liftCode hC]
  exact Submodule.map_mono h

omit [DecidableEq V] in
/-- `⟨kE⟩ = M_⟨𝟙⟩`. -/
theorem span_kE_eq (hV : Fintype.card V = 2 * n) :
    F₂ ∙ kE hV = liftCode (F₂ ∙ (1 : V → F₂)) := by
  have hts : IsTotSing (F₂ ∙ kE hV) := fun z hz ↦ by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [QuadraticMap.map_smul, qE_kE hV, smul_zero]
  rw [← liftCode_codeOf hts, codeOf, Submodule.map_span, Set.image_singleton]
  rfl

omit [DecidableEq V] in
/-- `F₂ ∙ 𝟙` is self-orthogonal for `|V| = 2n`. -/
theorem isSelfOrth_span_one (hV : Fintype.card V = 2 * n) : IsSelfOrth (F₂ ∙ (1 : V → F₂)) := by
  rw [IsSelfOrth, ← U_eq_codeOrth, Submodule.span_singleton_le_iff_mem]
  exact one_mem_U hV

omit [DecidableEq V] in
/-- Opposition in code form: `M_C ∩ M_C' = 0` in `Ũ_n` iff `C ∩ C' ≤ ⟨𝟙⟩` (Theorem 1.1.6 of
`results/spinor-codes.md`, organize-archive d846b99, the step from part 5). -/
theorem liftCode_inf_le_span_kE_iff (hV : Fintype.card V = 2 * n) (hC : IsSelfOrth C)
    (hC' : IsSelfOrth C') :
    liftCode C ⊓ liftCode C' ≤ F₂ ∙ kE hV ↔ C ⊓ C' ≤ F₂ ∙ (1 : V → F₂) := by
  rw [← liftCode_inf hC hC', span_kE_eq hV]
  exact liftCode_le_liftCode_iff (hC.mono inf_le_left) (isSelfOrth_span_one hV)

end Extended

end Pairing.PerfectMatching
