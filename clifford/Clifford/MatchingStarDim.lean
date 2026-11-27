import Clifford.Frame
import Clifford.PolarSection

/-!
# Matching stars of the first blocks (COD-275)

`E_j = {(2a, 2a+1) : a < j}` is the set of the first `j` edges of `P0`. Its matching star
`L_{E_j} = ⋂_{e ∈ E_j} ker(1 + Γ_e)` (`matchingStar`, `Clifford.PolarSection`) is spanned by the
rows `w_S = r_{X_S}` of the completions `X_S ⊇ E_j`, namely the `S` with no gap below `j`. These
rows are part of `wBasis`, so `dim L_{E_j} = 2^(n-1-j)`.

This is Corollary A4 of `results/presentation-consequences-extend.md` (organize-archive 3ba2201),
proved with the lowering operators `lower_w` of `Clifford.Frame`. It is archive Theorem 7.2 for
the first blocks, as corrected in `results/switch-patterns-factcheck-extend.md` (3293188).

* `mem_matchingStar_firstBlocks` : `x ∈ L_{E_j}` iff every block swap `a < j` fixes `x`.
* `completions` : the gap sets `S` with `j ≤ g` for every `g ∈ S`.
* `matchingStar_firstBlocks_eq_span` : `L_{E_j} = span{w_S : S ∈ completions j}`.
* `finrank_matchingStar_firstBlocks` : `dim L_{E_j} = 2^(n-1-j)`.
-/

namespace Pairing.PerfectMatching

open Equiv

variable (n : ℕ)

/-- The first `j` edges `(2a, 2a+1)` of `P0`. -/
def firstBlocks (j : ℕ) : Set (Sym2 (Fin (2 * n))) :=
  {e | ∃ a : Fin n, (a : ℕ) < j ∧ e = s(blockLo n a, blockHi n a)}

/-- `x ∈ L_{E_j}` iff the block swaps `a < j` fix `x`. -/
theorem mem_matchingStar_firstBlocks {j : ℕ} {x : W (Fin (2 * n))} :
    x ∈ matchingStar (firstBlocks n j) ↔ ∀ a : Fin n, (a : ℕ) < j → B n a x = x := by
  rw [mem_matchingStar]
  constructor
  · intro h a ha
    exact mem_edgeStar_mk.mp (h _ ⟨a, ha, rfl⟩)
  · rintro h _ ⟨a, ha, rfl⟩
    exact mem_edgeStar_mk.mpr (h a ha)

/-- The gap sets of the completions of `E_j`, those with no gap below `j`. -/
def completions (j : ℕ) : Finset (Finset (Fin (n - 1))) :=
  Finset.univ.filter fun S ↦ ∀ g ∈ S, j ≤ (g : ℕ)

theorem mem_completions {j : ℕ} {S : Finset (Fin (n - 1))} :
    S ∈ completions n j ↔ ∀ g ∈ S, j ≤ (g : ℕ) := by
  simp [completions]

/-- `#completions j = 2^(n-1-j)`. -/
theorem card_completions (j : ℕ) : (completions n j).card = 2 ^ (n - 1 - j) := by
  have e : completions n j = (Finset.univ.filter fun g : Fin (n - 1) ↦ j ≤ (g : ℕ)).powerset := by
    ext S
    simp [completions, Finset.subset_iff]
  have hlt := Fin.card_filter_val_lt (n := n - 1) (m := j)
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun g : Fin (n - 1) ↦ (g : ℕ) < j)
  simp only [not_lt, Finset.card_univ, Fintype.card_fin] at hsum
  rw [e, Finset.card_powerset]
  congr 1
  omega

/-- A completion row lies in `L_{E_j}`. -/
theorem w_mem_matchingStar_firstBlocks {j : ℕ} {S : Finset (Fin (n - 1))}
    (hS : S ∈ completions n j) : w n S ∈ matchingStar (firstBlocks n j) := by
  rw [mem_matchingStar_firstBlocks]
  intro a ha
  rw [mem_completions] at hS
  rw [B_w, Finset.filter_false_of_mem (fun g hg ↦ by have := hS g hg; omega), Finset.sum_empty,
    add_zero]

/-- `lower k` kills `L_{E_j}` for `k < j`. -/
theorem lower_eq_zero_of_mem {j : ℕ} {x : W (Fin (2 * n))}
    (hx : x ∈ matchingStar (firstBlocks n j)) (k : Fin (n - 1)) (hk : (k : ℕ) < j) :
    lower n k k.2 x = 0 := by
  rw [mem_matchingStar_firstBlocks] at hx
  rw [lower, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  rw [LinearMap.add_apply, hx _ (by have := a.isLt; change (a : ℕ) < j; omega),
    Module.End.one_apply, W_add_self]

private theorem coe_ite_apply {p : Prop} [Decidable p] (a : W (Fin (2 * n)))
    (Q : PerfectMatching (Fin (2 * n))) :
    ((if p then a else 0 : W (Fin (2 * n))) : PerfectMatching (Fin (2 * n)) → F₂) Q =
      if p then (a : PerfectMatching (Fin (2 * n)) → F₂) Q else 0 := by
  split_ifs <;> rfl

/-- The coordinate of `x ∈ L_{E_j}` at `w_S` vanishes when `S` has a gap below `j`. -/
theorem repr_eq_zero_of_mem (hn : 1 ≤ n) {j : ℕ} {x : W (Fin (2 * n))}
    (hx : x ∈ matchingStar (firstBlocks n j)) {S : Finset (Fin (n - 1))} {k : Fin (n - 1)}
    (hkS : k ∈ S) (hk : (k : ℕ) < j) : (wBasis n hn).repr x S = 0 := by
  have h := congrArg
    (fun f : W (Fin (2 * n)) ↦ (f : PerfectMatching (Fin (2 * n)) → F₂) (X n (S.erase k)ᶜ))
    (lower_eq_zero_of_mem n hx k hk)
  have hcond : ∀ T : Finset (Fin (n - 1)), (k ∈ T ∧ T.erase k = S.erase k) ↔ T = S := by
    intro T
    constructor
    · rintro ⟨hkT, hT⟩
      rw [← Finset.insert_erase hkT, hT, Finset.insert_erase hkS]
    · rintro rfl
      exact ⟨hkS, rfl⟩
  rw [← (wBasis n hn).sum_repr x] at h
  simp only [map_sum, map_smul, wBasis_apply, lower_w'] at h
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    coe_ite_apply, w, coe_rowW, H_X n hn, symmDiff_compl_eq_univ, ZeroMemClass.coe_zero,
    Pi.zero_apply, mul_ite, mul_one, mul_zero, ← ite_and, hcond, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  exact h

/-- `L_{E_j}` is spanned by the rows of the completions of `E_j`
(`results/presentation-consequences-extend.md` Corollary A4, organize-archive 3ba2201). -/
theorem matchingStar_firstBlocks_eq_span (hn : 1 ≤ n) (j : ℕ) :
    matchingStar (firstBlocks n j) = Submodule.span F₂ (w n '' completions n j) := by
  refine le_antisymm (fun x hx ↦ ?_) (Submodule.span_le.mpr ?_)
  · rw [← (wBasis n hn).sum_repr x, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (· ∈ completions n j)]
    refine add_mem (Submodule.sum_mem _ fun S hS ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨S, (Finset.mem_filter.mp hS).2, (wBasis_apply n hn S).symm⟩))
      (Submodule.sum_mem _ fun S hS ↦ ?_)
    have hS' : S ∉ completions n j := (Finset.mem_filter.mp hS).2
    rw [mem_completions] at hS'
    simp only [not_forall, not_le] at hS'
    obtain ⟨k, hkS, hk⟩ := hS'
    rw [repr_eq_zero_of_mem n hn hx hkS hk, zero_smul]
    exact zero_mem _
  · rintro _ ⟨S, hS, rfl⟩
    exact w_mem_matchingStar_firstBlocks n hS

/-- `dim L_{E_j} = 2^(n-1-j)`, the matching-star dimension of archive Theorem 7.2 for the first
blocks (`results/presentation-consequences-extend.md` Corollary A4, organize-archive 3ba2201). -/
theorem finrank_matchingStar_firstBlocks (hn : 1 ≤ n) (j : ℕ) :
    Module.finrank F₂ (matchingStar (firstBlocks n j)) = 2 ^ (n - 1 - j) := by
  have hli := (linearIndependent_w n hn).comp
    (Subtype.val : completions n j → Finset (Fin (n - 1))) Subtype.val_injective
  have hr : Set.range (w n ∘ (Subtype.val : completions n j → Finset (Fin (n - 1)))) =
      w n '' completions n j := by
    rw [Set.range_comp, Subtype.range_coe_subtype]
    rfl
  rw [matchingStar_firstBlocks_eq_span n hn, ← hr, finrank_span_eq_card hli, Fintype.card_coe,
    card_completions]

end Pairing.PerfectMatching
