import Mathlib.GroupTheory.OrderOfElement
import Pairing.Automorphism

/-!
# Cameron's theorem for `GK(A)`, `A` abelian of odd order (COD-299)

Let `A` be a finite abelian group of odd order, written additively, so `x ↦ 2x` is a bijection
with inverse `half`. `GK(A)` is the 1-factorization of the complete graph on `A ∪ {∞}`, encoded
as `Option A` with `none = ∞`, whose factor `F_c` pairs `∞` with `c` and `x ≠ c` with `2c - x`.
This is Cameron's colouring derived from `A` (Cameron 1975, §2). At `A = ℤ/n` it is the
round-robin 1-factorization of `Pairing.Automorphism`.

Source: Lemma 1, Lemma 2 and Theorem 3 of `results/audit-manuscript-extend.md` (organize-archive
313d6ea), §4.1. The non-mediality witness is Lemma 2(b), the corrected form of the audit's
identity. For `a ≠ 0` and `b ∉ {0, a, -a, a/2, 2a}`, `(a ∘₀ a) ∘₀ (0 ∘₀ b) = a + 2b` and
`(a ∘₀ 0) ∘₀ (a ∘₀ b) = 3a + b`, which differ by `2a - b ≠ 0`.

* `twoEquiv`, `half` : `x ↦ 2x` as an additive automorphism of `A`, and its inverse.
* `factor A c = F_c` and `factor_injective`. `IsAut A σ`, `autGroup A` : the automorphisms of
  `GK(A)`, the permutations of `A ∪ {∞}` mapping every factor to a factor.
* `affPerm α b` : `x ↦ α x + b`, fixing `∞`. `affPerm_smul_factor`, `isAut_affPerm` : it sends
  `F_c` to `F_(α c + b)`.
* `edgeLabel`, `localSq A v` : the operation `∘_v`. `localSq_smul` : an automorphism carries
  `∘_v` to `∘_(σ v)` (Lemma 8.1(i) of the paper, as used in the source).
* Lemma 1. `localSq_none`, `isMedial_localSq_none` : `c ∘_∞ d = (c + d)/2`, and `∘_∞` is medial.
  `localSq_zero` : `c ∘₀ d = c + d` for distinct nonzero `c, d`. `localSq_zero_left`,
  `localSq_zero_right` : `0 ∘₀ d = d ∘₀ 0 = 2d` for `d ≠ 0`.
* Lemma 2(b). `not_isMedial_localSq_zero` : `∘₀` is not medial for `|A| ≥ 7`.
* Theorem 3. `IsAut.apply_none` : for `|A| ≥ 7` every automorphism fixes `∞`.
  `IsAut.exists_affPerm` : an automorphism fixing `∞` is `x ↦ α x + b`, for every odd `|A|`.
  `isAut_iff` : for `|A| ≥ 7`, `Aut(GK(A)) = {x ↦ α x + b : α ∈ Aut(A), b ∈ A}`.
  `autEquiv : Aut(A) × A ≃ Aut(GK(A))`, `card_autGroup : |Aut(GK(A))| = |A| |Aut(A)|`, and
  `autGroupMulEquiv : (A ≃ᵃ[ℤ] A) ≃* Aut(GK(A))`, where the affine group `A ≃ᵃ[ℤ] A` is the
  holomorph `Hol(A) = A ⋊ Aut(A)`.
* `factor_zmod`, `isAut_zmod_iff` : at `A = ℤ/(2m - 1)`, `GK(A)` is the round-robin
  1-factorization `RoundRobin.Canonical.factor`, so `RoundRobin.Canonical.isAut_iff` is the cyclic
  case. The `ℤ/n` development of `Pairing.Automorphism` is unchanged.
-/

namespace Pairing.GK

open PerfectMatching

variable {A : Type*} [AddCommGroup A]

section Half

variable [Fact (Odd (Nat.card A))]

variable (A) in
/-- `x ↦ 2x` as an additive automorphism of `A`, a bijection since `|A|` is odd
(`results/audit-manuscript-extend.md`, organize-archive 313d6ea, §4.1, Setup). -/
noncomputable def twoEquiv : A ≃+ A :=
  AddEquiv.ofBijective (nsmulAddMonoidHom 2)
    (Nat.Coprime.nsmul_right_bijective (Nat.coprime_two_right.mpr Fact.out))

/-- `twoEquiv A x = 2x`. -/
@[simp]
theorem twoEquiv_apply (x : A) : twoEquiv A x = 2 • x :=
  rfl

/-- `x/2`, the inverse of `x ↦ 2x` in `A` (`results/audit-manuscript-extend.md`,
organize-archive 313d6ea, §4.1, Setup). -/
noncomputable def half (x : A) : A :=
  (twoEquiv A).symm x

/-- `2 (x/2) = x`. -/
@[simp]
theorem two_nsmul_half (x : A) : 2 • half x = x :=
  (twoEquiv A).apply_symm_apply x

/-- `(2x)/2 = x`. -/
@[simp]
theorem half_two_nsmul (x : A) : half (2 • x) = x :=
  (twoEquiv A).symm_apply_apply x

/-- `(x + x)/2 = x`. -/
theorem half_add_self (x : A) : half (x + x) = x := by
  rw [← two_nsmul, half_two_nsmul]

/-- Halving is additive. -/
theorem half_add (x y : A) : half (x + y) = half x + half y :=
  map_add (twoEquiv A).symm x y

/-- Halving is injective. -/
theorem half_injective : Function.Injective (half (A := A)) :=
  (twoEquiv A).symm.injective

/-- Doubling is injective, since `|A|` is odd. -/
theorem two_nsmul_injective : Function.Injective fun x : A ↦ 2 • x :=
  (twoEquiv A).injective

/-- `2x = 0` only for `x = 0`. -/
theorem two_nsmul_ne_zero {x : A} (hx : x ≠ 0) : 2 • x ≠ 0 := fun h ↦
  hx (two_nsmul_injective (h.trans (smul_zero 2).symm))

end Half

section Factor

variable [DecidableEq A]

/-- The partner of a vertex in `F_c`, `∞ ↔ c` and `x ↔ 2c - x`
(`results/audit-manuscript-extend.md`, organize-archive 313d6ea, §4.1, Setup). -/
def mateFn (c : A) : Option A → Option A
  | none => some c
  | some x => if x = c then none else some (2 • c - x)

/-- `F_c` pairs `∞` with `c`. -/
@[simp]
theorem mateFn_none (c : A) : mateFn c none = some c :=
  rfl

/-- `F_c` pairs `c` with `∞`. -/
@[simp]
theorem mateFn_self (c : A) : mateFn c (some c) = none := by
  simp [mateFn]

/-- `F_c` pairs `x ≠ c` with `2c - x`. -/
theorem mateFn_of_ne {c x : A} (h : x ≠ c) : mateFn c (some x) = some (2 • c - x) := by
  simp [mateFn, h]

omit [DecidableEq A] in
private theorem two_nsmul_sub_ne {c x : A} (h : x ≠ c) : 2 • c - x ≠ c := fun e ↦ by
  rw [sub_eq_iff_eq_add, two_nsmul] at e
  exact h (add_left_cancel e).symm

/-- `F_c` is an involution. -/
theorem mateFn_involutive (c : A) : Function.Involutive (mateFn c) := by
  rintro (_ | x)
  · simp
  rcases eq_or_ne x c with rfl | hx
  · simp
  rw [mateFn_of_ne hx, mateFn_of_ne (two_nsmul_sub_ne hx), sub_sub_cancel]

variable [Fact (Odd (Nat.card A))]

/-- `F_c` has no fixed point, since `|A|` is odd. -/
theorem mateFn_ne (c : A) (v : Option A) : mateFn c v ≠ v := by
  rcases v with _ | x
  · simp
  rcases eq_or_ne x c with rfl | hx
  · simp
  rw [mateFn_of_ne hx, Ne, Option.some_inj]
  intro e
  rw [sub_eq_iff_eq_add, ← two_nsmul] at e
  exact hx (two_nsmul_injective e).symm

variable (A) in
/-- The factor `F_c` of `GK(A)` on `A ∪ {∞}`, pairing `∞` with `c` and `x ≠ c` with `2c - x`
(`results/audit-manuscript-extend.md`, organize-archive 313d6ea, §4.1, Setup; Cameron 1975, §2). -/
def factor (c : A) : PerfectMatching (Option A) where
  mate := Function.Involutive.toPerm _ (mateFn_involutive c)
  mate_mate := mateFn_involutive c
  mate_ne := mateFn_ne c

/-- The partner map of `F_c`. -/
@[simp]
theorem factor_mate (c : A) (v : Option A) : (factor A c).mate v = mateFn c v :=
  rfl

/-- `F_c` contains `∞c`, so distinct `c` give distinct factors. -/
theorem factor_injective : Function.Injective (factor A) := by
  intro c d h
  simpa using congrArg (fun F : PerfectMatching (Option A) ↦ F.mate none) h

end Factor

section Affine

/-- The holomorph map `x ↦ α x + b` of `A ∪ {∞}`, fixing `∞` (`results/audit-manuscript-extend.md`,
organize-archive 313d6ea, Theorem 3). -/
def affPerm (α : A ≃+ A) (b : A) : Equiv.Perm (Option A) :=
  Equiv.optionCongr ((α : A ≃ A).trans (Equiv.addRight b))

/-- `affPerm α b` fixes `∞`. -/
@[simp]
theorem affPerm_none (α : A ≃+ A) (b : A) : affPerm α b none = none :=
  rfl

/-- `affPerm α b` sends `x` to `α x + b`. -/
@[simp]
theorem affPerm_some (α : A ≃+ A) (b x : A) : affPerm α b (some x) = some (α x + b) :=
  rfl

/-- The inverse of `affPerm α b` fixes `∞`. -/
@[simp]
theorem affPerm_inv_none (α : A ≃+ A) (b : A) : (affPerm α b)⁻¹ none = none := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  rfl

/-- The map `x ↦ α x + b` determines `α` and `b` (`results/audit-manuscript-extend.md`,
organize-archive 313d6ea, Theorem 3, step 5). -/
theorem affPerm_inj {α α' : A ≃+ A} {b b' : A} (h : affPerm α b = affPerm α' b') :
    α = α' ∧ b = b' := by
  have h0 := congrArg (fun σ : Equiv.Perm (Option A) ↦ σ (some 0)) h
  simp only [affPerm_some, map_zero, zero_add, Option.some_inj] at h0
  subst h0
  refine ⟨AddEquiv.ext fun x ↦ ?_, rfl⟩
  have hx := congrArg (fun σ : Equiv.Perm (Option A) ↦ σ (some x)) h
  simp only [affPerm_some, Option.some_inj] at hx
  exact add_right_cancel hx

variable (A) in
/-- An affine permutation `f` of `A` acting on `A ∪ {∞}`, `x ↦ f x` and `∞ ↦ ∞`, as a
homomorphism from the affine group `A ≃ᵃ[ℤ] A = Hol(A)` (`results/audit-manuscript-extend.md`,
organize-archive 313d6ea, Theorem 3). -/
def affinePerm : (A ≃ᵃ[ℤ] A) →* Equiv.Perm (Option A) where
  toFun f := Equiv.optionCongr f.toEquiv
  map_one' := Equiv.ext fun v ↦ by cases v <;> rfl
  map_mul' f g := Equiv.ext fun v ↦ by cases v <;> rfl

/-- `affinePerm` sends `x` to `f x`. -/
@[simp]
theorem affinePerm_some (f : A ≃ᵃ[ℤ] A) (x : A) : affinePerm A f (some x) = some (f x) :=
  rfl

/-- `affinePerm` is injective. -/
theorem affinePerm_injective : Function.Injective (affinePerm A) := fun f g h ↦
  AffineEquiv.ext fun x ↦ Option.some_inj.1 (by rw [← affinePerm_some, h, affinePerm_some])

end Affine

section Aut

variable [DecidableEq A] [Fact (Odd (Nat.card A))]

variable (A) in
/-- `σ` is an automorphism of `GK(A)` when it maps every factor `F_c` to some factor
(`results/audit-manuscript-extend.md`, organize-archive 313d6ea, Theorem 3). -/
def IsAut (σ : Equiv.Perm (Option A)) : Prop :=
  ∀ c, ∃ d, σ • factor A c = factor A d

/-- The pointwise form of `σ • F_c = F_d`, `F_d(σ v) = σ (F_c(v))`. -/
theorem mate_smul_eq {σ : Equiv.Perm (Option A)} {c d : A} (h : σ • factor A c = factor A d)
    (v : Option A) : (factor A d).mate (σ v) = σ ((factor A c).mate v) := by
  rw [← h, smul_mate, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]

/-- `x ↦ α x + b` sends `F_c` to `F_(α c + b)` (`results/audit-manuscript-extend.md`,
organize-archive 313d6ea, Theorem 3, step 5). -/
theorem affPerm_smul_factor (α : A ≃+ A) (b c : A) :
    affPerm α b • factor A c = factor A (α c + b) := by
  refine PerfectMatching.ext (Equiv.ext fun v ↦ ?_)
  rw [smul_mate]
  rcases v with _ | y
  · simp
  · obtain ⟨x, rfl⟩ : ∃ x, y = α x + b := ⟨α.symm (y - b), by simp⟩
    have hinv : (affPerm α b)⁻¹ (some (α x + b)) = some x := by
      rw [Equiv.Perm.inv_eq_iff_eq, affPerm_some]
    rw [hinv]
    rcases eq_or_ne x c with rfl | hx
    · simp
    · have hne : α x + b ≠ α c + b := fun h ↦ hx (α.injective (add_right_cancel h))
      rw [factor_mate, factor_mate, mateFn_of_ne hx, mateFn_of_ne hne, affPerm_some, map_sub,
        map_nsmul, Option.some_inj]
      abel

/-- The maps `x ↦ α x + b` are automorphisms of `GK(A)` (`results/audit-manuscript-extend.md`,
organize-archive 313d6ea, Theorem 3, step 5). -/
theorem isAut_affPerm (α : A ≃+ A) (b : A) : IsAut A (affPerm α b) :=
  fun c ↦ ⟨α c + b, affPerm_smul_factor α b c⟩

variable [Finite A]

/-- An automorphism permutes the factor labels, `σ • F_c = F_(π c)` for a permutation `π` of `A`. -/
theorem IsAut.exists_perm {σ : Equiv.Perm (Option A)} (hσ : IsAut A σ) :
    ∃ π : Equiv.Perm A, ∀ c, σ • factor A c = factor A (π c) := by
  choose f hf using hσ
  have hinj : Function.Injective f := fun c d h ↦
    factor_injective ((smul_left_cancel_iff σ).1 (by rw [hf, hf, h]))
  exact ⟨Equiv.ofBijective f hinj.bijective_of_finite, hf⟩

variable (A) in
/-- The automorphism group `Aut(GK(A))`, a subgroup of the permutations of `A ∪ {∞}`
(`results/audit-manuscript-extend.md`, organize-archive 313d6ea, Theorem 3). -/
def autGroup : Subgroup (Equiv.Perm (Option A)) where
  carrier := {σ | IsAut A σ}
  mul_mem' := by
    intro σ τ hσ hτ c
    obtain ⟨d, hd⟩ := hτ c
    obtain ⟨e, he⟩ := hσ d
    exact ⟨e, by rw [mul_smul, hd, he]⟩
  one_mem' := fun c ↦ ⟨c, one_smul _ _⟩
  inv_mem' := by
    intro σ hσ d
    obtain ⟨π, hπ⟩ := IsAut.exists_perm hσ
    refine ⟨π.symm d, ?_⟩
    rw [← smul_left_cancel_iff σ, smul_inv_smul, hπ, Equiv.apply_symm_apply]

/-- Membership in `Aut(GK(A))` is `IsAut`. -/
@[simp]
theorem mem_autGroup {σ : Equiv.Perm (Option A)} : σ ∈ autGroup A ↔ IsAut A σ :=
  Iff.rfl

end Aut

section LocalSquare

variable [DecidableEq A] [Fact (Odd (Nat.card A))]

variable (A) in
/-- The label of the factor holding the edge `uw`. `∞x` lies in `F_x` and `xy` in
`F_((x + y)/2)` (`results/audit-manuscript-extend.md`, organize-archive 313d6ea, §4.1, Setup). -/
noncomputable def edgeLabel : Option A → Option A → A
  | none, none => 0
  | none, some y => y
  | some x, none => x
  | some x, some y => half (x + y)

/-- `F_(edgeLabel u w)` pairs `u` with `w`. -/
theorem mate_edgeLabel {u w : Option A} (h : u ≠ w) :
    (factor A (edgeLabel A u w)).mate u = w := by
  rcases u with _ | x <;> rcases w with _ | y
  · exact absurd rfl h
  · rfl
  · simp [edgeLabel]
  · have hxy : x ≠ y := fun e ↦ h (congrArg some e)
    have hx : x ≠ half (x + y) := fun e ↦ hxy (by
      have h2 : 2 • x = 2 • half (x + y) := by rw [← e]
      rw [two_nsmul_half, two_nsmul] at h2
      exact add_left_cancel h2)
    rw [edgeLabel, factor_mate, mateFn_of_ne hx, two_nsmul_half, add_sub_cancel_left]

/-- An edge `uw` of `F_c` has label `c`. -/
theorem edgeLabel_eq {c : A} {u w : Option A} (h : (factor A c).mate u = w) :
    edgeLabel A u w = c := by
  rw [factor_mate] at h
  subst h
  rcases u with _ | x
  · rfl
  rcases eq_or_ne x c with rfl | hx
  · simp [edgeLabel]
  · rw [mateFn_of_ne hx, edgeLabel, add_sub_cancel, half_two_nsmul]

/-- For `c ≠ d`, the partners `F_c(v)` and `F_d(v)` differ. -/
theorem mate_ne_mate {c d : A} (hcd : c ≠ d) (v : Option A) :
    (factor A c).mate v ≠ (factor A d).mate v := fun h ↦
  hcd ((edgeLabel_eq (c := c) rfl).symm.trans (edgeLabel_eq h.symm))

/-- An automorphism with label map `π` preserves edge labels,
`edgeLabel (σ u) (σ w) = π (edgeLabel u w)`. -/
theorem edgeLabel_smul {σ : Equiv.Perm (Option A)} {π : A → A}
    (hπ : ∀ c, σ • factor A c = factor A (π c)) {u w : Option A} (h : u ≠ w) :
    edgeLabel A (σ u) (σ w) = π (edgeLabel A u w) := by
  apply edgeLabel_eq
  rw [mate_smul_eq (hπ _), mate_edgeLabel h]

variable (A) in
/-- The operation `∘_v` at a vertex `v`. `c ∘_v d` is the label of the factor holding the edge
`F_c(v) F_d(v)` for `c ≠ d`, and `c ∘_v c = c` (`results/audit-manuscript-extend.md`,
organize-archive 313d6ea, §4.1). -/
noncomputable def localSq (v : Option A) (c d : A) : A :=
  if c = d then c else edgeLabel A ((factor A c).mate v) ((factor A d).mate v)

/-- `c ∘_v c = c`. -/
theorem localSq_self (v : Option A) (c : A) : localSq A v c c = c :=
  ite_eq_left rfl

/-- Lemma 8.1(i) of the paper, as used in Theorem 3 of `results/audit-manuscript-extend.md`
(organize-archive 313d6ea). If `σ` maps `F_c` to `F_(π c)`, then
`π c ∘_(σ v) π d = π (c ∘_v d)`. -/
theorem localSq_smul {σ : Equiv.Perm (Option A)} {π : Equiv.Perm A}
    (hπ : ∀ c, σ • factor A c = factor A (π c)) (v : Option A) (c d : A) :
    localSq A (σ v) (π c) (π d) = π (localSq A v c d) := by
  unfold localSq
  by_cases hcd : c = d
  · rw [ite_eq_left hcd, ite_eq_left (congrArg π hcd)]
  · rw [ite_eq_right hcd, ite_eq_right (π.injective.ne hcd), mate_smul_eq (hπ c),
      mate_smul_eq (hπ d)]
    exact edgeLabel_smul hπ (mate_ne_mate hcd v)

/-- Lemma 1(1) of `results/audit-manuscript-extend.md` (organize-archive 313d6ea),
`c ∘_∞ d = (c + d)/2`. -/
theorem localSq_none (c d : A) : localSq A none c d = half (c + d) := by
  unfold localSq
  split_ifs with hcd
  · rw [hcd, half_add_self]
  · rfl

/-- Lemma 1(1) of `results/audit-manuscript-extend.md` (organize-archive 313d6ea), `∘_∞` is
medial. -/
theorem isMedial_localSq_none : RoundRobin.Canonical.IsMedial (localSq A none) := by
  intro a b c d
  simp only [localSq_none, half_add]
  abel

/-- Lemma 1(2) of `results/audit-manuscript-extend.md` (organize-archive 313d6ea),
`c ∘₀ d = c + d` for distinct nonzero `c, d`, including `c + d = 0`. -/
theorem localSq_zero {c d : A} (hc : c ≠ 0) (hd : d ≠ 0) (hcd : c ≠ d) :
    localSq A (some 0) c d = c + d := by
  rw [localSq, ite_eq_right hcd, factor_mate, factor_mate, mateFn_of_ne (Ne.symm hc),
    mateFn_of_ne (Ne.symm hd), sub_zero, sub_zero, edgeLabel, ← nsmul_add, half_two_nsmul]

/-- Lemma 1(3) of `results/audit-manuscript-extend.md` (organize-archive 313d6ea),
`0 ∘₀ d = 2d` for `d ≠ 0`. The audit's value `d/2` is wrong. -/
theorem localSq_zero_left {d : A} (hd : d ≠ 0) : localSq A (some 0) 0 d = 2 • d := by
  rw [localSq, ite_eq_right (Ne.symm hd), factor_mate, factor_mate, mateFn_self,
    mateFn_of_ne (Ne.symm hd), sub_zero]
  rfl

/-- Lemma 1(3) of `results/audit-manuscript-extend.md` (organize-archive 313d6ea),
`d ∘₀ 0 = 2d` for `d ≠ 0`. The audit's value `d/2` is wrong. -/
theorem localSq_zero_right {d : A} (hd : d ≠ 0) : localSq A (some 0) d 0 = 2 • d := by
  rw [localSq, ite_eq_right hd, factor_mate, factor_mate, mateFn_self, mateFn_of_ne (Ne.symm hd),
    sub_zero]
  rfl

/-- Lemma 2(b) of `results/audit-manuscript-extend.md` (organize-archive 313d6ea), the corrected
witness. For `|A| ≥ 7`, `∘₀` is not medial. With `a ≠ 0` and `b ∉ {0, a, -a, a/2, 2a}`,
`(a ∘₀ a) ∘₀ (0 ∘₀ b) = a + 2b` and `(a ∘₀ 0) ∘₀ (a ∘₀ b) = 3a + b`, which differ. -/
theorem not_isMedial_localSq_zero [Finite A] (h7 : 7 ≤ Nat.card A) :
    ¬RoundRobin.Canonical.IsMedial (localSq A (some 0)) := by
  intro hmed
  have := Fintype.ofFinite A
  have hcard : Nat.card A = (Finset.univ : Finset A).card := by
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0} : Finset A)) (t := Finset.univ) (by rw [Finset.card_singleton]; omega)
  rw [Finset.mem_singleton] at ha
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, a, -a, half a, 2 • a} : Finset A)) (t := Finset.univ)
    (Finset.card_le_five.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  obtain ⟨hb0, hba, hbna, hbh, hb2⟩ := hb
  have h2b : 2 • b ≠ 0 := two_nsmul_ne_zero hb0
  have h2a : 2 • a ≠ 0 := two_nsmul_ne_zero ha
  have hab2 : a ≠ 2 • b := fun e ↦ hbh (by rw [e, half_two_nsmul])
  have hab : a + b ≠ 0 := fun e ↦ hbna (eq_neg_of_add_eq_zero_right e)
  have h2ab : 2 • a ≠ a + b := fun e ↦ hba (by rw [two_nsmul] at e; exact (add_left_cancel e).symm)
  have key := hmed a a 0 b
  rw [localSq_self, localSq_zero_left hb0, localSq_zero_right ha, localSq_zero ha hb0 (Ne.symm hba),
    localSq_zero ha h2b hab2, localSq_zero h2a hab h2ab] at key
  apply hb2
  calc b = (a + 2 • b) - (a + b) := by abel
    _ = (2 • a + (a + b)) - (a + b) := by rw [key]
    _ = 2 • a := by abel

end LocalSquare

section Theorem

variable [Finite A] [DecidableEq A] [Fact (Odd (Nat.card A))]

/-- Theorem 3 of `results/audit-manuscript-extend.md` (organize-archive 313d6ea), step 2. For
`|A| ≥ 7` every automorphism of `GK(A)` fixes `∞`. `∘_∞` is medial, while every `∘_v` with `v`
finite is isomorphic to `∘₀` through a translation, and `∘₀` is not medial. -/
theorem IsAut.apply_none (h7 : 7 ≤ Nat.card A) {σ : Equiv.Perm (Option A)} (hσ : IsAut A σ) :
    σ none = none := by
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x, σ (some x) = none := by
    rcases h : σ⁻¹ none with _ | x
    · exact absurd (Equiv.Perm.inv_eq_iff_eq.1 h).symm hne
    · exact ⟨x, (Equiv.Perm.inv_eq_iff_eq.1 h).symm⟩
  have hτ : IsAut A (σ * affPerm (AddEquiv.refl A) x) :=
    (autGroup A).mul_mem hσ (isAut_affPerm _ x)
  obtain ⟨π, hπ⟩ := hτ.exists_perm
  have h0 : (σ * affPerm (AddEquiv.refl A) x) (some 0) = none := by simpa using hx
  have hconj : ∀ c d, localSq A none (π c) (π d) = π (localSq A (some 0) c d) := by
    intro c d
    rw [← h0]
    exact localSq_smul hπ _ c d
  exact not_isMedial_localSq_zero h7
    (RoundRobin.Canonical.IsMedial.of_hom π.injective hconj isMedial_localSq_none)

/-- Theorem 3 of `results/audit-manuscript-extend.md` (organize-archive 313d6ea), steps 3 and 4.
An automorphism of `GK(A)` fixing `∞` is `x ↦ α x + b` with `α ∈ Aut(A)`, for every `A` of odd
order. It preserves midpoints, `σ((u + w)/2) = (σ u + σ w)/2`, so `x ↦ σ x - σ 0` is additive. -/
theorem IsAut.exists_affPerm {σ : Equiv.Perm (Option A)} (hσ : IsAut A σ)
    (hfix : σ none = none) : ∃ (α : A ≃+ A) (b : A), σ = affPerm α b := by
  obtain ⟨π, hπ⟩ := hσ.exists_perm
  have hs : ∀ x, σ (some x) = some (π x) := by
    intro x
    have h := mate_smul_eq (hπ x) none
    rw [hfix] at h
    simpa using h.symm
  have hmid : ∀ x y, π (half (x + y)) = half (π x + π y) := by
    intro x y
    rcases eq_or_ne x y with rfl | hxy
    · rw [half_add_self, half_add_self]
    · have h := edgeLabel_smul hπ (u := some x) (w := some y) (by simpa using hxy)
      rw [hs, hs] at h
      exact h.symm
  have hadd : ∀ x y, π (x + y) - π 0 = (π x - π 0) + (π y - π 0) := by
    intro x y
    have h1 := hmid x y
    have h2 := hmid (x + y) 0
    rw [add_zero] at h2
    have h3 : π x + π y = π (x + y) + π 0 := half_injective (h1.symm.trans h2)
    calc π (x + y) - π 0 = (π (x + y) + π 0) - π 0 - π 0 := by abel
      _ = (π x + π y) - π 0 - π 0 := by rw [h3]
      _ = (π x - π 0) + (π y - π 0) := by abel
  let f : A →+ A :=
    { toFun := fun x ↦ π x - π 0
      map_zero' := sub_self _
      map_add' := hadd }
  have hinj : Function.Injective f := fun x y h ↦ π.injective (sub_left_injective h)
  refine ⟨AddEquiv.ofBijective f hinj.bijective_of_finite, π 0, Equiv.ext fun v ↦ ?_⟩
  rcases v with _ | x
  · rw [hfix, affPerm_none]
  · rw [hs, affPerm_some, AddEquiv.ofBijective_apply, Option.some_inj]
    exact (sub_add_cancel _ _).symm

/-- **Cameron's theorem for `|A| ≥ 7`.** Theorem 3 of `results/audit-manuscript-extend.md`
(organize-archive 313d6ea). For a finite abelian group `A` of odd order at least `7`, a permutation
of `A ∪ {∞}` is an automorphism of `GK(A)` iff it is `x ↦ α x + b` with `α ∈ Aut(A)`, fixing `∞`.
Cameron 1975, Theorem 2.2. -/
theorem isAut_iff (h7 : 7 ≤ Nat.card A) {σ : Equiv.Perm (Option A)} :
    IsAut A σ ↔ ∃ (α : A ≃+ A) (b : A), σ = affPerm α b :=
  ⟨fun hσ ↦ hσ.exists_affPerm (hσ.apply_none h7), fun ⟨α, b, h⟩ ↦ h ▸ isAut_affPerm α b⟩

/-- The bijection `Aut(A) × A ≃ Aut(GK(A))`, `(α, b) ↦ (x ↦ α x + b)`, for `|A| ≥ 7`
(`results/audit-manuscript-extend.md`, organize-archive 313d6ea, Theorem 3). -/
noncomputable def autEquiv (h7 : 7 ≤ Nat.card A) : (A ≃+ A) × A ≃ autGroup A :=
  Equiv.ofBijective (fun p ↦ ⟨affPerm p.1 p.2, isAut_affPerm p.1 p.2⟩)
    ⟨fun p q h ↦
      Prod.ext (affPerm_inj (Subtype.ext_iff.1 h)).1 (affPerm_inj (Subtype.ext_iff.1 h)).2,
      fun σ ↦ by
        obtain ⟨α, b, h⟩ := (isAut_iff h7).1 σ.2
        exact ⟨(α, b), Subtype.ext h.symm⟩⟩

/-- `|Aut(GK(A))| = |A| |Aut(A)|` for `|A| ≥ 7`, the order of `Hol(A)`
(`results/audit-manuscript-extend.md`, organize-archive 313d6ea, Theorem 3). -/
theorem card_autGroup (h7 : 7 ≤ Nat.card A) :
    Nat.card (autGroup A) = Nat.card A * Nat.card (A ≃+ A) := by
  rw [← Nat.card_congr (autEquiv h7), Nat.card_prod, mul_comm]

/-- The image of `affinePerm` is `Aut(GK(A))` for `|A| ≥ 7` (`results/audit-manuscript-extend.md`,
organize-archive 313d6ea, Theorem 3). -/
theorem range_affinePerm (h7 : 7 ≤ Nat.card A) : (affinePerm A).range = autGroup A := by
  ext σ
  constructor
  · rintro ⟨f, rfl⟩
    rw [mem_autGroup, show affinePerm A f = affPerm f.linear.toAddEquiv (f 0) from
      Equiv.ext fun v ↦ by
        rcases v with _ | x
        · rfl
        · rw [affinePerm_some, affPerm_some, Option.some_inj]
          exact congrFun f.toAffineMap.decomp x]
    exact isAut_affPerm _ _
  · intro hσ
    obtain ⟨α, b, rfl⟩ := (isAut_iff h7).1 hσ
    refine ⟨AffineEquiv.constVAdd ℤ A b * α.toIntLinearEquiv.toAffineEquiv,
      Equiv.ext fun v ↦ ?_⟩
    rcases v with _ | x
    · rfl
    · rw [affinePerm_some, affPerm_some, Option.some_inj, AffineEquiv.coe_mul,
        Function.comp_apply, AffineEquiv.constVAdd_apply, LinearEquiv.coe_toAffineEquiv,
        vadd_eq_add]
      exact add_comm _ _

/-- **`Hol(A) ≃* Aut(GK(A))`** for a finite abelian group `A` of odd order at least `7`. The
affine group `A ≃ᵃ[ℤ] A = A ⋊ Aut(A)` is isomorphic to the automorphism group of `GK(A)` through
`affinePerm` (`results/audit-manuscript-extend.md`, organize-archive 313d6ea, Theorem 3; Cameron
1975, Theorem 2.2). -/
noncomputable def autGroupMulEquiv (h7 : 7 ≤ Nat.card A) : (A ≃ᵃ[ℤ] A) ≃* autGroup A :=
  (MonoidHom.ofInjective affinePerm_injective).trans (MulEquiv.subgroupCongr (range_affinePerm h7))

end Theorem

section Cyclic

/-- `ℤ/(2m - 1)` has odd order. -/
instance fact_odd_card_zmod (m : ℕ) [NeZero m] : Fact (Odd (Nat.card (ZMod (2 * m - 1)))) :=
  ⟨by rw [Nat.card_zmod]; exact RoundRobin.Canonical.modulus_odd m⟩

/-- At `A = ℤ/(2m - 1)`, `GK(A)` is the round-robin 1-factorization: `F_c` is
`RoundRobin.Canonical.factor m c`. -/
theorem factor_zmod (m : ℕ) [NeZero m] (c : ZMod (2 * m - 1)) :
    factor (ZMod (2 * m - 1)) c = RoundRobin.Canonical.factor m c := by
  refine PerfectMatching.ext (Equiv.ext fun v ↦ ?_)
  rcases v with _ | x
  · rfl
  · rcases eq_or_ne x c with rfl | hx
    · simp [RoundRobin.Canonical.factor]
    · rw [factor_mate, mateFn_of_ne hx, RoundRobin.Canonical.factor, RoundRobin.factor_mate,
        RoundRobin.mateFn_of_ne c x hx, show (2 : ZMod (2 * m - 1)) * c = 2 • c from
          (two_mul c).trans (two_nsmul c).symm]

/-- At `A = ℤ/(2m - 1)`, `IsAut A` is the round-robin `RoundRobin.Canonical.IsAut m`, so
`RoundRobin.Canonical.isAut_iff` is the cyclic case of `isAut_iff`. -/
theorem isAut_zmod_iff (m : ℕ) [NeZero m] (σ : Equiv.Perm (Option (ZMod (2 * m - 1)))) :
    IsAut (ZMod (2 * m - 1)) σ ↔ RoundRobin.Canonical.IsAut m σ := by
  simp only [IsAut, RoundRobin.Canonical.IsAut, factor_zmod]

end Cyclic

end Pairing.GK
