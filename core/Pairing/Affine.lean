import Pairing.RoundRobin

/-!
# Affine maps of `V_m` (COD-259)

Put `n = 2m - 1`. The affine maps `v ↦ a v + b` of `ℤ/n`, with `a` a unit, act on
`V_m = ℤ/n ∪ {∞}` fixing `∞`, and permute the canonical round-robin factors `F_t`.

* `shift m b` : the translation `v ↦ v + b`. `shift_smul_factor` : it maps `F_t` to `F_{t + b}`.
* `scale m a` : the scaling `v ↦ a v` by a unit `a`, the multiplicative twin of `shift`.
  `scale_smul_factor` : it maps `F_t` to `F_{a t}`, and `scale_mate_factor` is the pointwise form
  `a F_t(v) = F_{a t}(a v)`.
* `affine_smul_factor` : the affine map `v ↦ a v + b` maps `F_t` to `F_{a t + b}`.
* `isZeroState_affine_smul_iff` : affine maps preserve zero states.
* `two_mul_natCast_self` : `2m = 1` in `ℤ/n`, so `m` inverts `2`. `natCast_injOn` : labels below
  `n` are distinct in `ℤ/n`.

Moved from ham_pairings for COD-259, with names unchanged: `shift` and its lemmas from
`suppression/Suppression/HamCount.lean`, `scale` and its lemmas from
`repair/Repair/FactorCap/Scale.lean`, and the two label lemmas from `repair/Repair/ZeroState.lean`
(all ham_pairings main d1cda40).
-/

namespace Pairing

namespace RoundRobin.Canonical

open PerfectMatching

/-- The translation `v ↦ v + b` of `V_m`, fixing `∞`. -/
def shift (m : ℕ) (b : ZMod (2 * m - 1)) : Equiv.Perm (Vertex m) :=
  Equiv.optionCongr (Equiv.addRight b)

/-- The translation fixes `∞`. -/
@[simp]
theorem shift_none (m : ℕ) (b : ZMod (2 * m - 1)) : shift m b none = none :=
  rfl

/-- The translation sends `x` to `x + b`. -/
@[simp]
theorem shift_some (m : ℕ) (b x : ZMod (2 * m - 1)) :
    shift m b (some x) = some (x + b) :=
  rfl

/-- The inverse translation fixes `∞`. -/
@[simp]
theorem shift_inv_none (m : ℕ) (b : ZMod (2 * m - 1)) : (shift m b)⁻¹ none = none := by
  rw [Equiv.Perm.inv_eq_iff_eq, shift_none]

/-- The inverse translation sends `x` to `x - b`. -/
@[simp]
theorem shift_inv_some (m : ℕ) (b x : ZMod (2 * m - 1)) :
    (shift m b)⁻¹ (some x) = some (x - b) := by
  rw [Equiv.Perm.inv_eq_iff_eq, shift_some, sub_add_cancel]

/-- The translation by `b` maps `F_t` to `F_{t + b}`. -/
theorem shift_smul_factor (m : ℕ) [NeZero m] (b t : ZMod (2 * m - 1)) :
    shift m b • factor m t = factor m (t + b) := by
  refine PerfectMatching.ext (Equiv.ext fun v ↦ ?_)
  rcases v with _ | y
  · simp [factor]
  rcases eq_or_ne y (t + b) with rfl | hy
  · simp [factor]
  have h : y - b ≠ t := fun h ↦ hy (by rw [← h, sub_add_cancel])
  simp only [smul_mate, shift_inv_some, factor, factor_mate, mateFn_of_ne _ _ h,
    mateFn_of_ne _ _ hy, shift_some, Option.some_inj]
  ring

/-- The scaling `v ↦ a v` of `V_m` by a unit `a`, fixing `∞`. -/
def scale (m : ℕ) (a : (ZMod (2 * m - 1))ˣ) : Equiv.Perm (Vertex m) :=
  Equiv.optionCongr a.mulLeft

/-- The scaling fixes `∞`. -/
@[simp]
theorem scale_none (m : ℕ) (a : (ZMod (2 * m - 1))ˣ) : scale m a none = none :=
  rfl

/-- The scaling sends `x` to `a x`. -/
@[simp]
theorem scale_some (m : ℕ) (a : (ZMod (2 * m - 1))ˣ) (x : ZMod (2 * m - 1)) :
    scale m a (some x) = some (a * x) :=
  rfl

/-- The inverse scaling fixes `∞`. -/
@[simp]
theorem scale_inv_none (m : ℕ) (a : (ZMod (2 * m - 1))ˣ) :
    (scale m a)⁻¹ none = none := by
  rw [Equiv.Perm.inv_eq_iff_eq, scale_none]

/-- The inverse scaling sends `x` to `a⁻¹ x`. -/
@[simp]
theorem scale_inv_some (m : ℕ) (a : (ZMod (2 * m - 1))ˣ) (x : ZMod (2 * m - 1)) :
    (scale m a)⁻¹ (some x) = some (↑a⁻¹ * x) := by
  rw [Equiv.Perm.inv_eq_iff_eq, scale_some, ← mul_assoc, Units.mul_inv, one_mul]

/-- The scaling by `a` maps `F_t` to `F_{a t}` (Lemma 1 of
`cod-186-direct-construction-spike.md`). -/
theorem scale_smul_factor (m : ℕ) [NeZero m] (a : (ZMod (2 * m - 1))ˣ) (t : ZMod (2 * m - 1)) :
    scale m a • factor m t = factor m (a * t) := by
  refine PerfectMatching.ext (Equiv.ext fun v ↦ ?_)
  rcases v with _ | y
  · simp [factor]
  rcases eq_or_ne y (a * t) with rfl | hy
  · simp [factor]
  have h : ↑a⁻¹ * y ≠ t := fun h ↦ hy (by rw [← h, ← mul_assoc, Units.mul_inv, one_mul])
  simp only [smul_mate, scale_inv_some, factor, factor_mate, mateFn_of_ne _ _ h,
    mateFn_of_ne _ _ hy, scale_some, Option.some_inj]
  linear_combination (-y) * Units.mul_inv a

/-- The pointwise form of `scale_smul_factor`, `a F_t(v) = F_{a t}(a v)`. -/
theorem scale_mate_factor (m : ℕ) [NeZero m] (a : (ZMod (2 * m - 1))ˣ) (t : ZMod (2 * m - 1))
    (v : Vertex m) : scale m a ((factor m t).mate v) = (factor m (a * t)).mate (scale m a v) := by
  rw [← scale_smul_factor, smul_mate]
  simp

/-- The affine map `v ↦ a v + b` maps `F_t` to `F_{a t + b}`. -/
theorem affine_smul_factor (m : ℕ) [NeZero m] (a : (ZMod (2 * m - 1))ˣ) (b t : ZMod (2 * m - 1)) :
    (shift m b * scale m a) • factor m t = factor m (a * t + b) := by
  rw [mul_smul, scale_smul_factor, shift_smul_factor]

/-- Affine maps preserve zero states, `IsZeroState F (σ • P) ↔ IsZeroState F P` for
`σ = (v ↦ a v + b)`. -/
theorem isZeroState_affine_smul_iff (m : ℕ) [NeZero m] (a : (ZMod (2 * m - 1))ˣ)
    (b : ZMod (2 * m - 1)) (P : PerfectMatching (Vertex m)) :
    IsZeroState (factor m) ((shift m b * scale m a) • P) ↔ IsZeroState (factor m) P := by
  have hs : Function.Surjective fun t : ZMod (2 * m - 1) ↦ ↑a * t + b := fun s ↦
    ⟨↑a⁻¹ * (s - b), by
      simp only
      rw [← mul_assoc, Units.mul_inv, one_mul, sub_add_cancel]⟩
  constructor
  · intro h t
    rw [← ham_smul (shift m b * scale m a), affine_smul_factor]
    exact h _
  · intro h s
    obtain ⟨t, rfl⟩ := hs s
    rw [← affine_smul_factor, ham_smul]
    exact h t

section Labels

variable {m : ℕ} [NeZero m]

/-- `2m ≡ 1` in `ℤ/(2m-1)`, so `m` inverts `2`. -/
theorem two_mul_natCast_self : (2 : ZMod (2 * m - 1)) * m = 1 := by
  have hm := NeZero.pos m
  have h : ((2 * m - 1 + 1 : ℕ) : ZMod (2 * m - 1)) = 1 := by
    rw [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  rw [show 2 * m - 1 + 1 = 2 * m by omega] at h
  exact_mod_cast h

omit [NeZero m] in
/-- Labels below `2m - 1` are distinct in `ℤ/(2m-1)`. -/
theorem natCast_injOn {x y : ℕ} (hx : x < 2 * m - 1) (hy : y < 2 * m - 1)
    (h : (x : ZMod (2 * m - 1)) = y) : x = y := by
  have h' := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] at h'

end Labels

end RoundRobin.Canonical

end Pairing
