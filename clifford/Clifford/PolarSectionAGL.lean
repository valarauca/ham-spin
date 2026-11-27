import Clifford.PolarSection
import Pairing.Automorphism

/-!
# The polar section under `AGL(1, ℤ/n)` (COD-259)

Put `n = 2m - 1`. The affine map `v ↦ a v + b` of `V_m`, with `a ∈ (ℤ/n)ˣ` and fixing `∞`, sends
the round-robin factor `F_t` to `F_{a t + b}` (`affine_smul_factor`, ham-spin c1941cf). So the
polar section of `clifford/Clifford/PolarSection.lean` (ham-spin ca8c6cf) is invariant under it.

* `affine_mem_fpSpanStab` : `v ↦ a v + b` lies in `fpSpanStab (factor m)`.
* `rrSpan_map_and_isZeroState_affine_smul` : `v ↦ a v + b` maps `R_rr` onto itself under `ρW`
  and preserves the round-robin zero set, for every `m`.
* `autGroup_le_fpSpanStab` : `Aut(𝓕) ≤ fpSpanStab (factor m)`, for every `m`.
* `rrSpan_map_and_isZeroState_autGroupMulEquiv` : the same through
  `autGroupMulEquiv : AGL(1, ℤ/n) ≃* Aut(𝓕)` (ham-spin c1941cf), for `n ≥ 7`.

All four are corollaries of `mem_fpSpanStab_of_perm` and `isZeroState_smul_iff_of_perm`
(ham-spin ca8c6cf).
-/

namespace Pairing.RoundRobin.Canonical

open Equiv PerfectMatching

variable {m : ℕ} [NeZero m]

/-- The affine map `v ↦ a v + b` of `V_m`, `a` a unit, fixing `∞`, preserves
`R_rr = span{φ(F_t)}` under `ρW`. By `mem_fpSpanStab_of_perm` (ham-spin ca8c6cf) with the label
map `t ↦ a t + b` of `affine_smul_factor` (ham-spin c1941cf). -/
theorem affine_mem_fpSpanStab (a : (ZMod (2 * m - 1))ˣ) (b : ZMod (2 * m - 1)) :
    shift m b * scale m a ∈ fpSpanStab (factor m) :=
  mem_fpSpanStab_of_perm ((Units.mulLeft a).trans (Equiv.addRight b)) (affine_smul_factor m a b)

/-- **The polar section is `AGL(1, ℤ/n)`-invariant.** For `n = 2m - 1`, every affine map
`v ↦ a v + b` of `V_m`, `a ∈ (ℤ/n)ˣ`, fixing `∞`, maps `R_rr` onto itself under `ρW` and
preserves the round-robin zero set. A corollary of `isZeroState_smul_iff_of_perm` and
`mem_fpSpanStab_of_perm` (ham-spin ca8c6cf) and `affine_smul_factor` (ham-spin c1941cf). -/
theorem rrSpan_map_and_isZeroState_affine_smul (a : (ZMod (2 * m - 1))ˣ)
    (b : ZMod (2 * m - 1)) :
    (rrSpan m).map (ρW (shift m b * scale m a)) = rrSpan m ∧
      ∀ P, IsZeroState (factor m) ((shift m b * scale m a) • P) ↔ IsZeroState (factor m) P :=
  rrSpan_map_and_isZeroState_smul_of_perm ((Units.mulLeft a).trans (Equiv.addRight b))
    (affine_smul_factor m a b)

/-- Every automorphism of the round-robin 1-factorization preserves `R_rr` under `ρW`, for every
`m`, so `Aut(𝓕) ≤ fpSpanStab (factor m)`. By `IsAut.exists_perm` (ham-spin c1941cf) and
`mem_fpSpanStab_of_perm` (ham-spin ca8c6cf). -/
theorem autGroup_le_fpSpanStab : autGroup m ≤ fpSpanStab (factor m) := fun _ hσ ↦
  let ⟨π, hπ⟩ := IsAut.exists_perm hσ
  mem_fpSpanStab_of_perm π hπ

/-- **`AGL(1, ℤ/n)` preserves the polar section**, stated through
`autGroupMulEquiv : AGL(1, ℤ/n) ≃* Aut(𝓕)` (ham-spin c1941cf). For odd `n = 2m - 1 ≥ 7` and an
affine equivalence `g` of `ℤ/n`, the permutation `autGroupMulEquiv hm g` of `V_m` maps `R_rr`
onto itself under `ρW` and preserves the round-robin zero set. A corollary of
`isZeroState_smul_iff_of_perm` (ham-spin ca8c6cf) and `IsAut.exists_perm` (ham-spin c1941cf). -/
theorem rrSpan_map_and_isZeroState_autGroupMulEquiv (hm : 4 ≤ m)
    (g : ZMod (2 * m - 1) ≃ᵃ[ZMod (2 * m - 1)] ZMod (2 * m - 1)) :
    (rrSpan m).map (ρW (autGroupMulEquiv hm g : Perm (Vertex m))) = rrSpan m ∧
      ∀ P, IsZeroState (factor m) ((autGroupMulEquiv hm g : Perm (Vertex m)) • P) ↔
        IsZeroState (factor m) P :=
  let ⟨π, hπ⟩ := IsAut.exists_perm (autGroupMulEquiv hm g).2
  rrSpan_map_and_isZeroState_smul_of_perm π hπ

end Pairing.RoundRobin.Canonical
