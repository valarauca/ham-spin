import Clifford.ConceptualForm
import Clifford.Presentation
import Pairing.Union
import Mathlib.Algebra.Polynomial.Coeff

/-!
# `W` as a functor on the Brauer category at `δ = 0` (COD-278)

Theorem C of `results/presentation-consequences-extend.md` §3.2 (organize-archive 3ba2201), with
the corrections of items 12 to 14 of `results/presentation-consequences-factcheck-extend.md`
(3ba2201). Vectors of `𝔽₂[𝓜(V)]` are functions `𝓜(V) → 𝔽₂`, with basis `δ P`.

* C.1. `brauerPairing x y = ∑_{P,Q} x_P y_Q δ^{c(P ∪ Q)}` in `𝔽₂[δ]`, and
  `coeff_one_brauerPairing` : its `δ¹` coefficient is the Hamiltonicity form `hamForm x y`.
* `offPair a b = V ∖ {a, b}`. `cup hab Q = Q ∪ {ab}` for `Q ∈ 𝓜(V ∖ {a, b})`, and
  `boundary hab F = ∂_ab F` removes `a`, `b` and joins `F(a)` to `F(b)`. `cupLin` and `capLin`
  are the linear cup `e_Q ↦ e_{Q ∪ ab}` and cap `e_F ↦ [ab ∉ F] e_{∂_ab F}`.
* C.2. `H_cup` : `H[Q ∪ ab, F] = [ab ∉ F] H[Q, ∂_ab F]` when `V ∖ {a, b}` is nonempty, the one-edge
  case of `H_glue` (`core/Pairing/Contraction.lean`, ham-spin 5ecf8a5). `hamForm_cupLin` : the cap
  is the `H`-adjoint of the cup. The statement fails at `|V| = 2` (fact check item 13).
* C.4. `R4`, spanned by the four-point orbit sums, and `cupLin_capLin_add_mem_R4` : on
  `𝔽₂[𝓜] ⧸ R_4` the cap-cup on `{a, b}` acts as `1 + (a b)`. Each four-point orbit sum is a
  three-cycle orbit sum (fact check item 14), so `R4_le_R3`.
* C.3. `cupLin_R3_le`, `capLin_R3_le`, `congrLin_R3_le` : cups, caps and bijections preserve
  `R_3`, so they descend to `Q V = 𝔽₂[𝓜] ⧸ R_3` (`Clifford/Presentation.lean`, ham-spin 11916af)
  as `cupQ`, `capQ`, `congrQ`. `cupQ_capQ` is C.4 on `Q V`.
-/

namespace Pairing.PerfectMatching

open Equiv

variable {V : Type*} [Fintype V] [DecidableEq V]

section BrauerPairing

/-- The generic Brauer pairing `⟨x, y⟩_δ = ∑_{P,Q} x_P y_Q δ^{c(P ∪ Q)}` in `𝔽₂[δ]`, with `c` the
cycle count (`results/presentation-consequences-extend.md` Theorem C.1, 3ba2201). -/
noncomputable def brauerPairing (x y : PerfectMatching V → F₂) : Polynomial F₂ :=
  ∑ P, ∑ Q, Polynomial.C (x P * y Q) * Polynomial.X ^ cycleCount P Q

/-- `H[P, Q]` is the `δ¹` coefficient of `δ^{c(P ∪ Q)}` (Theorem C.1 on matchings). -/
theorem H_eq_coeff_X_pow (P Q : PerfectMatching V) :
    H P Q = ((Polynomial.X : Polynomial F₂) ^ cycleCount P Q).coeff 1 := by
  rw [H_apply, Polynomial.coeff_X_pow]
  by_cases h : Ham P Q
  · rw [ite_eq_left h, ite_eq_left ((ham_iff_cycleCount_eq_one P Q).mp h).symm]
  · rw [ite_eq_right h, ite_eq_right fun h' ↦ h ((ham_iff_cycleCount_eq_one P Q).mpr h'.symm)]

/-- **Theorem C.1.** `H(x, y)` is the `δ¹` coefficient of the Brauer pairing
`∑_{P,Q} x_P y_Q δ^{c(P ∪ Q)}` (`results/presentation-consequences-extend.md` §3.2, 3ba2201,
and archive Theorem 10.1 as fact check item 12 notes). -/
theorem coeff_one_brauerPairing (x y : PerfectMatching V → F₂) :
    (brauerPairing x y).coeff 1 = hamForm x y := by
  rw [brauerPairing, hamForm, Matrix.toBilin'_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun Q _ ↦ ?_
  rw [Polynomial.coeff_C_mul, ← H_eq_coeff_X_pow]
  ring

end BrauerPairing

section Cup

variable {a b : V}

variable (a b) in
/-- `V ∖ {a, b}`. -/
def offPair : Finset V :=
  ({a, b} : Finset V)ᶜ

/-- Membership in `V ∖ {a, b}`. -/
theorem mem_offPair {v : V} : v ∈ offPair a b ↔ v ≠ a ∧ v ≠ b := by
  simp [offPair]

/-- `a ∉ V ∖ {a, b}`. -/
theorem left_notMem_offPair : a ∉ offPair a b := by
  simp [offPair]

/-- `b ∉ V ∖ {a, b}`. -/
theorem right_notMem_offPair : b ∉ offPair a b := by
  simp [offPair]

/-- A vertex outside `V ∖ {a, b}` is `a` or `b`. -/
theorem eq_or_eq_of_notMem_offPair {v : V} (h : v ∉ offPair a b) : v = a ∨ v = b := by
  rw [mem_offPair] at h
  tauto

variable (a b) in
/-- The partner function of `Q ∪ {ab}`. -/
def cupFun (Q : PerfectMatching (offPair a b)) (v : V) : V :=
  if h : v ∈ offPair a b then Q.mate ⟨v, h⟩ else if v = a then b else a

/-- Off `{a, b}`, `Q ∪ {ab}` agrees with `Q`. -/
theorem cupFun_of_mem (Q : PerfectMatching (offPair a b)) {v : V} (h : v ∈ offPair a b) :
    cupFun a b Q v = Q.mate ⟨v, h⟩ :=
  dite_eq_left h

/-- `Q ∪ {ab}` sends `a` to `b`. -/
theorem cupFun_left (Q : PerfectMatching (offPair a b)) : cupFun a b Q a = b := by
  rw [cupFun, dite_eq_right left_notMem_offPair, ite_eq_left rfl]

/-- `Q ∪ {ab}` sends `b` to `a`. -/
theorem cupFun_right (hab : a ≠ b) (Q : PerfectMatching (offPair a b)) : cupFun a b Q b = a := by
  rw [cupFun, dite_eq_right right_notMem_offPair, ite_eq_right hab.symm]

/-- The partner function of `Q ∪ {ab}` is an involution. -/
theorem cupFun_involutive (hab : a ≠ b) (Q : PerfectMatching (offPair a b)) :
    Function.Involutive (cupFun a b Q) := by
  intro v
  by_cases h : v ∈ offPair a b
  · rw [cupFun_of_mem Q h, cupFun_of_mem Q (Q.mate ⟨v, h⟩).2]
    simp
  · rcases eq_or_eq_of_notMem_offPair h with rfl | rfl
    · rw [cupFun_left, cupFun_right hab]
    · rw [cupFun_right hab, cupFun_left]

/-- `cup hab Q = Q ∪ {ab}`, a matching of `V` from a matching of `V ∖ {a, b}`. -/
def cup (hab : a ≠ b) (Q : PerfectMatching (offPair a b)) : PerfectMatching V where
  mate := Function.Involutive.toPerm _ (cupFun_involutive hab Q)
  mate_mate := cupFun_involutive hab Q
  mate_ne v := by
    change cupFun a b Q v ≠ v
    by_cases h : v ∈ offPair a b
    · rw [cupFun_of_mem Q h]
      exact fun h' ↦ Q.mate_ne ⟨v, h⟩ (Subtype.ext h')
    · rcases eq_or_eq_of_notMem_offPair h with rfl | rfl
      · rw [cupFun_left]
        exact hab.symm
      · rw [cupFun_right hab]
        exact hab

/-- The partner function of `cup hab Q` is `cupFun a b Q`. -/
theorem cup_mate (hab : a ≠ b) (Q : PerfectMatching (offPair a b)) (v : V) :
    (cup hab Q).mate v = cupFun a b Q v :=
  rfl

/-- `V ∖ {a, b}` is a union of edges of `Q ∪ {ab}`. -/
theorem cup_mate_mem (hab : a ≠ b) (Q : PerfectMatching (offPair a b)) :
    ∀ v ∈ offPair a b, (cup hab Q).mate v ∈ offPair a b := fun v h ↦ by
  rw [cup_mate, cupFun_of_mem Q h]
  exact (Q.mate ⟨v, h⟩).2

/-- Gluing `X` into `Q ∪ {ab}` along `V ∖ {a, b}` gives `X ∪ {ab}`. -/
theorem glue_cup (hab : a ≠ b) (Q X : PerfectMatching (offPair a b)) :
    glue (cup hab Q) (offPair a b) (cup_mate_mem hab Q) X = cup hab X := by
  ext v
  by_cases h : v ∈ offPair a b
  · rw [glue_mate_of_mem _ _ _ _ h, cup_mate, cupFun_of_mem X h]
  · rw [glue_mate_of_notMem _ _ _ _ h, cup_mate, cup_mate, cupFun, cupFun, dite_eq_right h,
      dite_eq_right h]

end Cup

section Cap

variable {a b : V}

variable (a b) in
/-- The partner function of `∂_ab F` on `V ∖ {a, b}`: `F(a)` and `F(b)` become partners. -/
def capFun (F : PerfectMatching V) (v : V) : V :=
  if F.mate v = a then F.mate b else if F.mate v = b then F.mate a else F.mate v

omit [Fintype V] in
/-- If `F(v) = a` then `∂_ab F` sends `v` to `F(b)`. -/
theorem capFun_of_eq_left (F : PerfectMatching V) {v : V} (h : F.mate v = a) :
    capFun a b F v = F.mate b := by
  simp only [capFun, h, ↓reduceIte]

omit [Fintype V] in
/-- If `F(v) = b` then `∂_ab F` sends `v` to `F(a)`. -/
theorem capFun_of_eq_right (hab : a ≠ b) (F : PerfectMatching V) {v : V} (h : F.mate v = b) :
    capFun a b F v = F.mate a := by
  simp only [capFun, h, hab.symm, ↓reduceIte]

omit [Fintype V] in
/-- If `F(v) ∉ {a, b}` then `∂_ab F` agrees with `F` at `v`. -/
theorem capFun_of_ne (F : PerfectMatching V) {v : V} (h1 : F.mate v ≠ a) (h2 : F.mate v ≠ b) :
    capFun a b F v = F.mate v := by
  simp only [capFun, h1, h2, ↓reduceIte]

/-- `∂_ab F` maps `V ∖ {a, b}` into itself. -/
theorem capFun_mem (F : PerfectMatching V) {v : V} (hv : v ∈ offPair a b) :
    capFun a b F v ∈ offPair a b := by
  rw [mem_offPair] at hv ⊢
  unfold capFun
  split_ifs with h1 h2
  · refine ⟨fun h ↦ hv.2 (F.mate.injective (h.trans h1.symm)).symm, F.mate_ne b⟩
  · refine ⟨F.mate_ne a, fun h ↦ hv.1 (F.mate.injective (h.trans h2.symm)).symm⟩
  · exact ⟨h1, h2⟩

/-- `∂_ab F` is an involution on `V ∖ {a, b}`. -/
theorem capFun_capFun (hab : a ≠ b) (F : PerfectMatching V) {v : V} (hv : v ∈ offPair a b) :
    capFun a b F (capFun a b F v) = v := by
  rw [mem_offPair] at hv
  by_cases h1 : F.mate v = a
  · rw [capFun_of_eq_left F h1, capFun_of_eq_right hab F (mate_mate F b), ← h1, mate_mate]
  · by_cases h2 : F.mate v = b
    · rw [capFun_of_eq_right hab F h2, capFun_of_eq_left F (mate_mate F a), ← h2, mate_mate]
    · rw [capFun_of_ne F h1 h2, capFun_of_ne F (by rw [mate_mate]; exact hv.1)
        (by rw [mate_mate]; exact hv.2), mate_mate]

omit [Fintype V] in
/-- `∂_ab F` has no fixed point. -/
theorem capFun_ne (hab : a ≠ b) (F : PerfectMatching V) (v : V) : capFun a b F v ≠ v := by
  unfold capFun
  split_ifs with h1 h2
  · intro h
    rw [← h, mate_mate] at h1
    exact hab h1.symm
  · intro h
    rw [← h, mate_mate] at h2
    exact hab h2
  · exact F.mate_ne v

/-- `∂_ab F`, the matching of `V ∖ {a, b}` that removes `a` and `b` and joins `F(a)` to `F(b)`.
If `ab ∈ F` it is the restriction of `F`. -/
def boundary (hab : a ≠ b) (F : PerfectMatching V) : PerfectMatching (offPair a b) where
  mate := Function.Involutive.toPerm (fun v ↦ ⟨capFun a b F v, capFun_mem F v.2⟩)
    fun v ↦ Subtype.ext (capFun_capFun hab F v.2)
  mate_mate v := Subtype.ext (capFun_capFun hab F v.2)
  mate_ne v h := capFun_ne hab F v (congrArg Subtype.val h)

/-- The partner function of `boundary hab F` is `capFun a b F`. -/
theorem boundary_mate (hab : a ≠ b) (F : PerfectMatching V) (v : offPair a b) :
    ((boundary hab F).mate v : V) = capFun a b F v :=
  rfl

/-- The endpoint pairing of `F ∪ {ab}` on `V ∖ {a, b}` is `∂_ab F` when `ab ∉ F`. -/
theorem contract_cup (hab : a ≠ b) (Q : PerfectMatching (offPair a b)) {F : PerfectMatching V}
    (hF : F.mate a ≠ b) :
    contract (cup hab Q) F (offPair a b) (cup_mate_mem hab Q) = boundary hab F := by
  ext x
  rw [boundary_mate]
  have hv := x.2
  by_cases h : F.mate x ∈ offPair a b
  · rw [contract_mate_of_mem _ _ _ _ _ h]
    rw [mem_offPair] at h
    simp only [capFun, h.1, h.2, ↓reduceIte]
  · have hFb : F.mate b ≠ a := fun h' ↦ hF (F.mate_eq_comm.mp h')
    have hstep : ∀ c d : V, F.mate x = c → (cup hab Q).mate c = d → F.mate d ∈ offPair a b →
        ((contract (cup hab Q) F (offPair a b) (cup_mate_mem hab Q)).mate x : V) = F.mate d := by
      intro c d hc hd hm
      have h1 : exitIdx (cup hab Q) F (offPair a b) (cup_mate_mem hab Q) x = 1 := by
        unfold exitIdx
        rw [Nat.find_eq_iff]
        refine ⟨?_, fun k hk ↦ ?_⟩
        · rwa [oddPt, evenPt_succ, oddPt, evenPt_zero, hc, hd]
        · obtain rfl : k = 0 := by omega
          rwa [oddPt, evenPt_zero]
      rw [contract_mate, coe_contractFun, h1, oddPt, evenPt_succ, oddPt, evenPt_zero, hc, hd]
    rcases eq_or_eq_of_notMem_offPair h with h' | h'
    · rw [hstep a b h' (cupFun_left Q) (mem_offPair.mpr ⟨hFb, F.mate_ne b⟩)]
      simp only [capFun, h', ↓reduceIte]
    · rw [hstep b a h' (cupFun_right hab Q) (mem_offPair.mpr ⟨F.mate_ne a, hF⟩)]
      simp only [capFun, h', hab.symm, ↓reduceIte]

/-- `F ∪ {ab}` has a closed cycle off `V ∖ {a, b}` exactly when `ab ∈ F`. -/
theorem hasClosedCycle_cup_iff (hab : a ≠ b) (Q : PerfectMatching (offPair a b))
    (F : PerfectMatching V) : HasClosedCycle (cup hab Q) F (offPair a b) ↔ F.mate a = b := by
  constructor
  · rintro ⟨C, ⟨v, hv⟩, hdisj, -, hF⟩
    have hnot : ∀ w ∈ C, w = a ∨ w = b := fun w hw ↦
      eq_or_eq_of_notMem_offPair (Finset.disjoint_left.mp hdisj hw)
    rcases hnot v hv with rfl | rfl
    · rcases hnot _ (hF v hv) with h | h
      · exact absurd h (F.mate_ne v)
      · exact h
    · rcases hnot _ (hF v hv) with h | h
      · exact F.mate_eq_comm.mpr h
      · exact absurd h (F.mate_ne v)
  · intro h
    refine ⟨{a, b}, ⟨a, Finset.mem_insert_self a _⟩, ?_, ?_, ?_⟩
    · rw [offPair]
      exact disjoint_compl_right
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · rw [cup_mate, cupFun_left]
        simp
      · rw [Finset.mem_singleton.mp hv, cup_mate, cupFun_right hab]
        simp
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · rw [h]
        simp
      · rw [Finset.mem_singleton.mp hv, F.mate_eq_comm.mp h]
        simp

/-- **Theorem C.2 on matchings.** For `Q ∈ 𝓜(V ∖ {a, b})` and `F ∈ 𝓜(V)`,
`H[Q ∪ ab, F] = [ab ∉ F] H[Q, ∂_ab F]`, provided `V ∖ {a, b}` is nonempty, which for matchings
means `|V ∖ {a, b}| ≥ 2` (`results/presentation-consequences-extend.md` §3.2 with fact check item
13 of `results/presentation-consequences-factcheck-extend.md`, 3ba2201). It is the one-edge case
of `H_glue` and `H_glue_of_hasClosedCycle` (`core/Pairing/Contraction.lean`, ham-spin 5ecf8a5). -/
theorem H_cup (hab : a ≠ b) (hA : (offPair a b).Nonempty) (Q : PerfectMatching (offPair a b))
    (F : PerfectMatching V) :
    H (cup hab Q) F = if F.mate a = b then 0 else H Q (boundary hab F) := by
  rw [← glue_cup hab Q Q]
  split_ifs with h
  · exact H_glue_of_hasClosedCycle _ _ _ _ ((hasClosedCycle_cup_iff hab Q F).mpr h) hA Q
  · rw [H_glue _ _ _ _ (mt (hasClosedCycle_cup_iff hab Q F).mp h), contract_cup hab Q h]

end Cap

section Linear

variable {a b : V}

/-- The cup `e_Q ↦ e_{Q ∪ ab}`, `𝔽₂[𝓜(V ∖ {a, b})] → 𝔽₂[𝓜(V)]`. -/
def cupLin (hab : a ≠ b) : (PerfectMatching (offPair a b) → F₂) →ₗ[F₂] (PerfectMatching V → F₂) :=
  Fintype.linearCombination F₂ fun Q ↦ δ (cup hab Q)

/-- The cup on a basis vector, `e_Q ↦ e_{Q ∪ ab}`. -/
theorem cupLin_δ (hab : a ≠ b) (Q : PerfectMatching (offPair a b)) :
    cupLin hab (δ Q) = δ (cup hab Q) := by
  rw [cupLin, δ, Fintype.linearCombination_apply_single, one_smul]

/-- The cap of one matching, `[ab ∉ F] e_{∂_ab F}`. -/
def capVec (hab : a ≠ b) (F : PerfectMatching V) : PerfectMatching (offPair a b) → F₂ :=
  if F.mate a = b then 0 else δ (boundary hab F)

/-- The cap `e_F ↦ [ab ∉ F] e_{∂_ab F}`, `𝔽₂[𝓜(V)] → 𝔽₂[𝓜(V ∖ {a, b})]`. A closed loop on
`{a, b}` is sent to `0`, as at `δ = 0`. -/
def capLin (hab : a ≠ b) : (PerfectMatching V → F₂) →ₗ[F₂] (PerfectMatching (offPair a b) → F₂) :=
  Fintype.linearCombination F₂ (capVec hab)

/-- The cap on a basis vector, `e_F ↦ [ab ∉ F] e_{∂_ab F}`. -/
theorem capLin_δ (hab : a ≠ b) (F : PerfectMatching V) : capLin hab (δ F) = capVec hab F := by
  rw [capLin, δ, Fintype.linearCombination_apply_single, one_smul]

/-- On basis vectors the Hamiltonicity form is `H`. -/
theorem hamForm_δ (P Q : PerfectMatching V) : hamForm (δ P) (δ Q) = H P Q := by
  rw [δ, δ, hamForm_single, H_apply]

/-- **Theorem C.2.** The cap is the `H`-adjoint of the cup, `H(cup_ab x, y) = H(x, cap_ab y)`,
when `|V ∖ {a, b}| ≥ 2` (`results/presentation-consequences-extend.md` §3.2, corrected by fact
check item 13 of `results/presentation-consequences-factcheck-extend.md`, 3ba2201). -/
theorem hamForm_cupLin (hab : a ≠ b) (hA : (offPair a b).Nonempty)
    (x : PerfectMatching (offPair a b) → F₂) (y : PerfectMatching V → F₂) :
    hamForm (cupLin hab x) y = hamForm x (capLin hab y) := by
  have key : (hamForm (V := V)).compl₁₂ (cupLin hab) LinearMap.id =
      (hamForm (V := offPair a b)).compl₁₂ LinearMap.id (capLin hab) := by
    refine LinearMap.ext_basis (Pi.basisFun F₂ _) (Pi.basisFun F₂ _) fun Q F ↦ ?_
    simp only [LinearMap.compl₁₂_apply, LinearMap.id_apply, Pi.basisFun_apply]
    change hamForm (cupLin hab (δ Q)) (δ F) = hamForm (δ Q) (capLin hab (δ F))
    rw [cupLin_δ, capLin_δ, hamForm_δ, H_cup hab hA, capVec]
    split_ifs
    · rw [map_zero]
    · rw [hamForm_δ]
  exact LinearMap.congr_fun₂ key x y

end Linear

section FourPoint

/-- The four-point orbit sum `e_X + e_{τX} + e_{τ²X}` for `τ = (a X(a)) (a c)`, a three-cycle on
`a`, `X(a)`, `c` whose orbit consists of the three pairings of the four points `a`, `X(a)`, `c`,
`X(c)` (`results/presentation-consequences-extend.md` Theorem C.4, 3ba2201). -/
def fourSum (X : PerfectMatching V) (a c : V) : PerfectMatching V → F₂ :=
  δ X + δ ((swap a (X.mate a) * swap a c) • X) + δ ((swap a (X.mate a) * swap a c) ^ 2 • X)

variable (V) in
/-- `R_4`, the span of the four-point orbit sums. `𝔽₂[𝓜] ⧸ R_4` is the four-switch quotient. -/
def R4 : Submodule F₂ (PerfectMatching V → F₂) :=
  Submodule.span F₂ {f | ∃ (X : PerfectMatching V) (a c : V), c ≠ a ∧ c ≠ X.mate a ∧
    f = fourSum X a c}

/-- The permutation in `fourSum X a c` is a three-cycle when `c ∉ {a, X(a)}`. -/
theorem isThreeCycle_four {X : PerfectMatching V} {a c : V} (hca : c ≠ a) (hcX : c ≠ X.mate a) :
    (swap a (X.mate a) * swap a c).IsThreeCycle :=
  Perm.isThreeCycle_swap_mul_swap_same (X.mate_ne a).symm hca.symm hcX.symm

/-- Each four-point orbit sum is a three-cycle orbit sum (fact check item 14 of
`results/presentation-consequences-factcheck-extend.md`, 3ba2201), so `R_4 ⊆ R_3`. -/
theorem R4_le_R3 : R4 V ≤ R3 V := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨X, a, c, hca, hcX, rfl⟩
  exact orbitSum_mem_R3 X (isThreeCycle_four hca hcX)

variable {a b : V}

omit [Fintype V] in
/-- `(a b) F = F` when `ab` is an edge of `F`. -/
theorem swap_smul_of_mate (F : PerfectMatching V) (h : F.mate a = b) : swap a b • F = F := by
  rw [← h]
  exact swap_mate_smul F a

/-- `Q ∪ {ab}` with `Q = ∂_ab F` is `(F(a) b) F`, when `ab ∉ F`. -/
theorem cup_boundary (hab : a ≠ b) {F : PerfectMatching V} (hF : F.mate a ≠ b) :
    cup hab (boundary hab F) = swap (F.mate a) b • F := by
  have hb'b : F.mate b ≠ b := F.mate_ne b
  have hb'a' : F.mate b ≠ F.mate a := fun h ↦ hab (F.mate.injective h).symm
  have ha'a : F.mate a ≠ a := F.mate_ne a
  ext v
  rw [smul_mate, swap_inv, cup_mate]
  by_cases hva : v = a
  · subst hva
    rw [cupFun_left, swap_apply_of_ne_of_ne ha'a.symm hab, swap_apply_left]
  by_cases hvb : v = b
  · subst hvb
    rw [cupFun_right hab, swap_apply_right, mate_mate, swap_apply_of_ne_of_ne ha'a.symm hab]
  have hv : v ∈ offPair a b := mem_offPair.mpr ⟨hva, hvb⟩
  rw [cupFun_of_mem _ hv, boundary_mate]
  change capFun a b F v = swap (F.mate a) b (F.mate (swap (F.mate a) b v))
  by_cases hva' : v = F.mate a
  · have h1 : F.mate v = a := by rw [hva', mate_mate]
    rw [capFun_of_eq_left F h1, hva', swap_apply_left, swap_apply_of_ne_of_ne hb'a' hb'b]
  by_cases hvb' : v = F.mate b
  · have h2 : F.mate v = b := by rw [hvb', mate_mate]
    rw [capFun_of_eq_right hab F h2, swap_apply_of_ne_of_ne hva' hvb, h2, swap_apply_right]
  · have h1 : F.mate v ≠ a := fun h ↦ hva' (by rw [← h, mate_mate])
    have h2 : F.mate v ≠ b := fun h ↦ hvb' (by rw [← h, mate_mate])
    have h3 : F.mate v ≠ F.mate a := fun h ↦ hva (F.mate.injective h)
    rw [capFun_of_ne F h1 h2, swap_apply_of_ne_of_ne hva' hvb, swap_apply_of_ne_of_ne h3 h2]

/-- The three-cycle `τ = (a F(a)) (a b)` moves `F` to `∂_ab F ∪ {ab}` and `τ²` moves it to
`(a b) F`, when `ab ∉ F`. -/
theorem fourSum_eq (hab : a ≠ b) {F : PerfectMatching V} (hF : F.mate a ≠ b) :
    fourSum F a b = δ F + δ (cup hab (boundary hab F)) + δ (swap a b • F) := by
  have hb : swap a (F.mate a) b = b := swap_apply_of_ne_of_ne hab.symm (Ne.symm hF)
  have hconj : swap (F.mate a) b * swap a (F.mate a) = swap a (F.mate a) * swap a b := by
    have h := swap_apply_apply (swap a (F.mate a)) a b
    rw [swap_apply_left, hb] at h
    rw [h, mul_assoc, mul_assoc, swap_inv, swap_mul_self, mul_one]
  have h1 : (swap a (F.mate a) * swap a b) • F = cup hab (boundary hab F) := by
    rw [cup_boundary hab hF, ← hconj, mul_smul, swap_mate_smul]
  have hsq : (swap a (F.mate a) * swap a b) ^ 2 = swap (F.mate a) b * swap a b := by
    rw [pow_two]
    nth_rewrite 1 [← hconj]
    rw [mul_assoc, ← mul_assoc (swap a (F.mate a)), swap_mul_self, one_mul]
  have h2 : (swap a (F.mate a) * swap a b) ^ 2 • F = swap a b • F := by
    have hm : (swap a b • F).mate (F.mate a) = b := by
      rw [smul_mate, swap_inv, swap_apply_of_ne_of_ne (F.mate_ne a) hF, mate_mate, swap_apply_left]
    have key := swap_mate_smul (swap a b • F) (F.mate a)
    rw [hm] at key
    rw [hsq, mul_smul, key]
  rw [fourSum, h1, h2]

/-- **Theorem C.4.** On the four-switch quotient `𝔽₂[𝓜] ⧸ R_4`, the cap-cup on `{a, b}` acts as
`1 + (a b)`: `cup_ab (cap_ab x) + x + (a b) x ∈ R_4` for every `x`
(`results/presentation-consequences-extend.md` §3.2, 3ba2201). The four-point triple is a
three-cycle orbit sum (fact check item 14), so this also holds modulo `R_3`. -/
theorem cupLin_capLin_add_mem_R4 (hab : a ≠ b) (x : PerfectMatching V → F₂) :
    cupLin hab (capLin hab x) + x + ρ (swap a b) x ∈ R4 V := by
  rw [← sum_smul_δ x]
  simp only [map_sum, map_smul, ← Finset.sum_add_distrib, ← smul_add]
  refine Submodule.sum_mem _ fun F _ ↦ Submodule.smul_mem _ _ ?_
  rw [capLin_δ, ρ_δ, capVec]
  split_ifs with hF
  · rw [map_zero, zero_add, swap_smul_of_mate F hF, add_self_F₂]
    exact zero_mem _
  · rw [cupLin_δ]
    have hmem : fourSum F a b ∈ R4 V :=
      Submodule.subset_span ⟨F, a, b, Ne.symm hab, Ne.symm hF, rfl⟩
    rw [fourSum_eq hab hF] at hmem
    convert hmem using 1
    abel

/-- **Theorem C.4 on the quotient.** In `𝔽₂[𝓜] ⧸ R_4`, `[cup_ab (cap_ab x)] = [x + (a b) x]`. -/
theorem mk_cupLin_capLin (hab : a ≠ b) (x : PerfectMatching V → F₂) :
    (Submodule.Quotient.mk (cupLin hab (capLin hab x)) : _ ⧸ R4 V) =
      Submodule.Quotient.mk (x + ρ (swap a b) x) := by
  rw [Submodule.Quotient.eq, sub_eq_add_neg, neg_eq_of_add_eq_zero_left (add_self_F₂ _),
    ← add_assoc]
  exact cupLin_capLin_add_mem_R4 hab x

end FourPoint

section Descent

variable {a b : V}

/-- `(τ Q) ∪ {ab} = τ̃ (Q ∪ {ab})`, where `τ̃` extends `τ ∈ S_{V ∖ {a, b}}` by the identity on
`{a, b}`. -/
theorem cup_smul (hab : a ≠ b) (τ : Perm (offPair a b)) (Q : PerfectMatching (offPair a b)) :
    cup hab (τ • Q) = Perm.ofSubtype τ • cup hab Q := by
  ext v
  rw [smul_mate, cup_mate, cup_mate, ← map_inv]
  by_cases h : v ∈ offPair a b
  · rw [cupFun_of_mem _ h, Perm.ofSubtype_apply_of_mem _ h, cupFun_of_mem _ (τ⁻¹ ⟨v, h⟩).2,
      smul_mate, ← Perm.ofSubtype_apply_coe]
  · have hc : cupFun a b Q v ∉ offPair a b := by
      rcases eq_or_eq_of_notMem_offPair h with rfl | rfl
      · rw [cupFun_left]
        exact right_notMem_offPair
      · rw [cupFun_right hab]
        exact left_notMem_offPair
    rw [Perm.ofSubtype_apply_of_not_mem _ h, Perm.ofSubtype_apply_of_not_mem _ hc, cupFun, cupFun,
      dite_eq_right h, dite_eq_right h]

/-- **Theorem C.3, cups.** The cup carries `R_3(V ∖ {a, b})` into `R_3(V)`, since a three-cycle of
`V ∖ {a, b}` is a three-cycle of `V` fixing `a` and `b`
(`results/presentation-consequences-extend.md` §3.2, 3ba2201). -/
theorem cupLin_R3_le (hab : a ≠ b) : R3 (offPair a b) ≤ (R3 V).comap (cupLin hab) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨Q, τ, hτ, rfl⟩
  have hτ' : (Perm.ofSubtype τ).IsThreeCycle := by
    rw [Perm.IsThreeCycle, Perm.cycleType_ofSubtype]
    exact hτ
  change cupLin hab _ ∈ R3 V
  rw [map_add, map_add, cupLin_δ, cupLin_δ, cupLin_δ, cup_smul, cup_smul, map_pow]
  exact orbitSum_mem_R3 _ hτ'

/-- The row map is `x ↦ x H`. -/
theorem coe_Θ (x : PerfectMatching V → F₂) :
    (Θ x : PerfectMatching V → F₂) = Matrix.vecMul x H := by
  rw [Θ, Fintype.linearCombination_apply, Submodule.coe_sum, Matrix.vecMul_eq_sum]
  simp only [Submodule.coe_smul, coe_rowW]

/-- For `|V| = 2n`, `n ≥ 1`, `R_3` is the radical of the Hamiltonicity form, from
`ker_Θ_eq_R3` (`Clifford/Presentation.lean`, ham-spin 11916af) and `ker_hamForm`. -/
theorem mem_R3_iff {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 1 ≤ n)
    (x : PerfectMatching V → F₂) : x ∈ R3 V ↔ ∀ y, hamForm x y = 0 := by
  rw [← ker_Θ_eq_R3 hV hn, LinearMap.mem_ker, ← Submodule.coe_eq_zero, coe_Θ,
    ← Matrix.vecMulLinear_apply, ← LinearMap.mem_ker, ← ker_hamForm, LinearMap.mem_ker]
  exact ⟨fun h y ↦ by rw [h, LinearMap.zero_apply], fun h ↦ LinearMap.ext h⟩

/-- `|V ∖ {a, b}| = |V| - 2`. -/
theorem card_offPair (hab : a ≠ b) : Fintype.card (offPair a b) = Fintype.card V - 2 := by
  rw [Fintype.card_coe, offPair, Finset.card_compl, Finset.card_pair hab]

/-- **Theorem C.3, caps.** For `|V| = 2n`, `n ≥ 2`, the cap carries `R_3(V)` into
`R_3(V ∖ {a, b})`. On both sides `R_3` is the radical of `H`, and the cap is the `H`-adjoint of
the cup (`hamForm_cupLin`), as in `results/presentation-consequences-extend.md` §3.2 (3ba2201). -/
theorem capLin_R3_le {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 2 ≤ n) (hab : a ≠ b) :
    R3 V ≤ (R3 (offPair a b)).comap (capLin hab) := by
  intro y hy
  have hA : Fintype.card (offPair a b) = 2 * (n - 1) := by
    rw [card_offPair hab, hV]
    omega
  have hne : (offPair a b).Nonempty := by
    rw [← Finset.card_pos, ← Fintype.card_coe, hA]
    omega
  rw [Submodule.mem_comap, mem_R3_iff hA (by omega)]
  intro x
  rw [hamForm_comm, ← hamForm_cupLin hab hne, hamForm_comm]
  exact (mem_R3_iff hV (by omega) y).mp hy _

variable {V' : Type*} [Fintype V'] [DecidableEq V']

/-- Relabelling along a bijection `e : V ≃ V'`, `e_P ↦ e_{e P}`. -/
def congrLin (e : V ≃ V') : (PerfectMatching V → F₂) →ₗ[F₂] (PerfectMatching V' → F₂) :=
  Fintype.linearCombination F₂ fun P ↦ δ (congr e P)

/-- Relabelling on a basis vector, `e_P ↦ e_{e P}`. -/
theorem congrLin_δ (e : V ≃ V') (P : PerfectMatching V) : congrLin e (δ P) = δ (congr e P) := by
  rw [congrLin, δ, Fintype.linearCombination_apply_single, one_smul]

/-- **Theorem C.3, bijections.** Relabelling along `e : V ≃ V'` carries `R_3(V)` into `R_3(V')`
(`results/presentation-consequences-extend.md` §3.2, 3ba2201). -/
theorem congrLin_R3_le (e : V ≃ V') : R3 V ≤ (R3 V').comap (congrLin e) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨P, τ, hτ, rfl⟩
  change congrLin e _ ∈ R3 V'
  rw [map_add, map_add, congrLin_δ, congrLin_δ, congrLin_δ, congr_smul, congr_smul, pow_two,
    permCongr_mul, ← pow_two]
  exact orbitSum_mem_R3 _ (isThreeCycle_permCongr e hτ)

/-- The cup on `Q = 𝔽₂[𝓜] ⧸ R_3`, `Q(V ∖ {a, b}) → Q(V)` (Theorem C.3). -/
def cupQ (hab : a ≠ b) : Q (offPair a b) →ₗ[F₂] Q V :=
  (R3 (offPair a b)).mapQ (R3 V) (cupLin hab) (cupLin_R3_le hab)

/-- The cap on `Q = 𝔽₂[𝓜] ⧸ R_3`, `Q(V) → Q(V ∖ {a, b})`, for `|V| = 2n`, `n ≥ 2`
(Theorem C.3). -/
def capQ {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 2 ≤ n) (hab : a ≠ b) :
    Q V →ₗ[F₂] Q (offPair a b) :=
  (R3 V).mapQ (R3 (offPair a b)) (capLin hab) (capLin_R3_le hV hn hab)

/-- Relabelling on `Q = 𝔽₂[𝓜] ⧸ R_3`, `Q(V) → Q(V')` (Theorem C.3). -/
def congrQ (e : V ≃ V') : Q V →ₗ[F₂] Q V' :=
  (R3 V).mapQ (R3 V') (congrLin e) (congrLin_R3_le e)

/-- `cupQ` on classes. -/
theorem cupQ_mk (hab : a ≠ b) (x : PerfectMatching (offPair a b) → F₂) :
    cupQ hab (Submodule.Quotient.mk x) = Submodule.Quotient.mk (cupLin hab x) :=
  rfl

/-- `capQ` on classes. -/
theorem capQ_mk {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 2 ≤ n) (hab : a ≠ b)
    (x : PerfectMatching V → F₂) :
    capQ hV hn hab (Submodule.Quotient.mk x) = Submodule.Quotient.mk (capLin hab x) :=
  rfl

/-- **Theorem C.4 on `Q V`.** The cap-cup on `{a, b}` acts on `Q V = 𝔽₂[𝓜] ⧸ R_3` as `1 + (a b)`,
which is `N_ab` of `results/presentation-consequences-extend.md` Theorem C.4 (3ba2201). -/
theorem cupQ_capQ {n : ℕ} (hV : Fintype.card V = 2 * n) (hn : 2 ≤ n) (hab : a ≠ b) (x : Q V) :
    cupQ hab (capQ hV hn hab x) = x + ρQ V (swap a b) x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [capQ_mk, cupQ_mk, ρQ_mk, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, sub_eq_add_neg,
    neg_eq_of_add_eq_zero_left (add_self_F₂ _), ← add_assoc]
  exact R4_le_R3 (cupLin_capLin_add_mem_R4 hab y)

end Descent

end Pairing.PerfectMatching
