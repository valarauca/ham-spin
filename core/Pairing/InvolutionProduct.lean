import Mathlib.GroupTheory.Perm.Cycle.Type
import Pairing.Union

/-!
# The involution product of two matchings (COD-266)

Two perfect matchings `P` and `Q` of `V` are fixed-point-free involutions, and their union is read
off the product `g = P.mate * Q.mate`, so `g v = P (Q v)`. One step of `g` is two steps of an
alternating walk, a `Q`-edge followed by a `P`-edge. This file proves the dictionary once, on
Mathlib's `Equiv.Perm` cycle API, so that later files can trade hand-rolled walks for `SameCycle`,
`cycleType` and `partition`.

* `PerfectMatching.reachable_iff_sameCycle`: `v` and `w` lie in one component of `P ∪ Q` iff
  `w` or `P w` lies in the `g`-cycle of `v`.
* `PerfectMatching.not_sameCycle_mate_left`: `v` and `P v` never lie in one `g`-cycle. With
  `PerfectMatching.sameCycle_iff_reachable` this says the `g`-cycles are the classes of the
  component relation restricted to one side of the alternation.
* `PerfectMatching.card_reachable_eq_two_mul` and `PerfectMatching.card_sameCycle_mate_left`: a
  component with `2k` vertices is the disjoint union of the `g`-cycle of `v` and the `g`-cycle of
  `P v`, two distinct cycles of length `k` swapped by `P`. For `k = 1` the component is a common
  edge `{v, P v}` and the two cycles are the fixed points `v` and `P v`
  (`PerfectMatching.mate_mul_mate_apply_eq_self_iff`).
* `card_quotient_sameCycle`: for any permutation the `SameCycle` classes, fixed points included,
  number `g.partition.parts.card`.
* `PerfectMatching.two_mul_cycleCount`: `2 κ(P ∪ Q) = g.partition.parts.card`, so `κ(P ∪ Q)` is
  half the number of cycles of `g` counting fixed points.
* `PerfectMatching.ham_iff_partition`: for `|V| = 2n`, `Ham P Q` iff `g` has exactly two cycles,
  each of length `n`, fixed points included. This holds for every `n`. For `n = 0` both sides
  fail, and for `n = 1` the product is `1` with partition `{1, 1}`.
* `PerfectMatching.ham_iff_cycleType`: the same with `cycleType` once `2 ≤ n`.
* `PerfectMatching.smul_mate_mul_smul_mate`: `(σ • P)(σ • Q) = σ (P Q) σ⁻¹`, hence the invariance
  of `cycleType` and `partition` under relabelling, and `PerfectMatching.cycleCount_smul`.
-/

namespace Pairing

open Equiv Equiv.Perm Finset

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The cycles of a permutation `g`, with each fixed point counted as a `1`-cycle, are its
`SameCycle` classes, and they number `g.partition.parts.card`. -/
theorem card_quotient_sameCycle (g : Perm α) :
    Nat.card (Quotient (SameCycle.setoid g)) = g.partition.parts.card := by
  have hne : ∀ c : g.cycleFactorsFinset, (c : Perm α).support.Nonempty := fun c ↦
    nonempty_iff_ne_empty.mpr (support_eq_empty_iff.not.mpr
      (mem_cycleFactorsFinset_iff.mp c.2).1.ne_one)
  let f : {x // x ∉ g.support} ⊕ g.cycleFactorsFinset → Quotient (SameCycle.setoid g) :=
    Sum.elim (fun x ↦ Quotient.mk _ x.1) (fun c ↦ Quotient.mk _ (hne c).choose)
  have hsupp : ∀ c : g.cycleFactorsFinset, (hne c).choose ∈ g.support := fun c ↦
    mem_cycleFactorsFinset_support_le c.2 (hne c).choose_spec
  have hf : Function.Bijective f := by
    constructor
    · rintro (x | c) (y | d) h
      · have h' : g.SameCycle x.1 y.1 := Quotient.exact h
        exact congrArg Sum.inl (Subtype.ext (h'.eq_of_left (notMem_support.mp x.2)))
      · have h' : g.SameCycle x.1 (hne d).choose := Quotient.exact h
        exact absurd ((h'.eq_of_left (notMem_support.mp x.2)) ▸ hsupp d) x.2
      · have h' : g.SameCycle (hne c).choose y.1 := Quotient.exact h
        exact absurd ((h'.eq_of_right (notMem_support.mp y.2)) ▸ hsupp c) y.2
      · have h' : g.SameCycle (hne c).choose (hne d).choose := Quotient.exact h
        refine congrArg Sum.inr (Subtype.ext ?_)
        rw [cycle_is_cycleOf (hne c).choose_spec c.2, cycle_is_cycleOf (hne d).choose_spec d.2]
        exact h'.cycleOf_eq
    · intro q
      induction q using Quotient.inductionOn with
      | h x =>
        by_cases hx : x ∈ g.support
        · let c : g.cycleFactorsFinset := ⟨g.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr hx⟩
          refine ⟨Sum.inr c, ?_⟩
          change Quotient.mk _ (hne c).choose = Quotient.mk _ x
          exact Quotient.sound (mem_support_cycleOf_iff.mp (hne c).choose_spec).1.symm
        · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
  have h1 : Nat.card {x // x ∉ g.support} = Fintype.card α - #g.support := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe]
  have h2 : Nat.card g.cycleFactorsFinset = Multiset.card g.cycleFactorsFinset.val := by
    rw [Nat.card_eq_finsetCard, Finset.card_def]
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_sum, parts_partition, Multiset.card_add,
    Multiset.card_replicate, cycleType_def, Multiset.card_map, h1, h2, add_comm]

/-- Each part of `g.partition` is the size of some `SameCycle` class of `g`. -/
theorem exists_card_sameCycle_of_mem_parts (g : Perm α) {c : ℕ} (hc : c ∈ g.partition.parts) :
    ∃ x, Nat.card {y // g.SameCycle x y} = c := by
  rw [parts_partition, Multiset.mem_add] at hc
  rcases hc with hc | hc
  · rw [cycleType_def, Multiset.mem_map] at hc
    obtain ⟨τ, hτ, rfl⟩ := hc
    have hτ' : τ ∈ g.cycleFactorsFinset := hτ
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr (support_eq_empty_iff.not.mpr
      (mem_cycleFactorsFinset_iff.mp hτ').1.ne_one)
    have hgx : x ∈ g.support := mem_cycleFactorsFinset_support_le hτ' hx
    refine ⟨x, ?_⟩
    rw [cycle_is_cycleOf hx hτ', Function.comp_apply, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y ↦ by
      rw [mem_support_cycleOf_iff, and_iff_left hgx])
  · obtain ⟨hk, rfl⟩ := Multiset.mem_replicate.mp hc
    obtain ⟨x, hx⟩ : ∃ x, x ∉ g.support := by
      by_contra h
      push Not at h
      exact hk (by rw [eq_univ_of_forall h, card_univ, Nat.sub_self])
    refine ⟨x, Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b ↦ Subtype.ext ?_⟩,
      ⟨⟨x, SameCycle.refl _ _⟩⟩⟩⟩
    exact (a.2.eq_of_left (notMem_support.mp hx)).symm.trans (b.2.eq_of_left (notMem_support.mp hx))

end Perm

namespace PerfectMatching

variable {V : Type*}

/-- A matching is its own inverse. -/
theorem mate_inv (P : PerfectMatching V) : P.mate⁻¹ = P.mate := by
  ext v
  rw [Perm.inv_eq_iff_eq, mate_mate]

/-- `P P = 1`. -/
theorem mate_mul_self (P : PerfectMatching V) : P.mate * P.mate = 1 := by
  ext v
  simp

/-- `(P Q)⁻¹ = Q P`. -/
theorem mate_mul_mate_inv (P Q : PerfectMatching V) : (P.mate * Q.mate)⁻¹ = Q.mate * P.mate := by
  rw [mul_inv_rev, mate_inv, mate_inv]

/-- The fixed points of `P Q` are the ends of the common edges of `P` and `Q`. -/
theorem mate_mul_mate_apply_eq_self_iff (P Q : PerfectMatching V) (v : V) :
    (P.mate * Q.mate) v = v ↔ P.mate v = Q.mate v :=
  P.mate_eq_comm

/-- `P Q = 1` iff `P = Q`. -/
theorem mate_mul_mate_eq_one_iff (P Q : PerfectMatching V) : P.mate * Q.mate = 1 ↔ P = Q := by
  constructor
  · intro h
    ext v
    exact (mate_mul_mate_apply_eq_self_iff P Q v).mp (by rw [h, Perm.one_apply])
  · rintro rfl
    ext v
    simp

/-- `P` maps `g`-cycles to `g`-cycles, `g = P Q`, since `P g P⁻¹ = g⁻¹`. -/
theorem sameCycle_mate_left_iff (P Q : PerfectMatching V) {v w : V} :
    (P.mate * Q.mate).SameCycle (P.mate v) (P.mate w) ↔ (P.mate * Q.mate).SameCycle v w := by
  have h : P.mate * (P.mate * Q.mate) * P.mate⁻¹ = (P.mate * Q.mate)⁻¹ := by
    rw [mate_mul_mate_inv, mate_inv]
    ext x
    simp
  rw [← sameCycle_inv, ← h, sameCycle_conj, mate_inv, mate_mate, mate_mate]

/-- `Q` maps `g`-cycles to `g`-cycles, `g = P Q`. -/
theorem sameCycle_mate_right_iff (P Q : PerfectMatching V) {v w : V} :
    (P.mate * Q.mate).SameCycle (Q.mate v) (Q.mate w) ↔ (P.mate * Q.mate).SameCycle v w := by
  rw [← sameCycle_inv, mate_mul_mate_inv, sameCycle_mate_left_iff, ← mate_mul_mate_inv,
    sameCycle_inv]

/-- No power of `g = P Q` sends a vertex `u` to `P u`. Two steps of `g` move the problem from `u`
to `g u`, and the cases `g⁰ u = P u` and `g u = P u` would give fixed points of `P` and `Q`. -/
theorem pow_apply_ne_mate_left (P Q : PerfectMatching V) :
    ∀ (j : ℕ) (u : V), ((P.mate * Q.mate) ^ j) u ≠ P.mate u
  | 0, u => by
    rw [pow_zero, Perm.one_apply]
    exact (P.mate_ne u).symm
  | 1, u => by
    rw [pow_one, Perm.mul_apply]
    exact fun h ↦ Q.mate_ne u (P.mate.injective h)
  | j + 2, u => by
    intro h
    refine pow_apply_ne_mate_left P Q j ((P.mate * Q.mate) u) ?_
    have e : ((P.mate * Q.mate) ^ (j + 1)) u = ((P.mate * Q.mate) ^ j) ((P.mate * Q.mate) u) := by
      rw [pow_succ, Perm.mul_apply]
    rw [pow_succ', Perm.mul_apply, Perm.mul_apply] at h
    rw [← e, Perm.mul_apply, mate_mate]
    exact (Q.mate_eq_comm.mp (P.mate.injective h)).symm

/-- `v` and `P v` never lie in one cycle of `P Q`. A negative power `g⁻ʲ v = P v` is the positive
power `gʲ (P v) = P (P v)`. -/
theorem not_sameCycle_mate_left (P Q : PerfectMatching V) (v : V) :
    ¬(P.mate * Q.mate).SameCycle v (P.mate v) := by
  rintro ⟨i, hi⟩
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · exact pow_apply_ne_mate_left P Q j v (by rwa [zpow_natCast] at hi)
  · refine pow_apply_ne_mate_left P Q j (P.mate v) ?_
    rw [mate_mate, ← hi, zpow_neg, zpow_natCast]
    exact Equiv.apply_symm_apply _ v

/-- `v` and `Q v` never lie in one cycle of `P Q`. -/
theorem not_sameCycle_mate_right (P Q : PerfectMatching V) (v : V) :
    ¬(P.mate * Q.mate).SameCycle v (Q.mate v) := by
  rw [← sameCycle_inv, mate_mul_mate_inv]
  exact not_sameCycle_mate_left Q P v

/-- A `P`-edge is a step of the union. -/
theorem reachable_mate_left (P Q : PerfectMatching V) (v : V) :
    (P.toGraph ⊔ Q.toGraph).Reachable v (P.mate v) :=
  SimpleGraph.Adj.reachable (Or.inl rfl)

/-- A `Q`-edge is a step of the union. -/
theorem reachable_mate_right (P Q : PerfectMatching V) (v : V) :
    (P.toGraph ⊔ Q.toGraph).Reachable v (Q.mate v) :=
  SimpleGraph.Adj.reachable (Or.inr rfl)

/-- Each power of `g = P Q` moves inside one component of `P ∪ Q`. -/
theorem reachable_pow_apply (P Q : PerfectMatching V) (v : V) :
    ∀ k : ℕ, (P.toGraph ⊔ Q.toGraph).Reachable v (((P.mate * Q.mate) ^ k) v)
  | 0 => by
    rw [pow_zero, Perm.one_apply]
  | k + 1 => by
    rw [pow_succ', Perm.mul_apply, Perm.mul_apply]
    exact ((reachable_pow_apply P Q v k).trans (reachable_mate_right P Q _)).trans
      (reachable_mate_left P Q _)

/-- Each integer power of `g = P Q` moves inside one component of `P ∪ Q`. -/
theorem reachable_zpow_apply (P Q : PerfectMatching V) (v : V) (i : ℤ) :
    (P.toGraph ⊔ Q.toGraph).Reachable v (((P.mate * Q.mate) ^ i) v) := by
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · rw [zpow_natCast]
    exact reachable_pow_apply P Q v j
  · rw [zpow_neg, zpow_natCast, ← inv_pow, mate_mul_mate_inv, sup_comm]
    exact reachable_pow_apply Q P v j

/-- The component relation of `P ∪ Q` in terms of `g = P Q`: `v` and `w` lie in one component iff
`w` or `P w` lies in the `g`-cycle of `v`. -/
theorem reachable_iff_sameCycle (P Q : PerfectMatching V) {v w : V} :
    (P.toGraph ⊔ Q.toGraph).Reachable v w ↔
      (P.mate * Q.mate).SameCycle v w ∨ (P.mate * Q.mate).SameCycle v (P.mate w) := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Or.inl (SameCycle.refl _ _)
    | @tail b c _ hbc ih =>
      rcases (SimpleGraph.sup_adj _ _ _ _).mp hbc with hb | hb
      · rw [toGraph_adj] at hb
        subst hb
        rw [mate_mate]
        exact ih.symm
      · rw [toGraph_adj] at hb
        subst hb
        rcases ih with h | h
        · exact Or.inr (sameCycle_apply_right.mpr h)
        · have e : (P.mate * Q.mate).symm (P.mate b) = Q.mate b := by
            rw [Equiv.symm_apply_eq, Perm.mul_apply, mate_mate]
          exact Or.inl (e ▸ sameCycle_symm_apply_right.mpr h)
  · have key : ∀ {x : V}, (P.mate * Q.mate).SameCycle v x → (P.toGraph ⊔ Q.toGraph).Reachable v x :=
      fun ⟨i, hi⟩ ↦ hi ▸ reachable_zpow_apply P Q v i
    rintro (h | h)
    · exact key h
    · exact (key h).trans (reachable_mate_left P Q w).symm

/-- The cycles of `g = P Q` are the component relation of `P ∪ Q` restricted to one side of the
alternation: `w` lies in the `g`-cycle of `v` iff it lies in the component of `v` and `P w` does
not lie in the `g`-cycle of `v`. -/
theorem sameCycle_iff_reachable (P Q : PerfectMatching V) {v w : V} :
    (P.mate * Q.mate).SameCycle v w ↔
      (P.toGraph ⊔ Q.toGraph).Reachable v w ∧ ¬(P.mate * Q.mate).SameCycle v (P.mate w) := by
  rw [reachable_iff_sameCycle]
  constructor
  · intro h
    exact ⟨Or.inl h, fun h' ↦ not_sameCycle_mate_left P Q w (h.symm.trans h')⟩
  · rintro ⟨h | h, h'⟩
    · exact h
    · exact absurd h h'

/-- `Ham P Q` in terms of `g = P Q`: `V` is nonempty and every `w` or its `P`-partner lies in the
`g`-cycle of every `v`. -/
theorem ham_iff_forall_sameCycle (P Q : PerfectMatching V) :
    Ham P Q ↔ Nonempty V ∧ ∀ v w : V,
      (P.mate * Q.mate).SameCycle v w ∨ (P.mate * Q.mate).SameCycle v (P.mate w) := by
  rw [Ham, SimpleGraph.connected_iff, and_comm]
  exact and_congr_right fun _ ↦ forall₂_congr fun _ _ ↦ reachable_iff_sameCycle P Q

/-- The `g`-cycle of `P v` is the `P`-image of the `g`-cycle of `v`, so the two have the same
length, `g = P Q`. -/
theorem card_sameCycle_mate_left (P Q : PerfectMatching V) (v : V) :
    Nat.card {w // (P.mate * Q.mate).SameCycle (P.mate v) w} =
      Nat.card {w // (P.mate * Q.mate).SameCycle v w} := by
  refine Nat.card_congr (P.mate.subtypeEquiv fun w ↦ ?_)
  rw [← sameCycle_mate_left_iff P Q, mate_mate]

/-- A component of `P ∪ Q` with `2k` vertices is the disjoint union of the `g`-cycle of `v` and
the `g`-cycle of `P v`, `g = P Q`, so each has `k` vertices. -/
theorem card_reachable_eq_two_mul [Finite V] (P Q : PerfectMatching V) (v : V) :
    Nat.card {w // (P.toGraph ⊔ Q.toGraph).Reachable v w} =
      2 * Nat.card {w // (P.mate * Q.mate).SameCycle v w} := by
  classical
  have hdis : Disjoint (fun w ↦ (P.mate * Q.mate).SameCycle v w)
      (fun w ↦ (P.mate * Q.mate).SameCycle v (P.mate w)) := by
    rw [Pi.disjoint_iff]
    exact fun w ↦ Prop.disjoint_iff.mpr fun h ↦ not_sameCycle_mate_left P Q w (h.1.symm.trans h.2)
  have e : {w // (P.toGraph ⊔ Q.toGraph).Reachable v w} ≃
      {w // (P.mate * Q.mate).SameCycle v w} ⊕ {w // (P.mate * Q.mate).SameCycle v (P.mate w)} :=
    (Equiv.subtypeEquivRight fun w ↦ reachable_iff_sameCycle P Q).trans
      (subtypeOrEquiv _ _ hdis)
  have e' : {w // (P.mate * Q.mate).SameCycle v (P.mate w)} ≃
      {w // (P.mate * Q.mate).SameCycle v w} :=
    P.mate.subtypeEquiv fun _ ↦ Iff.rfl
  rw [Nat.card_congr e, Nat.card_sum, Nat.card_congr e', two_mul]

/-- `2 κ(P ∪ Q)` is the number of `SameCycle` classes of `P Q`. Each component of `P ∪ Q` holds
exactly two of them, the classes of `v` and of `P v`. -/
theorem two_mul_cycleCount_eq_card_quotient (P Q : PerfectMatching V) :
    2 * cycleCount P Q = Nat.card (Quotient (SameCycle.setoid (P.mate * Q.mate))) := by
  let f : (P.toGraph ⊔ Q.toGraph).ConnectedComponent × Bool →
      Quotient (SameCycle.setoid (P.mate * Q.mate)) := fun p ↦
    Quotient.mk _ (bif p.2 then Quot.out p.1 else P.mate (Quot.out p.1))
  have hout : ∀ c : (P.toGraph ⊔ Q.toGraph).ConnectedComponent,
      (P.toGraph ⊔ Q.toGraph).connectedComponentMk (Quot.out c) = c := Quot.out_eq
  have hc : ∀ c d : (P.toGraph ⊔ Q.toGraph).ConnectedComponent,
      (P.toGraph ⊔ Q.toGraph).Reachable (Quot.out c) (Quot.out d) → c = d := fun c d h ↦
    (hout c).symm.trans ((SimpleGraph.ConnectedComponent.eq.mpr h).trans (hout d))
  have hr : ∀ {x y : V}, (P.mate * Q.mate).SameCycle x y → (P.toGraph ⊔ Q.toGraph).Reachable x y :=
    fun h ↦ (reachable_iff_sameCycle P Q).mpr (Or.inl h)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨c, _ | _⟩ ⟨d, _ | _⟩ h
      · have h' : (P.mate * Q.mate).SameCycle (P.mate (Quot.out c)) (P.mate (Quot.out d)) :=
          Quotient.exact h
        rw [hc c d (hr ((sameCycle_mate_left_iff P Q).mp h'))]
      · have h' : (P.mate * Q.mate).SameCycle (P.mate (Quot.out c)) (Quot.out d) :=
          Quotient.exact h
        obtain rfl := hc c d ((reachable_mate_left P Q _).trans (hr h'))
        exact absurd h'.symm (not_sameCycle_mate_left P Q _)
      · have h' : (P.mate * Q.mate).SameCycle (Quot.out c) (P.mate (Quot.out d)) :=
          Quotient.exact h
        obtain rfl := hc c d ((hr h').trans (reachable_mate_left P Q _).symm)
        exact absurd h' (not_sameCycle_mate_left P Q _)
      · have h' : (P.mate * Q.mate).SameCycle (Quot.out c) (Quot.out d) := Quotient.exact h
        rw [hc c d (hr h')]
    · intro q
      induction q using Quotient.inductionOn with
      | h x =>
        have hx : (P.toGraph ⊔ Q.toGraph).Reachable
            (Quot.out ((P.toGraph ⊔ Q.toGraph).connectedComponentMk x)) x :=
          SimpleGraph.ConnectedComponent.eq.mp (hout _)
        rcases (reachable_iff_sameCycle P Q).mp hx with h | h
        · exact ⟨((P.toGraph ⊔ Q.toGraph).connectedComponentMk x, true), Quotient.sound h⟩
        · refine ⟨((P.toGraph ⊔ Q.toGraph).connectedComponentMk x, false), Quotient.sound ?_⟩
          rw [← sameCycle_mate_left_iff, mate_mate] at h
          exact h
  rw [cycleCount, ← Nat.card_eq_of_bijective f hf, Nat.card_prod,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm]

/-- `κ(P ∪ Q)` is half the number of cycles of `P Q`, fixed points counted as `1`-cycles. -/
theorem two_mul_cycleCount [Fintype V] [DecidableEq V] (P Q : PerfectMatching V) :
    2 * cycleCount P Q = (P.mate * Q.mate).partition.parts.card := by
  rw [two_mul_cycleCount_eq_card_quotient, card_quotient_sameCycle]

/-- For `|V| = 2n`, `P ∪ Q` is one cycle iff `P Q` has exactly two cycles, each of length `n`,
fixed points counted as `1`-cycles. No case split is needed: for `n = 0` both sides fail, and for
`n = 1` the product is `1`, with partition `{1, 1}`. -/
theorem ham_iff_partition [Fintype V] [DecidableEq V] {n : ℕ} (hV : Fintype.card V = 2 * n)
    (P Q : PerfectMatching V) : Ham P Q ↔ (P.mate * Q.mate).partition.parts = {n, n} := by
  constructor
  · intro hham
    have hcard : (P.mate * Q.mate).partition.parts.card = 2 := by
      rw [← two_mul_cycleCount, (ham_iff_cycleCount_eq_one P Q).mp hham]
    have hall : ∀ c ∈ (P.mate * Q.mate).partition.parts, c = n := by
      intro c hc
      obtain ⟨x, rfl⟩ := exists_card_sameCycle_of_mem_parts _ hc
      have h2 : Nat.card {w // (P.toGraph ⊔ Q.toGraph).Reachable x w} = 2 * n := by
        rw [← hV, ← Nat.card_eq_fintype_card]
        exact Nat.card_congr (Equiv.subtypeUnivEquiv fun w ↦ hham.preconnected x w)
      rw [card_reachable_eq_two_mul] at h2
      omega
    exact Multiset.eq_replicate.mpr ⟨hcard, hall⟩
  · intro h
    have h2 : 2 * cycleCount P Q = 2 := by
      rw [two_mul_cycleCount, h]
      rfl
    exact (ham_iff_cycleCount_eq_one P Q).mpr (by omega)

/-- For `|V| = 2n` with `2 ≤ n`, `P ∪ Q` is one cycle iff `P Q` has cycle type `{n, n}`. -/
theorem ham_iff_cycleType [Fintype V] [DecidableEq V] {n : ℕ} (hV : Fintype.card V = 2 * n)
    (hn : 2 ≤ n) (P Q : PerfectMatching V) : Ham P Q ↔ (P.mate * Q.mate).cycleType = {n, n} := by
  rw [ham_iff_partition hV]
  constructor
  · intro h
    rw [← filter_parts_partition_eq_cycleType, h]
    exact Multiset.filter_eq_self.mpr fun a ha ↦ by
      rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, or_self] at ha
      omega
  · intro h
    have hs : #(P.mate * Q.mate).support = Fintype.card V := by
      rw [← sum_cycleType, h, hV]
      simp [two_mul]
    rw [parts_partition, h, hs, Nat.sub_self, Multiset.replicate_zero, add_zero]

/-- Relabelling both matchings by `σ` conjugates their product by `σ`. -/
theorem smul_mate_mul_smul_mate (σ : Perm V) (P Q : PerfectMatching V) :
    (σ • P).mate * (σ • Q).mate = σ * (P.mate * Q.mate) * σ⁻¹ := by
  ext v
  simp

/-- The cycle type of `P Q` is invariant under relabelling. -/
theorem cycleType_smul_mate_mul_smul_mate [Fintype V] [DecidableEq V] (σ : Perm V)
    (P Q : PerfectMatching V) :
    ((σ • P).mate * (σ • Q).mate).cycleType = (P.mate * Q.mate).cycleType := by
  rw [smul_mate_mul_smul_mate, cycleType_conj]

/-- The partition of `P Q`, fixed points included, is invariant under relabelling. -/
theorem partition_smul_mate_mul_smul_mate [Fintype V] [DecidableEq V] (σ : Perm V)
    (P Q : PerfectMatching V) :
    ((σ • P).mate * (σ • Q).mate).partition = (P.mate * Q.mate).partition := by
  rw [smul_mate_mul_smul_mate]
  exact (partition_eq_of_isConj.mp (isConj_iff.mpr ⟨σ, rfl⟩)).symm

/-- `κ(σ P ∪ σ Q) = κ(P ∪ Q)`, on any `V`. Relabelling is an isomorphism of union graphs, and
on a finite `V` this is also `two_mul_cycleCount` with `partition_smul_mate_mul_smul_mate`. -/
theorem cycleCount_smul (σ : Perm V) (P Q : PerfectMatching V) :
    cycleCount (σ • P) (σ • Q) = cycleCount P Q :=
  (Nat.card_congr (unionIso σ P Q).connectedComponentEquiv).symm

/-- Transport along `e : V ≃ V'` carries the product `P Q` to its `e`-conjugate. -/
theorem congr_mate_mul_congr_mate {V' : Type*} (e : V ≃ V') (P Q : PerfectMatching V) :
    (congr e P).mate * (congr e Q).mate = e.permCongr (P.mate * Q.mate) := by
  ext v
  simp

end PerfectMatching

end Pairing
