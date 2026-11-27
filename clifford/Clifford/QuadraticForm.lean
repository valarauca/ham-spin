import Clifford.PolarSection
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The Hamiltonian-pair quadratic form (COD-293)

Fix vertices `v, x, y`, put `e = vx`, `f = vy`, `A = 1 + Γ_e` and `B = 1 + Γ_f` on the CKN
module `W V` (`Γ`, `fpForm`, ham-spin e88ff2d), and `Q(u) = ⟨ABu, BAu⟩`. This is the elementary
construction of `results/parity-apps-contra.md` §1 (organize-archive d6e5620), verified in
`results/parity-apps-factcheck-contra.md` (d6e5620). It gives Theorem A and Corollary B of
`results/outside-applications-extend.md` §§1–2 and Theorem Q of `results/p1f-spin-extend.md` §1.2
(d6e5620), without the presentation `ker Θ = R_3`.

* `quadT v x y = AB` and `quadS v x y = BA`. `fpForm_Γ_left` : `Γ_e` is self-adjoint, so
  `fpForm_quadT_left` and `fpForm_quadS_left` : `AB` and `BA` are adjoint to each other.
  `quadT_add_quadS` : `AB + BA = 1`, from `Γ_anticomm_of_adj`. `quadT_mul_quadS` and
  `quadS_mul_quadT` : `AB · BA = BA · AB = 0`, from `A² = B² = 0` (`one_add_Γ_mul_self`).
* `hamQuad v x y = Q`. (i) `polar_hamQuad`, `polarBilin_hamQuad` : the polar form of `Q` is
  `fpForm` for distinct `v, x, y`, and `hamQuad_add` is the polarization identity.
* (ii) `hamQuad_rowW` : `Q(φ(P)) = 0` once `|V| ≥ 7`. Some edge `ab` of `P` misses `v, x, y`. Then
  `ABφ(P)` and `BAφ(P)` lie in the span of the fingerprints of the matchings through `ab`, and two
  such matchings share an edge, so they are never Hamiltonian. This replaces the four-case check
  of the contra §1 Theorem 1.2, and needs no distinctness of `v, x, y`.
* `quadraticForm_eq_of_polarBilin` : a quadratic form with polar form `fpForm` that vanishes on
  every `φ(P)` is unique, since the `φ(P)` span (`span_rowW`). `existsUnique_quadraticForm` : for
  `|V| = 2m`, `m ≥ 4`, it exists. `hamQuad_eq` : `Q` does not depend on `(v, x, y)`.
* (iii) `quadraticForm_sum_rowW`, `hamQuad_sum_rowW` : for every finite family,
  `Q(Σ_{i ∈ s} φ(F_i)) = #{i < j : F_i ∪ F_j one cycle}` mod 2.
* Corollary B. `coe_sum_rowW_apply` : `Σ_i φ(F_i)` evaluated at `P` is `X(P) = #{i | Ham P F_i}`
  mod 2. `sum_rowW_ne_zero_of_odd` and `exists_odd_ham_of_odd` : an odd number of Hamiltonian
  pairs forces `Σ_i φ(F_i) ≠ 0` and some `P` with `X(P)` odd. `even_hamPairs_of_sum_rowW_eq_zero` :
  every relation `Σ_{i ∈ s} φ(F_i) = 0` has an even number of Hamiltonian pairs.
-/

namespace Pairing.PerfectMatching

open Equiv Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

section Operators

/-- `Γ_{ij}` is self-adjoint for the fingerprint pairing, being an isometric involution
(`fpForm_ρW`, `Γ_mul_self`, ham-spin e88ff2d). -/
theorem fpForm_Γ_left (i j : V) (f g : W V) : fpForm (Γ i j f) g = fpForm f (Γ i j g) := by
  have h : Γ i j (Γ i j f) = f := by
    rw [← Module.End.mul_apply, Γ_mul_self, Module.End.one_apply]
  rw [← fpForm_ρW (swap i j) (Γ i j f) g]
  change fpForm (Γ i j (Γ i j f)) (Γ i j g) = _
  rw [h]

/-- `(1 + Γ_{ij})² = 0` over `𝔽₂` (`Γ_mul_self`, ham-spin e88ff2d). -/
theorem one_add_Γ_mul_self (i j : V) : (1 + Γ i j) * (1 + Γ i j) = 0 := by
  have h : (1 + Γ i j) * (1 + Γ i j) = (1 + 1) + (Γ i j + Γ i j) := by
    simp only [add_mul, mul_add, one_mul, mul_one, Γ_mul_self]
    abel
  rw [h, end_add_self, end_add_self, add_zero]

/-- `1 + Γ_{ij}` is self-adjoint for the fingerprint pairing (`fpForm`, ham-spin e88ff2d). -/
theorem fpForm_one_add_Γ_left (i j : V) (f g : W V) :
    fpForm ((1 + Γ i j) f) g = fpForm f ((1 + Γ i j) g) := by
  simp only [LinearMap.add_apply, Module.End.one_apply, map_add, fpForm_Γ_left]

/-- `AB = (1 + Γ_{vx})(1 + Γ_{vy})`, the first factor of the quadratic form `hamQuad`
(`results/parity-apps-contra.md` §1, organize-archive d6e5620). -/
def quadT (v x y : V) : Module.End F₂ (W V) :=
  (1 + Γ v x) * (1 + Γ v y)

/-- `BA = (1 + Γ_{vy})(1 + Γ_{vx})`, the second factor of the quadratic form `hamQuad`
(`results/parity-apps-contra.md` §1, organize-archive d6e5620). -/
def quadS (v x y : V) : Module.End F₂ (W V) :=
  (1 + Γ v y) * (1 + Γ v x)

/-- `⟨ABf, g⟩ = ⟨f, BAg⟩` for the fingerprint pairing (`fpForm`, ham-spin e88ff2d). -/
theorem fpForm_quadT_left (v x y : V) (f g : W V) :
    fpForm (quadT v x y f) g = fpForm f (quadS v x y g) := by
  rw [quadT, quadS, Module.End.mul_apply, Module.End.mul_apply, fpForm_one_add_Γ_left,
    fpForm_one_add_Γ_left]

/-- `⟨BAf, g⟩ = ⟨f, ABg⟩` for the fingerprint pairing (`fpForm`, ham-spin e88ff2d). -/
theorem fpForm_quadS_left (v x y : V) (f g : W V) :
    fpForm (quadS v x y f) g = fpForm f (quadT v x y g) := by
  rw [quadT, quadS, Module.End.mul_apply, Module.End.mul_apply, fpForm_one_add_Γ_left,
    fpForm_one_add_Γ_left]

/-- `AB · BA = 0`, since `B² = 0`. -/
theorem quadT_mul_quadS (v x y : V) : quadT v x y * quadS v x y = 0 := by
  rw [quadT, quadS, mul_assoc, ← mul_assoc (1 + Γ v y), one_add_Γ_mul_self, zero_mul, mul_zero]

/-- `BA · AB = 0`, since `A² = 0`. -/
theorem quadS_mul_quadT (v x y : V) : quadS v x y * quadT v x y = 0 := by
  rw [quadT, quadS, mul_assoc, ← mul_assoc (1 + Γ v x), one_add_Γ_mul_self, zero_mul, mul_zero]

/-- `AB + BA = Γ_eΓ_f + Γ_fΓ_e = 1` for the adjacent edges `e = vx`, `f = vy`
(`Γ_anticomm_of_adj`, ham-spin e88ff2d). -/
theorem quadT_add_quadS {v x y : V} (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y) :
    quadT v x y + quadS v x y = 1 := by
  have h := Γ_anticomm_of_adj hvx.symm hvy hxy
  rw [Γ_comm x v] at h
  have e : quadT v x y + quadS v x y =
      (Γ v x * Γ v y + Γ v y * Γ v x) + ((1 + 1) + (Γ v x + Γ v x) + (Γ v y + Γ v y)) := by
    simp only [quadT, quadS, add_mul, mul_add, one_mul, mul_one]
    abel
  rw [e, h]
  simp only [end_add_self, add_zero]

end Operators

section Form

/-- The Hamiltonian-pair quadratic form `Q(u) = ⟨ABu, BAu⟩` with `A = 1 + Γ_{vx}`,
`B = 1 + Γ_{vy}` on the CKN module `W V` (`fpForm`, `Γ`, ham-spin e88ff2d). This is the form of
`results/parity-apps-contra.md` §1 (organize-archive d6e5620), and Theorem A of
`results/outside-applications-extend.md` §1 (d6e5620). -/
noncomputable def hamQuad (v x y : V) : QuadraticForm F₂ (W V) :=
  LinearMap.BilinMap.toQuadraticMap (fpForm.compl₁₂ (quadT v x y) (quadS v x y))

/-- `Q(u) = ⟨ABu, BAu⟩`. -/
theorem hamQuad_apply (v x y : V) (u : W V) :
    hamQuad v x y u = fpForm (quadT v x y u) (quadS v x y u) :=
  rfl

/-- (i) The polar form of `Q` is the fingerprint pairing `fpForm` (ham-spin e88ff2d), for
distinct `v, x, y` (`results/parity-apps-contra.md` Lemma 1.1, organize-archive d6e5620). -/
theorem polar_hamQuad {v x y : V} (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y) (f g : W V) :
    QuadraticMap.polar (hamQuad v x y) f g = fpForm f g := by
  have hTS := quadT_add_quadS hvx hvy hxy
  have hf : quadT v x y f + quadS v x y f = f := by
    rw [← LinearMap.add_apply, hTS, Module.End.one_apply]
  have hg : quadT v x y g + quadS v x y g = g := by
    rw [← LinearMap.add_apply, hTS, Module.End.one_apply]
  have h1 : fpForm (quadT v x y f) (quadT v x y g) = 0 := by
    rw [fpForm_quadT_left, ← Module.End.mul_apply, quadS_mul_quadT, LinearMap.zero_apply,
      map_zero]
  have h2 : fpForm (quadS v x y f) (quadS v x y g) = 0 := by
    rw [fpForm_quadS_left, ← Module.End.mul_apply, quadT_mul_quadS, LinearMap.zero_apply,
      map_zero]
  rw [hamQuad, LinearMap.BilinMap.polar_toQuadraticMap, LinearMap.compl₁₂_apply,
    LinearMap.compl₁₂_apply]
  conv_rhs => rw [← hf, ← hg]
  simp only [map_add, LinearMap.add_apply]
  rw [h1, h2, fpForm_comm (quadS v x y f)]
  ring

/-- (i) `polarBilin Q = fpForm` (ham-spin e88ff2d), for distinct `v, x, y`. -/
theorem polarBilin_hamQuad {v x y : V} (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y) :
    QuadraticMap.polarBilin (hamQuad v x y) = fpForm :=
  LinearMap.ext₂ fun f g ↦ by
    rw [QuadraticMap.polarBilin_apply_apply, polar_hamQuad hvx hvy hxy]

/-- A quadratic form on `W V` whose polar form is `fpForm` (ham-spin e88ff2d) satisfies
`Q(f + g) = Q(f) + Q(g) + ⟨f, g⟩`. -/
theorem quadraticForm_add_of_polarBilin {Q : QuadraticForm F₂ (W V)}
    (hQ : QuadraticMap.polarBilin Q = fpForm) (f g : W V) :
    Q (f + g) = Q f + Q g + fpForm f g := by
  rw [← hQ, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  ring

/-- The polarization identity `Q(f + g) = Q(f) + Q(g) + ⟨f, g⟩` for `hamQuad`, with distinct
`v, x, y` (`fpForm`, ham-spin e88ff2d). -/
theorem hamQuad_add {v x y : V} (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y) (f g : W V) :
    hamQuad v x y (f + g) = hamQuad v x y f + hamQuad v x y g + fpForm f g :=
  quadraticForm_add_of_polarBilin (polarBilin_hamQuad hvx hvy hxy) f g

end Form

section Vanishing

/-- The span of the fingerprints of the matchings that contain the edge `ab`. -/
private def edgeRowSpan (a b : V) : Submodule F₂ (W V) :=
  Submodule.span F₂ (rowW '' {Q | Q.mate a = b})

/-- Two matchings through `ab` are never Hamiltonian, so `edgeRowSpan a b` is totally isotropic. -/
private theorem fpForm_eq_zero_of_mem_edgeRowSpan {a b : V} (hV : 2 < Fintype.card V)
    {f g : W V} (hf : f ∈ edgeRowSpan a b) (hg : g ∈ edgeRowSpan a b) : fpForm f g = 0 := by
  have hrow : ∀ Q : PerfectMatching V, Q.mate a = b → fpForm (rowW Q) g = 0 := by
    intro Q hQ
    have hle : edgeRowSpan a b ≤ LinearMap.ker (fpForm (rowW Q)) := by
      rw [edgeRowSpan, Submodule.span_le]
      rintro _ ⟨Q', hQ' : Q'.mate a = b, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, fpForm_rowW, H_apply,
        ite_eq_right (not_ham_of_mate_eq_of_two_lt hV (hQ.trans hQ'.symm))]
    exact LinearMap.mem_ker.mp (hle hg)
  have hle : edgeRowSpan a b ≤ LinearMap.ker (fpForm g) := by
    rw [edgeRowSpan, Submodule.span_le]
    rintro _ ⟨Q, hQ : Q.mate a = b, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, fpForm_comm]
    exact hrow Q hQ
  rw [fpForm_comm]
  exact LinearMap.mem_ker.mp (hle hf)

/-- `Γ_{ij}` preserves `edgeRowSpan a b` when `i, j ∉ {a, b}`. -/
private theorem Γ_mem_edgeRowSpan {a b i j : V} (hai : a ≠ i) (haj : a ≠ j) (hbi : b ≠ i)
    (hbj : b ≠ j) {f : W V} (hf : f ∈ edgeRowSpan a b) : Γ i j f ∈ edgeRowSpan a b := by
  have hle : edgeRowSpan a b ≤ (edgeRowSpan a b).comap (Γ i j) := by
    rw [edgeRowSpan, Submodule.span_le]
    rintro _ ⟨Q, hQ : Q.mate a = b, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    refine Submodule.subset_span ⟨swap i j • Q, ?_, (ρW_rowW (swap i j) Q).symm⟩
    change (swap i j • Q).mate a = b
    rw [smul_mate, swap_inv, swap_apply_of_ne_of_ne hai haj, hQ, swap_apply_of_ne_of_ne hbi hbj]
  exact hle hf

/-- `1 + Γ_{ij}` preserves `edgeRowSpan a b` when `i, j ∉ {a, b}`. -/
private theorem one_add_Γ_mem_edgeRowSpan {a b i j : V} (hai : a ≠ i) (haj : a ≠ j)
    (hbi : b ≠ i) (hbj : b ≠ j) {f : W V} (hf : f ∈ edgeRowSpan a b) :
    (1 + Γ i j) f ∈ edgeRowSpan a b := by
  rw [LinearMap.add_apply, Module.End.one_apply]
  exact add_mem hf (Γ_mem_edgeRowSpan hai haj hbi hbj hf)

omit [DecidableEq V] in
/-- On at least `7` vertices, every matching has an edge that misses three given vertices. -/
private theorem exists_edge_avoiding (hV : 6 < Fintype.card V) (P : PerfectMatching V)
    (v x y : V) :
    ∃ a, a ≠ v ∧ a ≠ x ∧ a ≠ y ∧ P.mate a ≠ v ∧ P.mate a ≠ x ∧ P.mate a ≠ y := by
  classical
  have hcard : ({v, x, y, P.mate v, P.mate x, P.mate y} : Finset V).card <
      (Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    exact lt_of_le_of_lt Finset.card_le_six hV
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ha
  refine ⟨a, h1, h2, h3, fun h ↦ h4 ?_, fun h ↦ h5 ?_, fun h ↦ h6 ?_⟩ <;> rw [← h, mate_mate]

/-- (ii) `Q(φ(P)) = 0` for every perfect matching `P` once `|V| ≥ 7`, for any `v, x, y`
(`hamQuad`; `results/parity-apps-contra.md` Theorem 1.2, organize-archive d6e5620). An edge `ab`
of `P` misses `v, x, y`, so `ABφ(P)` and `BAφ(P)` are sums of fingerprints of matchings through
`ab`, and no two of those are Hamiltonian. -/
theorem hamQuad_rowW (hV : 6 < Fintype.card V) (v x y : V) (P : PerfectMatching V) :
    hamQuad v x y (rowW P) = 0 := by
  obtain ⟨a, hav, hax, hay, hbv, hbx, hby⟩ := exists_edge_avoiding hV P v x y
  have hP : rowW P ∈ edgeRowSpan a (P.mate a) := Submodule.subset_span ⟨P, rfl, rfl⟩
  have hA : ∀ {f : W V}, f ∈ edgeRowSpan a (P.mate a) →
      (1 + Γ v x) f ∈ edgeRowSpan a (P.mate a) :=
    one_add_Γ_mem_edgeRowSpan hav hax hbv hbx
  have hB : ∀ {f : W V}, f ∈ edgeRowSpan a (P.mate a) →
      (1 + Γ v y) f ∈ edgeRowSpan a (P.mate a) :=
    one_add_Γ_mem_edgeRowSpan hav hay hbv hby
  rw [hamQuad_apply, quadT, quadS, Module.End.mul_apply, Module.End.mul_apply]
  exact fpForm_eq_zero_of_mem_edgeRowSpan (by omega) (hA (hB hP)) (hB (hA hP))

end Vanishing

section Unique

/-- Uniqueness in Theorem A part 1 of `results/outside-applications-extend.md` (organize-archive
d6e5620). Two quadratic forms on `W V` with polar form `fpForm` that vanish on every fingerprint
`φ(P)` agree, because the `φ(P)` span `W V` (`span_rowW`, ham-spin e88ff2d). -/
theorem quadraticForm_eq_of_polarBilin {Q₁ Q₂ : QuadraticForm F₂ (W V)}
    (h₁ : QuadraticMap.polarBilin Q₁ = fpForm) (h₂ : QuadraticMap.polarBilin Q₂ = fpForm)
    (z₁ : ∀ P, Q₁ (rowW P) = 0) (z₂ : ∀ P, Q₂ (rowW P) = 0) : Q₁ = Q₂ := by
  ext u
  have hu : u ∈ Submodule.span F₂ (Set.range (rowW (V := V))) := by
    rw [span_rowW]
    exact Submodule.mem_top
  induction hu using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨P, rfl⟩ := hf
    rw [z₁, z₂]
  | zero => rw [QuadraticMap.map_zero, QuadraticMap.map_zero]
  | add f g _ _ hf hg =>
    rw [quadraticForm_add_of_polarBilin h₁, quadraticForm_add_of_polarBilin h₂, hf, hg]
  | smul c f _ hf => rw [QuadraticMap.map_smul, QuadraticMap.map_smul, hf]

omit [DecidableEq V] in
/-- Three distinct vertices exist once `|V| ≥ 3`. -/
private theorem exists_three_ne (hV : 2 < Fintype.card V) :
    ∃ v x y : V, v ≠ x ∧ v ≠ y ∧ x ≠ y := by
  obtain ⟨e⟩ : Nonempty (Fin 3 ↪ V) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin]; omega)
  exact ⟨e 0, e 1, e 2, e.injective.ne (by decide), e.injective.ne (by decide),
    e.injective.ne (by decide)⟩

/-- Theorem A part 1 of `results/outside-applications-extend.md` and Lemma Q of
`results/p1f-spin-extend.md` (organize-archive d6e5620). For `|V| = 2m` with `m ≥ 4` there is
exactly one quadratic form on `W V` with polar form `fpForm` (ham-spin e88ff2d) that vanishes on
every fingerprint `φ(P)`. It is `hamQuad v x y` for any distinct `v, x, y`. -/
theorem existsUnique_quadraticForm {m : ℕ} (hV : Fintype.card V = 2 * m) (hm : 4 ≤ m) :
    ∃! Q : QuadraticForm F₂ (W V),
      QuadraticMap.polarBilin Q = fpForm ∧ ∀ P, Q (rowW P) = 0 := by
  obtain ⟨v, x, y, hvx, hvy, hxy⟩ := exists_three_ne (V := V) (by omega)
  refine ⟨hamQuad v x y, ⟨polarBilin_hamQuad hvx hvy hxy, hamQuad_rowW (by omega) v x y⟩, ?_⟩
  rintro Q ⟨hQ, hQ0⟩
  exact quadraticForm_eq_of_polarBilin hQ (polarBilin_hamQuad hvx hvy hxy) hQ0
    (hamQuad_rowW (by omega) v x y)

/-- `Q` does not depend on the choice of the two adjacent edges `vx`, `vy`, once `|V| ≥ 7`
(`hamQuad`, `quadraticForm_eq_of_polarBilin`). -/
theorem hamQuad_eq (hV : 6 < Fintype.card V) {v x y v' x' y' : V} (hvx : v ≠ x) (hvy : v ≠ y)
    (hxy : x ≠ y) (hvx' : v' ≠ x') (hvy' : v' ≠ y') (hxy' : x' ≠ y') :
    hamQuad v x y = hamQuad v' x' y' :=
  quadraticForm_eq_of_polarBilin (polarBilin_hamQuad hvx hvy hxy)
    (polarBilin_hamQuad hvx' hvy' hxy') (hamQuad_rowW hV v x y) (hamQuad_rowW hV v' x' y')

end Unique

section Parity

variable {ι : Type*}

/-- `Q(Σ_{i ∈ s} f_i) = Σ_i Q(f_i) + Σ_{i < j} ⟨f_i, f_j⟩` for a quadratic form with polar form
`fpForm` (ham-spin e88ff2d). -/
private theorem quadraticForm_sum_lt [LinearOrder ι] {Q : QuadraticForm F₂ (W V)}
    (hQ : QuadraticMap.polarBilin Q = fpForm) (s : Finset ι) (f : ι → W V) :
    Q (∑ i ∈ s, f i) =
      ∑ i ∈ s, Q (f i) + ∑ i ∈ s, ∑ j ∈ s, if i < j then fpForm (f i) (f j) else 0 := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h ↦ lt_irrefl a (ha a h)
    have h1 : ∑ j ∈ insert a s, (if a < j then fpForm (f a) (f j) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj ↦ ite_eq_right ?_
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact lt_irrefl _
      · exact not_lt.mpr (ha j hj).le
    have h2 : ∀ i ∈ s, ∑ j ∈ insert a s, (if i < j then fpForm (f i) (f j) else 0) =
        fpForm (f a) (f i) + ∑ j ∈ s, (if i < j then fpForm (f i) (f j) else 0) := by
      intro i hi
      rw [Finset.sum_insert has, ite_eq_left (ha i hi), fpForm_comm]
    have h3 : fpForm (f a) (∑ i ∈ s, f i) = ∑ i ∈ s, fpForm (f a) (f i) := map_sum _ _ _
    rw [Finset.sum_insert has, Finset.sum_insert has, Finset.sum_insert has, h1,
      Finset.sum_congr rfl h2, Finset.sum_add_distrib, quadraticForm_add_of_polarBilin hQ, ih, h3]
    ring

/-- (iii) for any quadratic form with polar form `fpForm` vanishing on fingerprints
(`rowW`, `Ham`, ham-spin e88ff2d). For every finite family,
`Q(Σ_{i ∈ s} φ(F_i)) = #{i < j : F_i ∪ F_j one cycle}` mod 2 (`results/p1f-spin-extend.md`
Theorem Q, organize-archive d6e5620). -/
theorem quadraticForm_sum_rowW [LinearOrder ι] {Q : QuadraticForm F₂ (W V)}
    (hQ : QuadraticMap.polarBilin Q = fpForm) (hQ0 : ∀ P, Q (rowW P) = 0) (s : Finset ι)
    (F : ι → PerfectMatching V) :
    Q (∑ i ∈ s, rowW (F i)) = (#{p ∈ s ×ˢ s | p.1 < p.2 ∧ Ham (F p.1) (F p.2)} : F₂) := by
  rw [quadraticForm_sum_lt hQ, Finset.sum_eq_zero fun i _ ↦ hQ0 (F i), zero_add,
    Finset.natCast_card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [fpForm_rowW, H_apply]
  by_cases hij : i < j <;> by_cases hh : Ham (F i) (F j) <;> simp [hij, hh]

/-- (iii) for `hamQuad` (`results/outside-applications-extend.md` Theorem A part 1 and
`results/p1f-spin-extend.md` Theorem Q, organize-archive d6e5620). For distinct `v, x, y` on
`|V| ≥ 7` vertices and every finite family `F`,
`Q(Σ_{i ∈ s} φ(F_i)) = #{i < j : F_i ∪ F_j one cycle}` mod 2 (`rowW`, `Ham`, ham-spin e88ff2d). -/
theorem hamQuad_sum_rowW [LinearOrder ι] (hV : 6 < Fintype.card V) {v x y : V} (hvx : v ≠ x)
    (hvy : v ≠ y) (hxy : x ≠ y) (s : Finset ι) (F : ι → PerfectMatching V) :
    hamQuad v x y (∑ i ∈ s, rowW (F i)) =
      (#{p ∈ s ×ˢ s | p.1 < p.2 ∧ Ham (F p.1) (F p.2)} : F₂) :=
  quadraticForm_sum_rowW (polarBilin_hamQuad hvx hvy hxy) (hamQuad_rowW hV v x y) s F

/-- `Σ_{i ∈ s} φ(F_i)` evaluated at `P` is `X(P) = #{i ∈ s | P ∪ F_i one cycle}` mod 2, that is
`⟨Σ_i φ(F_i), φ(P)⟩` (`rowW`, `Ham`, `fpForm_rowW_right`, ham-spin e88ff2d). -/
theorem coe_sum_rowW_apply (s : Finset ι) (F : ι → PerfectMatching V) (P : PerfectMatching V) :
    ((∑ i ∈ s, rowW (F i) : W V) : PerfectMatching V → F₂) P = (#{i ∈ s | Ham P (F i)} : F₂) := by
  rw [Submodule.coe_sum, Finset.sum_apply]
  simp_rw [coe_rowW, H_apply, ham_comm (F _) P]
  rw [Finset.sum_boole]

/-- Corollary B.1 of `results/outside-applications-extend.md` (organize-archive d6e5620), first
half. For `|V| = 2m` with `m ≥ 4`, a family with an odd number of Hamiltonian pairs has
`Σ_{i ∈ s} φ(F_i) ≠ 0` (`rowW`, `Ham`, ham-spin e88ff2d). -/
theorem sum_rowW_ne_zero_of_odd [LinearOrder ι] {m : ℕ} (hV : Fintype.card V = 2 * m)
    (hm : 4 ≤ m) (s : Finset ι) (F : ι → PerfectMatching V)
    (hodd : Odd #{p ∈ s ×ˢ s | p.1 < p.2 ∧ Ham (F p.1) (F p.2)}) :
    ∑ i ∈ s, rowW (F i) ≠ 0 := by
  obtain ⟨Q, ⟨hQ, hQ0⟩, -⟩ := existsUnique_quadraticForm hV hm
  intro h
  have hq := quadraticForm_sum_rowW hQ hQ0 s F
  rw [h, QuadraticMap.map_zero, eq_comm, ZMod.natCast_eq_zero_iff_even] at hq
  exact Nat.not_even_iff_odd.mpr hodd hq

/-- Corollary B.1 of `results/outside-applications-extend.md` (organize-archive d6e5620). For
`|V| = 2m` with `m ≥ 4`, if a family has an odd number of Hamiltonian pairs, some perfect matching
`P` closes one cycle with an odd number of its members. This is the nondegeneracy of `fpForm`
(`fpForm_nondegenerate`, ham-spin e88ff2d) read through `coe_sum_rowW_apply`. -/
theorem exists_odd_ham_of_odd [LinearOrder ι] {m : ℕ} (hV : Fintype.card V = 2 * m) (hm : 4 ≤ m)
    (s : Finset ι) (F : ι → PerfectMatching V)
    (hodd : Odd #{p ∈ s ×ˢ s | p.1 < p.2 ∧ Ham (F p.1) (F p.2)}) :
    ∃ P : PerfectMatching V, Odd #{i ∈ s | Ham P (F i)} := by
  by_contra hcon
  apply sum_rowW_ne_zero_of_odd hV hm s F hodd
  refine Subtype.ext (funext fun P ↦ ?_)
  rw [coe_sum_rowW_apply, Submodule.coe_zero, Pi.zero_apply, ZMod.natCast_eq_zero_iff_even]
  exact Nat.not_odd_iff_even.mp fun h ↦ hcon ⟨P, h⟩

/-- Corollary B.3 of `results/outside-applications-extend.md` (organize-archive d6e5620). For
`|V| = 2m` with `m ≥ 4`, every relation `Σ_{i ∈ s} φ(F_i) = 0` has an even number of Hamiltonian
pairs (`rowW`, `Ham`, ham-spin e88ff2d). A set `S` of matchings is the case `F = id` under any
linear order. -/
theorem even_hamPairs_of_sum_rowW_eq_zero [LinearOrder ι] {m : ℕ} (hV : Fintype.card V = 2 * m)
    (hm : 4 ≤ m) (s : Finset ι) (F : ι → PerfectMatching V) (h : ∑ i ∈ s, rowW (F i) = 0) :
    Even #{p ∈ s ×ˢ s | p.1 < p.2 ∧ Ham (F p.1) (F p.2)} := by
  by_contra hcon
  exact sum_rowW_ne_zero_of_odd hV hm s F (Nat.not_even_iff_odd.mp hcon) h

end Parity

end Pairing.PerfectMatching
