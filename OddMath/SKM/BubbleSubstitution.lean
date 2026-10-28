/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleCoefficientBasis
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Triangular substitutions of the coefficient algebra

Research issue #345, vacuum evaluation of the swapped detecting action
(`docs/Nondegeneracy/SwappedNondegeneracy.md`, §4). The normalized bubbles
of the vacuum act on the coefficient algebra of Brundan–Ellis (1.21)–(1.22)
through a triangular substitution: the generating series
`G_i(z) = 1 + Σ_n e_(i,n) z^(n+1)` of colour `i` goes to `G_i(-z) u_i(z)`, where
`u_i` is a power series with constant term one, and the odd generator `δ_i`
is multiplied by a unit scalar.

## Main declarations

* `SYM.polynomialSubstitution`: the substitution on the polynomial factor.
* `SYM.substitutionHom`, `SYM.substitutionEquiv`: the substitution and its
  inverse, given by the series `u_i(-z)⁻¹` and the inverse scalars.
* `SYM.preservesWeight_of_generators`: an algebra endomorphism preserves the
  coefficient-weight filtration as soon as its generator images do.
* `SYM.substitutionHom_mem_coefficientAtMost`: every triangular substitution
  preserves the weight filtration.
* `SYM.probeSubstitution`: the substitution of the vacuum evaluation,
  `C_i(z) ↦ C_i(-z)(1+z)^(-M_i)`, `δ_i ↦ (-1)^(N_i+1) δ_i` at odd colours and
  `E_i(z) ↦ E_i(-z)(1-z)^(-M_i)` at even colours.
-/

noncomputable section
open scoped Classical TensorProduct
namespace OddMath.SKM.SYM
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
variable (D : Datum I X) (k : Type w) [CommRing k]

/-! ### The weight filtration is multiplicative -/

theorem coefficientBasis_mul_mem_low {a b : CoefficientIndex D} {m n : ℕ}
    (ha : coefficientWeight D a ≤ m) (hb : coefficientWeight D b ≤ n) :
    coefficientBasis D k a * coefficientBasis D k b ∈ CoefficientAtMost D k (m + n) := by
  by_cases hd : Disjoint a.2 b.2
  · obtain ⟨c, hc⟩ := coefficientBasis_mul_scalar D k hd
    rw [hc]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨(a.1 + b.1, a.2 ∪ b.2), ?_, rfl⟩
    change coefficientWeight D (a.1 + b.1, a.2 ∪ b.2) ≤ m + n
    rw [coefficientWeight_mul D hd]
    omega
  · rw [coefficientBasis_mul_zero D k hd]
    exact Submodule.zero_mem _

theorem coefficientAtMost_mul {m n : ℕ} {x y : SYM D k}
    (hx : x ∈ CoefficientAtMost D k m) (hy : y ∈ CoefficientAtMost D k n) :
    x * y ∈ CoefficientAtMost D k (m + n) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      exact coefficientBasis_mul_mem_low D k ha hb
    | zero => simp
    | add y z _ _ hy hz =>
      rw [mul_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c hy
  | zero => simp
  | add x z _ _ hx hz =>
    rw [add_mul]
    exact Submodule.add_mem _ hx hz
  | smul c x _ hx =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

theorem coefficientAtMost_mono {m n : ℕ} (h : m ≤ n) :
    CoefficientAtMost D k m ≤ CoefficientAtMost D k n :=
  Submodule.span_mono (Set.image_mono fun _ ha => le_trans ha h)

/-! ### Generators as basis vectors -/

theorem oddExteriorBasis_empty : oddExteriorBasis D k ∅ = 1 := by
  let : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  simp [oddExteriorBasis, ExteriorAlgebra.basis_apply, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply]

theorem oddExteriorBasis_singleton (i : {i : I // D.parity i = 1}) :
    oddExteriorBasis D k {i} = ExteriorAlgebra.ι k (Finsupp.single i 1) := by
  let : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  rw [oddExteriorBasis, ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton i),
    ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply]
  have hj : Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard (Finset.card_singleton i)) 0 = i := by
    have := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
      (Set.powersetCard.ofCard (Finset.card_singleton i))
      (Set.powersetCard.ofFinEmbEquiv.symm
        (Set.powersetCard.ofCard (Finset.card_singleton i)) 0)).mp ⟨0, rfl⟩
    exact Finset.mem_singleton.mp (Set.powersetCard.mem_coe_iff.mpr this)
  simp [List.ofFn_succ, hj]

theorem polynomialExteriorEquiv_symm_tmul (p : MvPolynomial (I × ℕ) k)
    (x : ExteriorAlgebra k (OddModule D k)) :
    (polynomialExteriorEquiv D k).symm (p ⊗ₜ[k] x) =
      polynomialInclude D k p * exteriorInclude D k x :=
  polynomialExteriorInclude_tmul D k p x

theorem coefficientBasis_eq_mul (a : CoefficientIndex D) :
    coefficientBasis D k a = polynomialInclude D k (MvPolynomial.monomial a.1 1) *
      exteriorInclude D k (oddExteriorBasis D k a.2) := by
  rw [← polynomialExteriorEquiv_symm_tmul, ← coefficientBasis_projection,
    AlgEquiv.symm_apply_apply]

theorem one_eq_coefficientBasis : (1 : SYM D k) = coefficientBasis D k (0, ∅) := by
  rw [coefficientBasis_eq_mul, oddExteriorBasis_empty]
  simp

theorem e_eq_coefficientBasis (i : I) (n : ℕ) :
    e D k i n = coefficientBasis D k (Finsupp.single (i, n) 1, ∅) := by
  rw [coefficientBasis_eq_mul, oddExteriorBasis_empty, ← MvPolynomial.X]
  simp

theorem delta_eq_coefficientBasis (i : {i : I // D.parity i = 1}) :
    delta D k i = coefficientBasis D k (0, {i}) := by
  rw [coefficientBasis_eq_mul, oddExteriorBasis_singleton]
  simp

theorem one_mem_coefficientAtMost (n : ℕ) : (1 : SYM D k) ∈ CoefficientAtMost D k n := by
  rw [one_eq_coefficientBasis]
  exact Submodule.subset_span ⟨(0, ∅), by simp [coefficientWeight], rfl⟩

theorem e_mem_coefficientAtMost (i : I) (n : ℕ) :
    e D k i n ∈ CoefficientAtMost D k (elementaryWeight D (i, n)) := by
  rw [e_eq_coefficientBasis]
  exact Submodule.subset_span ⟨_, by simp [coefficientWeight], rfl⟩

theorem delta_mem_coefficientAtMost (i : {i : I // D.parity i = 1}) :
    delta D k i ∈ CoefficientAtMost D k 1 := by
  rw [delta_eq_coefficientBasis]
  exact Submodule.subset_span ⟨_, by simp [coefficientWeight], rfl⟩

theorem coefficientAtMost_pow {m : ℕ} {x : SYM D k} (hx : x ∈ CoefficientAtMost D k m)
    (n : ℕ) : x ^ n ∈ CoefficientAtMost D k (n * m) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_mul]
    exact one_mem_coefficientAtMost D k 0
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact coefficientAtMost_mul D k ih hx

/-! ### Weight preservation from generators -/

theorem elementaryWeight_mono (i : I) {m n : ℕ} (h : m ≤ n) :
    elementaryWeight D (i, m) ≤ elementaryWeight D (i, n) := by
  unfold elementaryWeight
  split_ifs <;> omega

theorem oddExteriorBasis_mem (s : Finset {i : I // D.parity i = 1}) :
    oddExteriorBasis D k s ∈ ⋀[k]^s.card (OddModule D k) := by
  let : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  have h := ExteriorAlgebra.basis_eq_coe_basis
    (Finsupp.basisSingleOne : Module.Basis {i : I // D.parity i = 1} k (OddModule D k))
    (Set.powersetCard.ofCard (rfl : s.card = s.card))
  simp only [oddExteriorBasis]
  exact h ▸ Submodule.coe_mem _

section Generators

variable {D k}
variable (φ : SYM D k →ₐ[k] SYM D k)
  (he : ∀ i n, φ (e D k i n) ∈ CoefficientAtMost D k (elementaryWeight D (i, n)))
  (hd : ∀ i, φ (delta D k i) ∈ CoefficientAtMost D k 1)
include he hd

omit hd in
theorem map_polynomialInclude_monomial_mem (f : (I × ℕ) →₀ ℕ) :
    φ (polynomialInclude D k (MvPolynomial.monomial f 1)) ∈
      CoefficientAtMost D k (f.sum fun a n => n * elementaryWeight D a) := by
  induction f using Finsupp.induction with
  | zero =>
    rw [Finsupp.sum_zero_index, ← MvPolynomial.C_apply, MvPolynomial.C_1, map_one, map_one]
    exact one_mem_coefficientAtMost D k 0
  | single_add a n f _ _ ih =>
    rw [show MvPolynomial.monomial (Finsupp.single a n + f) (1 : k) =
        MvPolynomial.X a ^ n * MvPolynomial.monomial f 1 by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, one_mul],
      map_mul, map_mul, map_pow, map_pow, polynomialInclude_X,
      Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul]),
      Finsupp.sum_single_index (by simp)]
    exact coefficientAtMost_mul D k (coefficientAtMost_pow D k (he a.1 a.2) n) ih

omit he in
theorem map_oddLinear_mem (x : OddModule D k) :
    φ (oddLinear D k x) ∈ CoefficientAtMost D k 1 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  | single i c => rw [oddLinear_single, map_smul]; exact Submodule.smul_mem _ c (hd i)

omit he in
theorem map_exteriorInclude_mem (m : ℕ) {x : ExteriorAlgebra k (OddModule D k)}
    (hx : x ∈ ⋀[k]^m (OddModule D k)) :
    φ (exteriorInclude D k x) ∈ CoefficientAtMost D k m := by
  induction m generalizing x with
  | zero =>
    obtain ⟨c, rfl⟩ := Submodule.mem_one.mp (by simpa [ExteriorAlgebra.exteriorPower] using hx)
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c (one_mem_coefficientAtMost D k 0)
  | succ m ih =>
    rw [ExteriorAlgebra.exteriorPower, pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun y hy z hz => ?_) (fun y z hy hz => ?_)
    · obtain ⟨v, rfl⟩ := hz
      rw [map_mul, map_mul, exteriorInclude_ι]
      exact coefficientAtMost_mul D k (ih hy) (map_oddLinear_mem φ hd v)
    · rw [map_add, map_add]; exact Submodule.add_mem _ hy hz

/-- An algebra endomorphism of `SYM` preserves the coefficient-weight
filtration as soon as each generator image has at most the generator's weight. -/
theorem preservesWeight_of_generators (n : ℕ) {x : SYM D k}
    (hx : x ∈ CoefficientAtMost D k n) : φ x ∈ CoefficientAtMost D k n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [coefficientBasis_eq_mul, map_mul]
    apply coefficientAtMost_mono D k ha
    exact coefficientAtMost_mul D k (map_polynomialInclude_monomial_mem φ he a.1)
      (map_exteriorInclude_mem φ hd _ (oddExteriorBasis_mem D k a.2))
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end Generators

/-! ### The polynomial substitution -/

theorem constantCoeff_rescale (a : k) (f : PowerSeries k) :
    PowerSeries.constantCoeff (PowerSeries.rescale a f) = PowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
    one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- The coefficients `1, X_(i,0), X_(i,1), ...` of the generating series of colour `i`. -/
def generatorCoeff (i : I) : ℕ → MvPolynomial (I × ℕ) k
  | 0 => 1
  | n + 1 => MvPolynomial.X (i, n)

/-- The generating series `1 + Σ_n X_(i,n) z^(n+1)` of colour `i`. -/
def generatorSeries (i : I) : PowerSeries (MvPolynomial (I × ℕ) k) :=
  PowerSeries.mk (generatorCoeff k i)

/-- The substitution `G_i(z) ↦ G_i(-z) u_i(z)` on the polynomial factor. -/
def polynomialSubstitution (u : I → PowerSeries k) :
    MvPolynomial (I × ℕ) k →ₐ[k] MvPolynomial (I × ℕ) k :=
  MvPolynomial.aeval fun a => PowerSeries.coeff (a.2 + 1)
    (PowerSeries.rescale (-1) (generatorSeries k a.1) *
      PowerSeries.map (algebraMap k (MvPolynomial (I × ℕ) k)) (u a.1))

theorem map_polynomialSubstitution_generatorSeries (u : I → PowerSeries k) (i : I)
    (hu : PowerSeries.constantCoeff (u i) = 1) :
    PowerSeries.map (polynomialSubstitution k u).toRingHom (generatorSeries k i) =
      PowerSeries.rescale (-1) (generatorSeries k i) *
        PowerSeries.map (algebraMap k (MvPolynomial (I × ℕ) k)) (u i) := by
  ext n
  cases n with
  | zero =>
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton]
    simp [generatorSeries, generatorCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hu]
  | succ n =>
    simp [PowerSeries.coeff_map, generatorSeries, generatorCoeff, polynomialSubstitution]

/-- Two substitutions whose series satisfy `w(-z) u(z) = 1` compose to the identity. -/
theorem polynomialSubstitution_comp {u w : I → PowerSeries k}
    (hu : ∀ i, PowerSeries.constantCoeff (u i) = 1)
    (hw : ∀ i, PowerSeries.constantCoeff (w i) = 1)
    (h : ∀ i, PowerSeries.rescale (-1) (w i) * u i = 1) :
    (polynomialSubstitution k w).comp (polynomialSubstitution k u) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, n⟩
  have h1 : PowerSeries.map (polynomialSubstitution k w).toRingHom
      (PowerSeries.map (algebraMap k (MvPolynomial (I × ℕ) k)) (u i)) =
        PowerSeries.map (algebraMap k (MvPolynomial (I × ℕ) k)) (u i) := by
    ext m
    simp [PowerSeries.coeff_map]
  have h2 : ∀ f : PowerSeries (MvPolynomial (I × ℕ) k),
      PowerSeries.map (polynomialSubstitution k w).toRingHom (PowerSeries.rescale (-1) f) =
        PowerSeries.rescale (-1) (PowerSeries.map (polynomialSubstitution k w).toRingHom f) := by
    intro f
    ext m
    simp [PowerSeries.coeff_map, PowerSeries.coeff_rescale]
  have h3 : PowerSeries.rescale (-1)
      (PowerSeries.map (algebraMap k (MvPolynomial (I × ℕ) k)) (w i)) =
        PowerSeries.map (algebraMap k (MvPolynomial (I × ℕ) k))
          (PowerSeries.rescale (-1) (w i)) := by
    ext m
    simp [PowerSeries.coeff_map, PowerSeries.coeff_rescale]
  have key : PowerSeries.map ((polynomialSubstitution k w).toRingHom.comp
      (polynomialSubstitution k u).toRingHom)
      (generatorSeries k i) = generatorSeries k i := by
    rw [PowerSeries.map_comp, RingHom.comp_apply,
      map_polynomialSubstitution_generatorSeries k u i (hu i), map_mul, h1, h2,
      map_polynomialSubstitution_generatorSeries k w i (hw i), map_mul,
      PowerSeries.rescale_rescale, h3, mul_assoc, ← map_mul, h i, map_one, mul_one,
      neg_one_mul, neg_neg, PowerSeries.rescale_one, RingHom.id_apply]
  have := congrArg (PowerSeries.coeff (n + 1)) key
  simpa [PowerSeries.coeff_map, generatorSeries, generatorCoeff] using this

/-- Each substituted generator is a combination of `1` and generators of the
same colour with index at most its own. -/
theorem polynomialSubstitution_X_mem (u : I → PowerSeries k) (i : I) (n : ℕ) :
    polynomialSubstitution k u (MvPolynomial.X (i, n)) ∈
      Submodule.span k (generatorCoeff k i '' Set.Iic (n + 1)) := by
  simp only [polynomialSubstitution, MvPolynomial.aeval_X, PowerSeries.coeff_mul]
  apply Submodule.sum_mem
  rintro ⟨p, q⟩ hpq
  rw [Finset.mem_antidiagonal] at hpq
  have hmem : generatorCoeff k i p ∈ Submodule.span k (generatorCoeff k i '' Set.Iic (n + 1)) :=
    Submodule.subset_span ⟨p, by simp only [Set.mem_Iic]; omega, rfl⟩
  have : PowerSeries.coeff p (PowerSeries.rescale (-1) (generatorSeries k i)) *
      PowerSeries.coeff q (PowerSeries.map (algebraMap k (MvPolynomial (I × ℕ) k)) (u i)) =
        ((-1) ^ p * PowerSeries.coeff q (u i)) • generatorCoeff k i p := by
    simp [generatorSeries, PowerSeries.coeff_map, Algebra.smul_def, mul_comm, mul_left_comm]
    ring
  rw [this]
  exact Submodule.smul_mem _ _ hmem

/-! ### The substitution of the coefficient algebra -/

private def substitutionGen (u : I → PowerSeries k) (s : {i : I // D.parity i = 1} → k) :
    SYMGen D → SYM D k
  | .inl a => polynomialInclude D k (polynomialSubstitution k u (MvPolynomial.X a))
  | .inr i => s i • delta D k i

private theorem substitution_rel (u : I → PowerSeries k) (s : {i : I // D.parity i = 1} → k)
    {x y : FreeAlgebra k (SYMGen D)} (h : SYMRel D k x y) :
    FreeAlgebra.lift k (substitutionGen D k u s) x =
      FreeAlgebra.lift k (substitutionGen D k u s) y := by
  cases h with
  | polynomial a b =>
    simp only [map_mul, FreeAlgebra.lift_ι_apply, substitutionGen]
    exact polynomialInclude_commute D k _ _
  | mixed a i =>
    simp only [map_mul, FreeAlgebra.lift_ι_apply, substitutionGen]
    exact polynomialInclude_commute D k _ _
  | exterior i j =>
    simp only [map_mul, map_neg, FreeAlgebra.lift_ι_apply, substitutionGen,
      smul_mul_smul_comm, delta_anticommute D k i j, smul_neg, mul_comm (s i) (s j)]
  | square i =>
    simp only [map_pow, map_zero, FreeAlgebra.lift_ι_apply, substitutionGen, smul_pow,
      delta_sq, smul_zero]

/-- The triangular substitution `G_i(z) ↦ G_i(-z) u_i(z)`, `δ_i ↦ s_i δ_i`. -/
def substitutionHom (u : I → PowerSeries k) (s : {i : I // D.parity i = 1} → k) :
    SYM D k →ₐ[k] SYM D k :=
  RingQuot.liftAlgHom k
    ⟨FreeAlgebra.lift k (substitutionGen D k u s), fun _ _ h => substitution_rel D k u s h⟩

@[simp] theorem substitutionHom_ι (u : I → PowerSeries k) (s : {i : I // D.parity i = 1} → k)
    (g : SYMGen D) : substitutionHom D k u s (ι D k g) = substitutionGen D k u s g := by
  simp only [substitutionHom, ι, mk, RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]

@[simp] theorem substitutionHom_e (u : I → PowerSeries k) (s : {i : I // D.parity i = 1} → k)
    (i : I) (n : ℕ) : substitutionHom D k u s (e D k i n) =
      polynomialInclude D k (polynomialSubstitution k u (MvPolynomial.X (i, n))) :=
  substitutionHom_ι D k u s (.inl (i, n))

@[simp] theorem substitutionHom_delta (u : I → PowerSeries k)
    (s : {i : I // D.parity i = 1} → k) (i : {i : I // D.parity i = 1}) :
    substitutionHom D k u s (delta D k i) = s i • delta D k i :=
  substitutionHom_ι D k u s (.inr i)

theorem substitutionHom_polynomialInclude (u : I → PowerSeries k)
    (s : {i : I // D.parity i = 1} → k) (p : MvPolynomial (I × ℕ) k) :
    substitutionHom D k u s (polynomialInclude D k p) =
      polynomialInclude D k (polynomialSubstitution k u p) := by
  have : (substitutionHom D k u s).comp (polynomialInclude D k) =
      (polynomialInclude D k).comp (polynomialSubstitution k u) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, n⟩
    simp
  exact DFunLike.congr_fun this p

theorem substitutionHom_comp {u w : I → PowerSeries k} {s t : {i : I // D.parity i = 1} → k}
    (hp : (polynomialSubstitution k w).comp (polynomialSubstitution k u) = AlgHom.id k _)
    (hs : ∀ i, t i * s i = 1) :
    (substitutionHom D k w t).comp (substitutionHom D k u s) = AlgHom.id k _ := by
  apply hom_ext
  intro g
  cases g with
  | inl a =>
    simp only [AlgHom.comp_apply, substitutionHom_ι, substitutionGen,
      substitutionHom_polynomialInclude, ← AlgHom.comp_apply (polynomialSubstitution k w), hp,
      AlgHom.id_apply, polynomialInclude_X]
    rfl
  | inr i =>
    simp only [AlgHom.comp_apply, substitutionHom_ι, substitutionGen, map_smul,
      substitutionHom_delta, smul_smul, mul_comm (s i), hs i, one_smul, AlgHom.id_apply]
    rfl

/-- The triangular substitution as an automorphism. The inverse substitution
uses the series `w_i(-z)`, where `w_i = u_i⁻¹`, and the inverse scalars. -/
def substitutionEquiv (u w : I → PowerSeries k) (s t : {i : I // D.parity i = 1} → k)
    (hu : ∀ i, PowerSeries.constantCoeff (u i) = 1) (huw : ∀ i, u i * w i = 1)
    (hst : ∀ i, s i * t i = 1) : SYM D k ≃ₐ[k] SYM D k :=
  have hw : ∀ i, PowerSeries.constantCoeff (w i) = 1 := fun i => by
    simpa [hu i] using congrArg PowerSeries.constantCoeff (huw i)
  have hw' : ∀ i, PowerSeries.constantCoeff (PowerSeries.rescale (-1) (w i)) = 1 := fun i => by
    rw [constantCoeff_rescale, hw i]
  AlgEquiv.ofAlgHom (substitutionHom D k u s)
    (substitutionHom D k (fun i => PowerSeries.rescale (-1) (w i)) t)
    (substitutionHom_comp D k (polynomialSubstitution_comp k hw' hu
      fun i => by rw [← map_mul, huw i, map_one]) hst)
    (substitutionHom_comp D k (polynomialSubstitution_comp k hu hw'
      fun i => by
        rw [PowerSeries.rescale_rescale, neg_one_mul, neg_neg, PowerSeries.rescale_one,
          RingHom.id_apply, mul_comm, huw i])
      fun i => by rw [mul_comm, hst i])

@[simp] theorem substitutionEquiv_apply (u w : I → PowerSeries k)
    (s t : {i : I // D.parity i = 1} → k) (hu : ∀ i, PowerSeries.constantCoeff (u i) = 1)
    (huw : ∀ i, u i * w i = 1) (hst : ∀ i, s i * t i = 1) (x : SYM D k) :
    substitutionEquiv D k u w s t hu huw hst x = substitutionHom D k u s x := rfl

/-- Every triangular substitution preserves the coefficient-weight filtration. -/
theorem substitutionHom_mem_coefficientAtMost (u : I → PowerSeries k)
    (s : {i : I // D.parity i = 1} → k) (n : ℕ) {x : SYM D k}
    (hx : x ∈ CoefficientAtMost D k n) :
    substitutionHom D k u s x ∈ CoefficientAtMost D k n := by
  refine preservesWeight_of_generators (substitutionHom D k u s) (fun i n => ?_)
    (fun i => ?_) n hx
  · rw [substitutionHom_e]
    have : Submodule.span k (generatorCoeff k i '' Set.Iic (n + 1)) ≤
        (CoefficientAtMost D k (elementaryWeight D (i, n))).comap
          (polynomialInclude D k).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      cases m with
      | zero => simpa [generatorCoeff] using one_mem_coefficientAtMost D k _
      | succ m =>
        simp only [Set.mem_Iic] at hm
        simp only [generatorCoeff, SetLike.mem_coe, Submodule.mem_comap, AlgHom.toLinearMap_apply,
          polynomialInclude_X]
        exact coefficientAtMost_mono D k (elementaryWeight_mono D i (by omega))
          (e_mem_coefficientAtMost D k i m)
    exact this (polynomialSubstitution_X_mem k u i n)
  · rw [substitutionHom_delta]
    exact Submodule.smul_mem _ _ (delta_mem_coefficientAtMost D k i)

/-! ### The vacuum substitution -/

/-- The scale `-1` at odd colours and `1` at even colours. -/
def colourScale (i : I) : k := if D.parity i = 1 then -1 else 1

/-- `(1+z)^(-m)` at odd colours, `(1-z)^(-m)` at even colours. -/
def probeSeries (M : I → ℕ) (i : I) : PowerSeries k :=
  PowerSeries.rescale (colourScale D k i) (PowerSeries.invUnitsSub 1) ^ M i

/-- The inverse series `(1+z)^m` at odd colours, `(1-z)^m` at even colours. -/
def probeSeriesInv (M : I → ℕ) (i : I) : PowerSeries k :=
  PowerSeries.rescale (colourScale D k i) (PowerSeries.C (1 : k) - PowerSeries.X) ^ M i

theorem probeSeries_mul_inv (M : I → ℕ) (i : I) :
    probeSeries D k M i * probeSeriesInv D k M i = 1 := by
  rw [probeSeries, probeSeriesInv, ← mul_pow, ← map_mul]
  have := PowerSeries.invUnitsSub_mul_sub (1 : kˣ)
  simp only [Units.val_one] at this
  rw [this, map_one, one_pow]

theorem constantCoeff_probeSeries (M : I → ℕ) (i : I) :
    PowerSeries.constantCoeff (probeSeries D k M i) = 1 := by
  rw [probeSeries, map_pow, constantCoeff_rescale, PowerSeries.constantCoeff_invUnitsSub]
  simp

/-- The sign `(-1)^(N_i+1)` on the odd generator of colour `i`. -/
def probeSign (N : I → ℕ) (i : {i : I // D.parity i = 1}) : k := (-1) ^ (N i + 1)

theorem probeSign_mul_self (N : I → ℕ) (i : {i : I // D.parity i = 1}) :
    probeSign D k N i * probeSign D k N i = 1 := by
  rw [probeSign, ← pow_add, ← two_mul, pow_mul]
  simp

/-- The substitution of the vacuum evaluation: `C_i(z) ↦ C_i(-z)(1+z)^(-M_i)` and
`δ_i ↦ (-1)^(N_i+1) δ_i` at odd colours, `E_i(z) ↦ E_i(-z)(1-z)^(-M_i)` at even
colours. In the notation of the written proof, `M_i = P_i/2` at odd colours and
`M_i = P_i` at even colours. -/
def probeSubstitution (M N : I → ℕ) : SYM D k ≃ₐ[k] SYM D k :=
  substitutionEquiv D k (probeSeries D k M) (probeSeriesInv D k M) (probeSign D k N)
    (probeSign D k N) (constantCoeff_probeSeries D k M) (probeSeries_mul_inv D k M)
    (probeSign_mul_self D k N)

theorem probeSubstitution_mem_coefficientAtMost (M N : I → ℕ) (n : ℕ) {x : SYM D k}
    (hx : x ∈ CoefficientAtMost D k n) :
    probeSubstitution D k M N x ∈ CoefficientAtMost D k n :=
  substitutionHom_mem_coefficientAtMost D k _ _ n hx

theorem probeSubstitution_symm_mem_coefficientAtMost (M N : I → ℕ) (n : ℕ) {x : SYM D k}
    (hx : x ∈ CoefficientAtMost D k n) :
    (probeSubstitution D k M N).symm x ∈ CoefficientAtMost D k n :=
  substitutionHom_mem_coefficientAtMost D k _ _ n hx

end OddMath.SKM.SYM
