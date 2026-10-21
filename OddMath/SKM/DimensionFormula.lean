/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.HomDimensions
import OddMath.SKM.DimensionConvolution
import OddMath.SKM.Theorem103

/-!
# The graded-dimension formula in BE2 Theorem 12.1

Equation (dum) is stated without division: the Hom dimension is the
sesquilinear form times the dimension of the abstract coefficient algebra.
We use the existing `signLaurent` API into `LaurentSeries ℚ`, for every rational
sign whose square is one. In particular both signs are retained, so parity
information is not discarded. The series for `SYM` is defined from intrinsic
component dimensions, not from the Euler product corrected in ERRATA [BE2] 8.
The local-finiteness hypothesis is an explicit intermediate scope condition.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams CoveringQuantum
open CoveringQuantum.UDot.GenericTensor CoveringQuantum.UDot.GenericVerma.MixedGram

universe u v w

/-- A parity-weighted coefficient from the dimensions of the even and odd parts. -/
def superdimensionCoeff (d : ℤ × ZMod 2 → ℕ) (σ : ℚ) (n : ℤ) : ℚ :=
  ∑ p : ZMod 2, σ ^ p.val * d (n, p)

/-- Package bounded-below component dimensions in the existing Laurent-series
ring. Finiteness of the dimensions is verified at the applications. -/
def dimensionSeries (d : ℤ × ZMod 2 → ℕ)
    (hd : ∃ N : ℤ, ∀ n < N, ∀ p, d (n, p) = 0) (σ : ℚ) : LaurentSeries ℚ :=
  HahnSeries.ofSuppBddBelow (superdimensionCoeff d σ) (by
    obtain ⟨N, hN⟩ := hd
    refine ⟨N, fun n hn => ?_⟩
    by_contra h
    apply hn
    simp only [superdimensionCoeff, hN n (lt_of_not_ge h), Nat.cast_zero,
      mul_zero, Finset.sum_const_zero])

@[simp] theorem dimensionSeries_coeff (d : ℤ × ZMod 2 → ℕ)
    (hd : ∃ N : ℤ, ∀ n < N, ∀ p, d (n, p) = 0) (σ : ℚ) (n : ℤ) :
    (dimensionSeries d hd σ).coeff n = superdimensionCoeff d σ n := rfl

section Components
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
variable (sy : Symmetrizer D) (k : Type w) [Field k]

/-- The graded dimension of the abstract `SYM`, with parity evaluated at `σ`.
No expression as a product over colours is used in this definition. -/
def symDimension (σ : ℚ) : LaurentSeries ℚ :=
  dimensionSeries (fun z => Module.finrank k (SYM.component sy k z))
    ⟨0, fun n hn p => by rw [SYM.component_eq_bot sy k (n, p) hn]; simp⟩ σ

@[simp] theorem symDimension_coeff (σ : ℚ) (n : ℤ) :
    (symDimension sy k σ).coeff n =
      ∑ p : ZMod 2, σ ^ p.val * Module.finrank k (SYM.component sy k (n, p)) := rfl

/-- Coefficient dimensions have no negative integer degrees. -/
theorem symDimension_coeff_neg (σ : ℚ) (n : ℤ) (hn : n < 0) :
    (symDimension sy k σ).coeff n = 0 := by
  rw [symDimension_coeff]
  apply Finset.sum_eq_zero
  intro p _
  rw [SYM.component_eq_bot sy k (n, p) hn]
  simp

variable {k} {Sc : Scalars D k} (cs : CScalars Sc)

/-- The graded dimension of a word Hom, from its integer/parity component
finranks. Homogeneity and local finiteness give the Laurentian bounds. -/
def homDimension (hc : Sc.Homogeneous) (hf : sy.DegreeLocallyFinite)
    (μ : X) (a b : List (Letter I)) (σ : ℚ) : LaurentSeries ℚ :=
  dimensionSeries (fun z => Module.finrank k (wordHomComponent sy Sc μ a b z)) (by
    obtain ⟨_, N, hN⟩ := hom_parity_laurentian sy Sc cs hc hf μ a b
    exact ⟨N, fun n hn p => by
      change Module.finrank k
        ↥((pres D Sc).homDeg (gdeg D sy) (ob D μ a) (ob D μ b) n ⊓ homPar D Sc μ a b p) = 0
      rw [hN n hn p]
      simp⟩) σ

@[simp] theorem homDimension_coeff (hc : Sc.Homogeneous) (hf : sy.DegreeLocallyFinite)
    (μ : X) (a b : List (Letter I)) (σ : ℚ) (n : ℤ) :
    (homDimension sy cs hc hf μ a b σ).coeff n =
      ∑ p : ZMod 2, σ ^ p.val * Module.finrank k (wordHomComponent sy Sc μ a b (n, p)) := rfl

end Components

/-- Shifting parity multiplies the signed dimension by the corresponding
parity monomial. Both `σ = 1` and `σ = -1` are covered. -/
theorem parity_sum_shift (σ : ℚ) (hσ : σ ^ 2 = 1) (ε : ZMod 2) (v : ZMod 2 → ℚ) :
    (∑ p : ZMod 2, σ ^ p.val * v (p - ε)) =
      σ ^ ε.val * ∑ p : ZMod 2, σ ^ p.val * v p := by
  rw [Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (Equiv.addRight ε)
  intro p
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hσ, pow_add]
  ring

section Formula
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
variable {k : Type w} [Field k] {Sc : Scalars D k}
variable {a b : List (Letter I)} (F : MatchingBasisChoice a b)
variable (sy : Symmetrizer D) (cs : CScalars Sc) (μ : X)

/-- The coefficientwise version retains both parity components and the
intrinsic coefficient-algebra dimensions. -/
theorem homDimension_coeff_basis (hc : Sc.Homogeneous) (hf : sy.DegreeLocallyFinite)
    (hF : F.IsBasis cs μ) (σ : ℚ) (hσ : σ ^ 2 = 1) (n : ℤ) :
    (homDimension sy cs hc hf μ a b σ).coeff n =
      ∑ t : F.boundedLabels sy μ n, σ ^ (F.labelBidegree sy μ t.val).2.val *
        (symDimension sy k σ).coeff (n - (F.labelBidegree sy μ t.val).1) := by
  rw [homDimension_coeff]
  simp_rw [wordHomComponent_finrank F sy cs μ hc hf hF, Nat.cast_sum, Finset.mul_sum]
  change (∑ p : ZMod 2, ∑ t : F.boundedLabels sy μ n,
    σ ^ p.val * (Module.finrank k (SYM.component sy k
      ((n, p) - F.labelBidegree sy μ t.val)) : ℚ)) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [symDimension_coeff]
  exact parity_sum_shift σ hσ (F.labelBidegree sy μ t.val).2
    (fun p => (Module.finrank k (SYM.component sy k
      (n - (F.labelBidegree sy μ t.val).1, p)) : ℚ))

end Formula

section RootDatum
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X) {k : Type*} [Field k]
variable {Sc : Scalars D.toSKM k} (cs : CScalars Sc)

/-- **BE2 Theorem 12.1, equation (dum), with local finiteness.**
The graded dimension of the presented Hom is the sesquilinear form times
`S`, the graded dimension of the abstract `SYM`. This is the intermediate
`DegreeLocallyFinite` scope tracked in issue #42, not a resolution of the
unrestricted infinite-colour source statement. The Nondegeneracy Conjecture
is a premise, not an axiom or a conclusion. Every rational parity sign is
allowed, including both `1` and `-1`; the existing Laurent-series embedding
of the covering form is used. Bar consistency is not needed for this step
of the proof, although Theorem 12.1 assumes it for form nondegeneracy. -/
theorem hom_dimension_eq_form_mul_sym (hc : Sc.Homogeneous)
    (hf : D.skmSymmetrizer.DegreeLocallyFinite) (hN : NondegeneracyConjecture cs)
    (μ : X) (a b : List (Letter I)) (hab : wt D.toSKM 0 a = wt D.toSKM 0 b)
    (σ : ℚ) (hσ : σ ^ 2 = 1) :
    homDimension D.skmSymmetrizer cs hc hf μ a b σ =
      signLaurent σ hσ (sesquilinearForm D (algebraWord D μ a) (algebraWord D μ b)) *
        symDimension D.skmSymmetrizer k σ := by
  classical
  obtain ⟨F⟩ := MatchingBasisChoice.nonempty a b
  have hcoeff (n : ℤ) := mixed_boundary_labelled_form_coeff D μ a b F.members
    F.matching F.complete F.unique F.points F.onStrand F.serialize F.decorates σ hσ n
  apply HahnSeries.ext
  funext n
  rw [homDimension_coeff_basis F D.skmSymmetrizer cs μ hc hf (hN a b hab μ F) σ hσ n]
  have hprod := laurentSeries_coeff_mul_eq_sum_bounded
    (fun t : F.Labels => (F.labelBidegree D.skmSymmetrizer μ t).1)
    (fun t => σ ^ (F.labelBidegree D.skmSymmetrizer μ t).2.val)
    (F.labelDegree_le_finite D.skmSymmetrizer μ)
    (signLaurent σ hσ (sesquilinearForm D (algebraWord D μ a) (algebraWord D μ b)))
    (symDimension D.skmSymmetrizer k σ)
    (fun n => hcoeff n) (symDimension_coeff_neg D.skmSymmetrizer k σ) n
  rw [hprod]
  exact (Finset.sum_subtype _ (fun t => (F.labelDegree_le_finite D.skmSymmetrizer μ n).mem_toFinset)
    (fun t => σ ^ (F.labelBidegree D.skmSymmetrizer μ t).2.val *
      (symDimension D.skmSymmetrizer k σ).coeff
        (n - (F.labelBidegree D.skmSymmetrizer μ t).1))).symm

end RootDatum
end OddMath.SKM
