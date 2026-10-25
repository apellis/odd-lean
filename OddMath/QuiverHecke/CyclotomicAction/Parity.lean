/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Quotient
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Parity input for cyclotomic induction

Ports the grading prerequisite for
`Categorification/KLR/CyclotomicAction/Induction.lean` to the quiver Hecke
superalgebra. Parity does not require an integer symmetrizer or integer
homogeneity of the parameters. The homogeneous-ideal theorem retains its
explicit generator-homogeneity premise.
-/

noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Entrywise parity, independently of the integer grading. -/
def affineParity (n : ℕ) (p : ZMod 2) : Submodule k (Hn D Sc n) :=
  FiniteHomMatrix.component
    (fun q => Supercategory.parity (R := k) (wordObj D Sc q.2) (wordObj D Sc q.1)) p

omit [Fintype I] in
theorem affineParity_internal (n : ℕ) : DirectSum.IsInternal (affineParity D Sc n) :=
  FiniteHomMatrix.isInternal_component _ fun _ => Supercategory.isInternal _ _

instance affineParity_graded (n : ℕ) : GradedAlgebra (affineParity D Sc n) where
  __ := (affineParity_internal D Sc n).chooseDecomposition
  one_mem := by
    change FiniteHomMatrix.localUnit Finset.univ ∈ _
    apply Submodule.sum_mem
    intro i _
    exact FiniteHomMatrix.single_mem_component i i (Supercategory.id_mem (R := k) _)
  mul_mem p q := by
    intro x y ha hb
    apply FiniteHomMatrix.mul_mem_component _ _ ha hb
    intro i j l p q f g hf hg
    simpa only [add_comm] using Supercategory.comp_mem hg hf

/-- The two-sided cyclotomic ideal is homogeneous if its first-dot
polynomial generators are homogeneous. Arbitrary right multipliers are
expanded into homogeneous components rather than assumed homogeneous. -/
theorem cyclotomicIdeal_homogeneous (a : I → _root_.Polynomial k) (n : ℕ)
    (ha : ∀ w : Word I (n + 1),
      SetLike.IsHomogeneousElem (affineParity D Sc (n + 1)) (cyclotomicGenerator D Sc a w)) :
    (cyclotomicIdeal D Sc a n).IsHomogeneous (affineParity D Sc (n + 1)) := by
  let G := affineParity D Sc (n + 1)
  let S : Set (Hn D Sc (n + 1)) := {z | ∃ (w : Word I (n + 1)) (b : Hn D Sc (n + 1)),
    SetLike.IsHomogeneousElem G b ∧ z = cyclotomicGenerator D Sc a w * b}
  have hS : (Ideal.span S).IsHomogeneous G := by
    apply Ideal.homogeneous_span
    rintro z ⟨w, b, hb, rfl⟩
    exact (ha w).mul hb
  have he : cyclotomicIdeal D Sc a n = Ideal.span S := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro z ⟨w, b, rfl⟩
      induction b using DirectSum.Decomposition.inductionOn G with
      | zero => simp
      | @homogeneous p b => exact Ideal.subset_span ⟨w, b, ⟨p, b.property⟩, rfl⟩
      | add b c hb hc =>
        rw [mul_add]
        exact Ideal.add_mem _ hb hc
    · apply Ideal.span_le.mpr
      rintro z ⟨w, b, _, rfl⟩
      exact Ideal.subset_span ⟨w, b, rfl⟩
  rw [he]
  exact hS

/-- With even coefficients, all nonzero terms of a cyclotomic polynomial
must have the same parity as its leading term. -/
def CyclotomicPolynomialParity (a : I → _root_.Polynomial k) : Prop :=
  ∀ i m, (a i).coeff m ≠ 0 → m • D.parity i = (a i).natDegree • D.parity i

omit [Fintype I] in
theorem firstDot_parity (i : I) (t : List I) :
    dotE D Sc (i :: t) 0 ∈ Supercategory.parity (R := k)
      ((pres D Sc).obj (ob D (i :: t))) ((pres D Sc).obj (ob D (i :: t))) (D.parity i) := by
  rw [dotE_eq]
  apply Presentation.diag_mem_homDeg'
  simp [degree_parity_mkD, pl, PG.ld, Shape.parity]

omit [Fintype I] in
theorem firstDot_pow_parity (i : I) (t : List I) (m : ℕ) :
    dotE D Sc (i :: t) 0 ^ m ∈ Supercategory.parity (R := k)
      ((pres D Sc).obj (ob D (i :: t))) ((pres D Sc).obj (ob D (i :: t))) (m • D.parity i) := by
  induction m with
  | zero => exact Supercategory.id_mem (R := k) _
  | succ m ih =>
    simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm] using
      Supercategory.comp_mem (firstDot_parity D Sc i t) ih

omit [Fintype I] in
/-- Homogeneous coefficient support gives homogeneous actual generators. -/
theorem cyclotomicGenerator_parity (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) {n : ℕ} (w : Word I (n + 1)) :
    SetLike.IsHomogeneousElem (affineParity D Sc (n + 1)) (cyclotomicGenerator D Sc a w) := by
  rcases w with ⟨l, hl⟩
  cases l with
  | nil => simp at hl
  | cons i t =>
    refine ⟨(a i).natDegree • D.parity i, ?_⟩
    apply FiniteHomMatrix.single_mem_component
    change _root_.Polynomial.aeval (dotE D Sc (i :: t) 0) (a i) ∈
      Supercategory.parity (R := k) _ _ ((a i).natDegree • D.parity i)
    rw [_root_.Polynomial.aeval_def, _root_.Polynomial.eval₂_eq_sum]
    change (∑ m ∈ (a i).support, algebraMap k _ ((a i).coeff m) * dotE D Sc (i :: t) 0 ^ m) ∈ _
    apply Submodule.sum_mem
    intro m hm
    rw [← Algebra.smul_def]
    apply Submodule.smul_mem
    rw [← ha i m (_root_.Polynomial.mem_support_iff.mp hm)]
    exact firstDot_pow_parity D Sc i t m

/-- The homogeneous-polynomial criterion closes the ideal-homogeneity premise. -/
theorem cyclotomicIdeal_homogeneous_of_polynomials (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    (cyclotomicIdeal D Sc a n).IsHomogeneous (affineParity D Sc (n + 1)) :=
  cyclotomicIdeal_homogeneous D Sc a n (cyclotomicGenerator_parity D Sc a ha)

end OddMath.QuiverHecke
