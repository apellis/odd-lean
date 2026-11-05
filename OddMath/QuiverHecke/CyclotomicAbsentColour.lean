/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Basis
import OddMath.QuiverHecke.MixedRelations
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.RingTheory.AdjoinRoot

/-!
# One-strand cyclotomic coordinates

Ports the one-strand polynomial and rank-zero cyclotomic coordinates of
`Categorification/KLR/CyclotomicAbsentColour.lean` to the existing quiver
Hecke supercategory. The coefficient ring is even; the strand may have either
parity. The quotient is constructed as an underlying algebra for any monic
polynomial; a super grading additionally requires a homogeneous polynomial.
This does not construct the higher-content induction bimodules.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

private theorem canWord_single (s : Equiv.Perm (Fin 1)) : canWord 1 s = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a ha
  have := validWord_canWord 1 s a ha
  omega

/-- At one strand, the normal-form label is just the number of dots. -/
def singleNFIndex (i : I) (n : ℕ) : NFIdx [i] [i] :=
  ⟨(List.replicate n 0, 1), by simp, by simp,
    by simpa [canWord_single, cw] using
      sChain_dot_pow [i] 0 n⟩

theorem singleNFIndex_bijective (i : I) : Function.Bijective (singleNFIndex i) := by
  constructor
  · intro n m h
    have := congrArg (fun z : NFIdx [i] [i] => z.1.1.length) h
    simpa [singleNFIndex] using this
  · intro z
    refine ⟨z.1.1.length, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change List.replicate z.1.1.length 0 = z.1.1
      symm
      apply List.eq_replicate_iff.mpr
      refine ⟨rfl, ?_⟩
      intro a ha
      have := z.2.2.1 a ha
      simp only [List.length_singleton] at this
      omega
    · apply Equiv.ext
      intro j
      apply Fin.ext
      have h₁ := (z.1.2 j).isLt
      have h₂ := j.isLt
      simp only [List.length_singleton] at h₁ h₂
      change j.val = (z.1.2 j).val
      omega

@[simp] theorem singleNFIndex_nf (i : I) (n : ℕ) :
    (singleNFIndex i n).nf (D := D) (Sc := Sc) = dotE D Sc [i] 0 ^ n := by
  rw [dotE_pow]
  unfold NFIdx.nf singleNFIndex
  simp only [List.length_singleton, canWord_single, cw_nil, List.append_nil,
    List.map_replicate]

/-- The powers of the dot are a basis, including for an odd strand. -/
def singleDotBasis (i : I) :
    Module.Basis ℕ k (End ((pres D Sc).obj (ob D [i]))) :=
  (basisNF D Sc [i] [i]).reindex (Equiv.ofBijective (singleNFIndex i)
    (singleNFIndex_bijective i)).symm

/-- Evaluation at the one-strand dot is an algebra equivalence, with no
restriction on the colour parity. -/
def singlePolynomialEquiv (i : I) :
    _root_.Polynomial k ≃ₐ[k] End ((pres D Sc).obj (ob D [i])) := by
  let e := (_root_.Polynomial.basisMonomials k).equiv (singleDotBasis D Sc i) (Equiv.refl ℕ)
  have he : (_root_.Polynomial.aeval (dotE D Sc [i] 0)).toLinearMap = e.toLinearMap := by
    apply (_root_.Polynomial.basisMonomials k).ext
    intro n
    change _ = e ((_root_.Polynomial.basisMonomials k) n)
    rw [Module.Basis.equiv_apply]
    simp [_root_.Polynomial.coe_basisMonomials,
      ← _root_.Polynomial.C_mul_X_pow_eq_monomial]
  exact AlgEquiv.ofBijective (_root_.Polynomial.aeval (dotE D Sc [i] 0))
    (show Function.Bijective (_root_.Polynomial.aeval (dotE D Sc [i] 0)) from
      by
        change Function.Bijective (_root_.Polynomial.aeval (dotE D Sc [i] 0)).toLinearMap
        rw [he]
        exact e.bijective)

/-- The cyclotomic ideal inside the existing one-strand endomorphism ring. -/
def singleCyclotomicIdeal (i : I) (a : _root_.Polynomial k) :
    Ideal (End ((pres D Sc).obj (ob D [i]))) :=
  (Ideal.span {a}).map (singlePolynomialEquiv D Sc i).toRingHom

instance singleCyclotomicIdeal_twoSided (i : I) (a : _root_.Polynomial k) :
    (singleCyclotomicIdeal D Sc i a).IsTwoSided where
  mul_mem_of_left b ha := by
    have hc : ∀ x y : End ((pres D Sc).obj (ob D [i])), x * y = y * x := by
      intro x y
      obtain ⟨x, rfl⟩ := (singlePolynomialEquiv D Sc i).surjective x
      obtain ⟨y, rfl⟩ := (singlePolynomialEquiv D Sc i).surjective y
      rw [← map_mul, ← map_mul, mul_comm]
    rw [hc]
    exact Ideal.mul_mem_left _ b ha

end OddMath.QuiverHecke
