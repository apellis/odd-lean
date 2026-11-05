import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundarySnake
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalInputPivots
import Mathlib.LinearAlgebra.Finsupp.Supported
import OddMath.Algebra.FiniteTriangularCoordinates
import OddMath.Algebra.LowPolynomialCoordinates

/-! # The negative-height crossing and its actual input-contraction rows

DeformedRouquierMatrix, section 4, reduces inversion to these concrete rows.
The cap vector is formed from the descended input contraction and moving
input dot. Its restriction to the concrete snake kernel has the prescribed
anti-triangular pivots. Finite elimination yields the whole raw augmented
matrix on arbitrary old Hom coefficients. Its categorical signed-dot/cap
comparison and naturality are separate obligations; no equality is assumed.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
open OddMath.LowPolynomialCoordinates
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The raw cap vector uses the actual descended contraction and input dot. -/
def offDiagonalInputCapVector (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ) :
    Source D Sc cutoff j.1 v t →ₗ[k] (Fin m → Old D Sc cutoff v t) :=
  LinearMap.pi fun r : Fin m =>
    (offDiagonalInputContraction D Sc cutoff j v t).comp ((offDiagonalCrossingInputDot D Sc cutoff j v t) ^ r.val)

@[simp] theorem offDiagonalInputCapVector_apply (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ) (s : Source D Sc cutoff j.1 v t) (r : Fin m) :
    offDiagonalInputCapVector D Sc cutoff j v t m s r =
      offDiagonalInputContraction D Sc cutoff j v t ((offDiagonalCrossingInputDot D Sc cutoff j v t)^[r.val] s) := by
  exact congrArg (offDiagonalInputContraction D Sc cutoff j v t)
    (Module.End.pow_apply (offDiagonalCrossingInputDot D Sc cutoff j v t) r.val s)

private def kernelWindowVectorEquiv (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (Fin m → Old D Sc cutoff v t) ≃ₗ[k] offDiagonalBoundaryKernelWindow D Sc cutoff j v t where
  toFun f := ⟨(lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m f).val, by
    intro d hd
    have hlt : d < m := (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m f).property hd
    change d + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v
    omega⟩
  invFun f := (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m).symm ⟨f.val, by
    intro d hd
    have hlt := f.property hd
    change d + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v at hlt
    change d < m
    omega⟩
  left_inv f := by
    apply (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m).injective
    rw [LinearEquiv.apply_symm_apply]
  right_inv f := by
    apply Subtype.ext
    exact congrArg (fun z : Finsupp.supported (Old D Sc cutoff v t) k (Set.Iio m) => (z : ℕ →₀ Old D Sc cutoff v t)) ((lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m).apply_symm_apply _)
  map_add' f g := by
    apply Subtype.ext
    exact congrArg (fun z : Finsupp.supported (Old D Sc cutoff v t) k (Set.Iio m) => (z : ℕ →₀ Old D Sc cutoff v t)) (map_add (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m) f g)
  map_smul' c f := by
    apply Subtype.ext
    exact congrArg (fun z : Finsupp.supported (Old D Sc cutoff v t) k (Set.Iio m) => (z : ℕ →₀ Old D Sc cutoff v t)) (map_smul (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m) c f)

/-- Coordinates in the actual boundary kernel, using the corrected low window. -/
def offDiagonalBoundaryKernelVectorEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (Fin m → Old D Sc cutoff v t) ≃ₗ[k]
      LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t) :=
  (kernelWindowVectorEquiv D Sc cutoff j v t m hm).trans
    (offDiagonalBoundaryKernelEquiv D Sc cutoff p j v t)

theorem offDiagonalBoundaryKernelVectorEquiv_single (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (d : Fin m) (b : Old D Sc cutoff v t) :
    ((offDiagonalBoundaryKernelVectorEquiv D Sc cutoff p j v t m hm (Pi.single d b)) :
      ℕ →₀ Old D Sc cutoff v t) =
      offDiagonalLongExtraction D Sc cutoff p j.1 v t (offDiagonalCorrectedLift D Sc cutoff p j v t d.val b) := by
  change offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t
    ((lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m (Pi.single d b)).val) = _
  rw [lowVectorEquiv_single, offDiagonalCorrectedCoordinateEquiv_single]

def offDiagonalCrossingKernelVectorEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (Fin m → Old D Sc cutoff v t) ≃ₗ[k]
      LinearMap.ker (toCyclotomic D Sc cutoff j.1 v t) :=
  (offDiagonalBoundaryKernelVectorEquiv D Sc cutoff p j v t m hm).trans
    (offDiagonalBoundarySnakeKernelEquiv D Sc cutoff p j v t)

/-- The actual boundary snake equals the decoded original long lift in the quotient. -/
theorem offDiagonalBoundarySnake_eq_boundaryCrossCoordinates (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (f : LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t)) :
    offDiagonalBoundarySnake D Sc cutoff p j v t f =
      q D Sc cutoff j.1 v t (offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t f) := by
  exact offDiagonalBoundarySnake_eq_lift D Sc cutoff p j v t f
    (offDiagonalLongSection D Sc cutoff p j.1 v t f)
    (offDiagonalLongExtraction_section D Sc cutoff p j.1 v t f)

/-- The actual cap vector evaluated on the actual snake kernel coordinates. -/
def offDiagonalCapOnKernelVector (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (Fin m → Old D Sc cutoff v t) →ₗ[k] (Fin m → Old D Sc cutoff v t) :=
  (offDiagonalInputCapVector D Sc cutoff j v t m).comp
    ((LinearMap.ker (toCyclotomic D Sc cutoff j.1 v t)).subtype.comp
      (offDiagonalCrossingKernelVectorEquiv D Sc cutoff p j v t m hm).toLinearMap)

theorem offDiagonalCapOnKernelVector_single (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (r d : Fin m) (b : Old D Sc cutoff v t) :
    offDiagonalCapOnKernelVector D Sc cutoff p j v t m hm (Pi.single d b) r =
      offDiagonalInputContractionAffine D Sc cutoff j v t
        ((offDiagonalCrossingInputDotAffine D Sc cutoff j v t)^[r.val]
          (offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t
            (offDiagonalLongExtraction D Sc cutoff p j.1 v t
              (offDiagonalCorrectedLift D Sc cutoff p j v t d.val b)))) := by
  change offDiagonalInputCapVector D Sc cutoff j v t m
    ((offDiagonalCrossingKernelVectorEquiv D Sc cutoff p j v t m hm (Pi.single d b)).val) r = _
  rw [offDiagonalInputCapVector_apply]
  change offDiagonalInputContraction D Sc cutoff j v t
    ((offDiagonalCrossingInputDot D Sc cutoff j v t)^[r.val]
      (offDiagonalBoundarySnake D Sc cutoff p j v t
        (offDiagonalBoundaryKernelVectorEquiv D Sc cutoff p j v t m hm (Pi.single d b)))) = _
  rw [offDiagonalBoundarySnake_eq_boundaryCrossCoordinates, offDiagonalInputContraction_iterate_q,
    offDiagonalBoundaryKernelVectorEquiv_single]

theorem offDiagonalCapOnKernelVector_bijective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    Function.Bijective (offDiagonalCapOnKernelVector D Sc cutoff p j v t m hm) := by
  classical
  let R := reversedVector (k := k) (M := Old D Sc cutoff v t) m
  let F := offDiagonalCapOnKernelVector D Sc cutoff p j v t m hm
  have ht : Function.Bijective (F.comp R.toLinearMap) := by
    apply OddMath.FiniteTriangularCoordinates.bijective m _ (offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t 0)
    · intro a b hab x
      change F (R (Pi.single b x)) a = 0
      rw [reversedVector_single, offDiagonalCapOnKernelVector_single]
      apply offDiagonalInputContractionAffine_corrected_below
      have hb : b.rev.val = m - (b.val + 1) := rfl
      have ha := a.isLt
      have hb' := b.isLt
      have hab' : a.val < b.val := hab
      omega
    · intro a x
      change F (R (Pi.single a x)) a = _
      rw [reversedVector_single, offDiagonalCapOnKernelVector_single]
      apply offDiagonalInputContractionAffine_corrected_pivot
      have ha : a.rev.val = m - (a.val + 1) := rfl
      have ha' := a.isLt
      omega
  constructor
  · intro f g hfg
    have he : R.symm f = R.symm g := by
      apply ht.1
      change F (R (R.symm f)) = F (R (R.symm g))
      simpa only [LinearEquiv.apply_symm_apply] using hfg
    exact R.symm.injective he
  · intro f
    obtain ⟨g, hg⟩ := ht.2 f
    exact ⟨R g, hg⟩

/-- Cap rows detect exactly the kernel of the prescribed crossing. -/
theorem offDiagonalInputCapVector_kernel_bijective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    Function.Bijective ((offDiagonalInputCapVector D Sc cutoff j v t m).comp
      (LinearMap.ker (toCyclotomic D Sc cutoff j.1 v t)).subtype) := by
  let e := offDiagonalCrossingKernelVectorEquiv D Sc cutoff p j v t m hm
  have hb := offDiagonalCapOnKernelVector_bijective D Sc cutoff p j v t m hm
  constructor
  · intro f g hfg
    change offDiagonalInputCapVector D Sc cutoff j v t m f.val = offDiagonalInputCapVector D Sc cutoff j v t m g.val at hfg
    have he : e.symm f = e.symm g := by
      apply hb.1
      change offDiagonalInputCapVector D Sc cutoff j v t m (e (e.symm f)).val =
        offDiagonalInputCapVector D Sc cutoff j v t m (e (e.symm g)).val
      simpa only [LinearEquiv.apply_symm_apply] using hfg
    exact e.symm.injective he
  · intro f
    obtain ⟨g, hg⟩ := hb.2 f
    exact ⟨e g, hg⟩

/-- The negative branch uses the prescribed crossing and actual dotted input contractions. -/
def offDiagonalInputMatrix (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ) :
    Source D Sc cutoff j.1 v t →ₗ[k]
      (Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) × (Fin m → Old D Sc cutoff v t)) :=
  (toCyclotomic D Sc cutoff j.1 v t).prod (offDiagonalInputCapVector D Sc cutoff j v t m)

theorem offDiagonalInputMatrix_bijective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    Function.Bijective (offDiagonalInputMatrix D Sc cutoff j v t m) := by
  have hb := offDiagonalInputCapVector_kernel_bijective D Sc cutoff p j v t m hm
  constructor
  · intro f g hfg
    have hcross := congrArg Prod.fst hfg
    have hcap := congrArg Prod.snd hfg
    change toCyclotomic D Sc cutoff j.1 v t f = toCyclotomic D Sc cutoff j.1 v t g at hcross
    change offDiagonalInputCapVector D Sc cutoff j v t m f = offDiagonalInputCapVector D Sc cutoff j v t m g at hcap
    let d : LinearMap.ker (toCyclotomic D Sc cutoff j.1 v t) :=
      ⟨f - g, by
        change toCyclotomic D Sc cutoff j.1 v t (f - g) = 0
        have hs : toCyclotomic D Sc cutoff j.1 v t (f - g) =
            toCyclotomic D Sc cutoff j.1 v t f - toCyclotomic D Sc cutoff j.1 v t g :=
          map_sub (toCyclotomic D Sc cutoff j.1 v t) f g
        exact hs.trans (sub_eq_zero.mpr hcross)⟩
    have hd : d = 0 := hb.1 (by
      change offDiagonalInputCapVector D Sc cutoff j v t m (f - g) =
        offDiagonalInputCapVector D Sc cutoff j v t m (0 : Source D Sc cutoff j.1 v t)
      have hs : offDiagonalInputCapVector D Sc cutoff j v t m (f - g) =
          offDiagonalInputCapVector D Sc cutoff j v t m f - offDiagonalInputCapVector D Sc cutoff j v t m g :=
        map_sub (offDiagonalInputCapVector D Sc cutoff j v t m) f g
      exact hs.trans ((sub_eq_zero.mpr hcap).trans
        (offDiagonalInputCapVector D Sc cutoff j v t m).map_zero.symm))
    exact sub_eq_zero.mp (congrArg Subtype.val hd)
  · rintro ⟨n, b⟩
    obtain ⟨z, hz⟩ := offDiagonalToCyclotomic_surjective_of_nonpositive_height
      D Sc cutoff p j v t (by omega) n
    obtain ⟨f, hf⟩ := hb.2 (b - offDiagonalInputCapVector D Sc cutoff j v t m z)
    refine ⟨z + f.val, ?_⟩
    apply Prod.ext
    · change toCyclotomic D Sc cutoff j.1 v t (z + f.val) = n
      have hfk := f.property
      change toCyclotomic D Sc cutoff j.1 v t f.val = 0 at hfk
      rw [map_add, hz, hfk, add_zero]
    · change offDiagonalInputCapVector D Sc cutoff j v t m (z + f.val) = b
      rw [map_add]
      change offDiagonalInputCapVector D Sc cutoff j v t m z +
        ((offDiagonalInputCapVector D Sc cutoff j v t m).comp
          (LinearMap.ker (toCyclotomic D Sc cutoff j.1 v t)).subtype) f = b
      rw [hf]
      abel

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

