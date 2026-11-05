import OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryKernel
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenInputPivots
import Mathlib.LinearAlgebra.Finsupp.Supported
import OddMath.Algebra.FiniteTriangularCoordinates
import OddMath.Algebra.LowPolynomialCoordinates

/-! # The even negative-height input matrix

DeformedRouquierMatrix, section 4: the prescribed even crossing and its
actual descended raw input cap rows form an invertible augmented map.
The ordinary low polynomial coefficients identify the crossing kernel;
its cap matrix has the proved anti-triangular unit pivots on every old Hom.
The categorical coefficient(0) counit comparison remains separate.
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
def evenInputCapVector (i : I) (hi : D.parity i = 0) (v t : List I) (m : ℕ) :
    Source D Sc cutoff i v t →ₗ[k] (Fin m → Old D Sc cutoff v t) :=
  LinearMap.pi fun r : Fin m =>
    (evenInputContraction D Sc cutoff i hi v t).comp ((evenCrossingInputDot D Sc cutoff i hi v t) ^ r.val)

@[simp] theorem evenInputCapVector_apply (i : I) (hi : D.parity i = 0)
    (v t : List I) (m : ℕ) (s : Source D Sc cutoff i v t) (r : Fin m) :
    evenInputCapVector D Sc cutoff i hi v t m s r =
      evenInputContraction D Sc cutoff i hi v t ((evenCrossingInputDot D Sc cutoff i hi v t)^[r.val] s) := by
  exact congrArg (evenInputContraction D Sc cutoff i hi v t)
    (Module.End.pow_apply (evenCrossingInputDot D Sc cutoff i hi v t) r.val s)

private def kernelWindowVectorEquiv (i : I)
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    (Fin m → Old D Sc cutoff v t) ≃ₗ[k] evenBoundaryKernelWindow D Sc cutoff i v t where
  toFun f := ⟨(lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m f).val, by
    intro d hd
    have hlt : d < m := (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m f).property hd
    change d + endpointQPDegree D cutoff i v < outputSDegree D i v
    omega⟩
  invFun f := (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m).symm ⟨f.val, by
    intro d hd
    have hlt := f.property hd
    change d + endpointQPDegree D cutoff i v < outputSDegree D i v at hlt
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

/-- Coordinates in the even boundary kernel, using the ordinary low window. -/
def evenBoundaryKernelVectorEquiv (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    (Fin m → Old D Sc cutoff v t) ≃ₗ[k]
      LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p i v t) :=
  (kernelWindowVectorEquiv D Sc cutoff i v t m hm).trans
    (evenBoundaryKernelEquiv D Sc cutoff p i hi v t)

theorem evenBoundaryKernelVectorEquiv_single (p : ZMod 2)
    (i : I) (hi : D.parity i = 0) (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m)
    (d : Fin m) (b : Old D Sc cutoff v t) :
    ((evenBoundaryKernelVectorEquiv D Sc cutoff p i hi v t m hm (Pi.single d b)) :
      ℕ →₀ Old D Sc cutoff v t) =
      Finsupp.single d.val b := by
  change ((lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m (Pi.single d b)).val) = _
  exact lowVectorEquiv_single m d b

def evenCrossingKernelVectorEquiv (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    (Fin m → Old D Sc cutoff v t) ≃ₗ[k]
      LinearMap.ker (toCyclotomic D Sc cutoff i v t) :=
  (evenBoundaryKernelVectorEquiv D Sc cutoff p i hi v t m hm).trans
    (offDiagonalBoundarySnakeKernelEquiv D Sc cutoff p i v t)

/-- The actual boundary snake equals the decoded original long lift in the quotient. -/
theorem evenBoundarySnake_eq_boundaryCrossCoordinates (p : ZMod 2)
    (i : I) (v t : List I)
    (f : LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p i v t)) :
    offDiagonalBoundarySnake D Sc cutoff p i v t f =
      q D Sc cutoff i v t (evenBoundaryCrossCoordinates D Sc cutoff p i v t f) := by
  exact offDiagonalBoundarySnake_eq_lift D Sc cutoff p i v t f
    (offDiagonalLongSection D Sc cutoff p i v t f)
    (offDiagonalLongExtraction_section D Sc cutoff p i v t f)

/-- The actual cap vector evaluated on the actual snake kernel coordinates. -/
def evenCapOnKernelVector (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    (Fin m → Old D Sc cutoff v t) →ₗ[k] (Fin m → Old D Sc cutoff v t) :=
  (evenInputCapVector D Sc cutoff i hi v t m).comp
    ((LinearMap.ker (toCyclotomic D Sc cutoff i v t)).subtype.comp
      (evenCrossingKernelVectorEquiv D Sc cutoff p i hi v t m hm).toLinearMap)

theorem evenCapOnKernelVector_single (p : ZMod 2)
    (i : I) (hi : D.parity i = 0) (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m)
    (r d : Fin m) (b : Old D Sc cutoff v t) :
    evenCapOnKernelVector D Sc cutoff p i hi v t m hm (Pi.single d b) r =
      evenInputContractionAffine D Sc cutoff i v t
        ((evenCrossingInputDotAffine D Sc cutoff i v t)^[r.val]
          (evenBoundaryCrossCoordinates D Sc cutoff p i v t
            (Finsupp.single d.val b))) := by
  change evenInputCapVector D Sc cutoff i hi v t m
    ((evenCrossingKernelVectorEquiv D Sc cutoff p i hi v t m hm (Pi.single d b)).val) r = _
  rw [evenInputCapVector_apply]
  change evenInputContraction D Sc cutoff i hi v t
    ((evenCrossingInputDot D Sc cutoff i hi v t)^[r.val]
      (offDiagonalBoundarySnake D Sc cutoff p i v t
        (evenBoundaryKernelVectorEquiv D Sc cutoff p i hi v t m hm (Pi.single d b)))) = _
  rw [evenBoundarySnake_eq_boundaryCrossCoordinates, evenInputContraction_iterate_q,
    evenBoundaryKernelVectorEquiv_single]

theorem evenCapOnKernelVector_bijective (p : ZMod 2)
    (i : I) (hi : D.parity i = 0) (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    Function.Bijective (evenCapOnKernelVector D Sc cutoff p i hi v t m hm) := by
  classical
  let R := reversedVector (k := k) (M := Old D Sc cutoff v t) m
  let F := evenCapOnKernelVector D Sc cutoff p i hi v t m hm
  have ht : Function.Bijective (F.comp R.toLinearMap) := by
    apply OddMath.FiniteTriangularCoordinates.bijective m _ (evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t)
    · intro a b hab x
      change F (R (Pi.single b x)) a = 0
      rw [reversedVector_single, evenCapOnKernelVector_single]
      apply evenInputContractionAffine_below D Sc cutoff p i hi v t
      have hb : b.rev.val = m - (b.val + 1) := rfl
      have ha := a.isLt
      have hb' := b.isLt
      have hab' : a.val < b.val := hab
      omega
    · intro a x
      change F (R (Pi.single a x)) a = _
      rw [reversedVector_single, evenCapOnKernelVector_single]
      apply evenInputContractionAffine_pivot D Sc cutoff p i hi v t
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
theorem evenInputCapVector_kernel_bijective (p : ZMod 2)
    (i : I) (hi : D.parity i = 0) (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    Function.Bijective ((evenInputCapVector D Sc cutoff i hi v t m).comp
      (LinearMap.ker (toCyclotomic D Sc cutoff i v t)).subtype) := by
  let e := evenCrossingKernelVectorEquiv D Sc cutoff p i hi v t m hm
  have hb := evenCapOnKernelVector_bijective D Sc cutoff p i hi v t m hm
  constructor
  · intro f g hfg
    change evenInputCapVector D Sc cutoff i hi v t m f.val = evenInputCapVector D Sc cutoff i hi v t m g.val at hfg
    have he : e.symm f = e.symm g := by
      apply hb.1
      change evenInputCapVector D Sc cutoff i hi v t m (e (e.symm f)).val =
        evenInputCapVector D Sc cutoff i hi v t m (e (e.symm g)).val
      simpa only [LinearEquiv.apply_symm_apply] using hfg
    exact e.symm.injective he
  · intro f
    obtain ⟨g, hg⟩ := hb.2 f
    exact ⟨e g, hg⟩

/-- The negative branch uses the prescribed crossing and actual dotted input contractions. -/
def evenInputMatrix (i : I) (hi : D.parity i = 0)
    (v t : List I) (m : ℕ) :
    Source D Sc cutoff i v t →ₗ[k]
      (Old D Sc cutoff (v ++ [i]) (t ++ [i]) × (Fin m → Old D Sc cutoff v t)) :=
  (toCyclotomic D Sc cutoff i v t).prod (evenInputCapVector D Sc cutoff i hi v t m)

theorem evenInputMatrix_bijective (p : ZMod 2)
    (i : I) (hi : D.parity i = 0) (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    Function.Bijective (evenInputMatrix D Sc cutoff i hi v t m) := by
  have hb := evenInputCapVector_kernel_bijective D Sc cutoff p i hi v t m hm
  constructor
  · intro f g hfg
    have hcross := congrArg Prod.fst hfg
    have hcap := congrArg Prod.snd hfg
    change toCyclotomic D Sc cutoff i v t f = toCyclotomic D Sc cutoff i v t g at hcross
    change evenInputCapVector D Sc cutoff i hi v t m f = evenInputCapVector D Sc cutoff i hi v t m g at hcap
    let d : LinearMap.ker (toCyclotomic D Sc cutoff i v t) :=
      ⟨f - g, by
        change toCyclotomic D Sc cutoff i v t (f - g) = 0
        have hs : toCyclotomic D Sc cutoff i v t (f - g) =
            toCyclotomic D Sc cutoff i v t f - toCyclotomic D Sc cutoff i v t g :=
          map_sub (toCyclotomic D Sc cutoff i v t) f g
        exact hs.trans (sub_eq_zero.mpr hcross)⟩
    have hd : d = 0 := hb.1 (by
      change evenInputCapVector D Sc cutoff i hi v t m (f - g) =
        evenInputCapVector D Sc cutoff i hi v t m (0 : Source D Sc cutoff i v t)
      have hs : evenInputCapVector D Sc cutoff i hi v t m (f - g) =
          evenInputCapVector D Sc cutoff i hi v t m f - evenInputCapVector D Sc cutoff i hi v t m g :=
        map_sub (evenInputCapVector D Sc cutoff i hi v t m) f g
      exact hs.trans ((sub_eq_zero.mpr hcap).trans
        (evenInputCapVector D Sc cutoff i hi v t m).map_zero.symm))
    exact sub_eq_zero.mp (congrArg Subtype.val hd)
  · rintro ⟨n, b⟩
    obtain ⟨z, hz⟩ := evenToCyclotomic_surjective_of_nonpositive_height
      D Sc cutoff p i hi v t (by omega) n
    obtain ⟨f, hf⟩ := hb.2 (b - evenInputCapVector D Sc cutoff i hi v t m z)
    refine ⟨z + f.val, ?_⟩
    apply Prod.ext
    · change toCyclotomic D Sc cutoff i v t (z + f.val) = n
      have hfk := f.property
      change toCyclotomic D Sc cutoff i v t f.val = 0 at hfk
      rw [map_add, hz, hfk, add_zero]
    · change evenInputCapVector D Sc cutoff i hi v t m (z + f.val) = b
      rw [map_add]
      change evenInputCapVector D Sc cutoff i hi v t m z +
        ((evenInputCapVector D Sc cutoff i hi v t m).comp
          (LinearMap.ker (toCyclotomic D Sc cutoff i v t)).subtype) f = b
      rw [hf]
      abel

/-- The whole raw negative-height augmented matrix on the independently defined source. -/
def evenInputMatrixEquiv (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    Source D Sc cutoff i v t ≃ₗ[k]
      (Old D Sc cutoff (v ++ [i]) (t ++ [i]) × (Fin m → Old D Sc cutoff v t)) :=
  LinearEquiv.ofBijective (evenInputMatrix D Sc cutoff i hi v t m)
    (evenInputMatrix_bijective D Sc cutoff p i hi v t m hm)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

