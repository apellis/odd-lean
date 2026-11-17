import Mathlib.LinearAlgebra.Finsupp.Supported
import OddMath.QuiverHecke.CyclotomicAction.CapInputMatrices.ShiftedCapRows
import OddMath.QuiverHecke.CyclotomicAction.OffDiagonalInput.OffDiagonalInputOperators
import OddMath.QuiverHecke.CyclotomicAction.OffDiagonalInput.UnitPositiveInverse

/-!
# Off diagonal input

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Input contraction pivots on the actual boundary lifts

These are the cap pivots used by DeformedRouquierMatrix, section 4.
The input shift has zero constant coefficient. Hence the actual contraction
of a decoded lift is the constant coefficient of the next boundary value.
This gives anti-diagonal vanishing and the prescribed leading equivalence.
These statements concern the prescribed input operators on arbitrary old
Hom coefficients. Their categorical counit/dot comparison remains separate.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def offDiagonalLiftBoundary (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] AppendTarget D Sc cutoff j.1 v (t ++ [j.1]) :=
  (pMap D Sc cutoff j.1 v (t ++ [j.1])).comp
    (offDiagonalLongSection D Sc cutoff p j.1 v t)

theorem offDiagonalLiftBoundary_rho (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalLiftBoundary D Sc cutoff p j v t
      (offDiagonalCoefficientRho D Sc cutoff p j v t f) =
      appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1
        (offDiagonalLiftBoundary D Sc cutoff p j v t f) := by
  change pMap D Sc cutoff j.1 v (t ++ [j.1])
    (offDiagonalLongSection D Sc cutoff p j.1 v t _) = _
  rw [← boundaryRho_offDiagonalLongSection, pMap_boundaryRho]
  rfl

def offDiagonalBoundaryCrossCoordinates (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] ShortTarget D Sc cutoff j.1 v t :=
  (ShortCrossCoordinates.decode D Sc cutoff j.1 v t).comp
    (offDiagonalLiftBoundary D Sc cutoff p j v t)

theorem offDiagonalCrossingInputDotAffine_boundaryCrossCoordinates (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalCrossingInputDotAffine D Sc cutoff j v t (offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t f) =
      offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t (offDiagonalCoefficientRho D Sc cutoff p j v t f) := by
  change ShortCrossCoordinates.decode D Sc cutoff j.1 v t
    (appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1
      (shortCross D Sc cutoff j.1 v t
        (ShortCrossCoordinates.decode D Sc cutoff j.1 v t (offDiagonalLiftBoundary D Sc cutoff p j v t f)))) = _
  rw [shortCross_decode_residual, map_sub, appendMovingPowerTarget_embedding_one,
    map_sub, ShortCrossCoordinates.decode_embedding, sub_zero,
    ← offDiagonalLiftBoundary_rho]
  rfl

theorem offDiagonalInputContractionAffine_boundaryCrossCoordinates (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalInputContractionAffine D Sc cutoff j v t (offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t f) =
      offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t (offDiagonalCoefficientRho D Sc cutoff p j v t f) 0 := by
  change appendC0InputDefect D Sc cutoff j.1 v t
    (shortCross D Sc cutoff j.1 v t
      (ShortCrossCoordinates.decode D Sc cutoff j.1 v t (offDiagonalLiftBoundary D Sc cutoff p j v t f))) 0 = _
  rw [shortCross_decode_residual, map_sub, appendC0InputDefect_embedding, sub_zero]
  change (appendC0 D Sc cutoff j.1 v t
    (appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1
      (offDiagonalLiftBoundary D Sc cutoff p j v t f)) -
      appendInputShift D Sc cutoff j.1 v t
        (appendC0 D Sc cutoff j.1 v t (offDiagonalLiftBoundary D Sc cutoff p j v t f))) 0 = _
  rw [Finsupp.sub_apply, appendInputShift_zero, sub_zero, ← offDiagonalLiftBoundary_rho]
  rfl

theorem offDiagonalCrossingInputDotAffine_iterate_boundaryCrossCoordinates (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (r : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    (offDiagonalCrossingInputDotAffine D Sc cutoff j v t)^[r] (offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t f) =
      offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t
        ((offDiagonalCoefficientRho D Sc cutoff p j v t)^[r] f) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih,
      offDiagonalCrossingInputDotAffine_boundaryCrossCoordinates, Function.iterate_succ_apply']

theorem offDiagonalInputContractionAffine_corrected_iterate (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (r d : ℕ)
    (b : Old D Sc cutoff v t) :
    offDiagonalInputContractionAffine D Sc cutoff j v t
      ((offDiagonalCrossingInputDotAffine D Sc cutoff j v t)^[r]
        (offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t
          (offDiagonalLongExtraction D Sc cutoff p j.1 v t
            (offDiagonalCorrectedLift D Sc cutoff p j v t d b)))) =
      offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
        (offDiagonalLongExtraction D Sc cutoff p j.1 v t
          (offDiagonalCorrectedLift D Sc cutoff p j v t (r + d + 1) b)) 0 := by
  rw [offDiagonalCrossingInputDotAffine_iterate_boundaryCrossCoordinates,
    offDiagonalInputContractionAffine_boundaryCrossCoordinates]
  simp only [offDiagonalLongExtraction_correctedLift]
  rw [← Function.iterate_add_apply]
  have hs : (offDiagonalCoefficientRho D Sc cutoff p j v t)^[r + d + 1] (Finsupp.single 0 b) =
      offDiagonalCoefficientRho D Sc cutoff p j v t
        ((offDiagonalCoefficientRho D Sc cutoff p j v t)^[r + d] (Finsupp.single 0 b)) :=
    Function.iterate_succ_apply' _ _ _
  rw [hs]

theorem offDiagonalInputContractionAffine_corrected_below (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (r d : ℕ)
    (b : Old D Sc cutoff v t)
    (h : r + d + 1 + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v) :
    offDiagonalInputContractionAffine D Sc cutoff j v t
      ((offDiagonalCrossingInputDotAffine D Sc cutoff j v t)^[r]
        (offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t
          (offDiagonalLongExtraction D Sc cutoff p j.1 v t
            (offDiagonalCorrectedLift D Sc cutoff p j v t d b)))) = 0 := by
  rw [offDiagonalInputContractionAffine_corrected_iterate]
  exact offDiagonalBoundary_corrected_above D Sc cutoff p j v t (r + d + 1) 0 b (by omega)

theorem offDiagonalInputContractionAffine_corrected_pivot (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (r d : ℕ)
    (b : Old D Sc cutoff v t)
    (h : outputSDegree D j.1 v = r + d + 1 + endpointQPDegree D cutoff j.1 v) :
    offDiagonalInputContractionAffine D Sc cutoff j v t
      ((offDiagonalCrossingInputDotAffine D Sc cutoff j v t)^[r]
        (offDiagonalBoundaryCrossCoordinates D Sc cutoff p j v t
          (offDiagonalLongExtraction D Sc cutoff p j.1 v t
            (offDiagonalCorrectedLift D Sc cutoff p j v t d b)))) =
      offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t 0 b := by
  rw [offDiagonalInputContractionAffine_corrected_iterate]
  exact offDiagonalBoundary_corrected_top D Sc cutoff p j v t (r + d + 1) 0 b (by omega)

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # The negative-height crossing and its actual input-contraction rows

DeformedRouquierMatrix, section 4, reduces inversion to these concrete rows.
The cap vector is formed from the descended input contraction and moving
input dot. Its restriction to the concrete snake kernel has the prescribed
anti-triangular pivots. Finite elimination yields the whole raw augmented
matrix on arbitrary old Hom coefficients. Its categorical signed-dot/cap
comparison and naturality are separate obligations; no equality is assumed.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Comparison of categorical cap data with the input matrix

The fixed adjunction counit and induction dot, with the prescribed source
grading, agree with the descended input operators of DeformedMatrixComparison,
section 3, on arbitrary old Hom endpoints. This transfers the input inverse
of DeformedRouquierMatrix, section 4, without another matrix-elimination proof.
The unshifted source and row sign/twist normalization remain separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

@[simp] theorem coefficientOneSourceEquiv_tensor (j : {j : I // D.parity j = 1})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [j.1]) t)
    (b : Old D Sc cutoff v (s ++ [j.1])) :
    coefficientOneSourceEquiv D Sc cutoff j v t
      (BalancedInduction.tensor (append D Sc cutoff j.1)
        (coefficientOneModule D Sc cutoff j.1 v).toFunctor
        (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      tensor D Sc cutoff j.1 v s t g b := by

  change ((BalancedInduction.induction (append D Sc cutoff j.1)).map
    (movingCoefficientBackward D Sc cutoff j v)).total
      (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor (append D Sc cutoff j.1)
        (coefficientOneModule D Sc cutoff j.1 v).toFunctor
        (⟨s⟩ : OldCategory D Sc cutoff) g b) = _
  change (BalancedInduction.moduleMap (append D Sc cutoff j.1)
    (movingCoefficientBackward D Sc cutoff j v)).total _
      (BalancedInduction.tensor _ _ _ g b) = _
  rw [BalancedInduction.moduleMap_total_tensor]
  simp only [movingCoefficientBackward_app, ↓reduceIte, one_ne_zero]
  change BalancedInduction.tensor (append D Sc cutoff j.1)
      (coefficient D Sc cutoff (D.parity j.1) j.1 v)
      (⟨s⟩ : OldCategory D Sc cutoff) g b +
    BalancedInduction.tensor (append D Sc cutoff j.1)
      (coefficient D Sc cutoff (D.parity j.1) j.1 v)
      (⟨s⟩ : OldCategory D Sc cutoff)
      (twist k 1 (X := (append D Sc cutoff j.1).obj (⟨s⟩ : OldCategory D Sc cutoff))
        (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g)
      (0 : Old D Sc cutoff v (s ++ [j.1])) = _
  rw [BalancedInduction.tensor_zero_right, add_zero]
  rfl

theorem sourceInputContraction_tensor (j : {j : I // D.parity j = 1})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [j.1]) t)
    (b : Old D Sc cutoff v (s ++ [j.1])) :
    sourceInputContraction D Sc cutoff j v t (tensor D Sc cutoff j.1 v s t g b) =
      oldComp D Sc cutoff v (s ++ [j.1]) t
        (oldTwist D Sc cutoff 1 v (s ++ [j.1]) b) g := by
  rw [← coefficientOneSourceEquiv_tensor, sourceInputContraction_carrier,
    shiftedInputContraction_tensor]

theorem sourceInputDot_tensor (j : {j : I // D.parity j = 1})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [j.1]) t)
    (b : Old D Sc cutoff v (s ++ [j.1])) :
    sourceInputDot D Sc cutoff j v t (tensor D Sc cutoff j.1 v s t g b) =
      -tensor D Sc cutoff j.1 v s t
        (oldAppendDotComponent D Sc cutoff j.1 (⟨s⟩ : OldCategory D Sc cutoff) ≫ g)
        (oldTwist D Sc cutoff 1 v (s ++ [j.1]) b) := by
  rw [← coefficientOneSourceEquiv_tensor, sourceInputDot_carrier,
    shiftedInputDot_tensor, map_neg, coefficientOneSourceEquiv_tensor]

theorem sourceInputContraction_q (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : ShortTarget D Sc cutoff j.1 v t) :
    sourceInputContraction D Sc cutoff j v t (q D Sc cutoff j.1 v t z) =
      offDiagonalInputContractionAffine D Sc cutoff j v t z := by
  suffices h : (sourceInputContraction D Sc cutoff j v t).comp
      (q D Sc cutoff j.1 v t) = offDiagonalInputContractionAffine D Sc cutoff j v t from
    LinearMap.congr_fun h z
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply]
  change sourceInputContraction D Sc cutoff j v t
    (q D Sc cutoff j.1 v t (shortTensor D Sc cutoff j.1 v s.word t g b)) = _
  rw [q_shortTensor, sourceInputContraction_tensor]
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [j.1])).mkQ_surjective b
  change _ = appendC0InputDefect D Sc cutoff j.1 v t
    (shortCross D Sc cutoff j.1 v t
      (shortTensor D Sc cutoff j.1 v s.word t g ((ideal D Sc cutoff _ _).mkQ r))) 0
  rw [ShortCrossCoordinates.column_mk, appendC0InputDefect_crossing]
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same]
  change (ideal D Sc cutoff v t).mkQ (twist k 1 r ≫ g) = _
  simp [j.property, SKM.zsign]

theorem sourceInputDot_q (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : ShortTarget D Sc cutoff j.1 v t) :
    sourceInputDot D Sc cutoff j v t (q D Sc cutoff j.1 v t z) =
      q D Sc cutoff j.1 v t (offDiagonalCrossingInputDotAffine D Sc cutoff j v t z) := by
  suffices h : (sourceInputDot D Sc cutoff j v t).comp
      (q D Sc cutoff j.1 v t) =
      (q D Sc cutoff j.1 v t).comp (offDiagonalCrossingInputDotAffine D Sc cutoff j v t) from
    LinearMap.congr_fun h z
  apply BalancedInduction.hom_ext
  intro s g b
  change sourceInputDot D Sc cutoff j v t
    (q D Sc cutoff j.1 v t (shortTensor D Sc cutoff j.1 v s.word t g b)) =
    q D Sc cutoff j.1 v t
      (offDiagonalCrossingInputDotAffine D Sc cutoff j v t
        (shortTensor D Sc cutoff j.1 v s.word t g b))
  rw [q_shortTensor, sourceInputDot_tensor]
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [j.1])).mkQ_surjective b
  have hx := offDiagonalCrossingInputDotAffine_representative
    D Sc cutoff j v s.word t r g
  have hq := congrArg (q D Sc cutoff j.1 v t) hx
  rw [map_smul, q_shortTensor] at hq
  rw [hq, oldAppendDotComponent_eq]
  change -tensor D Sc cutoff j.1 v s.word t
      ((ideal D Sc cutoff (s.word ++ [j.1]) t).mkQ
        (appendMovingPower D Sc cutoff j.1 s.word 1 ≫ g))
      ((ideal D Sc cutoff v (s.word ++ [j.1])).mkQ (twist k 1 r)) =
    SKM.zsign k (D.parity j.1 * D.parity j.1) •
      tensor D Sc cutoff j.1 v s.word t
        ((ideal D Sc cutoff (s.word ++ [j.1]) t).mkQ
          (appendMovingPower D Sc cutoff j.1 s.word 1 ≫ g))
        ((ideal D Sc cutoff v (s.word ++ [j.1])).mkQ (twist k (D.parity j.1) r))
  simp [j.property, SKM.zsign]

/-- Equality with the specified input contraction, proved on all balanced classes. -/
theorem sourceInputContraction_eq (j : {j : I // D.parity j = 1}) (v t : List I) :
    sourceInputContraction D Sc cutoff j v t =
      offDiagonalInputContraction D Sc cutoff j v t := by
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ := q_surjective D Sc cutoff j.1 v t z
  rw [sourceInputContraction_q, offDiagonalInputContraction_q]

/-- Equality with the specified input dot, retaining the whole coefficient twist. -/
theorem sourceInputDot_eq (j : {j : I // D.parity j = 1}) (v t : List I) :
    sourceInputDot D Sc cutoff j v t =
      offDiagonalCrossingInputDot D Sc cutoff j v t := by
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ := q_surjective D Sc cutoff j.1 v t z
  rw [sourceInputDot_q, offDiagonalCrossingInputDot_q]

/-- The crossing and rows from the constructed shifted counit and source dot. -/
def offDiagonalShiftedInputMatrix (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ) :
    Source D Sc cutoff j.1 v t →ₗ[k]
      (Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) × (Fin m → Old D Sc cutoff v t)) :=
  (toCyclotomic D Sc cutoff j.1 v t).prod
    (LinearMap.pi fun r : Fin m =>
      (sourceInputContraction D Sc cutoff j v t).comp
        ((sourceInputDot D Sc cutoff j v t) ^ r.val))

theorem offDiagonalShiftedInputMatrix_eq (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ) :
    offDiagonalShiftedInputMatrix D Sc cutoff j v t m =
      offDiagonalInputMatrix D Sc cutoff j v t m := by
  simp only [offDiagonalShiftedInputMatrix, sourceInputContraction_eq, sourceInputDot_eq,
    offDiagonalInputMatrix, offDiagonalInputCapVector]

/-- Transfer of the concrete inverse to the constructed shifted categorical maps. -/
def offDiagonalShiftedInputMatrixEquiv (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    Source D Sc cutoff j.1 v t ≃ₗ[k]
      (Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) × (Fin m → Old D Sc cutoff v t)) :=
  LinearEquiv.ofBijective (offDiagonalShiftedInputMatrix D Sc cutoff j v t m) (by
    rw [offDiagonalShiftedInputMatrix_eq]
    exact offDiagonalInputMatrix_bijective D Sc cutoff p j v t m hm)

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Ordinary dotted-counit input inverse

DeformedMatrixComparison (5) and the input inverse of DeformedRouquierMatrix,
section 4, give the inverse on the canonical induction-restriction carrier.
The cap rows below are the ordinary adjunction counit after induction-dot
powers. The first row is explicitly minus the balanced crossing after the
canonical source equivalence. Its identification with the ordered categorical
mate is a separate obligation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Prescribed whole-output twist and cap scalar, as an invertible row change. -/
def counitInputRowEquiv (v t : List I) (n : ℕ) :
    Old D Sc cutoff v t ≃ₗ[k] Old D Sc cutoff v t :=
  (LinearEquiv.ofInvolutive (oldTwist D Sc cutoff ((n + 1 : ℕ) : ZMod 2) v t)
    (oldTwist_twice D Sc cutoff _ v t)).trans
      (LinearEquiv.smulOfUnit ((-1 : kˣ) ^ (n + 1).choose 2))

@[simp] theorem counitInputRowEquiv_apply (v t : List I) (n : ℕ)
    (b : Old D Sc cutoff v t) :
    counitInputRowEquiv D Sc cutoff v t n b =
      capRowSign (k := k) n • oldTwist D Sc cutoff ((n + 1 : ℕ) : ZMod 2) v t b := by
  change (((-1 : kˣ) ^ (n + 1).choose 2 : kˣ) : k) •
    oldTwist D Sc cutoff ((n + 1 : ℕ) : ZMod 2) v t b = _
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, capRowSign]

/-- The single output change consists of crossing negation and all cap-row changes. -/
def counitInputOutputEquiv (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ) :
    (Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) × (Fin m → Old D Sc cutoff v t)) ≃ₗ[k]
      (Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) × (Fin m → Old D Sc cutoff v t)) :=
  (LinearEquiv.neg k).prodCongr
    (LinearEquiv.piCongrRight fun r : Fin m => counitInputRowEquiv D Sc cutoff v t r.val)

/-- Conjugation of every dot power by the induced coefficient comparison. -/
theorem sourceInputDot_iterate_carrier (j : {j : I // D.parity j = 1})
    (v t : List I) (n : ℕ) (z : shiftedCarrier D Sc cutoff j.1 v t) :
    (sourceInputDot D Sc cutoff j v t)^[n]
        (coefficientOneSourceEquiv D Sc cutoff j v t z) =
      coefficientOneSourceEquiv D Sc cutoff j v t
        ((shiftedInputDot D Sc cutoff j v t)^[n] z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, sourceInputDot_carrier,
      Function.iterate_succ_apply']

/-- Concrete inverse on the ordinary induction-restriction source. -/
def counitInputMatrixEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
      (Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) × (Fin m → Old D Sc cutoff v t)) :=
  ((shiftedSourceCanonicalEquiv D Sc cutoff j v t).trans
    (offDiagonalShiftedInputMatrixEquiv D Sc cutoff p j v t m hm)).trans
      (counitInputOutputEquiv D Sc cutoff j v t m)

@[simp] theorem counitInputMatrixEquiv_fst (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    (counitInputMatrixEquiv D Sc cutoff p j v t m hm z).1 =
      -toCyclotomic D Sc cutoff j.1 v t (shiftedSourceCanonicalEquiv D Sc cutoff j v t z) := rfl

/-- Every remaining row is literally the ordinary adjunction counit after a dot power. -/
theorem counitInputMatrixEquiv_cap (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) (r : Fin m) :
    (counitInputMatrixEquiv D Sc cutoff p j v t m hm z).2 r =
      ((BalancedInduction.adjunctionCounit (append D Sc cutoff j.1)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
          (⟨t⟩ : OldCategory D Sc cutoff)
          ((inductionDot D Sc cutoff j.1
            ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
              (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
            (⟨t⟩ : OldCategory D Sc cutoff))^[r.val] z) := by
  change counitInputRowEquiv D Sc cutoff v t r.val
    (sourceInputContraction D Sc cutoff j v t
      (((sourceInputDot D Sc cutoff j v t) ^ r.val)
        (shiftedSourceCanonicalEquiv D Sc cutoff j v t z))) = _
  rw [counitInputRowEquiv_apply, Module.End.pow_apply,
    shiftedSourceCanonicalEquiv_apply, sourceInputDot_iterate_carrier,
    sourceInputContraction_carrier]
  exact shiftedCapRow_normalization D Sc cutoff j v t r.val z

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Shifted cap-family component coordinates
The cap-row profile of DeformedMatrixComparison section 4, after removing
the common source parity shift, has targets Pi^p(Res Ind M) and Pi^(r p)M.
These are canonical component coordinates and the representable component
inverse. The actual mate evaluation and arbitrary-module transfer remain separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance capFamilyPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- Canonical target parity isomorphisms on the actual cap family. -/
def capFamilyPlainCoordinates (i : I) (v t : List I) (m : ℕ) :
    ((a : Option (Fin m)) →
      (capMatrixFamily D Sc cutoff i
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
    ((((BalancedInduction.restriction (append D Sc cutoff i)).obj
      ((BalancedInduction.induction (append D Sc cutoff i)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) × (Fin m → Old D Sc cutoff v t)) :=
  (LinearEquiv.piOptionEquivProd k).trans
    ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))))) ⟨t⟩).prodCongr
      (LinearEquiv.piCongrRight fun r : Fin m =>
        moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) ⟨t⟩))

/-- Canonical upper-Hom and parity coordinates for the finite cap target. -/
def capFamilyComponentCoordinates (i : I) (v t : List I) (m : ℕ) :
    ((a : Option (Fin m)) →
      (capMatrixFamily D Sc cutoff i
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
    (Old D Sc cutoff (v ++ [i]) (t ++ [i]) × (Fin m → Old D Sc cutoff v t)) :=
  (capFamilyPlainCoordinates D Sc cutoff i v t m).trans
    ((OldInductionRepresentable.upperHomEquiv D Sc cutoff i
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).prodCongr
        (LinearEquiv.refl k _))

/-- Odd negative-height inverse with the literal shifted finite cap target. -/
def capFamilyComponentEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
    ((a : Option (Fin m)) →
      (capMatrixFamily D Sc cutoff j.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :=
  (counitInputMatrixEquiv D Sc cutoff p j v t m hm).trans
    (capFamilyComponentCoordinates D Sc cutoff j.1 v t m).symm

/-- In canonical coordinates the map is the already checked ordinary counit matrix. -/
theorem capFamilyComponentEquiv_coordinates (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    capFamilyComponentCoordinates D Sc cutoff j.1 v t m
      (capFamilyComponentEquiv D Sc cutoff p j v t m hm z) =
      counitInputMatrixEquiv D Sc cutoff p j v t m hm z := by
  exact (capFamilyComponentCoordinates D Sc cutoff j.1 v t m).apply_symm_apply _

/-- The first canonical target coordinate is the specified signed balanced crossing. -/
theorem capFamilyComponentEquiv_fst (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    (capFamilyComponentCoordinates D Sc cutoff j.1 v t m
      (capFamilyComponentEquiv D Sc cutoff p j v t m hm z)).1 =
      -toCyclotomic D Sc cutoff j.1 v t (shiftedSourceCanonicalEquiv D Sc cutoff j v t z) := by
  rw [capFamilyComponentEquiv_coordinates, counitInputMatrixEquiv_fst]

/-- Every remaining canonical target coordinate is the ordinary counit after the dot power. -/
theorem capFamilyComponentEquiv_cap (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) (r : Fin m) :
    (capFamilyComponentCoordinates D Sc cutoff j.1 v t m
      (capFamilyComponentEquiv D Sc cutoff p j v t m hm z)).2 r =
      ((BalancedInduction.adjunctionCounit (append D Sc cutoff j.1)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
          (⟨t⟩ : OldCategory D Sc cutoff)
          ((inductionDot D Sc cutoff j.1
            ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
              (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
            (⟨t⟩ : OldCategory D Sc cutoff))^[r.val] z) := by
  rw [capFamilyComponentEquiv_coordinates]
  exact counitInputMatrixEquiv_cap D Sc cutoff p j v t m hm z r

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end
