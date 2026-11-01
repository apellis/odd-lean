import OddMath.QuiverHecke.CyclotomicAction.ELVBoundarySnake
import OddMath.QuiverHecke.CyclotomicAction.ELVCapInputRecurrence
import Mathlib.LinearAlgebra.Finsupp.Supported
import OddMath.Algebra.FiniteTriangularCoordinates

/-! # The negative-height crossing and its actual input-contraction rows

The cap vector is formed from the descended input contraction and moving
input dot. Its restriction to the concrete snake kernel has the prescribed
anti-triangular pivots. Finite elimination yields the whole raw augmented
matrix, before categorical signed-dot/cap comparison and naturality.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
universe u

private def finIioEquiv (m : ℕ) : Fin m ≃ Set.Iio m where
  toFun i := ⟨i.val, i.isLt⟩
  invFun i := ⟨i.val, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def lowVectorEquiv {k M : Type*} [CommRing k] [AddCommGroup M] [Module k M]
    (m : ℕ) : (Fin m → M) ≃ₗ[k] Finsupp.supported M k (Set.Iio m) :=
  ((Finsupp.linearEquivFunOnFinite k M (Fin m)).symm.trans
    (Finsupp.domLCongr (finIioEquiv m))).trans
      (Finsupp.supportedEquivFinsupp (R := k) (M := M) (Set.Iio m)).symm

private theorem lowVectorEquiv_single {k M : Type*} [CommRing k]
    [AddCommGroup M] [Module k M] (m : ℕ) (d : Fin m) (b : M) :
    ((lowVectorEquiv (k := k) (M := M) m (Pi.single d b) :
      Finsupp.supported M k (Set.Iio m)) : ℕ →₀ M) = Finsupp.single d.val b := by
  simp only [lowVectorEquiv, LinearEquiv.trans_apply,
    Finsupp.linearEquivFunOnFinite_symm_single, Finsupp.domLCongr_single,
    Finsupp.supportedEquivFinsupp_symm_single]
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The raw cap vector uses the actual descended contraction and input dot. -/
def inputCapVector (j : {j : I // D.parity j = 1}) (v : List I) (m : ℕ) :
    Source D Sc cutoff j.1 v v →ₗ[k] (Fin m → Old D Sc cutoff v v) :=
  LinearMap.pi fun r : Fin m =>
    (inputContraction D Sc cutoff j v).comp ((crossingInputDot D Sc cutoff j v) ^ r.val)

@[simp] theorem inputCapVector_apply (j : {j : I // D.parity j = 1})
    (v : List I) (m : ℕ) (s : Source D Sc cutoff j.1 v v) (r : Fin m) :
    inputCapVector D Sc cutoff j v m s r =
      inputContraction D Sc cutoff j v ((crossingInputDot D Sc cutoff j v)^[r.val] s) := by
  exact congrArg (inputContraction D Sc cutoff j v)
    (Module.End.pow_apply (crossingInputDot D Sc cutoff j v) r.val s)

private def kernelWindowVectorEquiv (j : {j : I // D.parity j = 1})
    (v : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (Fin m → Old D Sc cutoff v v) ≃ₗ[k] boundaryKernelWindow D Sc cutoff j v where
  toFun f := ⟨(lowVectorEquiv (k := k) (M := Old D Sc cutoff v v) m f).val, by
    intro d hd
    have hlt : d < m := (lowVectorEquiv (k := k) (M := Old D Sc cutoff v v) m f).property hd
    change d + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v
    omega⟩
  invFun f := (lowVectorEquiv (k := k) (M := Old D Sc cutoff v v) m).symm ⟨f.val, by
    intro d hd
    have hlt := f.property hd
    change d + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v at hlt
    change d < m
    omega⟩
  left_inv f := by
    apply (lowVectorEquiv (k := k) (M := Old D Sc cutoff v v) m).injective
    rw [LinearEquiv.apply_symm_apply]
  right_inv f := by
    apply Subtype.ext
    exact congrArg (fun z : Finsupp.supported (Old D Sc cutoff v v) k (Set.Iio m) => (z : ℕ →₀ Old D Sc cutoff v v)) ((lowVectorEquiv (k := k) (M := Old D Sc cutoff v v) m).apply_symm_apply _)
  map_add' f g := by
    apply Subtype.ext
    exact congrArg (fun z : Finsupp.supported (Old D Sc cutoff v v) k (Set.Iio m) => (z : ℕ →₀ Old D Sc cutoff v v)) (map_add (lowVectorEquiv (k := k) (M := Old D Sc cutoff v v) m) f g)
  map_smul' c f := by
    apply Subtype.ext
    exact congrArg (fun z : Finsupp.supported (Old D Sc cutoff v v) k (Set.Iio m) => (z : ℕ →₀ Old D Sc cutoff v v)) (map_smul (lowVectorEquiv (k := k) (M := Old D Sc cutoff v v) m) c f)

/-- Coordinates in the actual boundary kernel, using the corrected low window. -/
def boundaryKernelVectorEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (Fin m → Old D Sc cutoff v v) ≃ₗ[k]
      LinearMap.ker (outputPolynomialBoundary D Sc cutoff p j v) :=
  (kernelWindowVectorEquiv D Sc cutoff j v m hm).trans
    (boundaryKernelEquiv D Sc cutoff p j v)

theorem boundaryKernelVectorEquiv_single (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (d : Fin m) (b : Old D Sc cutoff v v) :
    ((boundaryKernelVectorEquiv D Sc cutoff p j v m hm (Pi.single d b)) :
      ℕ →₀ Old D Sc cutoff v v) =
      outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v d.val b) := by
  change outputCorrectedCoordinateEquiv D Sc cutoff p j v
    ((lowVectorEquiv (k := k) (M := Old D Sc cutoff v v) m (Pi.single d b)).val) = _
  rw [lowVectorEquiv_single, outputCorrectedCoordinateEquiv_single]

def crossingKernelVectorEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (Fin m → Old D Sc cutoff v v) ≃ₗ[k]
      LinearMap.ker (toCyclotomic D Sc cutoff j.1 v v) :=
  (boundaryKernelVectorEquiv D Sc cutoff p j v m hm).trans
    (boundarySnakeKernelEquiv D Sc cutoff p j v)

/-- The actual boundary snake equals the decoded original long lift in the quotient. -/
theorem boundarySnake_eq_boundaryCrossCoordinates (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (f : LinearMap.ker (outputPolynomialBoundary D Sc cutoff p j v)) :
    boundarySnake D Sc cutoff p j v f =
      q D Sc cutoff j.1 v v (boundaryCrossCoordinates D Sc cutoff p j v f) := by
  exact boundarySnake_eq_lift D Sc cutoff p j v f
    (outputLongSection D Sc cutoff p j.1 v f)
    (outputLongExtraction_section D Sc cutoff p j.1 v f)


private def reversedVector {k M : Type*} [CommRing k] [AddCommGroup M] [Module k M]
    (m : ℕ) : (Fin m → M) ≃ₗ[k] (Fin m → M) where
  toFun f i := f i.rev
  invFun f i := f i.rev
  left_inv f := by ext i; simp only [Fin.rev_rev]
  right_inv f := by ext i; simp only [Fin.rev_rev]
  map_add' f g := rfl
  map_smul' c f := rfl

private theorem reversedVector_single {k M : Type*} [CommRing k]
    [AddCommGroup M] [Module k M] (m : ℕ) (d : Fin m) (b : M) :
    reversedVector (k := k) m (Pi.single d b) = Pi.single d.rev b := by
  classical
  ext i
  change (Pi.single d b : Fin m → M) i.rev = (Pi.single d.rev b : Fin m → M) i
  by_cases hi : i = d.rev
  · subst i; simp
  · have hr : i.rev ≠ d := by
      intro h
      have hh := congrArg Fin.rev h
      simp only [Fin.rev_rev] at hh
      exact hi hh
    simp [hi, hr]

/-- The actual cap vector evaluated on the actual snake kernel coordinates. -/
def capOnKernelVector (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (Fin m → Old D Sc cutoff v v) →ₗ[k] (Fin m → Old D Sc cutoff v v) :=
  (inputCapVector D Sc cutoff j v m).comp
    ((LinearMap.ker (toCyclotomic D Sc cutoff j.1 v v)).subtype.comp
      (crossingKernelVectorEquiv D Sc cutoff p j v m hm).toLinearMap)

theorem capOnKernelVector_single (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (r d : Fin m) (b : Old D Sc cutoff v v) :
    capOnKernelVector D Sc cutoff p j v m hm (Pi.single d b) r =
      inputContractionAffine D Sc cutoff j v
        ((crossingInputDotAffine D Sc cutoff j v)^[r.val]
          (boundaryCrossCoordinates D Sc cutoff p j v
            (outputLongExtraction D Sc cutoff p j.1 v
              (outputCorrectedLift D Sc cutoff p j v d.val b)))) := by
  change inputCapVector D Sc cutoff j v m
    ((crossingKernelVectorEquiv D Sc cutoff p j v m hm (Pi.single d b)).val) r = _
  rw [inputCapVector_apply]
  change inputContraction D Sc cutoff j v
    ((crossingInputDot D Sc cutoff j v)^[r.val]
      (boundarySnake D Sc cutoff p j v
        (boundaryKernelVectorEquiv D Sc cutoff p j v m hm (Pi.single d b)))) = _
  rw [boundarySnake_eq_boundaryCrossCoordinates, inputContraction_iterate_q,
    boundaryKernelVectorEquiv_single]

theorem capOnKernelVector_bijective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    Function.Bijective (capOnKernelVector D Sc cutoff p j v m hm) := by
  classical
  let R := reversedVector (k := k) (M := Old D Sc cutoff v v) m
  let F := capOnKernelVector D Sc cutoff p j v m hm
  have ht : Function.Bijective (F.comp R.toLinearMap) := by
    apply OddMath.FiniteTriangularCoordinates.bijective m _ (outputBoundaryLeadingEquiv D Sc cutoff p j v 0)
    · intro a b hab x
      change F (R (Pi.single b x)) a = 0
      rw [reversedVector_single, capOnKernelVector_single]
      apply inputContractionAffine_corrected_below
      have hb : b.rev.val = m - (b.val + 1) := rfl
      have ha := a.isLt
      have hb' := b.isLt
      have hab' : a.val < b.val := hab
      omega
    · intro a x
      change F (R (Pi.single a x)) a = _
      rw [reversedVector_single, capOnKernelVector_single]
      apply inputContractionAffine_corrected_pivot
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
theorem inputCapVector_kernel_bijective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    Function.Bijective ((inputCapVector D Sc cutoff j v m).comp
      (LinearMap.ker (toCyclotomic D Sc cutoff j.1 v v)).subtype) := by
  let e := crossingKernelVectorEquiv D Sc cutoff p j v m hm
  have hb := capOnKernelVector_bijective D Sc cutoff p j v m hm
  constructor
  · intro f g hfg
    change inputCapVector D Sc cutoff j v m f.val = inputCapVector D Sc cutoff j v m g.val at hfg
    have he : e.symm f = e.symm g := by
      apply hb.1
      change inputCapVector D Sc cutoff j v m (e (e.symm f)).val =
        inputCapVector D Sc cutoff j v m (e (e.symm g)).val
      simpa only [LinearEquiv.apply_symm_apply] using hfg
    exact e.symm.injective he
  · intro f
    obtain ⟨g, hg⟩ := hb.2 f
    exact ⟨e g, hg⟩

/-- The negative branch uses the prescribed crossing and actual dotted input contractions. -/
def negativeCrossingAssembly (j : {j : I // D.parity j = 1})
    (v : List I) (m : ℕ) :
    Source D Sc cutoff j.1 v v →ₗ[k]
      (Old D Sc cutoff (v ++ [j.1]) (v ++ [j.1]) × (Fin m → Old D Sc cutoff v v)) :=
  (toCyclotomic D Sc cutoff j.1 v v).prod (inputCapVector D Sc cutoff j v m)

theorem negativeCrossingAssembly_bijective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    Function.Bijective (negativeCrossingAssembly D Sc cutoff j v m) := by
  have hb := inputCapVector_kernel_bijective D Sc cutoff p j v m hm
  constructor
  · intro f g hfg
    have hcross := congrArg Prod.fst hfg
    have hcap := congrArg Prod.snd hfg
    change toCyclotomic D Sc cutoff j.1 v v f = toCyclotomic D Sc cutoff j.1 v v g at hcross
    change inputCapVector D Sc cutoff j v m f = inputCapVector D Sc cutoff j v m g at hcap
    let d : LinearMap.ker (toCyclotomic D Sc cutoff j.1 v v) :=
      ⟨f - g, by
        change toCyclotomic D Sc cutoff j.1 v v (f - g) = 0
        have hs : toCyclotomic D Sc cutoff j.1 v v (f - g) =
            toCyclotomic D Sc cutoff j.1 v v f - toCyclotomic D Sc cutoff j.1 v v g :=
          map_sub (toCyclotomic D Sc cutoff j.1 v v) f g
        exact hs.trans (sub_eq_zero.mpr hcross)⟩
    have hd : d = 0 := hb.1 (by
      change inputCapVector D Sc cutoff j v m (f - g) =
        inputCapVector D Sc cutoff j v m (0 : Source D Sc cutoff j.1 v v)
      have hs : inputCapVector D Sc cutoff j v m (f - g) =
          inputCapVector D Sc cutoff j v m f - inputCapVector D Sc cutoff j v m g :=
        map_sub (inputCapVector D Sc cutoff j v m) f g
      exact hs.trans ((sub_eq_zero.mpr hcap).trans
        (inputCapVector D Sc cutoff j v m).map_zero.symm))
    exact sub_eq_zero.mp (congrArg Subtype.val hd)
  · rintro ⟨n, b⟩
    obtain ⟨z, hz⟩ := toCyclotomic_surjective_of_nonpositive_height
      D Sc cutoff p j v (by omega) n
    obtain ⟨f, hf⟩ := hb.2 (b - inputCapVector D Sc cutoff j v m z)
    refine ⟨z + f.val, ?_⟩
    apply Prod.ext
    · change toCyclotomic D Sc cutoff j.1 v v (z + f.val) = n
      have hfk := f.property
      change toCyclotomic D Sc cutoff j.1 v v f.val = 0 at hfk
      rw [map_add, hz, hfk, add_zero]
    · change inputCapVector D Sc cutoff j v m (z + f.val) = b
      rw [map_add]
      change inputCapVector D Sc cutoff j v m z +
        ((inputCapVector D Sc cutoff j v m).comp
          (LinearMap.ker (toCyclotomic D Sc cutoff j.1 v v)).subtype) f = b
      rw [hf]
      abel

/-- The whole raw negative-height augmented matrix on the independently defined source. -/
def negativeCrossingEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    Source D Sc cutoff j.1 v v ≃ₗ[k]
      (Old D Sc cutoff (v ++ [j.1]) (v ++ [j.1]) × (Fin m → Old D Sc cutoff v v)) :=
  LinearEquiv.ofBijective (negativeCrossingAssembly D Sc cutoff j v m)
    (negativeCrossingAssembly_bijective D Sc cutoff p j v m hm)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
