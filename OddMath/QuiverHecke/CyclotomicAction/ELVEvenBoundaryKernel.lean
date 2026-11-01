import OddMath.QuiverHecke.CyclotomicAction.ELVEvenCrossingHeight

/-! # The even low window and the crossing kernel

The negative-height kernel identification in DeformedRouquierMatrix, section4,
uses the ordinary even polynomial coefficients. The actual generic snake map
carries precisely that low window onto the balanced crossing kernel.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The literal even low-source polynomial window. -/
def evenBoundaryKernelWindow (i : I) (v t : List I) : Submodule k (ℕ →₀ Old D Sc cutoff v t) :=
  Finsupp.supported (Old D Sc cutoff v t) k
    {d | d + endpointQPDegree D cutoff i v < outputSDegree D i v}

/-- Ordinary coefficient inclusion identifies exactly the even boundary kernel. -/
def evenBoundaryKernelEquiv (p : ZMod 2) (i : I) (hi : D.parity i = 0) (v t : List I) :
    evenBoundaryKernelWindow D Sc cutoff i v t ≃ₗ[k]
      LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p i v t) :=
  LinearEquiv.ofBijective
    ((evenBoundaryKernelWindow D Sc cutoff i v t).subtype.codRestrict _ (by
      intro f
      exact (offDiagonalPolynomialBoundary_even_eq_zero_iff D Sc cutoff p i hi v t f).mpr
        (fun d hd => f.property hd))) (by
    constructor
    · intro f g hfg
      apply Subtype.ext
      exact congrArg (fun z : LinearMap.ker
        (offDiagonalPolynomialBoundary D Sc cutoff p i v t) => z.val) hfg
    · intro f
      refine ⟨⟨f.val, ?_⟩, Subtype.ext rfl⟩
      intro d hd
      exact (offDiagonalPolynomialBoundary_even_eq_zero_iff D Sc cutoff p i hi v t f.val).mp
        (LinearMap.mem_ker.mp f.property) d hd)

@[simp] theorem evenBoundaryKernelEquiv_apply (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (f : evenBoundaryKernelWindow D Sc cutoff i v t) :
    (evenBoundaryKernelEquiv D Sc cutoff p i hi v t f).val = f.val := rfl

/-- The low polynomial coordinates are exactly the kernel of the prescribed crossing. -/
def evenCrossingKernelEquiv (p : ZMod 2) (i : I) (hi : D.parity i = 0) (v t : List I) :
    evenBoundaryKernelWindow D Sc cutoff i v t ≃ₗ[k]
      LinearMap.ker (toCyclotomic D Sc cutoff i v t) :=
  (evenBoundaryKernelEquiv D Sc cutoff p i hi v t).trans
    (offDiagonalBoundarySnakeKernelEquiv D Sc cutoff p i v t)

@[simp] theorem evenCrossingKernelEquiv_apply (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (f : evenBoundaryKernelWindow D Sc cutoff i v t) :
    (evenCrossingKernelEquiv D Sc cutoff p i hi v t f).val =
      offDiagonalBoundarySnake D Sc cutoff p i v t
        (evenBoundaryKernelEquiv D Sc cutoff p i hi v t f) := rfl

/-- Low coefficients may be evaluated on the original long section, as in cap recurrences. -/
theorem evenCrossingKernelEquiv_lift (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (f : evenBoundaryKernelWindow D Sc cutoff i v t) :
    (evenCrossingKernelEquiv D Sc cutoff p i hi v t f).val =
      q D Sc cutoff i v t (ShortCrossCoordinates.decode D Sc cutoff i v t
        (pMap D Sc cutoff i v (t ++ [i]) (offDiagonalLongSection D Sc cutoff p i v t f.val))) := by
  rw [evenCrossingKernelEquiv_apply]
  exact offDiagonalBoundarySnake_eq_lift D Sc cutoff p i v t
    (evenBoundaryKernelEquiv D Sc cutoff p i hi v t f)
    (offDiagonalLongSection D Sc cutoff p i v t f.val)
    (offDiagonalLongExtraction_section D Sc cutoff p i v t f.val)

/-- At height -m the coordinates are literally the polynomials supported below m. -/
theorem evenBoundaryKernelWindow_eq_height (i : I) (v t : List I) (m : ℕ)
    (hm : outputSDegree D i v = endpointQPDegree D cutoff i v + m) :
    evenBoundaryKernelWindow D Sc cutoff i v t =
      Finsupp.supported (Old D Sc cutoff v t) k (Set.Iio m) := by
  unfold evenBoundaryKernelWindow
  congr 1
  ext d
  change d + endpointQPDegree D cutoff i v < outputSDegree D i v ↔ d < m
  omega

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
