import OddMath.QuiverHecke.CyclotomicAction.OffDiagonalLong
import OddMath.QuiverHecke.CyclotomicAction.ChronologicalTails
import OddMath.QuiverHecke.CyclotomicAction.CapInputMatrices
import OddMath.Algebra.LowPolynomialCoordinates
import Mathlib.LinearAlgebra.Finsupp.Supported
import OddMath.Algebra.FiniteTriangularCoordinates

/-!
# Off diagonal input

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Height consequences for the prescribed cyclotomic crossing

The polynomial boundary and actual short-column square give injectivity in
nonnegative KKO height and surjectivity in nonpositive KKO height. These are
diagram chases on the prescribed balanced source, not assumed snake data.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem offDiagonalToCyclotomic_injective_of_nonnegative_height (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Injective (toCyclotomic D Sc cutoff j.1 v t) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨y, rfl⟩ := q_surjective D Sc cutoff j.1 v t z
  have hy : shortCross D Sc cutoff j.1 v t y ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j.1 v (t ++ [j.1])) := by
    rw [LinearMap.mem_ker]
    have he := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j.1 v t) y
    exact he.trans hz
  rw [ker_canonicalAppendTarget] at hy
  obtain ⟨x, hx⟩ := hy
  have hc : appendC0 D Sc cutoff j.1 v t (shortCross D Sc cutoff j.1 v t y) = 0 := by
    have hm : shortCross D Sc cutoff j.1 v t y ∈
        appendCrossingSpan D Sc cutoff j.1 v t := by
      rw [← ShortCrossCoordinates.range_shortCross]
      exact ⟨y, rfl⟩
    rw [← appendC0_ker, LinearMap.mem_ker] at hm
    exact hm
  have hb : offDiagonalLongExtraction D Sc cutoff p j.1 v t x = 0 := by
    apply offDiagonalPolynomialBoundary_injective D Sc cutoff p j v t h
    rw [map_zero, ← appendC0_pMap_offDiagonal, hx]
    exact hc
  have hm : x ∈ LinearMap.range (alpha D Sc cutoff j.1 v t) := by
    rw [← ker_offDiagonalLongExtraction_eq_range_alpha D Sc cutoff p j.1 v t,
      LinearMap.mem_ker]
    exact hb
  obtain ⟨a, ha⟩ := hm
  have he : pprime D Sc cutoff j.1 v t a = y := by
    apply ShortCrossCoordinates.shortCross_injective D Sc cutoff j.1 v t
    have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v t) a
    simp only [LinearMap.comp_apply] at hs
    exact hs.symm.trans (by rw [ha]; exact hx)
  have hq : pprime D Sc cutoff j.1 v t a ∈ LinearMap.ker (q D Sc cutoff j.1 v t) := by
    rw [← range_pprime_eq_ker_q]
    exact ⟨a, rfl⟩
  rw [LinearMap.mem_ker, he] at hq
  exact hq

theorem offDiagonalToCyclotomic_surjective_of_nonpositive_height (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v) :
    Function.Surjective (toCyclotomic D Sc cutoff j.1 v t) := by
  intro n
  obtain ⟨z, rfl⟩ := canonicalAppendTarget_surjective D Sc cutoff j.1 v (t ++ [j.1]) n
  let f := offDiagonalBoundaryRowSection D Sc cutoff p j v t (appendC0 D Sc cutoff j.1 v t z)
  let x := offDiagonalSourceLongSection D Sc cutoff p j.1 v t f
  have hc : z - pMap D Sc cutoff j.1 v (t ++ [j.1]) x ∈
      appendCrossingSpan D Sc cutoff j.1 v t := by
    dsimp only [x, f]
    rw [← appendC0_ker, LinearMap.mem_ker, map_sub, appendC0_pMap_offDiagonal,
      offDiagonalLongExtraction_sourceLongSection, offDiagonalBoundaryRowSection_rightInverse D Sc cutoff p j v t h]
    exact sub_self _
  rw [← ShortCrossCoordinates.range_shortCross] at hc
  obtain ⟨y, hy⟩ := hc
  refine ⟨q D Sc cutoff j.1 v t y, ?_⟩
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j.1 v t) y
  simp only [LinearMap.comp_apply] at hs
  rw [← hs, hy, map_sub]
  have hx : pMap D Sc cutoff j.1 v (t ++ [j.1]) x ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j.1 v (t ++ [j.1])) := by
    rw [ker_canonicalAppendTarget]
    exact ⟨x, rfl⟩
  rw [LinearMap.mem_ker] at hx
  rw [hx, sub_zero]

/-- At height zero the prescribed crossing itself is an equivalence. -/
def offDiagonalToCyclotomicEquiv_zero_height (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v) :
    Source D Sc cutoff j.1 v t ≃ₗ[k] Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) :=
  LinearEquiv.ofBijective (toCyclotomic D Sc cutoff j.1 v t)
    ⟨offDiagonalToCyclotomic_injective_of_nonnegative_height D Sc cutoff p j v t h.ge,
      offDiagonalToCyclotomic_surjective_of_nonpositive_height D Sc cutoff p j v t h.le⟩

@[simp] theorem offDiagonalToCyclotomicEquiv_zero_height_apply (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v)
    (z : Source D Sc cutoff j.1 v t) :
    offDiagonalToCyclotomicEquiv_zero_height D Sc cutoff p j v t h z =
      toCyclotomic D Sc cutoff j.1 v t z := rfl

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # The prescribed crossing with the positive polynomial window

The nonnegative KKO-height branch of the matrix in
`DeformedRouquierMatrix.md` is the actual cyclotomic crossing augmented by
the literal low polynomial columns. Its bijectivity follows from the proved
arbitrary-Hom boundary division and the prescribed short-column diagram.
The old source and target words are independent.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def offDiagonalPositiveCrossingAssembly (j : {j : I // D.parity j = 1}) (v t : List I) :
    (Source D Sc cutoff j.1 v t × offDiagonalBoundaryRowWindow D Sc cutoff j v t) →ₗ[k]
      Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) :=
  (toCyclotomic D Sc cutoff j.1 v t).comp (LinearMap.fst k _ _) +
    (canonicalAppendTarget D Sc cutoff j.1 v (t ++ [j.1])).comp
      ((appendOutputEmbedding D Sc cutoff j.1 v t).comp
        ((offDiagonalBoundaryRowWindow D Sc cutoff j v t).subtype.comp (LinearMap.snd k _ _)))

@[simp] theorem offDiagonalPositiveCrossingAssembly_apply (j : {j : I // D.parity j = 1})
    (v t : List I) (s : Source D Sc cutoff j.1 v t)
    (r : offDiagonalBoundaryRowWindow D Sc cutoff j v t) :
    offDiagonalPositiveCrossingAssembly D Sc cutoff j v t (s, r) =
      toCyclotomic D Sc cutoff j.1 v t s +
        canonicalAppendTarget D Sc cutoff j.1 v (t ++ [j.1])
          (appendOutputEmbedding D Sc cutoff j.1 v t r) := rfl

theorem offDiagonalPositiveCrossingAssembly_injective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Injective (offDiagonalPositiveCrossingAssembly D Sc cutoff j v t) := by
  suffices hzero : ∀ z, offDiagonalPositiveCrossingAssembly D Sc cutoff j v t z = 0 → z = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero (x - y)
    have hs : offDiagonalPositiveCrossingAssembly D Sc cutoff j v t (x - y) = offDiagonalPositiveCrossingAssembly D Sc cutoff j v t x - offDiagonalPositiveCrossingAssembly D Sc cutoff j v t y :=
      map_sub (offDiagonalPositiveCrossingAssembly D Sc cutoff j v t) x y
    exact hs.trans (sub_eq_zero.mpr hxy)
  rintro ⟨s, r⟩ hz
  obtain ⟨y, rfl⟩ := q_surjective D Sc cutoff j.1 v t s
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j.1 v t) y
  simp only [LinearMap.comp_apply] at hs
  have hm : shortCross D Sc cutoff j.1 v t y + appendOutputEmbedding D Sc cutoff j.1 v t r ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j.1 v (t ++ [j.1])) := by
    rw [LinearMap.mem_ker, map_add, hs]
    exact hz
  rw [ker_canonicalAppendTarget] at hm
  obtain ⟨x, hx⟩ := hm
  have hc : appendC0 D Sc cutoff j.1 v t (shortCross D Sc cutoff j.1 v t y) = 0 := by
    apply appendCrossingSpan_le_ker D Sc cutoff j.1 v t
    rw [← ShortCrossCoordinates.range_shortCross]
    exact ⟨y, rfl⟩
  have hb : offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
      (offDiagonalLongExtraction D Sc cutoff p j.1 v t x) = r := by
    rw [← appendC0_pMap_offDiagonal D Sc cutoff p j.1 v t, hx, map_add, hc, appendC0_embedding, zero_add]
  have hrcoord : (offDiagonalBoundaryPositiveEquiv D Sc cutoff p j v t h).symm r = (0, r) := by
    apply (offDiagonalBoundaryPositiveEquiv D Sc cutoff p j v t h).injective
    rw [LinearEquiv.apply_symm_apply, offDiagonalBoundaryPositiveEquiv_apply, map_zero, zero_add]
  have hr : r = 0 := by
    have he := congrArg (fun z => ((offDiagonalBoundaryPositiveEquiv D Sc cutoff p j v t h).symm z).2) hb
    rw [offDiagonalBoundaryPositiveEquiv_symm_boundary, hrcoord] at he
    exact he.symm
  apply Prod.ext
  · change q D Sc cutoff j.1 v t y = 0
    apply offDiagonalToCyclotomic_injective_of_nonnegative_height D Sc cutoff p j v t h
    have hz' : toCyclotomic D Sc cutoff j.1 v t (q D Sc cutoff j.1 v t y) = 0 := by
      simpa only [offDiagonalPositiveCrossingAssembly_apply, hr, ZeroMemClass.coe_zero, map_zero, add_zero] using hz
    exact hz'.trans ((toCyclotomic D Sc cutoff j.1 v t).map_zero.symm)
  · exact hr

theorem offDiagonalPositiveCrossingAssembly_surjective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Surjective (offDiagonalPositiveCrossingAssembly D Sc cutoff j v t) := by
  intro n
  obtain ⟨z, rfl⟩ := canonicalAppendTarget_surjective D Sc cutoff j.1 v (t ++ [j.1]) n
  obtain ⟨⟨f, r⟩, hfr⟩ := (offDiagonalBoundaryPositiveAssembly_bijective D Sc cutoff p j v t h).2
    (appendC0 D Sc cutoff j.1 v t z)
  change offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t f + r =
    appendC0 D Sc cutoff j.1 v t z at hfr
  let x := offDiagonalSourceLongSection D Sc cutoff p j.1 v t f
  have hc : z - pMap D Sc cutoff j.1 v (t ++ [j.1]) x -
      appendOutputEmbedding D Sc cutoff j.1 v t r ∈ appendCrossingSpan D Sc cutoff j.1 v t := by
    rw [← appendC0_ker, LinearMap.mem_ker, map_sub, map_sub, appendC0_pMap_offDiagonal,
      appendC0_embedding]
    dsimp only [x]
    rw [offDiagonalLongExtraction_sourceLongSection, ← hfr]
    abel
  rw [← ShortCrossCoordinates.range_shortCross] at hc
  obtain ⟨y, hy⟩ := hc
  refine ⟨(q D Sc cutoff j.1 v t y, r), ?_⟩
  rw [offDiagonalPositiveCrossingAssembly_apply]
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j.1 v t) y
  simp only [LinearMap.comp_apply] at hs
  rw [← hs, hy, map_sub, map_sub]
  have hx : pMap D Sc cutoff j.1 v (t ++ [j.1]) x ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j.1 v (t ++ [j.1])) := by
    rw [ker_canonicalAppendTarget]
    exact ⟨x, rfl⟩
  rw [LinearMap.mem_ker] at hx
  rw [hx]
  abel

/-- The literal crossing and low polynomial columns form the positive branch. -/
def offDiagonalPositiveCrossingEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    (Source D Sc cutoff j.1 v t × offDiagonalBoundaryRowWindow D Sc cutoff j v t) ≃ₗ[k]
      Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) :=
  LinearEquiv.ofBijective (offDiagonalPositiveCrossingAssembly D Sc cutoff j v t)
    ⟨offDiagonalPositiveCrossingAssembly_injective D Sc cutoff p j v t h,
      offDiagonalPositiveCrossingAssembly_surjective D Sc cutoff p j v t h⟩

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Ordinary-source positive unit-column inverse

DeformedMatrixComparison (4) transports the positive inverse of
DeformedRouquierMatrix, section 4, to the ordinary induction-restriction
source and ordinary unit/dot columns. The first entry is explicitly minus
the balanced crossing after the canonical source equivalence; its ordered
mate identification remains separate. No coefficient elimination is repeated.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Positive inverse on the ordinary source, with the prescribed crossing sign. -/
def unitPositiveMatrixEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    ((((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) × offDiagonalBoundaryRowWindow D Sc cutoff j v t) ≃ₗ[k]
      Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) :=
  (((shiftedSourceCanonicalEquiv D Sc cutoff j v t).trans (LinearEquiv.neg k)).prodCongr
    (LinearEquiv.refl k (offDiagonalBoundaryRowWindow D Sc cutoff j v t))).trans
      (offDiagonalPositiveCrossingEquiv D Sc cutoff p j v t h)

/-- The columns are the normalized ordinary adjunction unit and induction-dot
powers; the first entry is the fixed signed canonical crossing. -/
theorem unitPositiveMatrixEquiv_apply (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v)
    (z : ((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff))
    (r : offDiagonalBoundaryRowWindow D Sc cutoff j v t) :
    unitPositiveMatrixEquiv D Sc cutoff p j v t h (z, r) =
      -toCyclotomic D Sc cutoff j.1 v t (shiftedSourceCanonicalEquiv D Sc cutoff j v t z) +
        unitDotPolynomialMap D Sc cutoff j.1 v t r.val := by
  change toCyclotomic D Sc cutoff j.1 v t
      (-(shiftedSourceCanonicalEquiv D Sc cutoff j v t z)) +
    canonicalAppendTarget D Sc cutoff j.1 v (t ++ [j.1])
      (appendOutputEmbedding D Sc cutoff j.1 v t r.val) = _
  rw [map_neg, unitDotPolynomialMap_eq]
  rfl

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Finite shifted coordinates for the unscaled unit columns

DeformedMatrixComparison (6) uses the explicit diagonal source units d_r.
They convert the literal polynomial columns to the ordinary, unscaled
adjunction-unit/induction-dot columns in the shifted finite source family.
The first coordinate remains the specified signed balanced crossing until
the ordered-mate comparison is proved. No column equality is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open OddMath.LowPolynomialCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance unitFamilyPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- The prescribed dot-power scalar as a unit, including either moving parity. -/
def inductionUnitDotUnit (p : ZMod 2) (n : ℕ) : kˣ where
  val := inductionUnitDotSign (k := k) p n
  inv := inductionUnitDotSign (k := k) p n
  val_inv := Supercategory.sign_mul_self _
  inv_val := Supercategory.sign_mul_self _

@[simp] theorem inductionUnitDotUnit_val (p : ZMod 2) (n : ℕ) :
    (inductionUnitDotUnit (k := k) p n : k) = inductionUnitDotSign (k := k) p n := rfl

/-- The finite coordinate sign change is invertible without a field premise. -/
def unitCoefficientDiagonal (p : ZMod 2) (v t : List I) (m : ℕ) :
    (Fin m → Old D Sc cutoff v t) ≃ₗ[k] (Fin m → Old D Sc cutoff v t) :=
  LinearEquiv.piCongrRight fun r => LinearEquiv.smulOfUnit (inductionUnitDotUnit (k := k) p r.val)

@[simp] theorem unitCoefficientDiagonal_apply (p : ZMod 2) (v t : List I) (m : ℕ)
    (b : Fin m → Old D Sc cutoff v t) (r : Fin m) :
    unitCoefficientDiagonal D Sc cutoff p v t m b r = inductionUnitDotSign (k := k) p r.val • b r := by
  change ((inductionUnitDotUnit (k := k) p r.val : kˣ) : k) • b r = _
  rfl

/-- The source diagonal produces the unscaled ordinary unit/dot columns. -/
theorem unitDotPolynomialMap_diagonal (i : I) (v t : List I) (m : ℕ)
    (b : Fin m → Old D Sc cutoff v t) :
    unitDotPolynomialMap D Sc cutoff i v t
      ((lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m
        (unitCoefficientDiagonal D Sc cutoff (D.parity i) v t m b)).val) =
      ∑ r : Fin m, inductionUnitDotColumn D Sc cutoff i v t r.val (b r) := by
  classical
  let L : (Fin m → Old D Sc cutoff v t) →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
    (unitDotPolynomialMap D Sc cutoff i v t).comp
      ((Finsupp.supported (Old D Sc cutoff v t) k (Set.Iio m)).subtype.comp
        (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m).toLinearMap)
  have hsum : unitCoefficientDiagonal D Sc cutoff (D.parity i) v t m b =
      ∑ r : Fin m, Pi.single r (inductionUnitDotSign (k := k) (D.parity i) r.val • b r) := by
    ext r
    simp only [unitCoefficientDiagonal_apply, Finset.sum_apply, Pi.single_apply]
    simp
  change L (unitCoefficientDiagonal D Sc cutoff (D.parity i) v t m b) = _
  rw [hsum, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  change unitDotPolynomialMap D Sc cutoff i v t
    ((lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m
      (Pi.single r (inductionUnitDotSign (k := k) (D.parity i) r.val • b r))).val) = _
  rw [lowVectorEquiv_single, ← Finsupp.smul_single, map_smul, unitDotPolynomialMap_single]
  exact (inductionUnitDotColumn_apply D Sc cutoff i v t r.val (b r)).symm

/-- Finite vectors identify the literal positive polynomial window. -/
def unitWindowVectorEquiv (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m) :
    (Fin m → Old D Sc cutoff v t) ≃ₗ[k] offDiagonalBoundaryRowWindow D Sc cutoff j v t :=
  (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m).trans
    (LinearEquiv.ofEq _ _ (offDiagonalBoundaryRowWindow_eq_height D Sc cutoff j v t m hm).symm)

private def parityComponentEquiv (p : ZMod 2)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (t : OldCategory D Sc cutoff) :
    ((SKM.homParityShift (k := k) p).obj M).obj t ≃ₗ[k] M.obj t :=
  moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) p).iso M) t

/-- Canonical parity isomorphisms remove the finite source shifts on components. -/
def unitFamilyPlainCoordinates (i : I) (v t : List I) (m : ℕ) :
    ((a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff i
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
    ((((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) × (Fin m → Old D Sc cutoff v t)) :=
  (LinearEquiv.piOptionEquivProd k).trans
    ((parityComponentEquiv D Sc cutoff (D.parity i)
      ((BalancedInduction.induction (append D Sc cutoff i)).obj
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))) ⟨t⟩).prodCongr
      (LinearEquiv.piCongrRight fun r : Fin m => parityComponentEquiv D Sc cutoff
        (r.val • D.parity i) (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) ⟨t⟩))

/-- The explicit diagonal source units followed by the literal polynomial window. -/
def unitFamilyComponentCoordinates (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m) :
    ((a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff j.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
    ((((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) × offDiagonalBoundaryRowWindow D Sc cutoff j v t) :=
  (unitFamilyPlainCoordinates D Sc cutoff j.1 v t m).trans
    ((LinearEquiv.refl k _).prodCongr
      ((unitCoefficientDiagonal D Sc cutoff (D.parity j.1) v t m).trans
        (unitWindowVectorEquiv D Sc cutoff j v t m hm)))

/-- Component inverse with the prescribed unscaled unit columns on the shifted source family. -/
def unitFamilyComponentEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m) :
    ((a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff j.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
      Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) :=
  (unitFamilyComponentCoordinates D Sc cutoff j v t m hm).trans
    (unitPositiveMatrixEquiv D Sc cutoff p j v t (by omega))

/-- Every unit slot is the ordinary, unscaled adjunction-unit/dot column.
The first slot remains the specified signed balanced crossing until the mate comparison. -/
theorem unitFamilyComponentEquiv_apply (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m)
    (x : (a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff j.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :
    unitFamilyComponentEquiv D Sc cutoff p j v t m hm x =
      -toCyclotomic D Sc cutoff j.1 v t
        (shiftedSourceCanonicalEquiv D Sc cutoff j v t
          (unitFamilyPlainCoordinates D Sc cutoff j.1 v t m x).1) +
      ∑ r : Fin m, inductionUnitDotColumn D Sc cutoff j.1 v t r.val
        ((unitFamilyPlainCoordinates D Sc cutoff j.1 v t m x).2 r) := by
  rw [unitFamilyComponentEquiv, LinearEquiv.trans_apply]
  rw [show (unitFamilyComponentCoordinates D Sc cutoff j v t m hm x) =
      ((unitFamilyPlainCoordinates D Sc cutoff j.1 v t m x).1,
        unitWindowVectorEquiv D Sc cutoff j v t m hm
          (unitCoefficientDiagonal D Sc cutoff (D.parity j.1) v t m
            (unitFamilyPlainCoordinates D Sc cutoff j.1 v t m x).2)) from rfl,
    unitPositiveMatrixEquiv_apply]
  congr 1
  change unitDotPolynomialMap D Sc cutoff j.1 v t
    ((lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m
      (unitCoefficientDiagonal D Sc cutoff (D.parity j.1) v t m
        (unitFamilyPlainCoordinates D Sc cutoff j.1 v t m x).2)).val) = _
  exact unitDotPolynomialMap_diagonal D Sc cutoff j.1 v t m _

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # The actual boundary-kernel map into the prescribed crossing source

The kernel arrow in the snake sequence of `DeformedRouquierMatrix.md` is
constructed from the existing source section, P map and short-cross decoder.
Its image is the kernel of the actual cyclotomic crossing. No exact-sequence
or faithful-action hypothesis is supplied. The construction and exactness
are valid for every moving colour; parity enters the subsequent row and cap
normal forms rather than this snake comparison.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem offDiagonalShortCross_decode_of_mem (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i]))
    (hz : z ∈ appendCrossingSpan D Sc cutoff i v t) :
    shortCross D Sc cutoff i v t (ShortCrossCoordinates.decode D Sc cutoff i v t z) = z := by
  rw [← ShortCrossCoordinates.range_shortCross] at hz
  obtain ⟨y, rfl⟩ := hz
  rw [ShortCrossCoordinates.decode_shortCross]

def offDiagonalBoundarySnake (p : ZMod 2) (j : I) (v t : List I) :
    LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j v t) →ₗ[k]
      Source D Sc cutoff j v t :=
  q D Sc cutoff j v t ∘ₗ ShortCrossCoordinates.decode D Sc cutoff j v t ∘ₗ
    pMap D Sc cutoff j v (t ++ [j]) ∘ₗ offDiagonalSourceLongSection D Sc cutoff p j v t ∘ₗ
      (LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j v t)).subtype

theorem offDiagonalBoundarySnake_lift (p : ZMod 2) (j : I) (v t : List I)
    (f : LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j v t)) :
    shortCross D Sc cutoff j v t
      (ShortCrossCoordinates.decode D Sc cutoff j v t
        (pMap D Sc cutoff j v (t ++ [j]) (offDiagonalSourceLongSection D Sc cutoff p j v t f))) =
      pMap D Sc cutoff j v (t ++ [j]) (offDiagonalSourceLongSection D Sc cutoff p j v t f) := by
  apply offDiagonalShortCross_decode_of_mem
  rw [← appendC0_ker, LinearMap.mem_ker, appendC0_pMap_offDiagonal,
    offDiagonalLongExtraction_sourceLongSection]
  exact f.property

theorem offDiagonalToCyclotomic_boundarySnake (p : ZMod 2)
    (j : I) (v t : List I)
    (f : LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j v t)) :
    toCyclotomic D Sc cutoff j v t (offDiagonalBoundarySnake D Sc cutoff p j v t f) = 0 := by
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j v t)
    (ShortCrossCoordinates.decode D Sc cutoff j v t
      (pMap D Sc cutoff j v (t ++ [j]) (offDiagonalSourceLongSection D Sc cutoff p j v t f)))
  simp only [LinearMap.comp_apply] at hs
  change _ = toCyclotomic D Sc cutoff j v t (offDiagonalBoundarySnake D Sc cutoff p j v t f) at hs
  rw [← hs, offDiagonalBoundarySnake_lift]
  have hm : pMap D Sc cutoff j v (t ++ [j]) (offDiagonalSourceLongSection D Sc cutoff p j v t f) ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j v (t ++ [j])) := by
    rw [ker_canonicalAppendTarget]
    exact ⟨_, rfl⟩
  exact hm

theorem offDiagonalBoundarySnake_injective (p : ZMod 2)
    (j : I) (v t : List I) :
    Function.Injective (offDiagonalBoundarySnake D Sc cutoff p j v t) := by
  suffices hzero : ∀ z, offDiagonalBoundarySnake D Sc cutoff p j v t z = 0 → z = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero (x - y)
    have hs : offDiagonalBoundarySnake D Sc cutoff p j v t (x - y) = offDiagonalBoundarySnake D Sc cutoff p j v t x - offDiagonalBoundarySnake D Sc cutoff p j v t y :=
      map_sub (offDiagonalBoundarySnake D Sc cutoff p j v t) x y
    exact hs.trans (sub_eq_zero.mpr hxy)
  intro f hf
  have hy : ShortCrossCoordinates.decode D Sc cutoff j v t
      (pMap D Sc cutoff j v (t ++ [j]) (offDiagonalSourceLongSection D Sc cutoff p j v t f)) ∈
      LinearMap.ker (q D Sc cutoff j v t) := hf
  rw [← range_pprime_eq_ker_q] at hy
  obtain ⟨a, ha⟩ := hy
  have he : alpha D Sc cutoff j v t a = offDiagonalSourceLongSection D Sc cutoff p j v t f := by
    apply pMap_injective D Sc cutoff j v (t ++ [j])
    have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j v t) a
    simp only [LinearMap.comp_apply] at hs
    exact hs.trans (by rw [ha, offDiagonalBoundarySnake_lift])
  have hb := congrArg (offDiagonalLongExtraction D Sc cutoff p j v t) he
  rw [offDiagonalLongExtraction_alpha, offDiagonalLongExtraction_sourceLongSection] at hb
  exact Subtype.ext hb.symm

/-- Changing the source lift by its prescribed short coordinate does not
change the cyclotomic snake class. This permits using the original corrected
rho lifts in subsequent cap recurrences. -/
theorem offDiagonalBoundarySnake_eq_lift (p : ZMod 2)
    (j : I) (v t : List I)
    (f : LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j v t))
    (z : Target D Sc cutoff j v (t ++ [j]))
    (hz : offDiagonalLongExtraction D Sc cutoff p j v t z = f) :
    offDiagonalBoundarySnake D Sc cutoff p j v t f =
      q D Sc cutoff j v t (ShortCrossCoordinates.decode D Sc cutoff j v t
        (pMap D Sc cutoff j v (t ++ [j]) z)) := by
  have he := offDiagonalSource_reconstruction D Sc cutoff p j v t z
  rw [hz] at he
  rw [← he, map_add]
  have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j v t)
    (extract D Sc cutoff j v t z)
  simp only [LinearMap.comp_apply] at hs
  rw [hs, map_add, ShortCrossCoordinates.decode_shortCross, map_add]
  have hq : q D Sc cutoff j v t
      (pprime D Sc cutoff j v t (extract D Sc cutoff j v t z)) = 0 := by
    have hm : pprime D Sc cutoff j v t (extract D Sc cutoff j v t z) ∈
        LinearMap.ker (q D Sc cutoff j v t) := by
      rw [← range_pprime_eq_ker_q]
      exact ⟨_, rfl⟩
    exact hm
  rw [hq, zero_add]
  rfl

theorem offDiagonalRange_boundarySnake (p : ZMod 2)
    (j : I) (v t : List I) :
    LinearMap.range (offDiagonalBoundarySnake D Sc cutoff p j v t) =
      LinearMap.ker (toCyclotomic D Sc cutoff j v t) := by
  apply le_antisymm
  · rintro z ⟨f, rfl⟩
    exact offDiagonalToCyclotomic_boundarySnake D Sc cutoff p j v t f
  · intro z hz
    obtain ⟨y, rfl⟩ := q_surjective D Sc cutoff j v t z
    have hy : shortCross D Sc cutoff j v t y ∈
        LinearMap.ker (canonicalAppendTarget D Sc cutoff j v (t ++ [j])) := by
      rw [LinearMap.mem_ker]
      have he := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j v t) y
      exact he.trans hz
    rw [ker_canonicalAppendTarget] at hy
    obtain ⟨x, hx⟩ := hy
    have hc : appendC0 D Sc cutoff j v t (shortCross D Sc cutoff j v t y) = 0 := by
      apply appendCrossingSpan_le_ker D Sc cutoff j v t
      rw [← ShortCrossCoordinates.range_shortCross]
      exact ⟨y, rfl⟩
    let f : LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j v t) :=
      ⟨offDiagonalLongExtraction D Sc cutoff p j v t x, by
        rw [LinearMap.mem_ker, ← appendC0_pMap_offDiagonal D Sc cutoff p j v t, hx]
        exact hc⟩
    let a := extract D Sc cutoff j v t x
    have he : y = pprime D Sc cutoff j v t a +
        ShortCrossCoordinates.decode D Sc cutoff j v t
          (pMap D Sc cutoff j v (t ++ [j]) (offDiagonalSourceLongSection D Sc cutoff p j v t f)) := by
      apply ShortCrossCoordinates.shortCross_injective D Sc cutoff j v t
      rw [map_add, offDiagonalBoundarySnake_lift]
      have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j v t) a
      simp only [LinearMap.comp_apply] at hs
      rw [← hs, ← map_add, offDiagonalSource_reconstruction, hx]
    refine ⟨f, ?_⟩
    have hqa : q D Sc cutoff j v t (pprime D Sc cutoff j v t a) = 0 := by
      have hm : pprime D Sc cutoff j v t a ∈ LinearMap.ker (q D Sc cutoff j v t) := by
        rw [← range_pprime_eq_ker_q]
        exact ⟨a, rfl⟩
      exact hm
    rw [he, map_add, hqa, zero_add]
    rfl

/-- The actual kernel of the prescribed cyclotomic crossing is the boundary kernel. -/
def offDiagonalBoundarySnakeKernelEquiv (p : ZMod 2)
    (j : I) (v t : List I) :
    LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j v t) ≃ₗ[k]
      LinearMap.ker (toCyclotomic D Sc cutoff j v t) :=
  LinearEquiv.ofBijective
    ((offDiagonalBoundarySnake D Sc cutoff p j v t).codRestrict _
      (fun f => offDiagonalToCyclotomic_boundarySnake D Sc cutoff p j v t f))
    ⟨fun f g hfg => offDiagonalBoundarySnake_injective D Sc cutoff p j v t (congrArg Subtype.val hfg),
      by
        intro z
        have hz : z.1 ∈ LinearMap.range (offDiagonalBoundarySnake D Sc cutoff p j v t) := by
          rw [offDiagonalRange_boundarySnake]
          exact z.property
        obtain ⟨f, hf⟩ := hz
        exact ⟨f, Subtype.ext hf⟩⟩

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Input contraction and moving dot on arbitrary old Hom coefficients

The input-oriented maps of DeformedMatrixComparison, section 3, are the
prescribed append defect and moving operator. They descend through the
Pprime relations. Corrected-rho preservation of the long-extraction kernel
proves descent. These are concrete input-oriented operators on Source;
their categorical counit/dot comparison is a separate obligation.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem offDiagonalInputDefect_pMap_alpha (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (a : CyclotomicCrossingTensor.PprimeDomain D Sc cutoff j.1 v t) :
    appendC0InputDefect D Sc cutoff j.1 v t
      (pMap D Sc cutoff j.1 v (t ++ [j.1])
        (CyclotomicCrossingTensor.alpha D Sc cutoff j.1 v t a)) = 0 := by
  have h0 : appendC0 D Sc cutoff j.1 v t
      (pMap D Sc cutoff j.1 v (t ++ [j.1])
        (CyclotomicCrossingTensor.alpha D Sc cutoff j.1 v t a)) = 0 := by
    rw [appendC0_pMap_offDiagonal D Sc cutoff p j.1 v t,
      CyclotomicCrossingTensor.offDiagonalLongExtraction_alpha, map_zero]
  have h1 : appendC0 D Sc cutoff j.1 v t
      (appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1
        (pMap D Sc cutoff j.1 v (t ++ [j.1])
          (CyclotomicCrossingTensor.alpha D Sc cutoff j.1 v t a))) = 0 := by
    rw [← pMap_boundaryRho, appendC0_pMap_offDiagonal D Sc cutoff p j.1 v t,
      offDiagonalLongExtraction_boundaryRho,
      CyclotomicCrossingTensor.offDiagonalLongExtraction_alpha, map_zero, map_zero]
  simp only [appendC0InputDefect, LinearMap.sub_apply, LinearMap.comp_apply,
    h0, h1, map_zero, sub_self]

/-- Vanishing on the independently prescribed Pprime relation, before quotient. -/
theorem offDiagonalInputDefect_shortCross_pprime (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (a : CyclotomicCrossingTensor.PprimeDomain D Sc cutoff j.1 v t) :
    appendC0InputDefect D Sc cutoff j.1 v t
      (CyclotomicCrossingTensor.shortCross D Sc cutoff j.1 v t
        (CyclotomicCrossingTensor.pprime D Sc cutoff j.1 v t a)) = 0 := by
  have hs := LinearMap.congr_fun
    (CyclotomicCrossingTensor.shortColumn_square D Sc cutoff j.1 v t) a
  simp only [LinearMap.comp_apply] at hs
  rw [← hs]
  exact offDiagonalInputDefect_pMap_alpha D Sc cutoff p j v t a

namespace CyclotomicCrossingTensor

/-- The actual polynomial-constant contraction before the cyclotomic quotient. -/
def offDiagonalInputContractionAffine (j : {j : I // D.parity j = 1}) (v t : List I) :
    ShortTarget D Sc cutoff j.1 v t →ₗ[k] Old D Sc cutoff v t where
  toFun z := appendC0InputDefect D Sc cutoff j.1 v t
    (shortCross D Sc cutoff j.1 v t z) 0
  map_add' a b := by simp only [map_add, Finsupp.add_apply]
  map_smul' a b := by simp only [map_smul, Finsupp.smul_apply, RingHom.id_apply]

theorem offDiagonalInputContractionAffine_ker_q (j : {j : I // D.parity j = 1}) (v t : List I) :
    LinearMap.ker (q D Sc cutoff j.1 v t) ≤
      LinearMap.ker (offDiagonalInputContractionAffine D Sc cutoff j v t) := by
  rw [← range_pprime_eq_ker_q]
  rintro z ⟨a, rfl⟩
  change appendC0InputDefect D Sc cutoff j.1 v t
    (shortCross D Sc cutoff j.1 v t (pprime D Sc cutoff j.1 v t a)) 0 = 0
  rw [offDiagonalInputDefect_shortCross_pprime D Sc cutoff 0 j v t, Finsupp.zero_apply]

/-- Descent of this specified contraction to the original cyclotomic source.
No cap comparison or arbitrary replacement row is supplied as a hypothesis. -/
def offDiagonalInputContraction (j : {j : I // D.parity j = 1}) (v t : List I) :
    Source D Sc cutoff j.1 v t →ₗ[k] Old D Sc cutoff v t :=
  ((LinearMap.ker (q D Sc cutoff j.1 v t)).liftQ
    (offDiagonalInputContractionAffine D Sc cutoff j v t)
    (offDiagonalInputContractionAffine_ker_q D Sc cutoff j v t)).comp
      ((q D Sc cutoff j.1 v t).quotKerEquivOfSurjective
        (q_surjective D Sc cutoff j.1 v t)).symm.toLinearMap

@[simp] theorem offDiagonalInputContraction_q (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : ShortTarget D Sc cutoff j.1 v t) :
    offDiagonalInputContraction D Sc cutoff j v t (q D Sc cutoff j.1 v t z) =
      offDiagonalInputContractionAffine D Sc cutoff j v t z := by
  simp only [offDiagonalInputContraction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

def offDiagonalCrossingInputDotAffine (j : {j : I // D.parity j = 1}) (v t : List I) :
    ShortTarget D Sc cutoff j.1 v t →ₗ[k] ShortTarget D Sc cutoff j.1 v t :=
  ShortCrossCoordinates.decode D Sc cutoff j.1 v t ∘ₗ
    appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1 ∘ₗ
      shortCross D Sc cutoff j.1 v t

/-- The moving input dot sends every Pprime relation to another Pprime relation. -/
theorem offDiagonalCrossingInputDotAffine_pprime (j : {j : I // D.parity j = 1}) (v t : List I)
    (a : PprimeDomain D Sc cutoff j.1 v t) :
    offDiagonalCrossingInputDotAffine D Sc cutoff j v t (pprime D Sc cutoff j.1 v t a) ∈
      LinearMap.range (pprime D Sc cutoff j.1 v t) := by
  have hz : boundaryRho D Sc cutoff j v (t ++ [j.1]) (alpha D Sc cutoff j.1 v t a) ∈
      LinearMap.range (alpha D Sc cutoff j.1 v t) := by
    rw [← ker_offDiagonalLongExtraction_eq_range_alpha D Sc cutoff 0 j.1 v t,
      LinearMap.mem_ker, offDiagonalLongExtraction_boundaryRho,
      offDiagonalLongExtraction_alpha, map_zero]
  obtain ⟨a', ha'⟩ := hz
  refine ⟨a', ?_⟩
  change pprime D Sc cutoff j.1 v t a' =
    ShortCrossCoordinates.decode D Sc cutoff j.1 v t
      (appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1
        (shortCross D Sc cutoff j.1 v t (pprime D Sc cutoff j.1 v t a)))
  have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v t) a
  have hs' := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v t) a'
  simp only [LinearMap.comp_apply] at hs hs'
  rw [← hs, ← pMap_boundaryRho, ← ha', hs', ShortCrossCoordinates.decode_shortCross]

theorem offDiagonalCrossingInputDotAffine_ker_q (j : {j : I // D.parity j = 1}) (v t : List I) :
    LinearMap.ker (q D Sc cutoff j.1 v t) ≤
      (LinearMap.ker (q D Sc cutoff j.1 v t)).comap
        (offDiagonalCrossingInputDotAffine D Sc cutoff j v t) := by
  intro z hz
  rw [← range_pprime_eq_ker_q] at hz
  obtain ⟨a, rfl⟩ := hz
  change offDiagonalCrossingInputDotAffine D Sc cutoff j v t (pprime D Sc cutoff j.1 v t a) ∈
    LinearMap.ker (q D Sc cutoff j.1 v t)
  rw [← range_pprime_eq_ker_q]
  exact offDiagonalCrossingInputDotAffine_pprime D Sc cutoff j v t a

/-- Concrete transport of the moving input dot to the original cyclotomic source. -/
def offDiagonalCrossingInputDot (j : {j : I // D.parity j = 1}) (v t : List I) :
    Source D Sc cutoff j.1 v t →ₗ[k] Source D Sc cutoff j.1 v t :=
  let e := (q D Sc cutoff j.1 v t).quotKerEquivOfSurjective (q_surjective D Sc cutoff j.1 v t)
  e.toLinearMap ∘ₗ
    (LinearMap.ker (q D Sc cutoff j.1 v t)).mapQ
      (LinearMap.ker (q D Sc cutoff j.1 v t)) (offDiagonalCrossingInputDotAffine D Sc cutoff j v t)
      (offDiagonalCrossingInputDotAffine_ker_q D Sc cutoff j v t) ∘ₗ e.symm.toLinearMap

@[simp] theorem offDiagonalCrossingInputDot_q (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : ShortTarget D Sc cutoff j.1 v t) :
    offDiagonalCrossingInputDot D Sc cutoff j v t (q D Sc cutoff j.1 v t z) =
      q D Sc cutoff j.1 v t (offDiagonalCrossingInputDotAffine D Sc cutoff j v t z) := by
  simp only [offDiagonalCrossingInputDot, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.mapQ_apply,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- Signed source-dot formula on full-coefficient representatives. -/
theorem offDiagonalCrossingInputDotAffine_representative (j : {j : I // D.parity j = 1})
    (v s t : List I) (r : hom D Sc cutoff v (s ++ [j.1]))
    (g : hom D Sc cutoff (s ++ [j.1]) t) :
    offDiagonalCrossingInputDotAffine D Sc cutoff j v t
      (shortTensor D Sc cutoff j.1 v s t g ((ideal D Sc cutoff v (s ++ [j.1])).mkQ r)) =
      SKM.zsign k (D.parity j.1 * D.parity j.1) •
        shortTensor D Sc cutoff j.1 v s t
          (appendMovingPower D Sc cutoff j.1 s 1 ≫ g)
          ((ideal D Sc cutoff v (s ++ [j.1])).mkQ (twist k (D.parity j.1) r)) := by
  change ShortCrossCoordinates.decode D Sc cutoff j.1 v t
    (appendMovingPowerTarget D Sc cutoff j.1 v (t ++ [j.1]) 1
      (shortCross D Sc cutoff j.1 v t
        (shortTensor D Sc cutoff j.1 v s t g ((ideal D Sc cutoff _ _).mkQ r)))) = _
  rw [ShortCrossCoordinates.column_mk, appendMovingPowerTarget_crossing_one]
  simp only [map_sub, map_smul, ShortCrossCoordinates.decode_embedding, smul_zero, sub_zero]
  rw [← ShortCrossCoordinates.column_mk, ShortCrossCoordinates.decode_shortCross]

theorem offDiagonalCrossingInputDot_iterate_q (j : {j : I // D.parity j = 1}) (v t : List I)
    (r : ℕ) (z : ShortTarget D Sc cutoff j.1 v t) :
    (offDiagonalCrossingInputDot D Sc cutoff j v t)^[r] (q D Sc cutoff j.1 v t z) =
      q D Sc cutoff j.1 v t ((offDiagonalCrossingInputDotAffine D Sc cutoff j v t)^[r] z) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, offDiagonalCrossingInputDot_q, Function.iterate_succ_apply']

theorem offDiagonalInputContraction_iterate_q (j : {j : I // D.parity j = 1}) (v t : List I)
    (r : ℕ) (z : ShortTarget D Sc cutoff j.1 v t) :
    offDiagonalInputContraction D Sc cutoff j v t
      ((offDiagonalCrossingInputDot D Sc cutoff j v t)^[r] (q D Sc cutoff j.1 v t z)) =
      offDiagonalInputContractionAffine D Sc cutoff j v t ((offDiagonalCrossingInputDotAffine D Sc cutoff j v t)^[r] z) := by
  rw [offDiagonalCrossingInputDot_iterate_q, offDiagonalInputContraction_q]

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld
end

end

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
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end
