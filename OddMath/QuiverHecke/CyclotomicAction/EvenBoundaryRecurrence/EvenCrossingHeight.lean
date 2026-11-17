import OddMath.QuiverHecke.CyclotomicAction.EvenBoundaryRecurrence.EvenCoefficientModule
import OddMath.QuiverHecke.CyclotomicAction.OffDiagonalInput.UnitPositiveInverse

/-!
# Even boundary recurrence

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Even crossing height consequences

The parity-zero polynomial division in DeformedBoundaryDivision (5) gives
injectivity or surjectivity of the prescribed balanced crossing in the two
height ranges of DeformedRouquierMatrix, section 4. The same generic snake
comparison identifies its kernel with the even polynomial boundary kernel.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem evenToCyclotomic_injective_of_nonnegative_height (p : ZMod 2)
    (j : I) (hj : D.parity j = 0) (v t : List I)
    (h : outputSDegree D j v ≤ endpointQPDegree D cutoff j v) :
    Function.Injective (toCyclotomic D Sc cutoff j v t) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨y, rfl⟩ := q_surjective D Sc cutoff j v t z
  have hy : shortCross D Sc cutoff j v t y ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j v (t ++ [j])) := by
    rw [LinearMap.mem_ker]
    have he := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j v t) y
    exact he.trans hz
  rw [ker_canonicalAppendTarget] at hy
  obtain ⟨x, hx⟩ := hy
  have hc : appendC0 D Sc cutoff j v t (shortCross D Sc cutoff j v t y) = 0 := by
    have hm : shortCross D Sc cutoff j v t y ∈
        appendCrossingSpan D Sc cutoff j v t := by
      rw [← ShortCrossCoordinates.range_shortCross]
      exact ⟨y, rfl⟩
    rw [← appendC0_ker, LinearMap.mem_ker] at hm
    exact hm
  have hb : offDiagonalLongExtraction D Sc cutoff p j v t x = 0 := by
    apply offDiagonalPolynomialBoundary_even_injective D Sc cutoff p j hj v t h
    rw [map_zero, ← appendC0_pMap_offDiagonal, hx]
    exact hc
  have hm : x ∈ LinearMap.range (alpha D Sc cutoff j v t) := by
    rw [← ker_offDiagonalLongExtraction_eq_range_alpha D Sc cutoff p j v t,
      LinearMap.mem_ker]
    exact hb
  obtain ⟨a, ha⟩ := hm
  have he : pprime D Sc cutoff j v t a = y := by
    apply ShortCrossCoordinates.shortCross_injective D Sc cutoff j v t
    have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j v t) a
    simp only [LinearMap.comp_apply] at hs
    exact hs.symm.trans (by rw [ha]; exact hx)
  have hq : pprime D Sc cutoff j v t a ∈ LinearMap.ker (q D Sc cutoff j v t) := by
    rw [← range_pprime_eq_ker_q]
    exact ⟨a, rfl⟩
  rw [LinearMap.mem_ker, he] at hq
  exact hq

theorem evenToCyclotomic_surjective_of_nonpositive_height (p : ZMod 2)
    (j : I) (hj : D.parity j = 0) (v t : List I)
    (h : endpointQPDegree D cutoff j v ≤ outputSDegree D j v) :
    Function.Surjective (toCyclotomic D Sc cutoff j v t) := by
  intro n
  obtain ⟨z, rfl⟩ := canonicalAppendTarget_surjective D Sc cutoff j v (t ++ [j]) n
  obtain ⟨f, hf⟩ := offDiagonalPolynomialBoundary_even_surjective D Sc cutoff p j hj v t h
    (appendC0 D Sc cutoff j v t z)
  let x := offDiagonalSourceLongSection D Sc cutoff p j v t f
  have hc : z - pMap D Sc cutoff j v (t ++ [j]) x ∈
      appendCrossingSpan D Sc cutoff j v t := by
    dsimp only [x]
    rw [← appendC0_ker, LinearMap.mem_ker, map_sub, appendC0_pMap_offDiagonal,
      offDiagonalLongExtraction_sourceLongSection, hf]
    exact sub_self _
  rw [← ShortCrossCoordinates.range_shortCross] at hc
  obtain ⟨y, hy⟩ := hc
  refine ⟨q D Sc cutoff j v t y, ?_⟩
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j v t) y
  simp only [LinearMap.comp_apply] at hs
  rw [← hs, hy, map_sub]
  have hx : pMap D Sc cutoff j v (t ++ [j]) x ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j v (t ++ [j])) := by
    rw [ker_canonicalAppendTarget]
    exact ⟨x, rfl⟩
  rw [LinearMap.mem_ker] at hx
  rw [hx, sub_zero]

/-- At height zero the prescribed crossing itself is an equivalence. -/
def evenToCyclotomicEquiv_zero_height (p : ZMod 2)
    (j : I) (hj : D.parity j = 0) (v t : List I)
    (h : endpointQPDegree D cutoff j v = outputSDegree D j v) :
    Source D Sc cutoff j v t ≃ₗ[k] Old D Sc cutoff (v ++ [j]) (t ++ [j]) :=
  LinearEquiv.ofBijective (toCyclotomic D Sc cutoff j v t)
    ⟨evenToCyclotomic_injective_of_nonnegative_height D Sc cutoff p j hj v t h.ge,
      evenToCyclotomic_surjective_of_nonpositive_height D Sc cutoff p j hj v t h.le⟩

@[simp] theorem evenToCyclotomicEquiv_zero_height_apply (p : ZMod 2)
    (j : I) (hj : D.parity j = 0) (v t : List I)
    (h : endpointQPDegree D cutoff j v = outputSDegree D j v)
    (z : Source D Sc cutoff j v t) :
    evenToCyclotomicEquiv_zero_height D Sc cutoff p j hj v t h z =
      toCyclotomic D Sc cutoff j v t z := rfl

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # The even low window and the crossing kernel

The negative-height kernel identification in DeformedRouquierMatrix, section4,
uses the ordinary even polynomial coefficients. The actual generic snake map
carries precisely that low window onto the balanced crossing kernel.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Even positive-height crossing and polynomial columns

The nonnegative-height branch of DeformedRouquierMatrix, section 4, uses
the prescribed balanced crossing plus literal low polynomial columns.
The actual even degree-shift division and separation prove its inverse on
arbitrary old Hom endpoints, without repeating coefficient elimination.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def evenPositiveCrossingAssembly (i : I) (v t : List I) :
    (Source D Sc cutoff i v t × evenBoundaryRowWindow D Sc cutoff i v t) →ₗ[k]
      Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  (toCyclotomic D Sc cutoff i v t).comp (LinearMap.fst k _ _) +
    (canonicalAppendTarget D Sc cutoff i v (t ++ [i])).comp
      ((appendOutputEmbedding D Sc cutoff i v t).comp
        ((evenBoundaryRowWindow D Sc cutoff i v t).subtype.comp (LinearMap.snd k _ _)))

@[simp] theorem evenPositiveCrossingAssembly_apply (i : I)
    (v t : List I) (s : Source D Sc cutoff i v t)
    (r : evenBoundaryRowWindow D Sc cutoff i v t) :
    evenPositiveCrossingAssembly D Sc cutoff i v t (s, r) =
      toCyclotomic D Sc cutoff i v t s +
        canonicalAppendTarget D Sc cutoff i v (t ++ [i])
          (appendOutputEmbedding D Sc cutoff i v t r) := rfl

theorem evenPositiveCrossingAssembly_injective (p : ZMod 2)
    (i : I) (hi : D.parity i = 0) (v t : List I)
    (h : outputSDegree D i v ≤ endpointQPDegree D cutoff i v) :
    Function.Injective (evenPositiveCrossingAssembly D Sc cutoff i v t) := by
  suffices hzero : ∀ z, evenPositiveCrossingAssembly D Sc cutoff i v t z = 0 → z = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero (x - y)
    have hs : evenPositiveCrossingAssembly D Sc cutoff i v t (x - y) = evenPositiveCrossingAssembly D Sc cutoff i v t x - evenPositiveCrossingAssembly D Sc cutoff i v t y :=
      map_sub (evenPositiveCrossingAssembly D Sc cutoff i v t) x y
    exact hs.trans (sub_eq_zero.mpr hxy)
  rintro ⟨s, r⟩ hz
  obtain ⟨y, rfl⟩ := q_surjective D Sc cutoff i v t s
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff i v t) y
  simp only [LinearMap.comp_apply] at hs
  have hm : shortCross D Sc cutoff i v t y + appendOutputEmbedding D Sc cutoff i v t r ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff i v (t ++ [i])) := by
    rw [LinearMap.mem_ker, map_add, hs]
    exact hz
  rw [ker_canonicalAppendTarget] at hm
  obtain ⟨x, hx⟩ := hm
  have hc : appendC0 D Sc cutoff i v t (shortCross D Sc cutoff i v t y) = 0 := by
    apply appendCrossingSpan_le_ker D Sc cutoff i v t
    rw [← ShortCrossCoordinates.range_shortCross]
    exact ⟨y, rfl⟩
  have hb : offDiagonalPolynomialBoundary D Sc cutoff p i v t
      (offDiagonalLongExtraction D Sc cutoff p i v t x) = r := by
    rw [← appendC0_pMap_offDiagonal D Sc cutoff p i v t, hx, map_add, hc, appendC0_embedding, zero_add]
  have hr : r = 0 := by
    have hzrow : offDiagonalPolynomialBoundary D Sc cutoff p i v t
        (offDiagonalLongExtraction D Sc cutoff p i v t x) + -(r.val) = 0 := by
      rw [hb, add_neg_cancel]
    have hh := OddMath.Algebra.DegreeShiftRow.separation
      (offDiagonalPolynomialBoundary D Sc cutoff p i v t)
      (fun _ => evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t)
      (outputSDegree D i v) (endpointQPDegree D cutoff i v)
      (offDiagonalBoundary_even_above D Sc cutoff p i hi v t)
      (offDiagonalBoundary_even_top D Sc cutoff p i hi v t)
      (offDiagonalLongExtraction D Sc cutoff p i v t x) (-r.val)
      (fun d _ => by omega)
      (fun n hn => by
        apply r.property
        change n ∈ r.val.support
        simpa only [Finsupp.support_neg] using hn) hzrow
    exact Subtype.ext (neg_eq_zero.mp hh.2)
  apply Prod.ext
  · change q D Sc cutoff i v t y = 0
    apply evenToCyclotomic_injective_of_nonnegative_height D Sc cutoff p i hi v t h
    have hz' : toCyclotomic D Sc cutoff i v t (q D Sc cutoff i v t y) = 0 := by
      simpa only [evenPositiveCrossingAssembly_apply, hr, ZeroMemClass.coe_zero, map_zero, add_zero] using hz
    exact hz'.trans ((toCyclotomic D Sc cutoff i v t).map_zero.symm)
  · exact hr

theorem evenPositiveCrossingAssembly_surjective (p : ZMod 2)
    (i : I) (hi : D.parity i = 0) (v t : List I)
    :
    Function.Surjective (evenPositiveCrossingAssembly D Sc cutoff i v t) := by
  intro n
  obtain ⟨z, rfl⟩ := canonicalAppendTarget_surjective D Sc cutoff i v (t ++ [i]) n
  let row := (evenBoundaryRowDivisionEquiv D Sc cutoff p i hi v t).symm
    (appendC0 D Sc cutoff i v t z)
  let f := row.1.val
  let r := row.2
  have hfr : offDiagonalPolynomialBoundary D Sc cutoff p i v t f + r.val =
      appendC0 D Sc cutoff i v t z := by
    exact (evenBoundaryRowDivisionEquiv D Sc cutoff p i hi v t).apply_symm_apply _
  let x := offDiagonalSourceLongSection D Sc cutoff p i v t f
  have hc : z - pMap D Sc cutoff i v (t ++ [i]) x -
      appendOutputEmbedding D Sc cutoff i v t r ∈ appendCrossingSpan D Sc cutoff i v t := by
    rw [← appendC0_ker, LinearMap.mem_ker, map_sub, map_sub, appendC0_pMap_offDiagonal,
      appendC0_embedding]
    dsimp only [x]
    rw [offDiagonalLongExtraction_sourceLongSection, ← hfr]
    abel
  rw [← ShortCrossCoordinates.range_shortCross] at hc
  obtain ⟨y, hy⟩ := hc
  refine ⟨(q D Sc cutoff i v t y, r), ?_⟩
  rw [evenPositiveCrossingAssembly_apply]
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff i v t) y
  simp only [LinearMap.comp_apply] at hs
  rw [← hs, hy, map_sub, map_sub]
  have hx : pMap D Sc cutoff i v (t ++ [i]) x ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff i v (t ++ [i])) := by
    rw [ker_canonicalAppendTarget]
    exact ⟨x, rfl⟩
  rw [LinearMap.mem_ker] at hx
  rw [hx]
  abel

/-- The literal crossing and low polynomial columns form the positive branch. -/
def evenPositiveCrossingEquiv (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (h : outputSDegree D i v ≤ endpointQPDegree D cutoff i v) :
    (Source D Sc cutoff i v t × evenBoundaryRowWindow D Sc cutoff i v t) ≃ₗ[k]
      Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  LinearEquiv.ofBijective (evenPositiveCrossingAssembly D Sc cutoff i v t)
    ⟨evenPositiveCrossingAssembly_injective D Sc cutoff p i hi v t h,
      evenPositiveCrossingAssembly_surjective D Sc cutoff p i hi v t⟩

/-- The polynomial complement is literally the coefficient window below the height. -/
theorem evenBoundaryRowWindow_eq_height (i : I) (v t : List I) (a : ℕ)
    (ha : endpointQPDegree D cutoff i v = outputSDegree D i v + a) :
    evenBoundaryRowWindow D Sc cutoff i v t =
      Finsupp.supported (Old D Sc cutoff v t) k (Set.Iio a) := by
  unfold evenBoundaryRowWindow OddMath.Algebra.DegreeShiftRow.window
  congr 1
  ext n
  change (n + outputSDegree D i v < endpointQPDegree D cutoff i v) ↔ n < a
  omega

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Even ordinary-source unit-column inverse
The positive profile of DeformedMatrixComparison §4 uses the canonical
even source, ordinary adjunction unit/dot columns, and signed crossing.
The ordered categorical mate identity remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- For even colours the ordinary columns require no scalar normalization. -/
def evenUnitDotPolynomialMap (i : {i : I // D.parity i = 0}) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] Old D Sc cutoff (v ++ [i.1]) (t ++ [i.1]) :=
  Finsupp.lsum k fun n => inductionUnitDotColumn D Sc cutoff i.1 v t n

@[simp] theorem evenUnitDotPolynomialMap_single (i : {i : I // D.parity i = 0})
    (v t : List I) (n : ℕ) (b : Old D Sc cutoff v t) :
    evenUnitDotPolynomialMap D Sc cutoff i v t (Finsupp.single n b) =
      inductionUnitDotColumn D Sc cutoff i.1 v t n b := by
  rw [evenUnitDotPolynomialMap, Finsupp.lsum_single]

theorem evenUnitDotPolynomialMap_eq (i : {i : I // D.parity i = 0}) (v t : List I) :
    evenUnitDotPolynomialMap D Sc cutoff i v t = unitDotPolynomialMap D Sc cutoff i.1 v t := by
  unfold evenUnitDotPolynomialMap unitDotPolynomialMap
  congr 1
  funext n
  simp only [inductionUnitDotSign, i.property, smul_zero, sign_zero, one_smul]

def evenUnitPositiveMatrixEquiv (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (h : outputSDegree D i.1 v ≤ endpointQPDegree D cutoff i.1 v) :
    ((((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff)) × evenBoundaryRowWindow D Sc cutoff i.1 v t) ≃ₗ[k]
      Old D Sc cutoff (v ++ [i.1]) (t ++ [i.1]) :=
  (((evenSourceEquiv D Sc cutoff i v t).trans (LinearEquiv.neg k)).prodCongr
    (LinearEquiv.refl k (evenBoundaryRowWindow D Sc cutoff i.1 v t))).trans
      (evenPositiveCrossingEquiv D Sc cutoff p i.1 i.property v t h)

/-- The positive columns are the literal ordinary unit/dot columns. -/
theorem evenUnitPositiveMatrixEquiv_apply (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (h : outputSDegree D i.1 v ≤ endpointQPDegree D cutoff i.1 v)
    (z : (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff)))
    (r : evenBoundaryRowWindow D Sc cutoff i.1 v t) :
    evenUnitPositiveMatrixEquiv D Sc cutoff p i v t h (z, r) =
      -toCyclotomic D Sc cutoff i.1 v t (evenSourceEquiv D Sc cutoff i v t z) +
        evenUnitDotPolynomialMap D Sc cutoff i v t r.val := by
  change toCyclotomic D Sc cutoff i.1 v t (-(evenSourceEquiv D Sc cutoff i v t z)) +
    canonicalAppendTarget D Sc cutoff i.1 v (t ++ [i.1])
      (appendOutputEmbedding D Sc cutoff i.1 v t r.val) = _
  rw [map_neg, evenUnitDotPolynomialMap_eq, unitDotPolynomialMap_eq]
  rfl

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Even shifted unit-family component coordinates
DeformedMatrixComparison (6) and the positive profile of section 4
specialize to identity coefficient units for an even moving colour.
The actual ordered-mate comparison remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
open OddMath.LowPolynomialCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance evenUnitFamilyPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- Even ordinary columns require the identity coefficient diagonal. -/
theorem unitCoefficientDiagonal_even (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ) (b : Fin m → Old D Sc cutoff v t) :
    unitCoefficientDiagonal D Sc cutoff (D.parity i.1) v t m b = b := by
  ext r
  simp only [unitCoefficientDiagonal_apply, inductionUnitDotSign, i.property,
    smul_zero, sign_zero, one_smul]

/-- The literal even polynomial window in finite coordinates. -/
def evenUnitWindowVectorEquiv (i : I) (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i v = outputSDegree D i v + m) :
    (Fin m → Old D Sc cutoff v t) ≃ₗ[k] evenBoundaryRowWindow D Sc cutoff i v t :=
  (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m).trans
    (LinearEquiv.ofEq _ _ (evenBoundaryRowWindow_eq_height D Sc cutoff i v t m hm).symm)

/-- Canonical parity coordinates and the literal even coefficient window. -/
def evenUnitFamilyComponentCoordinates (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i.1 v = outputSDegree D i.1 v + m) :
    ((a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff i.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
    ((((BalancedInduction.induction (append D Sc cutoff i.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) × evenBoundaryRowWindow D Sc cutoff i.1 v t) :=
  (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m).trans
    ((LinearEquiv.refl k _).prodCongr
      (evenUnitWindowVectorEquiv D Sc cutoff i.1 v t m hm))

/-- The even shifted-family component inverse, with unscaled ordinary unit columns. -/
def evenUnitFamilyComponentEquiv (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i.1 v = outputSDegree D i.1 v + m) :
    ((a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff i.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
      Old D Sc cutoff (v ++ [i.1]) (t ++ [i.1]) :=
  (evenUnitFamilyComponentCoordinates D Sc cutoff i v t m hm).trans
    (evenUnitPositiveMatrixEquiv D Sc cutoff p i v t (by omega))

/-- Every even unit slot is the ordinary adjunction-unit/dot column. -/
theorem evenUnitFamilyComponentEquiv_apply (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i.1 v = outputSDegree D i.1 v + m)
    (x : (a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff i.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :
    evenUnitFamilyComponentEquiv D Sc cutoff p i v t m hm x =
      -toCyclotomic D Sc cutoff i.1 v t
        (evenSourceEquiv D Sc cutoff i v t
          (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).1) +
      ∑ r : Fin m, inductionUnitDotColumn D Sc cutoff i.1 v t r.val
        ((unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2 r) := by
  rw [evenUnitFamilyComponentEquiv, LinearEquiv.trans_apply]
  rw [show (evenUnitFamilyComponentCoordinates D Sc cutoff i v t m hm x) =
      ((unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).1,
        evenUnitWindowVectorEquiv D Sc cutoff i.1 v t m hm
          (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2) from rfl]
  have he := evenUnitPositiveMatrixEquiv_apply D Sc cutoff p i v t (by omega)
    (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).1
    (evenUnitWindowVectorEquiv D Sc cutoff i.1 v t m hm
      (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2)
  refine he.trans ?_
  congr 1
  rw [evenUnitDotPolynomialMap_eq]
  change unitDotPolynomialMap D Sc cutoff i.1 v t
    ((lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m
      (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2).val) = _
  have h := unitDotPolynomialMap_diagonal D Sc cutoff i.1 v t m
    (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2
  rw [unitCoefficientDiagonal_even D Sc cutoff i] at h
  exact h

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end
