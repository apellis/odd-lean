import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumCap
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPolynomialCaps

/-! # All-power moments on the prescribed tensor vacuum

SwappedVacuumNonpositiveBubbles §2 (7) and §§3–4 (11): attach the
full coefficient moments to the given tensor-vacuum unit, restricted dot
and normalized native inverse cap. The even vacuum and content charts
are retained; no mixed inverse or normalized bubble identification is
assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u v w

private theorem restriction_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (w : C) :
    ((restriction J).map f).total w = f.total (J.obj w) := rfl

private theorem transport_end_value
    {k C U : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [AddCommGroup U] [Module k U]
    (F G : Superfunctor k C (SVec k)) (w : C) (e : F ≅ G) (c : U ≃ₗ[k] G.obj w)
    (f : End F) (g : End G) (h : f ≫ e.hom = e.hom ≫ g)
    (T : Module.End k U) (hg : ∀ a, c.symm (g.total w (c a)) = T a) (z : F.obj w) :
    c.symm (e.hom.total w (f.total w z)) = T (c.symm (e.hom.total w z)) := by
  have hv := congrArg (fun t => t.total w z) h
  simp only [Superfunctor.comp_total, SVec.comp_apply] at hv
  rw [hv]
  have ht := hg (c.symm (e.hom.total w z))
  simpa only [LinearEquiv.apply_symm_apply] using ht

private theorem column_input_even
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    {M P : Superfunctor k C (SVec k)} (f : M ⟶ P)
    (hf : f ∈ parity (R := k) M P 0) (n : ℕ) :
    unitDotColumn J hα M n ≫ (restriction J).map ((induction J).map f) =
      f ≫ unitDotColumn J hα P n := by
  have hd := (transformComponent_supernatural hα).naturality hf
  rw [mul_zero, sign_zero, one_smul] at hd
  change (induction J).map f ≫ dotEnd J hα P =
    dotEnd J hα M ≫ (induction J).map f at hd
  have hp (a : ℕ) : (dotEnd J hα M ^ a) ≫ (induction J).map f =
      (induction J).map f ≫ (dotEnd J hα P ^ a) := by
    induction a with
    | zero => simp only [pow_zero, End.one_def, Category.id_comp, Category.comp_id]
    | succ a ih =>
      calc
        (dotEnd J hα M ^ (a + 1)) ≫ (induction J).map f =
            dotEnd J hα M ≫ ((dotEnd J hα M ^ a) ≫ (induction J).map f) := by
          rw [pow_succ, End.mul_def, Category.assoc]
        _ = dotEnd J hα M ≫ ((induction J).map f ≫ (dotEnd J hα P ^ a)) :=
          congrArg (fun g => dotEnd J hα M ≫ g) ih
        _ = (dotEnd J hα M ≫ (induction J).map f) ≫ (dotEnd J hα P ^ a) :=
          (Category.assoc _ _ _).symm
        _ = ((induction J).map f ≫ dotEnd J hα P) ≫ (dotEnd J hα P ^ a) :=
          congrArg (fun g => g ≫ (dotEnd J hα P ^ a)) hd.symm
        _ = (induction J).map f ≫ (dotEnd J hα P ^ (a + 1)) := by
          rw [pow_succ, End.mul_def, Category.assoc]
  have hu := (adjunction J).unit.naturality f
  change f ≫ (adjunction J).unit.app P =
    (adjunction J).unit.app M ≫ (restriction J).map ((induction J).map f) at hu
  unfold unitDotColumn
  rw [Category.assoc, ← Functor.map_comp, hp, Functor.map_comp, ← Category.assoc,
    ← hu, Category.assoc]

namespace PowerVacuumCoefficient
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m cutoff : I → ℕ) (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "WM" => weightedVacuum D Sc cutoff L
local notation "Q₀" => contentInclusion D Sc cutoff bound (0 : Multiset I)
local notation "W₀" => Functor.obj (restriction Q₀) WM
local notation "H" => VacuumTensor.probeFunctor D Sc m cutoff bound W₀
private def tensorVacuumValue : ContentModules D Sc cutoff bound 0 :=
  Superfunctor.obj H (probeOldVacuumRegular D Sc m)
local notation "V" => tensorVacuumValue D Sc m cutoff L
private abbrev vacuumPoint : ContentCategory D Sc cutoff bound 0 := ⟨⟨[]⟩, rfl⟩
local notation "star" => vacuumPoint D Sc cutoff L
private def tensorVacuumIso : tensorVacuumValue D Sc m cutoff L ≅ W₀ :=
  VacuumTensor.probeVacuumIso D Sc m cutoff bound W₀
local notation "e" => tensorVacuumIso D Sc m cutoff L
local notation "AQ" => CoefficientPowerQuotient (k := k) D cutoff L
variable (i : I)
local notation "K" => contentAppendTo D Sc cutoff bound (0 : Multiset I) [i]
  ((0 : Multiset I) + ([i] : Multiset I)) (contentBlockCanonicalSum 0 [i])
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff bound 0 i
local notation "T" => truncatedAppend D Sc cutoff bound [i]

/-- The original empty coefficient chart, with the selected content
module endpoint retained in its type. -/
private def tensorVacuumCoefficientEquiv : AQ ≃ₗ[k] (W₀).obj star :=
  weightedEmptyEquiv D Sc cutoff L

/-- The original full coefficient decoder on the actual tensor value. -/
def tensorVacuumDecodeLinear : (V).obj star →ₗ[k] AQ :=
  (tensorVacuumCoefficientEquiv D Sc cutoff L).symm.toLinearMap ∘ₗ
    SVec.toLinearMap ((e).hom.total star)

/-- Its input is the prescribed tensor with the regular probe scalar
unit, before applying any cap or dot. -/
def tensorVacuumInputLinear : AQ →ₗ[k] (V).obj star where
  toFun a := tensorVacuumCoefficientEquiv D Sc cutoff L a ⊗ₜ[k] probeVacuumScalarEquiv D Sc m 1
  map_add' a b := by simp only [map_add, TensorProduct.add_tmul]
  map_smul' r a := by
    rw [map_smul]
    exact (TensorProduct.smul_tmul' r (tensorVacuumCoefficientEquiv D Sc cutoff L a)
      (probeVacuumScalarEquiv D Sc m 1)).symm

/-- The input chart is the literal given unit tensor under the existing
even tensor-vacuum isomorphism. -/
theorem tensorVacuumInput_chart (a : AQ) :
    (e).hom.total star (tensorVacuumInputLinear D Sc m cutoff L a) =
      tensorVacuumCoefficientEquiv D Sc cutoff L a :=
  VacuumTensor.probeVacuumIso_hom_tmul D Sc m cutoff bound W₀ star _

/-- Every coefficient vector is recovered from this original tensor input. -/
theorem tensorVacuumDecode_input (a : AQ) :
    tensorVacuumDecodeLinear D Sc m cutoff L (tensorVacuumInputLinear D Sc m cutoff L a) = a := by
  change (tensorVacuumCoefficientEquiv D Sc cutoff L).symm
    ((e).hom.total star (tensorVacuumInputLinear D Sc m cutoff L a)) = a
  rw [tensorVacuumInput_chart, LinearEquiv.symm_apply_apply]

/-- Every native tensor vector is the prescribed unit tensor in these
coordinates; the input chart is an actual inverse, not a replacement input. -/
theorem tensorVacuumInput_decode (z : (V).obj star) :
    tensorVacuumInputLinear D Sc m cutoff L (tensorVacuumDecodeLinear D Sc m cutoff L z) = z := by
  apply (moduleIsoLinearEquiv e star).injective
  change (e).hom.total star
    (tensorVacuumInputLinear D Sc m cutoff L (tensorVacuumDecodeLinear D Sc m cutoff L z)) =
      (e).hom.total star z
  rw [tensorVacuumInput_chart]
  exact (tensorVacuumCoefficientEquiv D Sc cutoff L).apply_symm_apply _

/-- Decoding retains the exact existing vacuum and empty charts. -/
theorem tensorVacuumDecodeLinear_apply (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L z =
      (tensorVacuumCoefficientEquiv D Sc cutoff L).symm ((e).hom.total star z) := rfl

/-- Every literal unit/dot/cap closure commutes with the even tensor
chart and the actual supported-content chart, at all powers. -/
theorem tensorPowerVacuumCap_moment_square (hN : 0 < cutoff i) (n : ℕ) :
    unitDotColumn K hDot V n ≫ tensorPowerVacuumCap D Sc m cutoff L i hN ≫ (e).hom =
      (e).hom ≫ (restriction Q₀).map
        (unitDotColumn T (truncatedDot_supernatural D Sc cutoff bound i) WM n) ≫
          weightedCoefficientCap D Sc cutoff i L hN := by
  calc
    _ = (e).hom ≫ unitDotColumn K hDot W₀ n ≫
        contentPowerVacuumCap D Sc cutoff i L hN := by
      have hc := column_input_even K hDot (e).hom
        (VacuumTensor.probeVacuumIso_hom_mem D Sc m cutoff bound W₀) n
      have h := congrArg (fun f => f ≫ contentPowerVacuumCap D Sc cutoff i L hN) hc
      have hcap : tensorPowerVacuumCap D Sc m cutoff L i hN ≫ (e).hom =
          (induction K ⋙ restriction K).map (e).hom ≫ contentPowerVacuumCap D Sc cutoff i L hN := by
        simpa only [tensorVacuumIso, tensorVacuumValue] using
          tensorPowerVacuumCap_compare D Sc m cutoff L i hN
      rw [hcap]
      simpa only [Functor.comp_map, Category.assoc, tensorVacuumValue, tensorVacuumIso] using h
    _ = _ := by
      have h := congrArg (fun f => (e).hom ≫ f ≫ weightedCoefficientCap D Sc cutoff i L hN)
        (contentVacuumTargetIso_unitDotColumn D Sc cutoff bound i WM
          (weightedVacuum_contentSupported D Sc cutoff L) n)
      simpa only [contentPowerVacuumCap, Category.assoc, tensorVacuumIso] using h

private def tensorVacuumCap (hN : 0 < cutoff i) :
    (restriction K).obj ((induction K).obj V) ⟶ V :=
  tensorPowerVacuumCap D Sc m cutoff L i hN

/-- The given unit/dot column closed by the same normalized inverse cap. -/
def tensorUnitCapClosure (hN : 0 < cutoff i) (n : ℕ) : End V :=
  unitDotColumn K hDot V n ≫ tensorVacuumCap D Sc m cutoff L i hN

private def weightedUnitCapClosure (hN : 0 < cutoff i) (n : ℕ) : End W₀ :=
  (restriction Q₀).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff bound i) WM n) ≫
    weightedCoefficientCap D Sc cutoff i L hN

private theorem weightedUnitCapClosure_value (hN : 0 < cutoff i) (n : ℕ) (a : AQ) :
    (tensorVacuumCoefficientEquiv D Sc cutoff L).symm
      ((weightedUnitCapClosure D Sc cutoff L i hN n).total star
        (tensorVacuumCoefficientEquiv D Sc cutoff L a)) =
      weightedMomentMap D Sc cutoff L i hN n a := by
  have h := (weightedFunctional_coefficientCap D Sc cutoff i L hN
    ((unitDotColumn T (truncatedDot_supernatural D Sc cutoff bound i) WM n).total
      ((oldTruncateFunctor D Sc cutoff bound).obj ⟨[]⟩) (weightedEmptyEquiv D Sc cutoff L a))).symm
  dsimp only [weightedUnitCapClosure, tensorVacuumCoefficientEquiv, weightedMomentMap]
  simp only [Superfunctor.comp_total, SVec.comp_apply, restriction_total,
    LinearMap.comp_apply, LinearEquiv.coe_coe, SVec.toLinearMap,
    contentInclusion, oldTruncateFunctor, vacuumPoint] at h ⊢
  convert! h using 1

/-- Every native tensor vector has the existing full-coefficient moment
of the actual prescribed unit, dot and normalized inverse cap. -/
theorem tensorPowerVacuumCap_moment_weighted (hN : 0 < cutoff i) (n : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
      ((tensorUnitCapClosure D Sc m cutoff L i hN n).total star z) =
      weightedMomentMap D Sc cutoff L i hN n (tensorVacuumDecodeLinear D Sc m cutoff L z) := by
  have hs : tensorUnitCapClosure D Sc m cutoff L i hN n ≫ (e).hom =
      (e).hom ≫ weightedUnitCapClosure D Sc cutoff L i hN n := by
    simpa only [tensorUnitCapClosure, tensorVacuumCap, weightedUnitCapClosure, Category.assoc] using
      tensorPowerVacuumCap_moment_square D Sc m cutoff L i hN n
  have h := transport_end_value V W₀ star e (tensorVacuumCoefficientEquiv D Sc cutoff L)
    (tensorUnitCapClosure D Sc m cutoff L i hN n) (weightedUnitCapClosure D Sc cutoff L i hN n)
    hs (weightedMomentMap D Sc cutoff L i hN n)
    (weightedUnitCapClosure_value D Sc cutoff L i hN n) z
  simpa only [tensorVacuumDecodeLinear_apply] using h

/-- The moment formula keeps every homogeneous and inhomogeneous input,
with the original scalar coefficient on the left. -/
theorem tensorPowerVacuumCap_moment_apply (hN : 0 < cutoff i) (n : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
      ((tensorUnitCapClosure D Sc m cutoff L i hN n).total star z) =
      signedMoment D Sc cutoff L i hN n * tensorVacuumDecodeLinear D Sc m cutoff L z := by
  rw [tensorPowerVacuumCap_moment_weighted, weightedMomentMap_apply]

/-- The even-index odd-colour series is the complete raw reservoir series. -/
theorem tensorPowerVacuumCap_moment_even (hi : D.parity i = 1) (hN : 0 < cutoff i)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
      ((tensorUnitCapClosure D Sc m cutoff L i hN (cutoff i - 1 + 2 * r)).total star z) =
      completeCoefficient D cutoff L i r * tensorVacuumDecodeLinear D Sc m cutoff L z := by
  rw [tensorPowerVacuumCap_moment_weighted, weightedMomentMap_even D Sc cutoff L i hi hN r]
  rfl

/-- The odd series retains the original exterior coefficient and cutoff
normalization sign, before any independent bubble identification. -/
theorem tensorPowerVacuumCap_moment_odd (hi : D.parity i = 1) (hN : 0 < cutoff i)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
      ((tensorUnitCapClosure D Sc m cutoff L i hN (cutoff i - 1 + (2 * r + 1))).total star z) =
      ((-1 : k) ^ (cutoff i + 1) •
        (coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩) *
          completeCoefficient D cutoff L i r)) * tensorVacuumDecodeLinear D Sc m cutoff L z := by
  rw [tensorPowerVacuumCap_moment_weighted, weightedMomentMap_odd D Sc cutoff L i hi hN r]
  rfl

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELVOld
