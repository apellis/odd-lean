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

private def vectorClosureLinear
    {k U V : Type u} [CommRing k] [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V] (cap : V →ₗ[k] U) (cup : U →ₗ[k] V) :
    Module.End k V →ₗ[k] Module.End k U where
  toFun f := cap ∘ₗ f ∘ₗ cup
  map_add' f g := by
    ext z
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
  map_smul' r f := by
    ext z
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

private def observedEndLinear
    {k C U : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [AddCommGroup U] [Module k U]
    (F : Superfunctor k C (SVec k)) (w : C)
    (decode : F.obj w →ₗ[k] U) (input : U →ₗ[k] F.obj w) :
    End F →ₗ[k] Module.End k U :=
  (vectorClosureLinear decode input).comp
    ((svecEndEvaluation (F.obj w)).toLinearMap.comp
      (supernaturalTotalLinearMap F F w))

private theorem observedEndLinear_apply
    {k C U : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [AddCommGroup U] [Module k U]
    (F : Superfunctor k C (SVec k)) (w : C)
    (decode : F.obj w →ₗ[k] U) (input : U →ₗ[k] F.obj w) (f : End F) (a : U) :
    observedEndLinear F w decode input f a = decode (f.total w (input a)) := rfl

private theorem observedEndLinear_at_vector
    {k C U : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [AddCommGroup U] [Module k U]
    (F : Superfunctor k C (SVec k)) (w : C)
    (decode : F.obj w →ₗ[k] U) (input : U →ₗ[k] F.obj w)
    (f : End F) (z : F.obj w) (hz : input (decode z) = z) :
    observedEndLinear F w decode input f (decode z) = decode (f.total w z) := by
  rw [observedEndLinear_apply, hz]

private theorem observedEndLinear_comp
    {k C U : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [AddCommGroup U] [Module k U]
    (F G : Superfunctor k C (SVec k)) (w : C)
    (decode : F.obj w →ₗ[k] U) (input : U →ₗ[k] F.obj w)
    (cup : F ⟶ G) (cap : G ⟶ F) (a : U) :
    observedEndLinear F w decode input (cup ≫ cap) a =
      decode (cap.total w (cup.total w (input a))) := by
  rw [observedEndLinear_apply, Superfunctor.comp_total, SVec.comp_apply]

private theorem observedEndLinear_comp_at_vector
    {k C U : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [AddCommGroup U] [Module k U]
    (F G : Superfunctor k C (SVec k)) (w : C)
    (decode : F.obj w →ₗ[k] U) (input : U →ₗ[k] F.obj w)
    (cup : F ⟶ G) (cap : G ⟶ F) (z : F.obj w) (hz : input (decode z) = z) :
    observedEndLinear F w decode input (cup ≫ cap) (decode z) =
      decode (cap.total w (cup.total w z)) := by
  rw [observedEndLinear_comp, hz]

private def closureLinear
    {k U : Type u} {C : Type v} [CommRing k] [Category.{w} C]
    [Preadditive C] [Linear k C] [AddCommGroup U] [Module k U]
    {A B : C} (L : End A →ₗ[k] U) (cup : A ⟶ B) (cap : B ⟶ A) :
    End B →ₗ[k] U :=
  L.comp ((Linear.leftComp (R := k) A cup).comp (Linear.rightComp (R := k) B cap))

private theorem closureLinear_apply
    {k U : Type u} {C : Type v} [CommRing k] [Category.{w} C]
    [Preadditive C] [Linear k C] [AddCommGroup U] [Module k U]
    {A B : C} (L : End A →ₗ[k] U) (cup : A ⟶ B) (cap : B ⟶ A)
    (f : End B) : closureLinear L cup cap f = L (cup ≫ f ≫ cap) := rfl

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

/-- Decode the literal total endomorphism, linearly in every module map. -/
def tensorVacuumEndLinear : End V →ₗ[k] Module.End k AQ :=
  observedEndLinear V star (tensorVacuumDecodeLinear D Sc m cutoff L)
    (tensorVacuumInputLinear D Sc m cutoff L)

/-- The literal n-th unit/dot column closed by the same native inverse cap. -/
def tensorUnitCapClosure (hN : 0 < cutoff i) (n : ℕ) : End V :=
  unitDotColumn K hDot V n ≫ tensorPowerVacuumCap D Sc m cutoff L i hN

/-- The typed closure retains the whole prescribed tensor comparison. -/
theorem tensorUnitCapClosure_square (hN : 0 < cutoff i) (n : ℕ) :
    tensorUnitCapClosure D Sc m cutoff L i hN n ≫ (e).hom =
      (e).hom ≫ (restriction Q₀).map
        (unitDotColumn T (truncatedDot_supernatural D Sc cutoff bound i) WM n) ≫
          weightedCoefficientCap D Sc cutoff i L hN := by
  simpa only [tensorUnitCapClosure, Category.assoc] using
    tensorPowerVacuumCap_moment_square D Sc m cutoff L i hN n

/-- All-power moment operators are the given tensor columns followed by
the native inverse cap, decoded with the original full A/T coordinate. -/
def tensorMomentMap (hN : 0 < cutoff i) (n : ℕ) : Module.End k AQ :=
  tensorVacuumEndLinear D Sc m cutoff L
    (tensorUnitCapClosure D Sc m cutoff L i hN n)

/-- The moment operator evaluates the prescribed module closure. -/
theorem tensorMomentMap_apply (hN : 0 < cutoff i) (n : ℕ) (a : AQ) :
    tensorMomentMap D Sc m cutoff L i hN n a =
      tensorVacuumDecodeLinear D Sc m cutoff L
        ((tensorUnitCapClosure D Sc m cutoff L i hN n).total star
          ((tensorVacuumInputLinear D Sc m cutoff L) a)) := by
  simpa only [tensorMomentMap, tensorVacuumEndLinear] using
    observedEndLinear_apply V star (tensorVacuumDecodeLinear D Sc m cutoff L)
      (tensorVacuumInputLinear D Sc m cutoff L)
      (tensorUnitCapClosure D Sc m cutoff L i hN n) a

/-- The literal tensor closure has exactly the weighted all-power
moment, on every coefficient vector, including inhomogeneous vectors. -/
theorem tensorMomentMap_eq_weightedMomentMap (hN : 0 < cutoff i) (n : ℕ) :
    tensorMomentMap D Sc m cutoff L i hN n = weightedMomentMap D Sc cutoff L i hN n := by
  apply LinearMap.ext
  intro a
  let z := (tensorVacuumInputLinear D Sc m cutoff L) a
  have hz : (e).hom.total star z = tensorVacuumCoefficientEquiv D Sc cutoff L a :=
    tensorVacuumInput_chart D Sc m cutoff L a
  have h := congrArg (fun f => f.total star z)
    (tensorUnitCapClosure_square D Sc m cutoff L i hN n)
  simp only [Superfunctor.comp_total, SVec.comp_apply] at h
  dsimp only [z] at h hz
  rw [tensorMomentMap_apply, tensorVacuumDecodeLinear_apply]
  rw [h]
  simp only [SVec.comp_apply]
  rw [hz]
  simpa only [tensorVacuumCoefficientEquiv] using
    (weightedFunctional_coefficientCap D Sc cutoff i L hN _).symm

/-- The complete tensor moment is left multiplication by the original
signed reservoir coefficient, without specializing the input to one. -/
theorem tensorMomentMap_eq_mulLeft (hN : 0 < cutoff i) (n : ℕ) :
    tensorMomentMap D Sc m cutoff L i hN n =
      LinearMap.mulLeft k (signedMoment D Sc cutoff L i hN n) := by
  rw [tensorMomentMap_eq_weightedMomentMap, weightedMomentMap_eq_mulLeft]

/-- The decoded tensor closure retains the degree of its actual dot
power and last inverse row, with the original coefficient superstructure. -/
theorem tensorMomentMap_mem (hN : 0 < cutoff i) (n : ℕ) :
    tensorMomentMap D Sc m cutoff L i hN n ∈
      parity (R := k) (coefficientPowerSpace D cutoff L) (coefficientPowerSpace D cutoff L)
        ((n + (cutoff i - 1)) • D.parity i) := by
  rw [tensorMomentMap_eq_weightedMomentMap]
  exact weightedMomentMap_mem D Sc cutoff L i hN n

/-- The formula applies directly to every native tensor vector, before
choosing its full-coefficient coordinate. -/
theorem tensorPowerVacuumCap_moment_apply (hN : 0 < cutoff i) (n : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
      ((tensorUnitCapClosure D Sc m cutoff L i hN n).total star z) =
        signedMoment D Sc cutoff L i hN n * tensorVacuumDecodeLinear D Sc m cutoff L z := by
  have h := LinearMap.congr_fun (tensorMomentMap_eq_mulLeft D Sc m cutoff L i hN n)
    (tensorVacuumDecodeLinear D Sc m cutoff L z)
  have hc := observedEndLinear_at_vector V star (tensorVacuumDecodeLinear D Sc m cutoff L)
    (tensorVacuumInputLinear D Sc m cutoff L) (unitDotColumn K hDot V n ≫ tensorPowerVacuumCap D Sc m cutoff L i hN) z
    (tensorVacuumInput_decode D Sc m cutoff L z)
  have hcc : tensorMomentMap D Sc m cutoff L i hN n
      (tensorVacuumDecodeLinear D Sc m cutoff L z) =
      tensorVacuumDecodeLinear D Sc m cutoff L
        ((tensorUnitCapClosure D Sc m cutoff L i hN n).total star z) := by
    simpa only [tensorMomentMap, tensorVacuumEndLinear] using hc
  exact hcc.symm.trans h

/-- Both raw odd-colour series are retained in the actual tensor fields. -/
theorem tensorMomentMap_even (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    tensorMomentMap D Sc m cutoff L i hN (cutoff i - 1 + 2 * r) =
      LinearMap.mulLeft k (completeCoefficient D cutoff L i r) := by
  rw [tensorMomentMap_eq_weightedMomentMap, weightedMomentMap_even D Sc cutoff L i hi hN r]

/-- The odd series keeps the given cutoff sign and independent exterior
coefficient on all tensor-vacuum coefficient vectors. -/
theorem tensorMomentMap_odd (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    tensorMomentMap D Sc m cutoff L i hN (cutoff i - 1 + (2 * r + 1)) =
      LinearMap.mulLeft k ((-1 : k) ^ (cutoff i + 1) •
        (coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩) *
          completeCoefficient D cutoff L i r)) := by
  rw [tensorMomentMap_eq_weightedMomentMap, weightedMomentMap_odd D Sc cutoff L i hi hN r]

private theorem column_post_power (a n : ℕ) :
    unitDotColumn K hDot V n ≫ restrictedDotEnd K hDot V ^ a =
      unitDotColumn K hDot V (a + n) := by
  rw [unitDotColumn_eq_restrictedDotEnd, unitDotColumn_eq_restrictedDotEnd, Category.assoc]
  congr 1
  change restrictedDotEnd K hDot V ^ a * restrictedDotEnd K hDot V ^ n =
    restrictedDotEnd K hDot V ^ (a + n)
  exact (pow_add _ _ _).symm

/-- The plus-one probe polynomial followed by the same native inverse cap. -/
def tensorPolynomialCap (hN : 0 < cutoff i) (M : ℕ) :=
  ((restrictedDotEnd K hDot V ^ 2 + 1) ^ M) ≫ tensorPowerVacuumCap D Sc m cutoff L i hN

/-- Closure of an arbitrary native F/E endomorphism with the given
unit/dot column and normalized tensor inverse cap. -/
def tensorNativeClosureLinear (hN : 0 < cutoff i) (n : ℕ) :
    End ((restriction K).obj ((induction K).obj V)) →ₗ[k] End V :=
  closureLinear (LinearMap.id : End V →ₗ[k] End V)
    (unitDotColumn K hDot V n) (tensorPowerVacuumCap D Sc m cutoff L i hN)

private theorem tensorNativeClosureLinear_pow (hN : 0 < cutoff i) (n a : ℕ) :
    tensorNativeClosureLinear D Sc m cutoff L i hN n (restrictedDotEnd K hDot V ^ a) =
      tensorUnitCapClosure D Sc m cutoff L i hN (a + n) := by
  unfold tensorNativeClosureLinear
  rw [closureLinear_apply]
  change unitDotColumn K hDot V n ≫ restrictedDotEnd K hDot V ^ a ≫
    tensorPowerVacuumCap D Sc m cutoff L i hN = _
  rw [← Category.assoc, column_post_power]
  rfl

/-- Linear observation of the same typed native closures. -/
def tensorCapMomentLinear (hN : 0 < cutoff i) (n : ℕ) :
    End ((restriction K).obj ((induction K).obj V)) →ₗ[k] Module.End k AQ :=
  (tensorVacuumEndLinear D Sc m cutoff L).comp
    (tensorNativeClosureLinear D Sc m cutoff L i hN n)

/-- Evaluation keeps the prescribed native closure before decoding. -/
theorem tensorCapMomentLinear_apply (hN : 0 < cutoff i) (n : ℕ)
    (f : End ((restriction K).obj ((induction K).obj V))) (a : AQ) :
    tensorCapMomentLinear D Sc m cutoff L i hN n f a =
      tensorVacuumDecodeLinear D Sc m cutoff L
        ((tensorNativeClosureLinear D Sc m cutoff L i hN n f).total star
          (tensorVacuumInputLinear D Sc m cutoff L a)) := by
  simpa only [tensorCapMomentLinear, LinearMap.comp_apply, tensorVacuumEndLinear] using
    observedEndLinear_apply V star (tensorVacuumDecodeLinear D Sc m cutoff L)
      (tensorVacuumInputLinear D Sc m cutoff L)
      (tensorNativeClosureLinear D Sc m cutoff L i hN n f) a

private theorem tensorCapMomentLinear_pow (hN : 0 < cutoff i) (n a : ℕ) :
    tensorCapMomentLinear D Sc m cutoff L i hN n (restrictedDotEnd K hDot V ^ a) =
      tensorMomentMap D Sc m cutoff L i hN (a + n) := by
  change tensorVacuumEndLinear D Sc m cutoff L
    (tensorNativeClosureLinear D Sc m cutoff L i hN n (restrictedDotEnd K hDot V ^ a)) = _
  rw [tensorNativeClosureLinear_pow]
  rfl

/-- Actual dotted-unit closures of the literal tensor polynomial cap. -/
def tensorPolynomialCapMoment (hN : 0 < cutoff i) (M n : ℕ) : Module.End k AQ :=
  tensorCapMomentLinear D Sc m cutoff L i hN n ((restrictedDotEnd K hDot V ^ 2 + 1) ^ M)

/-- The polynomial closure applies the given restricted dot polynomial
before the native cap; its column remains the prescribed unit/dot field. -/
def tensorPolynomialClosure (hN : 0 < cutoff i) (M n : ℕ) : End V :=
  tensorNativeClosureLinear D Sc m cutoff L i hN n ((restrictedDotEnd K hDot V ^ 2 + 1) ^ M)

/-- Its whole native module map is the literal column followed by the
literal polynomial cap, before choosing any coefficient vector. -/
theorem tensorPolynomialClosure_eq (hN : 0 < cutoff i) (M n : ℕ) :
    tensorPolynomialClosure D Sc m cutoff L i hN M n =
      unitDotColumn K hDot V n ≫ tensorPolynomialCap D Sc m cutoff L i hN M := by
  unfold tensorPolynomialClosure tensorNativeClosureLinear
  rw [closureLinear_apply]
  rfl

/-- Every polynomial-cap moment is the observed literal native closure. -/
theorem tensorPolynomialCapMoment_moduleCap (hN : 0 < cutoff i) (M n : ℕ) (a : AQ) :
    tensorPolynomialCapMoment D Sc m cutoff L i hN M n a =
      tensorVacuumDecodeLinear D Sc m cutoff L
        ((tensorPolynomialClosure D Sc m cutoff L i hN M n).total star
          (tensorVacuumInputLinear D Sc m cutoff L a)) :=
  tensorCapMomentLinear_apply D Sc m cutoff L i hN n _ a

/-- Binomial expansion keeps the actual cap and all original coefficient
operators in their given order. -/
theorem tensorPolynomialCapMoment_sum (hN : 0 < cutoff i) (M n : ℕ) :
    tensorPolynomialCapMoment D Sc m cutoff L i hN M n =
      ∑ j ∈ Finset.range (M + 1), M.choose j •
        tensorMomentMap D Sc m cutoff L i hN (2 * j + n) := by
  change tensorCapMomentLinear D Sc m cutoff L i hN n
    ((restrictedDotEnd K hDot V ^ 2 + 1) ^ M) = _
  rw [(Commute.one_right (restrictedDotEnd K hDot V ^ 2)).add_pow]
  simp only [one_pow, mul_one, ← nsmul_eq_mul', ← pow_mul, map_sum, map_nsmul,
    tensorCapMomentLinear_pow]

/-- The literal tensor polynomial-cap closures have all of the existing
full coefficient moments, for every exponent and every coefficient vector. -/
theorem tensorPolynomialCapMoment_eq_weightedPolynomialCapMoment
    (hN : 0 < cutoff i) (M n : ℕ) :
    tensorPolynomialCapMoment D Sc m cutoff L i hN M n =
      weightedPolynomialCapMoment D Sc cutoff L i hN M n := by
  rw [tensorPolynomialCapMoment_sum, weightedPolynomialCapMoment_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [tensorMomentMap_eq_weightedMomentMap]

/-- The polynomial-cap formula acts on every native tensor vector,
with all raw weighted coefficients supplied by the existing moment map. -/
theorem tensorPolynomialCap_moment_apply (hN : 0 < cutoff i) (M n : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
      ((tensorPolynomialClosure D Sc m cutoff L i hN M n).total star z) =
      weightedPolynomialCapMoment D Sc cutoff L i hN M n
        (tensorVacuumDecodeLinear D Sc m cutoff L z) := by
  have h := observedEndLinear_at_vector V star
    (tensorVacuumDecodeLinear D Sc m cutoff L) (tensorVacuumInputLinear D Sc m cutoff L)
    (tensorPolynomialClosure D Sc m cutoff L i hN M n) z
    (tensorVacuumInput_decode D Sc m cutoff L z)
  have hh : tensorPolynomialCapMoment D Sc m cutoff L i hN M n
      (tensorVacuumDecodeLinear D Sc m cutoff L z) =
      tensorVacuumDecodeLinear D Sc m cutoff L
        ((tensorPolynomialClosure D Sc m cutoff L i hN M n).total star z) := by
    simpa only [tensorPolynomialCapMoment, tensorCapMomentLinear, LinearMap.comp_apply,
      tensorVacuumEndLinear, tensorPolynomialClosure] using h
  exact hh.symm.trans (LinearMap.congr_fun
    (tensorPolynomialCapMoment_eq_weightedPolynomialCapMoment D Sc m cutoff L i hN M n)
    (tensorVacuumDecodeLinear D Sc m cutoff L z))

/-- At either nonpositive height the first normalized polynomial-cap
closure retains the original independent exterior coefficient and sign. -/
theorem tensorPolynomialCapMoment_nonpositive_first_odd
    (hi : D.parity i = 1) (hN : 0 < cutoff i) (M : ℕ) (hMN : 2 * M ≤ cutoff i) :
    tensorPolynomialCapMoment D Sc m cutoff L i hN M (cutoff i - 2 * M) =
      LinearMap.mulLeft k ((-1 : k) ^ (cutoff i + 1) •
        coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) := by
  rw [tensorPolynomialCapMoment_eq_weightedPolynomialCapMoment]
  exact weightedPolynomialCapMoment_nonpositive_first_odd D Sc cutoff L i hi hN M hMN

/-- At height zero the cap gives minus the original exterior operator;
this uses the same literal tensor unit, dot and native inverse row. -/
theorem tensorPolynomialCapMoment_zero_height_odd
    (hi : D.parity i = 1) (hN : 0 < cutoff i) (M : ℕ) (hcut : cutoff i = 2 * M) :
    tensorPolynomialCapMoment D Sc m cutoff L i hN M 0 =
      LinearMap.mulLeft k (-(coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩))) := by
  rw [tensorPolynomialCapMoment_eq_weightedPolynomialCapMoment]
  exact weightedPolynomialCapMoment_zero_height_odd D Sc cutoff L i hi hN M hcut

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELVOld
