import OddMath.QuiverHecke.CyclotomicAction.CoefficientPowerSeries
import OddMath.QuiverHecke.CyclotomicAction.AppendSourceRows
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop
import OddMath.QuiverHecke.CyclotomicAction.CoefficientPowerAnnihilation
import OddMath.QuiverHecke.CyclotomicAction.ContentBlockExtension
import OddMath.QuiverHecke.CyclotomicAction.WeightedAppend
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier
import OddMath.QuiverHecke.CyclotomicAction.AppendContent
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate
import OddMath.QuiverHecke.CyclotomicAction.ContentModules
import OddMath.QuiverHecke.CyclotomicAction.ContentMatrix
import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.QuiverHecke.CyclotomicAction.ContentModule

/-!
# Power word content

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Actual regular-power vacuum coordinates at arbitrary words

SwappedVacuumCoordinates §§2–3. The source is the chosen actual regular
A/T vacuum. Coefficient insertion at an arbitrary old word is preserved by
the actual append functor, so the existing induction composition comparison
identifies these coends with iterated induction of that vacuum.
The balanced generator h tensor 1 is studied before identifying its kernel;
no action-faithfulness or replacement quotient premise is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ν : List I)

private def wordSourceScalar : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
    ((⟨ν⟩ : OldCategory D Sc cutoff) ⟶ ⟨ν⟩) :=
  (ideal D Sc cutoff ν ν).mkQ.comp (ELVPScalar.scalar D Sc cutoff ν)

/-- The existing full coefficient endomorphisms inserted at a specified old word. -/
def powerWordCoefficientSource : PowerCoefficientCategory (k := k) D cutoff ⥤ OldCategory D Sc cutoff where
  obj _ := ⟨ν⟩
  map f := wordSourceScalar D Sc cutoff ν (f : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
  map_id _ := rfl
  map_comp f g := (coefficientEndomorphism_comp D Sc cutoff ν
    (f : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (g : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)).symm

instance powerWordCoefficientSource_additive : (powerWordCoefficientSource D Sc cutoff ν).Additive where
  map_add := map_add (wordSourceScalar D Sc cutoff ν) _ _
instance powerWordCoefficientSource_linear : (powerWordCoefficientSource D Sc cutoff ν).Linear k where
  map_smul f r := map_smul (wordSourceScalar D Sc cutoff ν) r f
instance powerWordCoefficientSource_super : IsSuperfunctor k (powerWordCoefficientSource D Sc cutoff ν) where
  map_mem hf := coefficientEndomorphism_mem D Sc cutoff ν hf

/-- The actual right-append functor preserves these coefficient maps. -/
theorem powerWordCoefficientSource_append (i : I) :
    powerWordCoefficientSource D Sc cutoff ν ⋙ CyclotomicCrossingTensor.append D Sc cutoff i =
      powerWordCoefficientSource D Sc cutoff (ν ++ [i]) := by
  apply Functor.hext
    (F := powerWordCoefficientSource D Sc cutoff ν ⋙ CyclotomicCrossingTensor.append D Sc cutoff i)
    (G := powerWordCoefficientSource D Sc cutoff (ν ++ [i])) (fun _ => rfl)
  intro z z' a
  exact heq_of_eq (append_coefficientEndomorphism D Sc cutoff i ν
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff))

/-- Insert the literal regular quotient unit in the collapsed balanced coend. -/
def powerWordGenerator (w : OldCategory D Sc cutoff) :
    ((⟨ν⟩ : OldCategory D Sc cutoff) ⟶ w) →ₗ[k]
      BalancedInduction.Obj (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L).toFunctor w :=
  (BalancedInduction.inclusion (powerWordCoefficientSource D Sc cutoff ν)
    (liftedPowerRegular D cutoff L).toFunctor w (powerCoefficientStar D cutoff)).comp
      ((TensorProduct.mk k _ _).flip (1 : CoefficientPowerQuotient (k := k) D cutoff L))

/-- Balancing the actual left regular coefficient action generates every
vector of the actual coend from h tensor 1. -/
theorem powerWordGenerator_surjective (w : OldCategory D Sc cutoff) :
    Function.Surjective (powerWordGenerator D Sc cutoff L ν w) := by
  let J := powerWordCoefficientSource D Sc cutoff ν
  let R := (liftedPowerRegular (k := k) D cutoff L).toFunctor
  let G := powerWordGenerator D Sc cutoff L ν w
  have hz : (LinearMap.range G).mkQ = 0 := by
    apply BalancedInduction.hom_ext
    intro z h m
    have hs : z = powerCoefficientStar D cutoff := by
      rcases z with ⟨z⟩
      cases z
      rfl
    subst z
    change CoefficientPowerQuotient (k := k) D cutoff L at m
    obtain ⟨a, rfl⟩ := RingCon.mkₐ_surjective (α := k)
      (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon m
    let f : powerCoefficientStar D cutoff ⟶ powerCoefficientStar D cutoff := a
    have hb := BalancedInduction.balance J R f h
      (1 : CoefficientPowerQuotient (k := k) D cutoff L)
    change BalancedInduction.tensor J R _ (J.map f ≫ h)
      (1 : CoefficientPowerQuotient (k := k) D cutoff L) =
      BalancedInduction.tensor J R _ h
        ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a * 1) at hb
    rw [mul_one] at hb
    change (LinearMap.range G).mkQ (BalancedInduction.tensor J R _ h _) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨J.map f ≫ h, hb⟩
  have hr : LinearMap.range G = ⊤ := by
    apply top_unique
    intro x _
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have h := LinearMap.congr_fun hz x
    exact h
  exact LinearMap.range_eq_top.mp hr

/-- The intrinsic source-power relation submodule in actual old Homs.
Its coefficients range over the literal full two-sided power ideal A/T. -/
def powerWordRelationSpan (w : OldCategory D Sc cutoff) :
    Submodule k ((⟨ν⟩ : OldCategory D Sc cutoff) ⟶ w) :=
  Submodule.span k {f | ∃ a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff,
    a ∈ coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L ∧
      ∃ h : (⟨ν⟩ : OldCategory D Sc cutoff) ⟶ w,
        coefficientEndomorphism D Sc cutoff ν a ≫ h = f}

private theorem powerWordCoefficientSource_map
    (z z' : PowerCoefficientCategory (k := k) D cutoff) (a : z ⟶ z') :
    (powerWordCoefficientSource D Sc cutoff ν).map a =
      coefficientEndomorphism D Sc cutoff ν (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) := rfl

private def powerQuotientDesc {V : Type u} [AddCommGroup V] [Module k V]
    (f : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k] V)
    (hf : LinearMap.ker ((coefficientPowerIdeal D cutoff
      (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k).toLinearMap ≤ LinearMap.ker f) :
      CoefficientPowerQuotient (k := k) D cutoff L →ₗ[k] V :=
  ((LinearMap.ker ((coefficientPowerIdeal D cutoff
      (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k).toLinearMap).liftQ f hf).comp
    (((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k).toLinearMap.quotKerEquivOfSurjective (RingCon.mkₐ_surjective (α := k) _)).symm.toLinearMap

private theorem powerQuotientDesc_apply {V : Type u} [AddCommGroup V] [Module k V]
    (f : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k] V) (hf)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    powerQuotientDesc D cutoff L f hf
      ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a) = f a := by
  let q : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
      CoefficientPowerQuotient (k := k) D cutoff L :=
    ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k).toLinearMap
  change (LinearMap.ker q).liftQ f hf
    ((q.quotKerEquivOfSurjective (RingCon.mkₐ_surjective (α := k) _)).symm (q a)) = f a
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

private def powerWordCoefficientPairing (w : OldCategory D Sc cutoff)
    (h : (⟨ν⟩ : OldCategory D Sc cutoff) ⟶ w) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
      (((⟨ν⟩ : OldCategory D Sc cutoff) ⟶ w) ⧸ powerWordRelationSpan D Sc cutoff L ν w) where
  toFun a := (powerWordRelationSpan D Sc cutoff L ν w).mkQ
    (wordSourceScalar D Sc cutoff ν a ≫ h)
  map_add' a b := by rw [map_add, Preadditive.add_comp, map_add]
  map_smul' c a := by rw [map_smul, Linear.smul_comp, map_smul]; rfl

private theorem powerWordCoefficientPairing_kills (w : OldCategory D Sc cutoff)
    (h : (⟨ν⟩ : OldCategory D Sc cutoff) ⟶ w)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (ha : (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a = 0) :
    powerWordCoefficientPairing D Sc cutoff L ν w h a = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.subset_span ⟨a, Quotient.exact ha, h, rfl⟩

private def powerWordQuotientPairing (w : OldCategory D Sc cutoff)
    (h : (⟨ν⟩ : OldCategory D Sc cutoff) ⟶ w) :
    CoefficientPowerQuotient (k := k) D cutoff L →ₗ[k]
      (((⟨ν⟩ : OldCategory D Sc cutoff) ⟶ w) ⧸ powerWordRelationSpan D Sc cutoff L ν w) :=
  powerQuotientDesc D cutoff L (powerWordCoefficientPairing D Sc cutoff L ν w h)
    (fun a ha => powerWordCoefficientPairing_kills D Sc cutoff L ν w h a ha)

private theorem powerWordQuotientPairing_apply (w : OldCategory D Sc cutoff)
    (h : (⟨ν⟩ : OldCategory D Sc cutoff) ⟶ w)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    powerWordQuotientPairing D Sc cutoff L ν w h
      ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a) =
        (powerWordRelationSpan D Sc cutoff L ν w).mkQ
          (coefficientEndomorphism D Sc cutoff ν a ≫ h) :=
  powerQuotientDesc_apply D cutoff L _ _ a

private def powerWordPairing (w : OldCategory D Sc cutoff) :
    (((⟨ν⟩ : OldCategory D Sc cutoff) ⟶ w) ⊗[k] CoefficientPowerQuotient (k := k) D cutoff L) →ₗ[k]
      (((⟨ν⟩ : OldCategory D Sc cutoff) ⟶ w) ⧸ powerWordRelationSpan D Sc cutoff L ν w) :=
  TensorProduct.lift {
    toFun := powerWordQuotientPairing D Sc cutoff L ν w
    map_add' := by
      intro h h'
      apply LinearMap.ext
      intro m
      obtain ⟨a, rfl⟩ := RingCon.mkₐ_surjective (α := k)
        (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon m
      simp only [LinearMap.add_apply, powerWordQuotientPairing_apply,
        Preadditive.comp_add, map_add]
    map_smul' := by
      intro c h
      apply LinearMap.ext
      intro m
      obtain ⟨a, rfl⟩ := RingCon.mkₐ_surjective (α := k)
        (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon m
      simp only [LinearMap.smul_apply, powerWordQuotientPairing_apply,
        Linear.comp_smul, map_smul, RingHom.id_apply] }

private theorem powerWordPairing_tmul (w : OldCategory D Sc cutoff)
    (h : (⟨ν⟩ : OldCategory D Sc cutoff) ⟶ w)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    powerWordPairing D Sc cutoff L ν w
      (h ⊗ₜ[k] (coefficientPowerIdeal D cutoff
        (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a) =
        (powerWordRelationSpan D Sc cutoff L ν w).mkQ
          (coefficientEndomorphism D Sc cutoff ν a ≫ h) := by
  rw [powerWordPairing, TensorProduct.lift.tmul]
  exact powerWordQuotientPairing_apply D Sc cutoff L ν w h a

private def powerWordPairingFamily (w : OldCategory D Sc cutoff)
    (z : PowerCoefficientCategory (k := k) D cutoff) :
    (((powerWordCoefficientSource D Sc cutoff ν).obj z ⟶ w) ⊗[k]
      (liftedPowerRegular (k := k) D cutoff L).obj z) →ₗ[k]
      (((⟨ν⟩ : OldCategory D Sc cutoff) ⟶ w) ⧸ powerWordRelationSpan D Sc cutoff L ν w) :=
  powerWordPairing D Sc cutoff L ν w

private theorem powerWordPairing_balance (w : OldCategory D Sc cutoff)
    (z z' : PowerCoefficientCategory (k := k) D cutoff) (f : z ⟶ z')
    (h : (powerWordCoefficientSource D Sc cutoff ν).obj z' ⟶ w)
    (m : (liftedPowerRegular (k := k) D cutoff L).obj z) :
    powerWordPairingFamily D Sc cutoff L ν w z
      (((powerWordCoefficientSource D Sc cutoff ν).map f ≫ h) ⊗ₜ[k] m) =
    powerWordPairingFamily D Sc cutoff L ν w z'
      (h ⊗ₜ[k] (liftedPowerRegular (k := k) D cutoff L).map f m) := by
  let b : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff := f
  change CoefficientPowerQuotient (k := k) D cutoff L at m
  obtain ⟨a, rfl⟩ := RingCon.mkₐ_surjective (α := k)
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon m
  change powerWordPairing D Sc cutoff L ν w
      (((powerWordCoefficientSource D Sc cutoff ν).map f ≫ h) ⊗ₜ[k]
        (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a) =
    powerWordPairing D Sc cutoff L ν w
      (h ⊗ₜ[k] ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        b *
          (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a))
  rw [← map_mul, powerWordPairing_tmul, powerWordPairing_tmul,
    powerWordCoefficientSource_map]
  change (powerWordRelationSpan D Sc cutoff L ν w).mkQ
    (coefficientEndomorphism D Sc cutoff ν a ≫ (coefficientEndomorphism D Sc cutoff ν b ≫ h)) =
      (powerWordRelationSpan D Sc cutoff L ν w).mkQ (coefficientEndomorphism D Sc cutoff ν (b * a) ≫ h)
  apply congrArg (powerWordRelationSpan D Sc cutoff L ν w).mkQ
  rw [← Category.assoc]
  have hc : coefficientEndomorphism D Sc cutoff ν a ≫
      coefficientEndomorphism D Sc cutoff ν b =
        coefficientEndomorphism D Sc cutoff ν
          (b * a) :=
    coefficientEndomorphism_comp D Sc cutoff ν a
      b
  rw [hc]

private def powerWordContraction (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (powerWordCoefficientSource D Sc cutoff ν)
      (liftedPowerRegular D cutoff L).toFunctor w →ₗ[k]
      (((⟨ν⟩ : OldCategory D Sc cutoff) ⟶ w) ⧸ powerWordRelationSpan D Sc cutoff L ν w) :=
  BalancedInduction.lift _ _ w (powerWordPairingFamily D Sc cutoff L ν w)
    (powerWordPairing_balance D Sc cutoff L ν w)

private theorem powerWordContraction_generator (w : OldCategory D Sc cutoff)
    (h : (⟨ν⟩ : OldCategory D Sc cutoff) ⟶ w) :
    powerWordContraction D Sc cutoff L ν w (powerWordGenerator D Sc cutoff L ν w h) =
      (powerWordRelationSpan D Sc cutoff L ν w).mkQ h := by
  change BalancedInduction.lift _ _ w _ _
    (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
      (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) h
        (1 : CoefficientPowerQuotient (k := k) D cutoff L)) = _
  rw [BalancedInduction.lift_tensor]
  change powerWordPairing D Sc cutoff L ν w
    (h ⊗ₜ[k] (1 : CoefficientPowerQuotient (k := k) D cutoff L)) = _
  rw [← map_one ((coefficientPowerIdeal D cutoff
    (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k), powerWordPairing_tmul]
  change (powerWordRelationSpan D Sc cutoff L ν w).mkQ ((𝟙 (⟨ν⟩ : OldCategory D Sc cutoff)) ≫ h) = _
  rw [Category.id_comp]

private theorem powerWordRelationSpan_le_kernel (w : OldCategory D Sc cutoff) :
    powerWordRelationSpan D Sc cutoff L ν w ≤ LinearMap.ker (powerWordGenerator D Sc cutoff L ν w) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, h, rfl⟩
  let J := powerWordCoefficientSource D Sc cutoff ν
  let R := (liftedPowerRegular (k := k) D cutoff L).toFunctor
  let f : powerCoefficientStar D cutoff ⟶ powerCoefficientStar D cutoff := a
  have hb := BalancedInduction.balance J R f h
    (1 : CoefficientPowerQuotient (k := k) D cutoff L)
  change BalancedInduction.tensor J R _ (J.map f ≫ h)
      (1 : CoefficientPowerQuotient (k := k) D cutoff L) =
    BalancedInduction.tensor J R _ h
      ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a * 1) at hb
  rw [show (coefficientPowerIdeal D cutoff
    (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a = 0 from Quotient.sound ha,
    zero_mul, BalancedInduction.tensor_zero_right] at hb
  change BalancedInduction.tensor J R _ (coefficientEndomorphism D Sc cutoff ν a ≫ h)
    (1 : CoefficientPowerQuotient (k := k) D cutoff L) = 0
  exact hb

/-- The actual regular A/T word coend has precisely its full source-power
kernel. This is proved from the original balance relations, not assumed. -/
theorem powerWordGenerator_ker (w : OldCategory D Sc cutoff) :
    LinearMap.ker (powerWordGenerator D Sc cutoff L ν w) = powerWordRelationSpan D Sc cutoff L ν w := by
  apply le_antisymm
  · intro h hh
    have hz := congrArg (powerWordContraction D Sc cutoff L ν w) hh
    rw [powerWordContraction_generator, map_zero] at hz
    exact (Submodule.Quotient.mk_eq_zero _).mp hz
  · exact powerWordRelationSpan_le_kernel D Sc cutoff L ν w

/-- The canonical word value is the actual induction of the literal regular
power quotient along coefficient insertion at that word. -/
def powerWordModule : Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν) (liftedPowerRegular D cutoff L)

/-- The selected existing induction-composition comparison identifies actual
right append of a word value with the next word value. -/
def powerWordAppendIso (i : I) :
    BalancedInduction.induced (CyclotomicCrossingTensor.append D Sc cutoff i)
        (powerWordModule D Sc cutoff L ν) ≅ powerWordModule D Sc cutoff L (ν ++ [i]) :=
  ((BalancedInduction.inductionComp (powerWordCoefficientSource D Sc cutoff ν)
      (CyclotomicCrossingTensor.append D Sc cutoff i)).app (liftedPowerRegular D cutoff L)) ≪≫
    ((BalancedInduction.inductionFunctorIsoOfEq _ _
      (powerWordCoefficientSource_append D Sc cutoff ν i)).app (liftedPowerRegular D cutoff L))

private theorem powerIdeal_context_mem_image (w : OldCategory D Sc cutoff)
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L) :
    ∀ (x : (⟨ν⟩ : OldCategory D Sc cutoff) ⟶ ⟨ν⟩)
      (h : (⟨ν⟩ : OldCategory D Sc cutoff) ⟶ w),
      x ≫ coefficientEndomorphism D Sc cutoff ν a ≫ h ∈
        (elementaryPowerHomSpan D Sc cutoff L ν w.word).map (ideal D Sc cutoff ν w.word).mkQ := by
  change a ∈ TwoSidedIdeal.span (Set.range fun j => elementaryCoefficients (k := k) D cutoff j ^ L j) at ha
  induction ha using TwoSidedIdeal.span_induction with
  | mem a ha =>
    obtain ⟨j, rfl⟩ := ha
    intro x h
    obtain ⟨x, rfl⟩ := (ideal D Sc cutoff ν ν).mkQ_surjective x
    obtain ⟨h, rfl⟩ := (ideal D Sc cutoff ν w.word).mkQ_surjective h
    refine ⟨x ≫ ((elementaryCoefficients (k := k) D cutoff j ^ L j) ⊗ₜ[k]
        (𝟙 ((pres D Sc).obj (ob D ν))) : hom D Sc cutoff ν ν) ≫ h,
      Submodule.subset_span ⟨ν, rfl, _, ⟨j, rfl⟩, x, h, rfl⟩, rfl⟩
  | zero =>
    intro x h
    change x ≫ wordSourceScalar D Sc cutoff ν 0 ≫ h ∈ _
    rw [map_zero, Limits.zero_comp, Limits.comp_zero]
    exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    intro x h
    change x ≫ wordSourceScalar D Sc cutoff ν (a + b) ≫ h ∈ _
    rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
    exact Submodule.add_mem _ (ha x h) (hb x h)
  | neg a _ ha =>
    intro x h
    change x ≫ wordSourceScalar D Sc cutoff ν (-a) ≫ h ∈ _
    rw [map_neg, Preadditive.neg_comp, Preadditive.comp_neg]
    exact Submodule.neg_mem _ (ha x h)
  | left_absorb b a _ ha =>
    intro x h
    have he : coefficientEndomorphism D Sc cutoff ν (b * a) =
        coefficientEndomorphism D Sc cutoff ν a ≫ coefficientEndomorphism D Sc cutoff ν b :=
      (coefficientEndomorphism_comp D Sc cutoff ν a b).symm
    rw [he, Category.assoc]
    exact ha x (coefficientEndomorphism D Sc cutoff ν b ≫ h)
  | right_absorb b a _ ha =>
    intro x h
    have he : coefficientEndomorphism D Sc cutoff ν (a * b) =
        coefficientEndomorphism D Sc cutoff ν b ≫ coefficientEndomorphism D Sc cutoff ν a :=
      (coefficientEndomorphism_comp D Sc cutoff ν b a).symm
    rw [he]
    simpa only [Category.assoc] using ha (x ≫ coefficientEndomorphism D Sc cutoff ν b) h

/-- The intrinsic actual coend kernel lies in the independently defined
literal elementary-power image, without commuting arbitrary coefficients. -/
theorem powerWordRelationSpan_le_elementaryPowerImage (w : OldCategory D Sc cutoff) :
    powerWordRelationSpan D Sc cutoff L ν w ≤
      (elementaryPowerHomSpan D Sc cutoff L ν w.word).map (ideal D Sc cutoff ν w.word).mkQ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, h, rfl⟩
  change coefficientEndomorphism D Sc cutoff ν a ≫ h ∈
    (elementaryPowerHomSpan D Sc cutoff L ν w.word).map (ideal D Sc cutoff ν w.word).mkQ
  have ht := powerIdeal_context_mem_image D Sc cutoff L ν w ha (𝟙 _) h
  rw [Category.id_comp] at ht
  exact ht

/-- Even elementary generators can be slid to the representing source;
therefore the actual coend kernel equals the literal two-sided power image. -/
theorem powerWordRelationSpan_eq_elementaryPowerImage (w : OldCategory D Sc cutoff) :
    powerWordRelationSpan D Sc cutoff L ν w =
      (elementaryPowerHomSpan D Sc cutoff L ν w.word).map (ideal D Sc cutoff ν w.word).mkQ := by
  apply le_antisymm (powerWordRelationSpan_le_elementaryPowerImage D Sc cutoff L ν w)
  rintro _ ⟨r, hr, rfl⟩
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨v, _, a, ⟨j, rfl⟩, x, y, rfl⟩ := hr
    let p : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff := elementaryCoefficients D cutoff j ^ L j
    let x₀ : (⟨ν⟩ : OldCategory D Sc cutoff) ⟶ ⟨v⟩ := (ideal D Sc cutoff ν v).mkQ x
    let y₀ : (⟨v⟩ : OldCategory D Sc cutoff) ⟶ w := (ideal D Sc cutoff v w.word).mkQ y
    change x₀ ≫ coefficientEndomorphism D Sc cutoff v p ≫ y₀ ∈ powerWordRelationSpan D Sc cutoff L ν w
    have hp : p ∈ SKM.SYM.elvCoefficientParity D cutoff 0 := by
      simpa only [nsmul_zero] using SetLike.pow_mem_graded (L j)
        (elementaryCoefficients_even (k := k) D cutoff j)
    have hs := coefficientEndomorphism_slide D Sc cutoff hp ν v x₀
    rw [twist_zero] at hs
    rw [← Category.assoc, hs, Category.assoc]
    apply Submodule.subset_span
    exact ⟨p, TwoSidedIdeal.subset_span ⟨j, rfl⟩, x₀ ≫ y₀, rfl⟩
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

/-- Every canonical actual word value lies in the literal power-annihilated
module subcategory. This uses the proved coend generator and the even
coefficient slide, without a weighted replacement. -/
theorem powerWordModule_property : coefficientPowerProperty D Sc cutoff
    (elementaryCoefficients (k := k) D cutoff) L (powerWordModule D Sc cutoff L ν) := by
  apply (coefficientPowerProperty_iff D Sc cutoff _ L _).mpr
  intro j v
  apply LinearMap.ext
  intro z
  obtain ⟨h, rfl⟩ := powerWordGenerator_surjective D Sc cutoff L ν (⟨v⟩ : OldCategory D Sc cutoff) z
  let p : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff := elementaryCoefficients D cutoff j ^ L j
  have hp : p ∈ SKM.SYM.elvCoefficientParity D cutoff 0 := by
    simpa only [nsmul_zero] using SetLike.pow_mem_graded (L j)
      (elementaryCoefficients_even (k := k) D cutoff j)
  change BalancedInduction.postcompose (powerWordCoefficientSource D Sc cutoff ν)
    (liftedPowerRegular D cutoff L).toFunctor (coefficientEndomorphism D Sc cutoff v p)
      (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) h
          (1 : CoefficientPowerQuotient (k := k) D cutoff L)) = 0
  rw [BalancedInduction.postcompose_tensor, coefficientEndomorphism_slide D Sc cutoff hp, twist_zero]
  change coefficientEndomorphism D Sc cutoff ν p ≫ h ∈
    LinearMap.ker (powerWordGenerator D Sc cutoff L ν (⟨v⟩ : OldCategory D Sc cutoff))
  rw [powerWordGenerator_ker]
  exact Submodule.subset_span ⟨p, TwoSidedIdeal.subset_span ⟨j, rfl⟩, h, rfl⟩

/-- The actual word value, in the paper's literal power module category. -/
def powerWordObject : CoefficientPowerModules D Sc cutoff
    (elementaryCoefficients (k := k) D cutoff) L :=
  ⟨powerWordModule D Sc cutoff L ν, powerWordModule_property D Sc cutoff L ν⟩

/-- Full source coordinates in an actual regular-power word value, by the
literal old quotient followed by h tensor 1. -/
def powerWordSourceMap (w : OldCategory D Sc cutoff) :
    (coefficientObj D Sc ν ⟶ coefficientObj D Sc w.word) →ₗ[k]
      (powerWordModule D Sc cutoff L ν).obj w :=
  (powerWordGenerator D Sc cutoff L ν w).comp (sourceToOldHom D Sc cutoff ν w.word)

/-- The precise native source presentation kernel of the actual word coend. -/
theorem powerWordSourceMap_ker (w : OldCategory D Sc cutoff) :
    LinearMap.ker (powerWordSourceMap D Sc cutoff L ν w) =
      ELVRelationSpan D Sc cutoff ν w.word ⊔ CoefficientGeneratorSpan D Sc
        (Set.range fun j : I × ℕ => SKM.SYM.e D k j.1 j.2 ^ L j) ν w.word := by
  rw [powerWordSourceMap, LinearMap.ker_comp, powerWordGenerator_ker,
    powerWordRelationSpan_eq_elementaryPowerImage, sourceToOldHom,
    Submodule.comap_comp, Submodule.comap_map_eq, Submodule.ker_mkQ, sup_comm]
  exact comap_oldIdeal_sup_elementaryPowers D Sc cutoff L ν w.word

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Scheduled word modules in the chosen content categories

SwappedVacuumCoordinates §§4–6 require the actual regular-power word modules
in the truncated content categories used by the chosen Rouquier generators.
The explicit upper coefficient-power bound supplies the required descent;
the actual inclusion counit recovers each supported module.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordContent
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- Explicit coefficient-weight cutoff of the literal power quotient. -/
abbrev powerBound : ℕ := SKM.SYM.elvPowerWeightBound D cutoff L + 1

theorem word_killsWeighted (ν : List I) :
    KillsWeightedCoefficients D Sc cutoff (powerBound D cutoff L) (powerWordModule D Sc cutoff L ν) :=
  (coefficientWeightedIdeal_le_annihilator_iff D Sc cutoff _ _).mp
    ((weighted_le_elementaryPowerIdeal D cutoff L).trans (powerWordObject D Sc cutoff L ν).property)

/-- Literal weighted descent on the unchanged regular-power word carriers. -/
def weightedWord (ν : List I) :
    Superfunctor k (TruncatedCategory D Sc cutoff (powerBound D cutoff L)) (SVec k) :=
  weightedModule D Sc cutoff (powerBound D cutoff L) (powerWordModule D Sc cutoff L ν)
    (word_killsWeighted D Sc cutoff L ν)

/-- Support is proved from the literal old Homs, not assumed of the model. -/
theorem weightedWord_supported (ν : List I) :
    ContentSupported D Sc cutoff (powerBound D cutoff L) (ν : Multiset I)
      (weightedWord D Sc cutoff L ν) := by
  intro w hw
  have hz : ∀ x : (powerWordModule D Sc cutoff L ν).obj (OldCategory.mk w.word), x = 0 := by
    intro x
    obtain ⟨g, rfl⟩ := powerWordGenerator_surjective D Sc cutoff L ν (OldCategory.mk w.word) x
    have hg : g = 0 := oldCategory_hom_eq_zero_of_content_ne D Sc cutoff (f := g) (Ne.symm hw)
    rw [hg, map_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The word module in the actual exact-content category. -/
def contentWord (ν : List I) :
    ContentModules D Sc cutoff (powerBound D cutoff L) (ν : Multiset I) :=
  (BalancedInduction.restriction (contentInclusion D Sc cutoff (powerBound D cutoff L) (ν : Multiset I))).obj
    (weightedWord D Sc cutoff L ν)

/-- The selected even inclusion counit recovers this actual supported module. -/
def contentExtensionIso (ν : List I) :
    BalancedInduction.induced (contentInclusion D Sc cutoff (powerBound D cutoff L) (ν : Multiset I))
      (contentWord D Sc cutoff L ν) ≅ weightedWord D Sc cutoff L ν :=
  contentSupportedCounitIso D Sc cutoff (powerBound D cutoff L) (ν : Multiset I)
    (weightedWord D Sc cutoff L ν) (weightedWord_supported D Sc cutoff L ν)

/-- The chosen truncated append induction is identified with the next actual
word module by the existing quotient/composition comparisons. -/
def weightedAppendIso (ν : List I) (i : I) :
    BalancedInduction.induced (truncatedAppend D Sc cutoff (powerBound D cutoff L) [i])
      (weightedWord D Sc cutoff L ν) ≅ weightedWord D Sc cutoff L (ν ++ [i]) :=
  let N := powerBound D cutoff L
  let M := weightedWord D Sc cutoff L ν
  let R := weightedRestriction D Sc cutoff N M
  let A := append D Sc cutoff i
  let F := BalancedInduction.induced A R
  let hF := induced_killsWeightedCoefficients D Sc cutoff N i R
    (weightedRestriction_kills D Sc cutoff N M)
  (appendWeightedModuleIso D Sc cutoff N i M).symm ≪≫
    weightedModuleIso D Sc cutoff N F (powerWordModule D Sc cutoff L (ν ++ [i])) hF
      (word_killsWeighted D Sc cutoff L (ν ++ [i]))
      ((BalancedInduction.induction A).mapIso
        (weightedRestrictionModuleIso D Sc cutoff N (powerWordModule D Sc cutoff L ν)
          (word_killsWeighted D Sc cutoff L ν)) ≪≫ powerWordAppendIso D Sc cutoff L ν i)

/-- The independently chosen exact-content E sends the chosen content word
to its actual next-word module through the prescribed extension comparison. -/
def contentAppendIso (ν : List I) (i : I) :
    BalancedInduction.induced
      (contentAppendTo D Sc cutoff (powerBound D cutoff L) (ν : Multiset I) [i]
        ((ν ++ [i] : List I) : Multiset I) (Multiset.coe_add ν [i])) (contentWord D Sc cutoff L ν) ≅
    contentWord D Sc cutoff L (ν ++ [i]) :=
  contentAppendToRestrictionIso D Sc cutoff (powerBound D cutoff L) (ν : Multiset I) [i]
      ((ν ++ [i] : List I) : Multiset I) (Multiset.coe_add ν [i]) (contentWord D Sc cutoff L ν) ≪≫
    (BalancedInduction.restriction
      (contentInclusion D Sc cutoff (powerBound D cutoff L) ((ν ++ [i] : List I) : Multiset I))).mapIso
      ((BalancedInduction.induction (truncatedAppend D Sc cutoff (powerBound D cutoff L) [i])).mapIso
        (contentExtensionIso D Sc cutoff L ν) ≪≫ weightedAppendIso D Sc cutoff L ν i)

end OddMath.QuiverHecke.ELVOld.PowerWordContent
end

end

section

/-! # Scheduled word modules under the chosen weight induction

SwappedVacuumCoordinates §§4–6: attach the bounded regular-power word model
to the original weight product and its independently chosen E functor.
All content components are retained. This is an object comparison; transport
of chosen dot/crossing maps remains a separate step.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordWeight
open CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- Every content component of the same actual descended word module. -/
def wordAt (ν : List I) (β : Multiset I) :
    ContentModules D Sc cutoff (PowerWordContent.powerBound D cutoff L) β :=
  (BalancedInduction.restriction (contentInclusion D Sc cutoff
    (PowerWordContent.powerBound D cutoff L) β)).obj (PowerWordContent.weightedWord D Sc cutoff L ν)

/-- The original weight product, retaining every content block. -/
def wordFamily (Λ x : X) (ν : List I) :
    ELVWeightProduct D Sc cutoff (PowerWordContent.powerBound D cutoff L) Λ x :=
  fun β => wordAt D Sc cutoff L ν β.1

/-- The source and target content labels are arbitrary equal presentations
of the same literal word contents. -/
def contentAppendIsoTo (ν : List I) (i : I) (β γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hγ : β + ([i] : Multiset I) = γ) :
    BalancedInduction.induced
      (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [i] γ hγ)
      (wordAt D Sc cutoff L ν β) ≅ wordAt D Sc cutoff L (ν ++ [i]) γ := by
  subst β
  have he : γ = ((ν ++ [i] : List I) : Multiset I) := hγ.symm.trans (Multiset.coe_add ν [i])
  subst γ
  exact PowerWordContent.contentAppendIso D Sc cutoff L ν i

/-- The unchanged original weight associated with the word content. -/
abbrev wordWeight (Λ : X) (ν : List I) : X := blockWeight D Λ (ν : Multiset I)

omit [Fintype I] in
theorem wordWeight_append (Λ : X) (ν : List I) (i : I) :
    wordWeight D Λ ν + D.α i = wordWeight D Λ (ν ++ [i]) := by
  unfold wordWeight
  rw [← Multiset.coe_add, add_comm (ν : Multiset I) ([i] : Multiset I)]
  exact (blockWeight_cons D Λ i (ν : Multiset I)).symm

/-- The occupied block of the original weight product. -/
def wordBlock (Λ : X) (ν : List I) : WeightBlocks D Λ (wordWeight D Λ ν) := ⟨ν, rfl⟩

/-- The actual E component at its actual successor block is the next
regular-power word component, via the given content append comparison. -/
def weightAppendComponentIso (Λ : X) (ν : List I) (i : I) :
    ((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ (wordWeight_append D Λ ν i)).obj
      (wordFamily D Sc cutoff L Λ (wordWeight D Λ ν) ν))
        (blockSucc D Λ i (wordWeight_append D Λ ν i) (wordBlock D Λ ν)) ≅
    wordAt D Sc cutoff L (ν ++ [i])
      (blockSucc D Λ i (wordWeight_append D Λ ν i) (wordBlock D Λ ν)).1 :=
  eqToIso (elvInductionComponent_obj_blockSucc D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    i Λ (wordWeight_append D Λ ν i) (wordBlock D Λ ν)
    (wordFamily D Sc cutoff L Λ (wordWeight D Λ ν) ν)) ≪≫
      contentAppendIsoTo D Sc cutoff L ν i _ _ rfl (by rw [blockSucc_val, add_comm]; rfl)

/-- Other content components are literally zero because the underlying
actual word module has the proved exact support. -/
theorem wordAt_isZero (ν : List I) (β : Multiset I) (hβ : β ≠ (ν : Multiset I)) :
    Limits.IsZero (wordAt D Sc cutoff L ν β) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply Superfunctor.hom_ext
  intro p w
  have hs : Subsingleton ((wordAt D Sc cutoff L ν β).obj w) :=
    PowerWordContent.weightedWord_supported D Sc cutoff L ν w.obj
      (fun he => hβ (w.content.symm.trans he))
  apply SVec.hom_ext
  intro x
  exact hs.elim _ _

private theorem induction_isZero {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Preadditive B] (F : C ⥤ B) [F.Additive] (x : C) (hx : Limits.IsZero x) :
    Limits.IsZero (F.obj x) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  have he : 𝟙 x = 0 := (Limits.IsZero.iff_id_eq_zero _).mp hx
  rw [← F.map_id, he, F.map_zero]

/-- Every nonselected output block of the actual E object is zero. This
includes both absent predecessors and present predecessors outside support. -/
theorem weightAppend_isZero (Λ : X) (ν : List I) (i : I)
    (δ : WeightBlocks D Λ (wordWeight D Λ (ν ++ [i])))
    (hδ : δ ≠ blockSucc D Λ i (wordWeight_append D Λ ν i) (wordBlock D Λ ν)) :
    Limits.IsZero (((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ
      (wordWeight_append D Λ ν i)).obj (wordFamily D Sc cutoff L Λ (wordWeight D Λ ν) ν)) δ) := by
  classical
  change Limits.IsZero ((elvInductionComponent D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    i Λ (wordWeight_append D Λ ν i) δ).obj (wordFamily D Sc cutoff L Λ (wordWeight D Λ ν) ν))
  by_cases hc : ∃ β, blockSucc D Λ i (wordWeight_append D Λ ν i) β = δ
  · obtain ⟨β, rfl⟩ := hc
    have hβ : β.1 ≠ (ν : Multiset I) := by
      intro he
      apply hδ
      exact congrArg (blockSucc D Λ i (wordWeight_append D Λ ν i)) (show β = wordBlock D Λ ν from Subtype.ext he)
    rw [elvInductionComponent_obj_blockSucc]
    exact induction_isZero (elvBlockInd D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      i Λ (wordWeight_append D Λ ν i) β).toFunctor _ (wordAt_isZero D Sc cutoff L ν β.1 hβ)
  · exact elvInductionComponent_isZero D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      i Λ (wordWeight_append D Λ ν i) δ hc _

/-- Component isomorphisms use the given selected comparison on the occupied
block and uniqueness of zero objects on every other block. -/
def weightAppendAtIso (Λ : X) (ν : List I) (i : I)
    (δ : WeightBlocks D Λ (wordWeight D Λ (ν ++ [i]))) :
    (((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ
      (wordWeight_append D Λ ν i)).obj (wordFamily D Sc cutoff L Λ (wordWeight D Λ ν) ν)) δ) ≅
      wordAt D Sc cutoff L (ν ++ [i]) δ.1 := by
  classical
  by_cases hδ : δ = blockSucc D Λ i (wordWeight_append D Λ ν i) (wordBlock D Λ ν)
  · subst δ
    exact weightAppendComponentIso D Sc cutoff L Λ ν i
  · have hβ : δ.1 ≠ ((ν ++ [i] : List I) : Multiset I) := by
      intro he
      apply hδ
      apply Subtype.ext
      change δ.1 = {i} + (ν : Multiset I)
      rw [he, ← Multiset.coe_add]
      exact add_comm _ _
    exact (weightAppend_isZero D Sc cutoff L Λ ν i δ hδ).iso
      (wordAt_isZero D Sc cutoff L (ν ++ [i]) δ.1 hβ)

/-- The whole independently chosen original-weight E object is the next
word family, including all present and absent content blocks. -/
def weightAppendIso (Λ : X) (ν : List I) (i : I) :
    (elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ
      (wordWeight_append D Λ ν i)).obj (wordFamily D Sc cutoff L Λ (wordWeight D Λ ν) ν) ≅
    wordFamily D Sc cutoff L Λ (wordWeight D Λ (ν ++ [i])) (ν ++ [i]) :=
  Pi.isoMk (fun δ => weightAppendAtIso D Sc cutoff L Λ ν i δ)

end OddMath.QuiverHecke.ELVOld.PowerWordWeight
end

end

section

/-! # Enriched Yoneda for actual regular-power word modules

SwappedVacuumCoordinates §3. The module source is actual induction of the
regular A/T vacuum, with its proved coend kernel. The inverse coordinate
map descends the full-parity twisted module-action formula through that
kernel, including every coefficient vector.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordYoneda
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ν : List I)
  (M : CoefficientPowerModules D Sc cutoff (elementaryCoefficients (k := k) D cutoff) L)
local notation "v" => (OldCategory.mk ν : OldCategory D Sc cutoff)
local notation "W" => powerWordModule D Sc cutoff L ν
local notation "F" => M.obj

private def rawComponent (m : (F).obj v) (p : ZMod 2) (w : OldCategory D Sc cutoff) :
    (v ⟶ w) →ₗ[k] (F).obj w where
  toFun h := (F).map (twist k p h) (((F).obj v).proj p m)
  map_add' h h' := by
    simp only [map_add, Superfunctor.map, Functor.map_add, SVec.add_apply]
  map_smul' c h := by
    simp only [map_smul, Superfunctor.map, Functor.map_smul, SVec.smul_apply, RingHom.id_apply]

private theorem rawComponent_kills (m : (F).obj v) (p : ZMod 2) (w : OldCategory D Sc cutoff) :
    LinearMap.ker (powerWordGenerator D Sc cutoff L ν w) ≤
      LinearMap.ker (rawComponent D Sc cutoff L ν M m p w) := by
  rw [powerWordGenerator_ker]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, h, rfl⟩
  have hk : KillsCoefficient D Sc cutoff F a :=
    (mem_coefficientAnnihilator D Sc cutoff F a).mp (M.property ha)
  have hz : (F).map (coefficientEndomorphism D Sc cutoff ν a) = 0 := hk ν
  have htw : (F).map (twist k p (coefficientEndomorphism D Sc cutoff ν a)) = 0 := by
    change (F).toFunctor.map (twist k p (coefficientEndomorphism D Sc cutoff ν a)) = 0
    rw [map_twist, show (F).toFunctor.map (coefficientEndomorphism D Sc cutoff ν a) = 0 from hz, map_zero]
  change (F).map (twist k p (coefficientEndomorphism D Sc cutoff ν a ≫ h)) (((F).obj v).proj p m) = 0
  rw [twist_comp]
  simp only [Superfunctor.map, Functor.map_comp, SVec.comp_apply]
  rw [show (F).toFunctor.map (twist k p (coefficientEndomorphism D Sc cutoff ν a)) = 0 from htw,
    SVec.zero_apply, map_zero]

/-- The full-parity module-action formula descends through the actual word
coend generator, using its proved presentation kernel. -/
def component (m : (F).obj v) (p : ZMod 2) (w : OldCategory D Sc cutoff) :
    (W).obj w →ₗ[k] (F).obj w :=
  ((LinearMap.ker (powerWordGenerator D Sc cutoff L ν w)).liftQ
    (rawComponent D Sc cutoff L ν M m p w) (rawComponent_kills D Sc cutoff L ν M m p w)).comp
      ((powerWordGenerator D Sc cutoff L ν w).quotKerEquivOfSurjective
        (powerWordGenerator_surjective D Sc cutoff L ν w)).symm.toLinearMap

/-- Coordinates on every generator, with the complete old-Hom parity twist. -/
theorem component_generator (m : (F).obj v) (p : ZMod 2) (w : OldCategory D Sc cutoff) (h : v ⟶ w) :
    component D Sc cutoff L ν M m p w (powerWordGenerator D Sc cutoff L ν w h) =
      (F).map (twist k p h) (((F).obj v).proj p m) := by
  change (LinearMap.ker (powerWordGenerator D Sc cutoff L ν w)).liftQ
    (rawComponent D Sc cutoff L ν M m p w) (rawComponent_kills D Sc cutoff L ν M m p w)
      (((powerWordGenerator D Sc cutoff L ν w).quotKerEquivOfSurjective
        (powerWordGenerator_surjective D Sc cutoff L ν w)).symm
          (powerWordGenerator D Sc cutoff L ν w h)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

private theorem tensor_proj_even {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (R : C ⥤ SVec k) [R.Additive] [R.Linear k] [IsSuperfunctor k R]
    (q : ZMod 2) (z : C) {w : B} (h : J.obj z ⟶ w) (m : R.obj z)
    (hm : m ∈ (R.obj z).part 0) :
    (BalancedInduction.superspace J R w).proj q (BalancedInduction.tensor J R z h m) =
      BalancedInduction.tensor J R z (proj k q h) m := by
  rw [BalancedInduction.proj_tensor]
  simp only [SVec.proj_apply_of_mem_part _ hm, ite_true, one_ne_zero, ite_false,
    BalancedInduction.tensor_zero_right, add_zero]

theorem generator_proj (q : ZMod 2) (w : OldCategory D Sc cutoff) (h : v ⟶ w) :
    ((W).obj w).proj q (powerWordGenerator D Sc cutoff L ν w h) =
      powerWordGenerator D Sc cutoff L ν w (proj k q h) := by
  let J := powerWordCoefficientSource D Sc cutoff ν
  let R := (liftedPowerRegular (k := k) D cutoff L).toFunctor
  have hone : (1 : CoefficientPowerQuotient (k := k) D cutoff L) ∈
      (R.obj (powerCoefficientStar D cutoff)).part 0 :=
    SetLike.GradedOne.one_mem (A := coefficientPowerParity (k := k) D cutoff L)
  change (BalancedInduction.superspace J R w).proj q
      (BalancedInduction.tensor J R (powerCoefficientStar D cutoff) h
        (1 : CoefficientPowerQuotient (k := k) D cutoff L)) =
    BalancedInduction.tensor J R (powerCoefficientStar D cutoff) (proj k q h)
      (1 : CoefficientPowerQuotient (k := k) D cutoff L)
  exact tensor_proj_even J R q _ h _ hone

theorem generator_mem {q : ZMod 2} (w : OldCategory D Sc cutoff) (h : v ⟶ w)
    (hh : h ∈ parity (R := k) v w q) :
    powerWordGenerator D Sc cutoff L ν w h ∈ ((W).obj w).part q := by
  rw [SVec.mem_part_iff, generator_proj, proj_of_mem hh]

theorem generator_naturality {w z : OldCategory D Sc cutoff}
    (a : w ⟶ z) (h : v ⟶ w) :
    (W).map a (powerWordGenerator D Sc cutoff L ν w h) =
      powerWordGenerator D Sc cutoff L ν z (h ≫ a) := by
  let J := powerWordCoefficientSource D Sc cutoff ν
  let R := (liftedPowerRegular (k := k) D cutoff L).toFunctor
  change BalancedInduction.postcompose J R a
    (BalancedInduction.tensor J R (powerCoefficientStar D cutoff) h
      (1 : CoefficientPowerQuotient (k := k) D cutoff L)) =
    BalancedInduction.tensor J R (powerCoefficientStar D cutoff) (h ≫ a)
      (1 : CoefficientPowerQuotient (k := k) D cutoff L)
  exact BalancedInduction.postcompose_tensor J R a (powerCoefficientStar D cutoff) h _

/-- The enriched transformation determined by an arbitrary vector. -/
def fromElement (m : (F).obj v) : W ⟶ F :=
  Superfunctor.homMk {
    app := component D Sc cutoff L ν M m
    app_mem := by
      intro p w
      apply SVec.mem_parityHom_of_apply_mem
      intro q x hx
      obtain ⟨h, rfl⟩ := powerWordGenerator_surjective D Sc cutoff L ν w x
      have hg : powerWordGenerator D Sc cutoff L ν w (proj k q h) =
          powerWordGenerator D Sc cutoff L ν w h := by
        rw [← generator_proj, (SVec.mem_part_iff _).mp hx]
      rw [← hg, component_generator]
      rw [add_comm q p]
      exact SVec.apply_mem_part ((F).map_mem (twist_mem p (proj_mem q h)))
        (((F).obj v).proj_mem_part p m)
    naturality := by
      intro p w z q a ha
      apply LinearMap.ext
      intro x
      obtain ⟨h, rfl⟩ := powerWordGenerator_surjective D Sc cutoff L ν w x
      change component D Sc cutoff L ν M m p z
        ((W).map a (powerWordGenerator D Sc cutoff L ν w h)) =
        koszulSign p q • (F).map a
          (component D Sc cutoff L ν M m p w (powerWordGenerator D Sc cutoff L ν w h))
      rw [generator_naturality, component_generator, component_generator,
        twist_comp, twist_of_mem p ha, Linear.comp_smul, koszulSign_smul (R := k)]
      simp only [Superfunctor.map, Functor.map_smul, Functor.map_comp, SVec.smul_apply,
        SVec.comp_apply] }

/-- The actual regular-power generator at the identity old arrow. -/
def unitVector : (W).obj v := powerWordGenerator D Sc cutoff L ν v (𝟙 v)

theorem unitVector_even : unitVector D Sc cutoff L ν ∈ ((W).obj v).part 0 :=
  generator_mem D Sc cutoff L ν v (𝟙 v) (id_mem v)

/-- Evaluation retains both parity components of an enriched transformation. -/
def evaluate (t : W ⟶ F) : (F).obj v :=
  t.app 0 v (unitVector D Sc cutoff L ν) + t.app 1 v (unitVector D Sc cutoff L ν)

theorem evaluate_part (t : W ⟶ F) (p : ZMod 2) :
    t.app p v (unitVector D Sc cutoff L ν) ∈ ((F).obj v).part p := by
  have hp := SVec.apply_mem_part (t.app_mem p v) (unitVector_even D Sc cutoff L ν)
  rw [zero_add] at hp
  exact hp

@[simp] theorem evaluate_fromElement (m : (F).obj v) :
    evaluate D Sc cutoff L ν M (fromElement D Sc cutoff L ν M m) = m := by
  change component D Sc cutoff L ν M m 0 v (powerWordGenerator D Sc cutoff L ν v (𝟙 v)) +
    component D Sc cutoff L ν M m 1 v (powerWordGenerator D Sc cutoff L ν v (𝟙 v)) = m
  rw [component_generator, component_generator, twist_id, twist_id]
  have hi : (F).map (𝟙 v : v ⟶ v) = 𝟙 ((F).obj v) := (F).toFunctor.map_id v
  rw [hi]
  exact ((F).obj v).proj_apply_add m

/-- Every component on every word generator is forced by enriched naturality. -/
theorem app_generator (t : W ⟶ F) (p : ZMod 2) (w : OldCategory D Sc cutoff) (h : v ⟶ w) :
    t.app p w (powerWordGenerator D Sc cutoff L ν w h) =
      (F).map (twist k p h) (t.app p v (unitVector D Sc cutoff L ν)) := by
  refine induction_on (R := k) h ?_ ?_ ?_
  · simp [Superfunctor.map]
  · intro q h hh
    have hn := congrArg (fun a => a (unitVector D Sc cutoff L ν)) (t.naturality p h hh)
    change t.app p w ((W).map h (powerWordGenerator D Sc cutoff L ν v (𝟙 v))) =
      koszulSign p q • (F).map h (t.app p v (unitVector D Sc cutoff L ν)) at hn
    rw [generator_naturality, Category.id_comp, koszulSign_smul (R := k)] at hn
    rw [twist_of_mem p hh]
    simpa only [Superfunctor.map, Functor.map_smul, SVec.smul_apply] using hn
  · intro a b ha hb
    simp only [map_add, Superfunctor.map, Functor.map_add, SVec.add_apply, ha, hb]

theorem evaluate_component (t : W ⟶ F) (p : ZMod 2) :
    ((F).obj v).proj p (evaluate D Sc cutoff L ν M t) =
      t.app p v (unitVector D Sc cutoff L ν) := by
  rw [evaluate, map_add, SVec.proj_apply_of_mem_part _ (evaluate_part D Sc cutoff L ν M t 0),
    SVec.proj_apply_of_mem_part _ (evaluate_part D Sc cutoff L ν M t 1)]
  rcases parity_eq_zero_or_one p with rfl | rfl <;> simp

theorem fromElement_evaluate (t : W ⟶ F) :
    fromElement D Sc cutoff L ν M (evaluate D Sc cutoff L ν M t) = t := by
  apply Superfunctor.hom_ext
  intro p w
  apply LinearMap.ext
  intro x
  obtain ⟨h, rfl⟩ := powerWordGenerator_surjective D Sc cutoff L ν w x
  change component D Sc cutoff L ν M (evaluate D Sc cutoff L ν M t) p w
    (powerWordGenerator D Sc cutoff L ν w h) = _
  rw [component_generator, evaluate_component]
  exact (app_generator D Sc cutoff L ν M t p w h).symm

/-- Enriched Yoneda for the actual induced regular A/T word module. -/
def homEquiv : (W ⟶ F) ≃ₗ[k] (F).obj v where
  toFun := evaluate D Sc cutoff L ν M
  invFun := fromElement D Sc cutoff L ν M
  left_inv := fromElement_evaluate D Sc cutoff L ν M
  right_inv := evaluate_fromElement D Sc cutoff L ν M
  map_add' t s := by
    change (t.app 0 v (unitVector D Sc cutoff L ν) + s.app 0 v (unitVector D Sc cutoff L ν)) +
      (t.app 1 v (unitVector D Sc cutoff L ν) + s.app 1 v (unitVector D Sc cutoff L ν)) =
      (t.app 0 v (unitVector D Sc cutoff L ν) + t.app 1 v (unitVector D Sc cutoff L ν)) +
      (s.app 0 v (unitVector D Sc cutoff L ν) + s.app 1 v (unitVector D Sc cutoff L ν))
    abel
  map_smul' r t := by
    change r • t.app 0 v (unitVector D Sc cutoff L ν) + r • t.app 1 v (unitVector D Sc cutoff L ν) =
      r • (t.app 0 v (unitVector D Sc cutoff L ν) + t.app 1 v (unitVector D Sc cutoff L ν))
    exact (smul_add _ _ _).symm

theorem evaluate_proj (t : W ⟶ F) (p : ZMod 2) :
    evaluate D Sc cutoff L ν M (proj k p t) =
      ((F).obj v).proj p (evaluate D Sc cutoff L ν M t) := by
  rw [evaluate_component]
  rcases parity_eq_zero_or_one p with rfl | rfl
  · change (proj k 0 t).app 0 v (unitVector D Sc cutoff L ν) +
      (proj k 0 t).app 1 v (unitVector D Sc cutoff L ν) = _
    simp only [Superfunctor.proj_app, ite_true, one_ne_zero, ite_false]
    exact add_zero _
  · change (proj k 1 t).app 0 v (unitVector D Sc cutoff L ν) +
      (proj k 1 t).app 1 v (unitVector D Sc cutoff L ν) = _
    simp only [Superfunctor.proj_app, ite_true, zero_ne_one, ite_false]
    exact zero_add _

end OddMath.QuiverHecke.ELVOld.PowerWordYoneda
end

end

section

/-! # Cyclicity of the full regular-power word module on exact content

SwappedVacuumCoordinates §4 uses the word identity as cyclic vector in the
signed Hom model. Equality on this unit determines whole supernatural module
maps: all full coefficient vectors are covered by the proved generator
surjectivity, not an assumed faithful evaluation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordContentCyclicity
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ν : List I) (β : Multiset I) (hν : (ν : Multiset I) = β)

/-- The literal word object in its own exact content category. -/
def wordObject : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) β :=
  ⟨⟨ν⟩, hν⟩

/-- The actual old-Hom identity tensor the regular coefficient unit. -/
def wordUnit : (PowerWordWeight.wordAt D Sc cutoff L ν β).obj (wordObject D Sc cutoff L ν β hν) :=
  PowerWordYoneda.unitVector D Sc cutoff L ν

theorem wordUnit_even : wordUnit D Sc cutoff L ν β hν ∈
    ((PowerWordWeight.wordAt D Sc cutoff L ν β).obj (wordObject D Sc cutoff L ν β hν)).part 0 :=
  PowerWordYoneda.unitVector_even D Sc cutoff L ν

/-- Each entire old arrow, including its coefficients, maps to this literal
quotient arrow inside the chosen content category. -/
def arrowFromOld (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) β)
    (g : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ OldCategory.mk w.obj.word) :
    wordObject D Sc cutoff L ν β hν ⟶ w :=
  truncateOld D Sc cutoff (PowerWordContent.powerBound D cutoff L) ν w.obj.word g

/-- The full old coefficient/Hom generator on the unchanged model carrier. -/
def generator (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) β) :
    ((OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ OldCategory.mk w.obj.word) →ₗ[k]
      (PowerWordWeight.wordAt D Sc cutoff L ν β).obj w :=
  powerWordGenerator D Sc cutoff L ν (OldCategory.mk w.obj.word)

theorem generator_surjective
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) β) :
    Function.Surjective (generator D Sc cutoff L ν β w) :=
  powerWordGenerator_surjective D Sc cutoff L ν (OldCategory.mk w.obj.word)

/-- Every vector is obtained from the unit by a full old arrow in the
actual descended content action. -/
theorem generator_as_map_unit
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) β)
    (g : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ OldCategory.mk w.obj.word) :
    (PowerWordWeight.wordAt D Sc cutoff L ν β).map (arrowFromOld D Sc cutoff L ν β hν w g)
      (wordUnit D Sc cutoff L ν β hν) = generator D Sc cutoff L ν β w g := by
  have hm := weightedRestrictionModule_map D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    (powerWordModule D Sc cutoff L ν) (PowerWordContent.word_killsWeighted D Sc cutoff L ν)
    (OldCategory.mk ν) (OldCategory.mk w.obj.word) g
  change (PowerWordContent.weightedWord D Sc cutoff L ν).map
    ((oldTruncateFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L)).map g) =
      (powerWordModule D Sc cutoff L ν).map g at hm
  change (PowerWordContent.weightedWord D Sc cutoff L ν).map
    ((oldTruncateFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L)).map g)
      (PowerWordYoneda.unitVector D Sc cutoff L ν) = _
  rw [hm]
  change (powerWordModule D Sc cutoff L ν).map g
    (powerWordGenerator D Sc cutoff L ν (OldCategory.mk ν) (𝟙 _)) =
      powerWordGenerator D Sc cutoff L ν (OldCategory.mk w.obj.word) g
  simpa only [Category.id_comp] using PowerWordYoneda.generator_naturality D Sc cutoff L ν g (𝟙 _)

variable (M : ContentModules D Sc cutoff (PowerWordContent.powerBound D cutoff L) β)

/-- The entire coefficient arrow remains inside the total parity twist. -/
theorem app_generator
    (f : PowerWordWeight.wordAt D Sc cutoff L ν β ⟶ M) (p : ZMod 2)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) β)
    (g : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ OldCategory.mk w.obj.word) :
    f.app p w (generator D Sc cutoff L ν β w g) =
      M.map (twist k p (arrowFromOld D Sc cutoff L ν β hν w g))
        (f.app p (wordObject D Sc cutoff L ν β hν) (wordUnit D Sc cutoff L ν β hν)) := by
  have hn := congrArg (fun a => a (wordUnit D Sc cutoff L ν β hν))
    ((f.isSupernatural p).naturality_twist (arrowFromOld D Sc cutoff L ν β hν w g))
  change f.app p w ((PowerWordWeight.wordAt D Sc cutoff L ν β).map
      (arrowFromOld D Sc cutoff L ν β hν w g) (wordUnit D Sc cutoff L ν β hν)) = _ at hn
  rw [generator_as_map_unit] at hn
  exact hn

/-- Unit evaluation retains both homogeneous components. -/
def evaluate (f : PowerWordWeight.wordAt D Sc cutoff L ν β ⟶ M) :
    M.obj (wordObject D Sc cutoff L ν β hν) := f.total (wordObject D Sc cutoff L ν β hν) (wordUnit D Sc cutoff L ν β hν)

private theorem evaluate_part (f : PowerWordWeight.wordAt D Sc cutoff L ν β ⟶ M) (p : ZMod 2) :
    f.app p (wordObject D Sc cutoff L ν β hν) (wordUnit D Sc cutoff L ν β hν) ∈
      (M.obj (wordObject D Sc cutoff L ν β hν)).part p := by
  have hp := SVec.apply_mem_part (f.app_mem p _) (wordUnit_even D Sc cutoff L ν β hν)
  rw [zero_add] at hp
  exact hp

theorem evaluate_component (f : PowerWordWeight.wordAt D Sc cutoff L ν β ⟶ M) (p : ZMod 2) :
    (M.obj (wordObject D Sc cutoff L ν β hν)).proj p (evaluate D Sc cutoff L ν β hν M f) =
      f.app p (wordObject D Sc cutoff L ν β hν) (wordUnit D Sc cutoff L ν β hν) := by
  change (M.obj (wordObject D Sc cutoff L ν β hν)).proj p (_ + _) = _
  rw [map_add, SVec.proj_apply_of_mem_part _ (evaluate_part D Sc cutoff L ν β hν M f 0),
    SVec.proj_apply_of_mem_part _ (evaluate_part D Sc cutoff L ν β hν M f 1)]
  rcases parity_eq_zero_or_one p with rfl | rfl <;> simp

/-- Equality on the unit implies equality on every vector of every content
component, including all exterior coefficient classes. -/
theorem hom_ext (f g : PowerWordWeight.wordAt D Sc cutoff L ν β ⟶ M)
    (h : evaluate D Sc cutoff L ν β hν M f = evaluate D Sc cutoff L ν β hν M g) : f = g := by
  apply Superfunctor.hom_ext
  intro p w
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := generator_surjective D Sc cutoff L ν β w x
  rw [app_generator, app_generator]
  rw [← evaluate_component, ← evaluate_component, h]

end OddMath.QuiverHecke.ELVOld.PowerWordContentCyclicity
end

end

section

/-! Native signed old-Hom maps between actual regular-power word modules. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordMorphisms
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (s t : List I)
local notation "vs" => (OldCategory.mk s : OldCategory D Sc cutoff)
local notation "vt" => (OldCategory.mk t : OldCategory D Sc cutoff)
local notation "Ws" => powerWordModule D Sc cutoff L s
local notation "Wt" => powerWordModule D Sc cutoff L t

/-- Contravariant native word map, retaining both homogeneous components. -/
def fromArrow (g : vt ⟶ vs) : Ws ⟶ Wt :=
  PowerWordYoneda.fromElement D Sc cutoff L s (powerWordObject D Sc cutoff L t)
    (powerWordGenerator D Sc cutoff L t vs g)

/-- The actual generator formula twists all of h, including its coefficients. -/
theorem fromArrow_generator (g : vt ⟶ vs) (p : ZMod 2) (w : OldCategory D Sc cutoff)
    (h : vs ⟶ w) :
    (fromArrow D Sc cutoff L s t g).app p w (powerWordGenerator D Sc cutoff L s w h) =
      powerWordGenerator D Sc cutoff L t w (proj k p g ≫ twist k p h) := by
  change PowerWordYoneda.component D Sc cutoff L s (powerWordObject D Sc cutoff L t)
    (powerWordGenerator D Sc cutoff L t vs g) p w (powerWordGenerator D Sc cutoff L s w h) = _
  rw [PowerWordYoneda.component_generator]
  change (Wt).map (twist k p h)
    (((Wt).obj vs).proj p (powerWordGenerator D Sc cutoff L t vs g)) = _
  rw [PowerWordYoneda.generator_proj, PowerWordYoneda.generator_naturality]

theorem fromArrow_mem {p : ZMod 2} (g : vt ⟶ vs) (hg : g ∈ parity (R := k) vt vs p) :
    fromArrow D Sc cutoff L s t g ∈ parity (R := k) _ _ p := by
  apply mem_iff_proj.mpr
  apply (PowerWordYoneda.homEquiv D Sc cutoff L s (powerWordObject D Sc cutoff L t)).injective
  change PowerWordYoneda.evaluate D Sc cutoff L s (powerWordObject D Sc cutoff L t)
    (proj k p (fromArrow D Sc cutoff L s t g)) =
    PowerWordYoneda.evaluate D Sc cutoff L s (powerWordObject D Sc cutoff L t)
      (fromArrow D Sc cutoff L s t g)
  rw [PowerWordYoneda.evaluate_proj]
  change ((Wt).obj vs).proj p
    (PowerWordYoneda.evaluate D Sc cutoff L s (powerWordObject D Sc cutoff L t)
      (PowerWordYoneda.fromElement D Sc cutoff L s (powerWordObject D Sc cutoff L t)
        (powerWordGenerator D Sc cutoff L t vs g))) = _
  rw [PowerWordYoneda.evaluate_fromElement]
  change ((Wt).obj vs).proj p (powerWordGenerator D Sc cutoff L t vs g) =
    PowerWordYoneda.evaluate D Sc cutoff L s (powerWordObject D Sc cutoff L t)
      (PowerWordYoneda.fromElement D Sc cutoff L s (powerWordObject D Sc cutoff L t)
        (powerWordGenerator D Sc cutoff L t vs g))
  rw [PowerWordYoneda.evaluate_fromElement, PowerWordYoneda.generator_proj, proj_of_mem hg]

/-- Actual coefficient sliding supplies the constant supernatural old-Hom
family. No separate commuting-coefficient premise is assumed. -/
theorem coefficientSourceNatural {p : ZMod 2} (g : vt ⟶ vs)
    (hg : g ∈ parity (R := k) vt vs p) :
    IsSupernatural k p (F := powerWordCoefficientSource D Sc cutoff t)
      (G := powerWordCoefficientSource D Sc cutoff s) (fun _ => g) where
  mem _ := hg
  naturality {z z'} {q} {f} hf := by
    let a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff := f
    have ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff q := hf
    change coefficientEndomorphism D Sc cutoff t a ≫ g =
      sign k (p * q) • (g ≫ coefficientEndomorphism D Sc cutoff s a)
    rw [coefficientEndomorphism_slide D Sc cutoff ha, twist_of_mem q hg,
      Linear.comp_smul, smul_smul, mul_comm q p, Supercategory.sign_mul_self, one_smul]

private theorem transform_unit {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J K : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {p : ZMod 2} {α : ∀ z, J.obj z ⟶ K.obj z} (hα : IsSupernatural k p α)
    (R : Superfunctor k C (SVec k)) (q : ZMod 2) (z : C) (m : R.obj z) :
    (BalancedInduction.transformComponent hα R).app q (K.obj z)
      (BalancedInduction.tensor K R.toFunctor z (𝟙 (K.obj z)) m) =
      if q = p then BalancedInduction.tensor J R.toFunctor z (α z) m else 0 := by
  rw [BalancedInduction.transformComponent_apply]
  split_ifs
  · rw [BalancedInduction.transformLinear_tensor, twist_id, Category.comp_id]
  · rfl

/-- The native word map agrees with the established actual induced
supernatural transformation, on the complete balanced quotient. -/
theorem fromArrow_eq_transform {p : ZMod 2} (g : vt ⟶ vs)
    (hg : g ∈ parity (R := k) vt vs p) :
    fromArrow D Sc cutoff L s t g =
      BalancedInduction.transformComponent (coefficientSourceNatural D Sc cutoff s t g hg)
        (liftedPowerRegular D cutoff L) := by
  apply (PowerWordYoneda.homEquiv D Sc cutoff L s (powerWordObject D Sc cutoff L t)).injective
  change PowerWordYoneda.evaluate D Sc cutoff L s (powerWordObject D Sc cutoff L t)
    (PowerWordYoneda.fromElement D Sc cutoff L s (powerWordObject D Sc cutoff L t)
      (powerWordGenerator D Sc cutoff L t vs g)) = _
  rw [PowerWordYoneda.evaluate_fromElement]
  let J := powerWordCoefficientSource D Sc cutoff t
  let K := powerWordCoefficientSource D Sc cutoff s
  let R := liftedPowerRegular (k := k) D cutoff L
  let hα := coefficientSourceNatural D Sc cutoff s t g hg
  change BalancedInduction.tensor J R.toFunctor (powerCoefficientStar D cutoff) g
      (1 : CoefficientPowerQuotient (k := k) D cutoff L) =
    (BalancedInduction.transformComponent hα R).app 0 (K.obj (powerCoefficientStar D cutoff))
      (BalancedInduction.tensor K R.toFunctor (powerCoefficientStar D cutoff)
        (𝟙 (K.obj (powerCoefficientStar D cutoff)))
        (1 : CoefficientPowerQuotient (k := k) D cutoff L)) +
    (BalancedInduction.transformComponent hα R).app 1 (K.obj (powerCoefficientStar D cutoff))
      (BalancedInduction.tensor K R.toFunctor (powerCoefficientStar D cutoff)
        (𝟙 (K.obj (powerCoefficientStar D cutoff)))
        (1 : CoefficientPowerQuotient (k := k) D cutoff L))
  rw [transform_unit J K hα R, transform_unit J K hα R]
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [ite_true, one_ne_zero, zero_ne_one, ite_false, zero_add, add_zero]

/-- Composition retains the super-opposite convolution, including the
odd-odd minus. It uses the full old Homs, with all exterior coefficients. -/
theorem composition_generator (u : List I) (g : vt ⟶ vs)
    (f : (OldCategory.mk u : OldCategory D Sc cutoff) ⟶ vt) (p : ZMod 2) :
    (fromArrow D Sc cutoff L s t g ≫ fromArrow D Sc cutoff L t u f).app p vs
      (powerWordGenerator D Sc cutoff L s vs (𝟙 vs)) =
      powerWordGenerator D Sc cutoff L u vs (proj k p f ≫ proj k 0 g) +
        sign k (p + 1) • powerWordGenerator D Sc cutoff L u vs
          (proj k (p + 1) f ≫ proj k 1 g) := by
  change (fromArrow D Sc cutoff L t u f).app p vs
      ((fromArrow D Sc cutoff L s t g).app 0 vs
        (powerWordGenerator D Sc cutoff L s vs (𝟙 vs))) +
    (fromArrow D Sc cutoff L t u f).app (p + 1) vs
      ((fromArrow D Sc cutoff L s t g).app 1 vs
        (powerWordGenerator D Sc cutoff L s vs (𝟙 vs))) = _
  rw [fromArrow_generator D Sc cutoff L s t g 0 vs (𝟙 vs),
    fromArrow_generator D Sc cutoff L s t g 1 vs (𝟙 vs), twist_id, twist_id,
    Category.comp_id, Category.comp_id, fromArrow_generator, fromArrow_generator,
    twist_of_mem p (proj_mem 0 g), twist_of_mem (p + 1) (proj_mem 1 g),
    mul_zero, mul_one, sign_zero, one_smul, Linear.comp_smul, map_smul]

end OddMath.QuiverHecke.ELVOld.PowerWordMorphisms
end

end

section

/-! The selected regular-power word append comparison and its actual dot. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordAppend
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ν : List I) (i : I)

/-- The literal total map of the selected word-append isomorphism. -/
def appendLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (append D Sc cutoff i)
      (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L)).toFunctor w →ₗ[k]
      BalancedInduction.Obj (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
        (liftedPowerRegular D cutoff L).toFunctor w :=
  (powerWordAppendIso D Sc cutoff L ν i).hom.total w

private theorem functorEq_tensor {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J K : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K] (h : J = K)
    (R : Superfunctor k C (SVec k)) (v : C) (w : B) (g : J.obj v ⟶ w) (m : R.obj v) :
    ((BalancedInduction.inductionFunctorIsoOfEq J K h).hom.app R).total w
      (BalancedInduction.tensor J R.toFunctor v g m) =
      BalancedInduction.tensor K R.toFunctor v
        (eqToHom (congrArg (fun F : C ⥤ B => F.obj v) h).symm ≫ g) m := by
  subst K
  simp only [BalancedInduction.inductionFunctorIsoOfEq, Iso.refl_hom, NatTrans.id_app,
    SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one,
    add_zero, eqToHom_refl, Category.id_comp]
  rfl

private theorem comparison_tensor {C B A : Type u}
    [Category.{u} C] [Category.{u} B] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ B) (K : B ⥤ A) (P : C ⥤ A)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    [P.Additive] [P.Linear k] [IsSuperfunctor k P] (he : J ⋙ K = P)
    (R : Superfunctor k C (SVec k)) (v : C) (s : B) (w : A)
    (g : K.obj s ⟶ w) (h : J.obj v ⟶ s) (a : R.obj v) :
    (((BalancedInduction.inductionComp J K).app R ≪≫
      (BalancedInduction.inductionFunctorIsoOfEq _ _ he).app R).hom.total w)
        (BalancedInduction.tensor K (BalancedInduction.induced J R).toFunctor s g
          (BalancedInduction.tensor J R.toFunctor v h a)) =
      BalancedInduction.tensor P R.toFunctor v
        (eqToHom (congrArg (fun F : C ⥤ A => F.obj v) he).symm ≫ (K.map h ≫ g)) a := by
  rw [Iso.trans_hom, Superfunctor.comp_total]
  change (((BalancedInduction.inductionFunctorIsoOfEq _ _ he).hom.app R).total w)
    ((((BalancedInduction.inductionComp J K).hom.app R).total w)
      (BalancedInduction.tensor K (BalancedInduction.induced J R).toFunctor s g
        (BalancedInduction.tensor J R.toFunctor v h a))) = _
  have hc : (((BalancedInduction.inductionComp J K).hom.app R).total w) =
      (((BalancedInduction.inductionComp J K).hom.app R).app 0 w) := by
    rw [SuperNatTrans.total, BalancedInduction.inductionComp_hom_app_one, add_zero]
  rw [hc, BalancedInduction.inductionComp_hom_tensor, functorEq_tensor]

/-- The selected comparison on every nested vector, including arbitrary
full regular-power coefficient classes. -/
theorem appendLinear_tensor (s w : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ w)
    (h : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ s)
    (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    appendLinear D Sc cutoff L ν i w
      (BalancedInduction.tensor (append D Sc cutoff i)
        (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L)).toFunctor s g
        (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
          (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) h a)) =
      BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
        (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff)
        ((append D Sc cutoff i).map h ≫ g) a := by
  have hh := comparison_tensor (powerWordCoefficientSource D Sc cutoff ν)
    (append D Sc cutoff i) (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
    (powerWordCoefficientSource_append D Sc cutoff ν i) (liftedPowerRegular D cutoff L)
    (powerCoefficientStar D cutoff) s w g h a
  have he : eqToHom (congrArg (fun F : PowerCoefficientCategory (k := k) D cutoff ⥤
      OldCategory D Sc cutoff => F.obj (powerCoefficientStar D cutoff))
        (powerWordCoefficientSource_append D Sc cutoff ν i)).symm =
      (𝟙 (OldCategory.mk (ν ++ [i]) : OldCategory D Sc cutoff)) := rfl
  erw [he, Category.id_comp] at hh
  unfold appendLinear powerWordAppendIso powerWordModule
  exact hh

private theorem transform_component_tensor {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J K : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {p : ZMod 2} {α : ∀ z, J.obj z ⟶ K.obj z} (hα : IsSupernatural k p α)
    (R : Superfunctor k C (SVec k)) (z : C) (w : B) (h : K.obj z ⟶ w) (m : R.obj z) :
    (BalancedInduction.transformComponent hα R).app p w
      (BalancedInduction.tensor K R.toFunctor z h m) =
      BalancedInduction.tensor J R.toFunctor z (α z ≫ twist k p h) m := by
  rw [BalancedInduction.transformComponent_apply, ite_eq_left rfl,
    BalancedInduction.transformLinear_tensor]
private theorem native_tensor {p : ZMod 2}
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s)
    (hg : g ∈ parity (R := k) _ _ p) (w : OldCategory D Sc cutoff)
    (h : (OldCategory.mk s : OldCategory D Sc cutoff) ⟶ w)
    (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    (PowerWordMorphisms.fromArrow D Sc cutoff L s t g).app p w
      (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff s)
        (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) h a) =
    BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff t)
      (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff)
      (g ≫ twist k p h) a := by
  have he := PowerWordMorphisms.fromArrow_eq_transform D Sc cutoff L s t g hg
  have hx := congrArg (fun f : powerWordModule D Sc cutoff L s ⟶ powerWordModule D Sc cutoff L t =>
    f.app p w (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff s)
      (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) h a)) he
  exact hx.trans (transform_component_tensor _ _
    (PowerWordMorphisms.coefficientSourceNatural D Sc cutoff s t g hg)
      (liftedPowerRegular D cutoff L) (powerCoefficientStar D cutoff) w h a)
/-- Native dot on the actual next-word module, using the literal old dot. -/
def directDot : BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
      (liftedPowerRegular D cutoff L) ⟶
    BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
      (liftedPowerRegular D cutoff L) :=
  PowerWordMorphisms.fromArrow D Sc cutoff L (ν ++ [i]) (ν ++ [i])
    (oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν))

/-- The selected append comparison intertwines the actual chosen induction
dot with the native Hom dot, on every nested full-coefficient vector. -/
theorem appendLinear_dot_tensor (s w : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ w)
    (h : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ s)
    (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    appendLinear D Sc cutoff L ν i w
      (inductionDot D Sc cutoff i (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L)) w
        (BalancedInduction.tensor (append D Sc cutoff i)
          (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L)).toFunctor s g
          (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
            (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) h a))) =
    (directDot D Sc cutoff L ν i).app (D.parity i) w
      (appendLinear D Sc cutoff L ν i w
        (BalancedInduction.tensor (append D Sc cutoff i)
          (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L)).toFunctor s g
          (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
            (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) h a))) := by
  rw [inductionDot_tensor, appendLinear_tensor, appendLinear_tensor]
  unfold directDot
  erw [native_tensor D Sc cutoff L (s := ν ++ [i]) (t := ν ++ [i])
    (oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν))
    ((oldAppendDot_supernatural D Sc cutoff i).mem (OldCategory.mk ν))]
  change BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
    (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff)
      ((append D Sc cutoff i).map h ≫
        (oldAppendDotComponent D Sc cutoff i s ≫ twist k (D.parity i) g)) a =
    BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
      (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff)
      (oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν) ≫
        twist k (D.parity i) ((append D Sc cutoff i).map h ≫ g)) a
  rw [twist_comp, ← map_twist, ← Category.assoc,
    (oldAppendDot_supernatural D Sc cutoff i).naturality_twist h, Category.assoc]

/-- The dot square is an equality of linear maps on the entire actual
induced word module, not only on its cyclic unit. -/
theorem appendLinear_dot (w : OldCategory D Sc cutoff) :
    appendLinear D Sc cutoff L ν i w ∘ₗ
      inductionDot D Sc cutoff i (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L)) w =
    (directDot D Sc cutoff L ν i).app (D.parity i) w ∘ₗ
      appendLinear D Sc cutoff L ν i w := by
  apply BalancedInduction.nested_hom_ext (powerWordCoefficientSource D Sc cutoff ν)
    (append D Sc cutoff i) (liftedPowerRegular D cutoff L) w
  intro z s g h a
  obtain rfl : z = powerCoefficientStar D cutoff := by
    rcases z with ⟨z⟩
    cases z
    rfl
  exact appendLinear_dot_tensor D Sc cutoff L ν i s w g h a

end OddMath.QuiverHecke.ELVOld.PowerWordAppend
end

end

section

/-! Selected recursive word comparisons and the actual signed equal-colour
crossing, via existing whole-comparison coherence and outer recasting. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordPair
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ν : List I) (i : I)

private def comparisonIso {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ B) (K : B ⥤ E) (P : C ⥤ E)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    [P.Additive] [P.Linear k] [IsSuperfunctor k P] (e : J ⋙ K = P)
    (R : Superfunctor k C (SVec k)) :
    (BalancedInduction.induction K).obj (BalancedInduction.induced J R) ≅
      (BalancedInduction.induction P).obj R := (inductionCompOfEq J K P e).app R

section Recursive
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ B) (K : B ⥤ B) (P Q : C ⥤ B)
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [P.Additive] [P.Linear k] [IsSuperfunctor k P]
  [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (eP : J ⋙ K = P) (eQ : P ⋙ K = Q) (R : Superfunctor k C (SVec k))
end Recursive

section Outer
private theorem total_of_mem {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (z : C) : f.total z = f.app p z := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]
private theorem homogeneous_total_ext {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} {f g : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (hg : g ∈ parity (R := k) _ _ p)
    (h : ∀ z, f.total z = g.total z) : f = g := by
  apply SuperNatTrans.ext
  funext q z
  by_cases hq : q = p
  · subst q
    rw [← total_of_mem hf, ← total_of_mem hg]
    exact h z
  · rw [Superfunctor.app_eq_zero_of_mem hf hq, Superfunctor.app_eq_zero_of_mem hg hq]

end Outer

section Signed
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ B) (K : B ⥤ B) (P Q : C ⥤ B)
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [P.Additive] [P.Linear k] [IsSuperfunctor k P]
  [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (eP : J ⋙ K = P) (eQ : P ⋙ K = Q) (R : Superfunctor k C (SVec k))
  (e : J ⋙ (K ⋙ K) = Q) {p : ZMod 2}
  {β : ∀ w, (K ⋙ K).obj w ⟶ (K ⋙ K).obj w} (hβ : IsSupernatural k p β)
  {α : ∀ v, Q.obj v ⟶ Q.obj v} (hα : IsSupernatural k p α)

end Signed

end OddMath.QuiverHecke.ELVOld.PowerWordPair
end

end

section

/-! # The chosen content dot on scheduled regular-power words

SwappedVacuumCoordinates §§4–6: transport the independently chosen dot
through the established word descent and selected content append comparison.
The full old-arrow parity twist and all exterior coefficients are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordContentDot
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private theorem total_of_mem {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (w : C) : f.total w = f.app p w := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]

private theorem transform_total {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ w, J.obj w ⟶ J.obj w} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (w : B) :
    (BalancedInduction.transformComponent hα M).total w =
      BalancedInduction.transformLinear hα M w := by
  rw [total_of_mem (BalancedInduction.transformComponent_mem hα M),
    BalancedInduction.transformComponent_app, ite_eq_left rfl]

private theorem square_of_total {C : Type*} [Category* C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M N : Superfunctor k C (SVec k)} (e : M ⟶ N) (x : M ⟶ M) (y : N ⟶ N)
    (h : ∀ w, e.total w ∘ₗ x.total w = y.total w ∘ₗ e.total w) : x ≫ e = e ≫ y := by
  apply FiniteSupermodule.hom_ext_total
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  exact h w

omit [Fintype I] in
/-- The previously checked whole linear-map dot square, as a module-map
identity needed by weighted descent. -/
theorem append_dot (ν : List I) (i : I) :
    BalancedInduction.transformComponent (oldAppendDot_supernatural D Sc cutoff i)
      (powerWordModule D Sc cutoff L ν) ≫ (powerWordAppendIso D Sc cutoff L ν i).hom =
    (powerWordAppendIso D Sc cutoff L ν i).hom ≫ PowerWordAppend.directDot D Sc cutoff L ν i := by
  apply square_of_total
  intro w
  rw [transform_total]
  have hn : PowerWordAppend.directDot D Sc cutoff L ν i ∈ parity (R := k) _ _ (D.parity i) :=
    PowerWordMorphisms.fromArrow_mem D Sc cutoff L (ν ++ [i]) (ν ++ [i]) _
      ((oldAppendDot_supernatural D Sc cutoff i).mem (OldCategory.mk ν))
  rw [total_of_mem hn]
  exact PowerWordAppend.appendLinear_dot D Sc cutoff L ν i w

/-- The content extension counit is even on the scheduled word model. -/
theorem contentExtension_even (ν : List I) :
    (PowerWordContent.contentExtensionIso D Sc cutoff L ν).hom ∈ parity (R := k) _ _ 0 := by
  unfold PowerWordContent.contentExtensionIso contentSupportedCounitIso
  exact moduleIsoOfEvenNatIso_hom_mem _ _ _ _ _

omit [Fintype I] in
private theorem weightedHom_total (N : ℕ)
    (M P : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) (hP : KillsWeightedCoefficients D Sc cutoff N P)
    (f : M ⟶ P) (w : TruncatedCategory D Sc cutoff N) :
    (weightedModuleHom D Sc cutoff N M P hM hP f).total w = f.total (OldCategory.mk w.word) := rfl

omit [Fintype I] in
private def weightedOldDot (N : ℕ) (i : I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    End (weightedInducedModule D Sc cutoff N i (weightedRestriction D Sc cutoff N M)
      (weightedRestriction_kills D Sc cutoff N M)) :=
  let R := weightedRestriction D Sc cutoff N M
  let F := BalancedInduction.induced (append D Sc cutoff i) R
  let hF := induced_killsWeightedCoefficients D Sc cutoff N i R (weightedRestriction_kills D Sc cutoff N M)
  weightedModuleHom D Sc cutoff N F F hF hF
    (BalancedInduction.transformComponent (oldAppendDot_supernatural D Sc cutoff i) R)

omit [Fintype I] in
private def truncatedDot (N : ℕ) (i : I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    End (BalancedInduction.induced (truncatedAppend D Sc cutoff N [i]) M) :=
  BalancedInduction.transformComponent
    (truncatedAppendComponent_supernatural D Sc cutoff N (by
      simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)) M

omit [Fintype I] in
private theorem weightedDot_square (N : ℕ) (i : I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    weightedOldDot D Sc cutoff N i M ≫ (appendWeightedModuleIso D Sc cutoff N i M).hom =
      (appendWeightedModuleIso D Sc cutoff N i M).hom ≫ truncatedDot D Sc cutoff N i M := by
  unfold weightedOldDot truncatedDot
  apply square_of_total
  intro w
  rw [weightedHom_total, transform_total, transform_total]
  exact appendWeightedModuleIso_hom_dot D Sc cutoff N i M (OldCategory.mk w.word)

private theorem natural_even {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p : ZMod 2} {α : ∀ X, F.obj X ⟶ G.obj X} (hα : IsSupernatural k p α)
    {X Y : C} (f : X ⟶ Y) (hf : f ∈ parity (R := k) _ _ 0) :
    α X ≫ G.map f = F.map f ≫ α Y := by
  simpa only [mul_zero, Supercategory.sign_zero, one_smul] using (hα.naturality hf).symm

private theorem compose_squares {C : Type*} [Category* C] {A B E : C}
    (e : A ≅ B) (f : B ≅ E) (x : A ⟶ A) (y : B ⟶ B) (z : E ⟶ E)
    (he : x ≫ e.hom = e.hom ≫ y) (hf : y ≫ f.hom = f.hom ≫ z) :
    x ≫ (e ≪≫ f).hom = (e ≪≫ f).hom ≫ z := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, he, Category.assoc, hf]

private def oldWordComparison (ν : List I) (i : I) :
    BalancedInduction.induced (append D Sc cutoff i)
      (weightedRestriction D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (PowerWordContent.weightedWord D Sc cutoff L ν)) ≅ powerWordModule D Sc cutoff L (ν ++ [i]) :=
  (BalancedInduction.induction (append D Sc cutoff i)).mapIso
    (weightedRestrictionModuleIso D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      (powerWordModule D Sc cutoff L ν) (PowerWordContent.word_killsWeighted D Sc cutoff L ν)) ≪≫
    powerWordAppendIso D Sc cutoff L ν i

private theorem oldWord_dot (ν : List I) (i : I) :
    BalancedInduction.transformComponent (oldAppendDot_supernatural D Sc cutoff i)
      (weightedRestriction D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (PowerWordContent.weightedWord D Sc cutoff L ν)) ≫ (oldWordComparison D Sc cutoff L ν i).hom =
      (oldWordComparison D Sc cutoff L ν i).hom ≫ PowerWordAppend.directDot D Sc cutoff L ν i := by
  unfold oldWordComparison
  apply compose_squares
  · exact natural_even
      (BalancedInduction.transformComponent_supernatural (oldAppendDot_supernatural D Sc cutoff i)) _
      (weightedRestrictionModuleIso_hom_mem D Sc cutoff _ _ _)
  · exact append_dot D Sc cutoff L ν i

/-- The literal descended old-Hom dot on the next word module. -/
def weightedWordDot (ν : List I) (i : I) : End (PowerWordContent.weightedWord D Sc cutoff L (ν ++ [i])) :=
  weightedModuleHom D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    (powerWordModule D Sc cutoff L (ν ++ [i])) (powerWordModule D Sc cutoff L (ν ++ [i]))
    (PowerWordContent.word_killsWeighted D Sc cutoff L (ν ++ [i]))
    (PowerWordContent.word_killsWeighted D Sc cutoff L (ν ++ [i]))
    (PowerWordAppend.directDot D Sc cutoff L ν i)

omit [Fintype I] in
private theorem descend_square (N : ℕ)
    (M P : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) (hP : KillsWeightedCoefficients D Sc cutoff N P)
    (e : M ⟶ P) (x : M ⟶ M) (y : P ⟶ P) (h : x ≫ e = e ≫ y) :
    weightedModuleHom D Sc cutoff N M M hM hM x ≫ weightedModuleHom D Sc cutoff N M P hM hP e =
      weightedModuleHom D Sc cutoff N M P hM hP e ≫ weightedModuleHom D Sc cutoff N P P hP hP y := by
  have he := congrArg (fun f => weightedModuleHom D Sc cutoff N M P hM hP f) h
  rw [weightedModuleHom_comp, weightedModuleHom_comp] at he
  exact he

private theorem conjugate_square {C : Type*} [Category* C] {A B E : C}
    (e : A ≅ B) (f : A ≅ E) (x : A ⟶ A) (y : B ⟶ B) (z : E ⟶ E)
    (he : x ≫ e.hom = e.hom ≫ y) (hf : x ≫ f.hom = f.hom ≫ z) :
    y ≫ (e.symm ≪≫ f).hom = (e.symm ≪≫ f).hom ≫ z := by
  have hi : y ≫ e.inv = e.inv ≫ x := by
    calc
      _ = (e.inv ≫ (e.hom ≫ y)) ≫ e.inv := by simp only [Iso.inv_hom_id_assoc]
      _ = (e.inv ≫ (x ≫ e.hom)) ≫ e.inv := by rw [← he]
      _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  rw [hi, Category.assoc, hf, Category.assoc]

private def oldWordWeightedComparison (ν : List I) (i : I) :
    weightedInducedModule D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (weightedRestriction D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (PowerWordContent.weightedWord D Sc cutoff L ν))
      (weightedRestriction_kills D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (PowerWordContent.weightedWord D Sc cutoff L ν)) ≅
      PowerWordContent.weightedWord D Sc cutoff L (ν ++ [i]) :=
  let N := PowerWordContent.powerBound D cutoff L
  let M := PowerWordContent.weightedWord D Sc cutoff L ν
  let R := weightedRestriction D Sc cutoff N M
  let F := BalancedInduction.induced (append D Sc cutoff i) R
  let hF := induced_killsWeightedCoefficients D Sc cutoff N i R (weightedRestriction_kills D Sc cutoff N M)
  weightedModuleIso D Sc cutoff N F (powerWordModule D Sc cutoff L (ν ++ [i])) hF
    (PowerWordContent.word_killsWeighted D Sc cutoff L (ν ++ [i])) (oldWordComparison D Sc cutoff L ν i)

private theorem oldWordWeightedDot_square (ν : List I) (i : I) :
    weightedOldDot D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (PowerWordContent.weightedWord D Sc cutoff L ν) ≫ (oldWordWeightedComparison D Sc cutoff L ν i).hom =
    (oldWordWeightedComparison D Sc cutoff L ν i).hom ≫ weightedWordDot D Sc cutoff L ν i :=
  descend_square D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    _ _ _ _ (oldWordComparison D Sc cutoff L ν i).hom
    (BalancedInduction.transformComponent (oldAppendDot_supernatural D Sc cutoff i)
      (weightedRestriction D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (PowerWordContent.weightedWord D Sc cutoff L ν)))
    (PowerWordAppend.directDot D Sc cutoff L ν i) (oldWord_dot D Sc cutoff L ν i)

/-- The independently chosen truncated induction dot intertwines with the
literal descended old-Hom word dot through the prescribed weighted comparison. -/
theorem weighted_append_dot (ν : List I) (i : I) :
    truncatedDot D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (PowerWordContent.weightedWord D Sc cutoff L ν) ≫
        (PowerWordContent.weightedAppendIso D Sc cutoff L ν i).hom =
    (PowerWordContent.weightedAppendIso D Sc cutoff L ν i).hom ≫ weightedWordDot D Sc cutoff L ν i :=
  conjugate_square
    (appendWeightedModuleIso D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (PowerWordContent.weightedWord D Sc cutoff L ν))
    (oldWordWeightedComparison D Sc cutoff L ν i)
    (weightedOldDot D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (PowerWordContent.weightedWord D Sc cutoff L ν))
    (truncatedDot D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (PowerWordContent.weightedWord D Sc cutoff L ν))
    (weightedWordDot D Sc cutoff L ν i)
    (weightedDot_square D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (PowerWordContent.weightedWord D Sc cutoff L ν))
    (oldWordWeightedDot_square D Sc cutoff L ν i)

private theorem restriction_total {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M P : Superfunctor k B (SVec k)} (f : M ⟶ P) (v : C) :
    ((BalancedInduction.restriction Q).map f).total v = f.total (Q.obj v) := rfl

omit [Fintype I] in
private def contentDot (N : ℕ) (β : Multiset I) (i : I) (γ : Multiset I)
    (hγ : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β) :
    End (BalancedInduction.induced (contentAppendTo D Sc cutoff N β [i] γ hγ) M) :=
  BalancedInduction.transformComponent
    (contentAppendTo_supernatural D Sc cutoff N hγ hγ (by
      simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)) M

omit [Fintype I] in
private theorem contentRestrictionLinear_dot (N : ℕ) (β : Multiset I) (i : I) (γ : Multiset I)
    (hγ : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β)
    (t : ContentCategory D Sc cutoff N γ) :
    contentAppendToRestrictionLinear D Sc cutoff N β [i] γ hγ M t ∘ₗ
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N hγ hγ (by
          simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)) M t =
    BalancedInduction.transformLinear
      (truncatedAppendComponent_supernatural D Sc cutoff N (by
        simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1))
      (BalancedInduction.induced (contentInclusion D Sc cutoff N β) M) t.obj ∘ₗ
        contentAppendToRestrictionLinear D Sc cutoff N β [i] γ hγ M t := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, BalancedInduction.transformLinear_tensor,
    contentAppendToRestrictionLinear_tensor]
  rfl

omit [Fintype I] in
private theorem contentRestriction_dot (N : ℕ) (β : Multiset I) (i : I) (γ : Multiset I)
    (hγ : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β) :
    contentDot D Sc cutoff N β i γ hγ M ≫ (contentAppendToRestrictionIso D Sc cutoff N β [i] γ hγ M).hom =
      (contentAppendToRestrictionIso D Sc cutoff N β [i] γ hγ M).hom ≫
        (BalancedInduction.restriction (contentInclusion D Sc cutoff N γ)).map
          (truncatedDot D Sc cutoff N i (BalancedInduction.induced (contentInclusion D Sc cutoff N β) M)) := by
  unfold contentDot truncatedDot
  apply square_of_total
  intro t
  rw [restriction_total, transform_total, transform_total]
  exact contentRestrictionLinear_dot D Sc cutoff N β i γ hγ M t

private theorem map_square {C B : Type*} [Category* C] [Category* B]
    (F : C ⥤ B) {M P : C} (e : M ≅ P) (x : M ⟶ M) (y : P ⟶ P)
    (h : x ≫ e.hom = e.hom ≫ y) :
    F.map x ≫ (F.mapIso e).hom = (F.mapIso e).hom ≫ F.map y := by
  simp only [Functor.mapIso_hom]
  rw [← F.map_comp, h, F.map_comp]

private def extendedWordComparison (ν : List I) (i : I) :
    BalancedInduction.induced (truncatedAppend D Sc cutoff (PowerWordContent.powerBound D cutoff L) [i])
      (BalancedInduction.induced
        (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
        (PowerWordContent.contentWord D Sc cutoff L ν)) ≅
    PowerWordContent.weightedWord D Sc cutoff L (ν ++ [i]) :=
  (BalancedInduction.induction (truncatedAppend D Sc cutoff (PowerWordContent.powerBound D cutoff L) [i])).mapIso
    (PowerWordContent.contentExtensionIso D Sc cutoff L ν) ≪≫ PowerWordContent.weightedAppendIso D Sc cutoff L ν i

private theorem extendedWord_dot (ν : List I) (i : I) :
    truncatedDot D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (BalancedInduction.induced
        (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
        (PowerWordContent.contentWord D Sc cutoff L ν)) ≫ (extendedWordComparison D Sc cutoff L ν i).hom =
      (extendedWordComparison D Sc cutoff L ν i).hom ≫ weightedWordDot D Sc cutoff L ν i := by
  unfold extendedWordComparison
  apply compose_squares
  · exact natural_even
      (BalancedInduction.transformComponent_supernatural
        (truncatedAppendComponent_supernatural D Sc cutoff (PowerWordContent.powerBound D cutoff L) (by
          simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1))) _
      (contentExtension_even D Sc cutoff L ν)
  · exact weighted_append_dot D Sc cutoff L ν i

/-- The literal old-Hom word dot after weighted descent and exact-content restriction. -/
def contentWordDot (ν : List I) (i : I) : End (PowerWordContent.contentWord D Sc cutoff L (ν ++ [i])) :=
  (BalancedInduction.restriction
    (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) ((ν ++ [i] : List I) : Multiset I))).map
      (weightedWordDot D Sc cutoff L ν i)

/-- The independently chosen content induction dot with its exact output content. -/
def chosenContentDot (ν : List I) (i : I) :
    End (BalancedInduction.induced
      (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I) [i]
        ((ν ++ [i] : List I) : Multiset I) (Multiset.coe_add ν [i]))
      (PowerWordContent.contentWord D Sc cutoff L ν)) :=
  contentDot D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I) i
    ((ν ++ [i] : List I) : Multiset I) (Multiset.coe_add ν [i]) (PowerWordContent.contentWord D Sc cutoff L ν)

private theorem transform_component_eq {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ w, J.obj w ⟶ J.obj w} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) :
    BalancedInduction.transformComponent hα M = (BalancedInduction.transform hα).app p M :=
  (congrFun (IsSupernatural.toSuperNatTrans_app (BalancedInduction.transformComponent_supernatural hα)) M).symm

/-- This is the existing normalized content generator, not a new conjugate. -/
theorem chosenContentDot_eq (ν : List I) (i : I) : chosenContentDot D Sc cutoff L ν i =
    (contentInductionTransform D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      (Multiset.coe_add ν [i]) (Multiset.coe_add ν [i]) (by
        simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)).app (D.parity i)
      (PowerWordContent.contentWord D Sc cutoff L ν) := by
  unfold chosenContentDot contentDot contentInductionTransform
  exact transform_component_eq _ _ _

/-- The chosen content E dot is the full old-Hom dot under the prescribed
scheduled word comparison, on every coefficient vector. -/
theorem content_append_dot (ν : List I) (i : I) :
    chosenContentDot D Sc cutoff L ν i ≫ (PowerWordContent.contentAppendIso D Sc cutoff L ν i).hom =
      (PowerWordContent.contentAppendIso D Sc cutoff L ν i).hom ≫ contentWordDot D Sc cutoff L ν i :=
  compose_squares
    (contentAppendToRestrictionIso D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I) [i]
      ((ν ++ [i] : List I) : Multiset I) (Multiset.coe_add ν [i]) (PowerWordContent.contentWord D Sc cutoff L ν))
    ((BalancedInduction.restriction
      (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        ((ν ++ [i] : List I) : Multiset I))).mapIso (extendedWordComparison D Sc cutoff L ν i))
    (chosenContentDot D Sc cutoff L ν i)
    ((BalancedInduction.restriction
      (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        ((ν ++ [i] : List I) : Multiset I))).map
      (truncatedDot D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
        (BalancedInduction.induced
          (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
          (PowerWordContent.contentWord D Sc cutoff L ν))))
    (contentWordDot D Sc cutoff L ν i)
    (contentRestriction_dot D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I) i
      ((ν ++ [i] : List I) : Multiset I) (Multiset.coe_add ν [i]) (PowerWordContent.contentWord D Sc cutoff L ν))
    (map_square (BalancedInduction.restriction
      (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        ((ν ++ [i] : List I) : Multiset I))) (extendedWordComparison D Sc cutoff L ν i) _ _
      (extendedWord_dot D Sc cutoff L ν i))

end OddMath.QuiverHecke.ELVOld.PowerWordContentDot
end

end
