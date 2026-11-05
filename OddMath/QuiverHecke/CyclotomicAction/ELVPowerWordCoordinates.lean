import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerVacuum
import OddMath.QuiverHecke.CyclotomicAction.ELVSourcePowerComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedInductionNaturality

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
