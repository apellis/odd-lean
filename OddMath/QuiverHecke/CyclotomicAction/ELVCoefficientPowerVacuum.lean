import OddMath.QuiverHecke.CyclotomicAction.ELVEmptyCoefficientEmbedding
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVFullyFaithfulInduction
import Mathlib.CategoryTheory.Category.ULift

/-! # The regular coefficient-power vacuum on the old category

The literal vacuum with coefficient module A/T in
`SwappedNondegeneracy.md`, §2. Balanced induction extends the actual
regular quotient module from the empty coefficient subcategory. The
fully faithful unit compares its empty component with the original A/T.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- Raise only the object universe of the one-object coefficient
category; its literal full-coefficient Homs remain unchanged. -/
def PowerCoefficientCategory := ULift.{u}
  (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := k) D cutoff))

instance powerCoefficientCategory : Category.{u} (PowerCoefficientCategory (k := k) D cutoff) :=
  CategoryTheory.uliftCategory (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := k) D cutoff))

instance powerCoefficientPreadditive : Preadditive (PowerCoefficientCategory (k := k) D cutoff) where
  homGroup v w := inferInstanceAs (AddCommGroup (v.down ⟶ w.down))
  add_comp := by
    intro v w z f g h
    exact Preadditive.add_comp v.down w.down z.down f g h
  comp_add := by
    intro v w z f g h
    exact Preadditive.comp_add v.down w.down z.down f g h

instance powerCoefficientLinear : Linear k (PowerCoefficientCategory (k := k) D cutoff) where
  homModule v w := inferInstanceAs (Module k (v.down ⟶ w.down))
  smul_comp := by
    intro v w z r f g
    exact Linear.smul_comp v.down w.down z.down r f g
  comp_smul := by
    intro v w z r f g
    exact Linear.comp_smul v.down w.down z.down r f g

instance powerCoefficientSupercategory : Supercategory k (PowerCoefficientCategory (k := k) D cutoff) where
  parity v w := parity (R := k) v.down w.down
  isInternal v w := Supercategory.isInternal v.down w.down
  id_mem v := id_mem v.down
  comp_mem := Supercategory.comp_mem
    (C := SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := k) D cutoff))

/-- Forget the object-universe lift, on the same coefficient arrows. -/
def powerCoefficientForget : PowerCoefficientCategory (k := k) D cutoff ⥤
    SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := k) D cutoff) where
  obj v := v.down
  map f := f

instance powerCoefficientForget_additive : (powerCoefficientForget (k := k) D cutoff).Additive where
  map_add := rfl
instance powerCoefficientForget_linear : (powerCoefficientForget (k := k) D cutoff).Linear k where
  map_smul _ _ := rfl
instance powerCoefficientForget_super : IsSuperfunctor k (powerCoefficientForget (k := k) D cutoff) where
  map_mem hf := hf

/-- The empty coefficient embedding with the source object universe
matched to the existing old balanced-induction construction. -/
def powerCoefficientEmbedding : PowerCoefficientCategory (k := k) D cutoff ⥤ OldCategory D Sc cutoff :=
  powerCoefficientForget D cutoff ⋙ emptyCoefficientEmbedding D Sc cutoff

instance powerCoefficientEmbedding_additive : (powerCoefficientEmbedding (k := k) D Sc cutoff).Additive := by
  unfold powerCoefficientEmbedding
  infer_instance
instance powerCoefficientEmbedding_linear : (powerCoefficientEmbedding (k := k) D Sc cutoff).Linear k := by
  unfold powerCoefficientEmbedding
  infer_instance
instance powerCoefficientEmbedding_super : IsSuperfunctor k (powerCoefficientEmbedding (k := k) D Sc cutoff) := by
  unfold powerCoefficientEmbedding
  infer_instance
instance powerCoefficientEmbedding_full : (powerCoefficientEmbedding (k := k) D Sc cutoff).Full where
  map_surjective f := (emptyCoefficientEquiv D Sc cutoff).surjective f
instance powerCoefficientEmbedding_faithful : (powerCoefficientEmbedding (k := k) D Sc cutoff).Faithful where
  map_injective h := (emptyCoefficientEquiv D Sc cutoff).injective h

/-- The same regular coefficient module on the lifted source objects;
neither vectors nor coefficient maps are lifted or rescaled. -/
def liftedPowerRegular : Superfunctor k (PowerCoefficientCategory (k := k) D cutoff) (SVec k) :=
  (⟨powerCoefficientForget D cutoff⟩ : Superfunctor k _ _).comp
    (coefficientPowerRegular D cutoff L)

/-- The actual old-category extension of the literal regular A/T
coefficient module, using the established balanced induction. -/
def coefficientPowerVacuum : Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  BalancedInduction.induced (powerCoefficientEmbedding D Sc cutoff)
    (liftedPowerRegular D cutoff L)

/-- The lifted unique coefficient object. -/
def powerCoefficientStar : PowerCoefficientCategory (k := k) D cutoff :=
  ⟨SuperalgebraCat.star (SKM.SYM.elvCoefficientParity (k := k) D cutoff)⟩

/-- The empty old-vacuum component is the literal A/T via the chosen
balanced unit and its established fully faithful inverse. -/
def coefficientPowerVacuumEmptyEquiv : CoefficientPowerQuotient (k := k) D cutoff L ≃ₗ[k]
    (coefficientPowerVacuum D Sc cutoff L).obj (⟨[]⟩ : OldCategory D Sc cutoff) :=
  LinearEquiv.ofLinearMap
    (BalancedInduction.unit (powerCoefficientEmbedding D Sc cutoff)
      (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff))
    (BalancedInduction.fullyFaithfulUnitInverse (powerCoefficientEmbedding D Sc cutoff)
      (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff))
    (BalancedInduction.unit_fullyFaithfulUnitInverse (powerCoefficientEmbedding D Sc cutoff)
      (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff))
    (BalancedInduction.fullyFaithfulUnitInverse_unit (powerCoefficientEmbedding D Sc cutoff)
      (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff))

/-- The literal A/T identification preserves every coefficient parity;
it is the chosen even balanced unit, not an ungraded replacement. -/
theorem coefficientPowerVacuumEmptyEquiv_mem {p : ZMod 2}
    {a : CoefficientPowerQuotient (k := k) D cutoff L}
    (ha : a ∈ coefficientPowerParity (k := k) D cutoff L p) :
    coefficientPowerVacuumEmptyEquiv D Sc cutoff L a ∈
      ((coefficientPowerVacuum D Sc cutoff L).obj (⟨[]⟩ : OldCategory D Sc cutoff)).part p := by
  have h := SVec.apply_mem_part
    (BalancedInduction.unit_mem (powerCoefficientEmbedding D Sc cutoff)
      (liftedPowerRegular D cutoff L) (powerCoefficientStar D cutoff)) ha
  rw [add_zero] at h
  change (BalancedInduction.unit (powerCoefficientEmbedding D Sc cutoff)
      (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff)) a ∈
    (BalancedInduction.superspace (powerCoefficientEmbedding D Sc cutoff)
      (liftedPowerRegular D cutoff L).toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)).part p
  exact h

/-- The actual induced regular quotient vacuum has no nonempty-word
component, by the old category's exact content support. -/
theorem coefficientPowerVacuum_support (w : OldCategory D Sc cutoff) (hw : w.word ≠ [])
    (z : (coefficientPowerVacuum D Sc cutoff L).obj w) : z = 0 := by
  let J := powerCoefficientEmbedding D Sc cutoff
  let R := liftedPowerRegular (k := k) D cutoff L
  have h : (LinearMap.id : BalancedInduction.Obj J R.toFunctor w →ₗ[k]
      BalancedInduction.Obj J R.toFunctor w) = 0 := by
    apply BalancedInduction.hom_ext
    intro s f m
    have hf : f = 0 := by
      change Old D Sc cutoff [] w.word at f
      obtain ⟨r, rfl⟩ := (ideal D Sc cutoff [] w.word).mkQ_surjective f
      rw [vacuum_hom_eq_zero D Sc cutoff hw r, map_zero]
    rw [hf, BalancedInduction.tensor_zero_left]
    rfl
  exact LinearMap.congr_fun h z

private theorem coefficientPowerVacuum_kills_even
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff 0)
    (hT : a ∈ coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L) :
    KillsCoefficient D Sc cutoff (coefficientPowerVacuum D Sc cutoff L) a := by
  intro w
  let J := powerCoefficientEmbedding D Sc cutoff
  let R := liftedPowerRegular (k := k) D cutoff L
  change BalancedInduction.postcompose J R.toFunctor (coefficientEndomorphism D Sc cutoff w a) = 0
  apply BalancedInduction.hom_ext
  intro s h m
  rw [BalancedInduction.postcompose_tensor, coefficientEndomorphism_slide D Sc cutoff ha]
  have hJ : coefficientEndomorphism D Sc cutoff [] a =
      J.map (X := s) (Y := s) a := rfl
  rw [hJ, BalancedInduction.balance]
  have hm : R.toFunctor.map (X := s) (Y := s) a m = 0 :=
    coefficientPowerRegular_kills D cutoff L hT m
  rw [hm, BalancedInduction.tensor_zero_right]
  rfl

/-- Every element of the literal full coefficient-power ideal acts as
zero on every old-vacuum component. -/
theorem coefficientPowerVacuum_property : coefficientPowerProperty D Sc cutoff
    (elementaryCoefficients (k := k) D cutoff) L (coefficientPowerVacuum D Sc cutoff L) := by
  apply (coefficientPowerProperty_iff D Sc cutoff _ L _).mpr
  intro j
  have hp : elementaryCoefficients (k := k) D cutoff j ^ L j ∈
      SKM.SYM.elvCoefficientParity D cutoff 0 := by
    simpa only [nsmul_zero] using
      SetLike.pow_mem_graded (L j) (elementaryCoefficients_even (k := k) D cutoff j)
  exact coefficientPowerVacuum_kills_even D Sc cutoff L hp
    (TwoSidedIdeal.subset_span (Set.mem_range_self j))

/-- The literal regular power vacuum as an object of the preserved
T-annihilated old-module category. -/
def coefficientPowerVacuumObject : CoefficientPowerModules D Sc cutoff
    (elementaryCoefficients (k := k) D cutoff) L :=
  ⟨coefficientPowerVacuum D Sc cutoff L, coefficientPowerVacuum_property D Sc cutoff L⟩

end OddMath.QuiverHecke.ELVOld
