import OddMath.QuiverHecke.CyclotomicAction.CoefficientPowerAnnihilation
import OddMath.QuiverHecke.CyclotomicAction.FullyFaithfulInduction
import Mathlib.CategoryTheory.Category.ULift
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading
import OddMath.QuiverHecke.CyclotomicAction.MovingShiftRelations
import Mathlib.RingTheory.PowerSeries.Inverse
import OddMath.SKM.BubbleSubstitution
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Coefficient power series

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The regular coefficient-power vacuum on the old category

The literal vacuum with coefficient module A/T in
`SwappedNondegeneracy.md`, §2. Balanced induction extends the actual
regular quotient module from the empty coefficient subcategory. The
fully faithful unit compares its empty component with the original A/T.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Coefficient extraction on the literal power vacuum

The normalized coefficient window in `SwappedVacuumNonpositiveBubbles.md`,
§2, on the actual regular A/T old vacuum. The prescribed inverse row and
the original even empty-component unit identify the target with literal A/T.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.PowerVacuumCoefficient
open CyclotomicCrossingTensor CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private theorem height (i : I) :
    0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I) := by
  simp [contentCrossingHeight]

private def topSlot (i : I) (hN : 0 < cutoff i) :
    Fin (contentUnitCount D cutoff i (([] : List I) : Multiset I)) :=
  ⟨cutoff i - 1, by rw [VacuumCoefficient.count]; omega⟩

/-- The ordinary append unit with its input the literal A/T, identified
with the empty old-vacuum component by the original even unit. -/
def unit (i : I) : CoefficientPowerQuotient (k := k) D cutoff L →ₗ[k]
    mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
      (⟨[]⟩ : OldCategory D Sc cutoff) :=
  ((((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app
    (coefficientPowerVacuum D Sc cutoff L)).total ⟨[]⟩)).comp
      (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).toLinearMap

/-- The literal last inverse row, with its target the actual A/T. No
coefficient extractor is supplied as a premise and no cap is rescaled. -/
def functional (i : I) (hN : 0 < cutoff i) :
    mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
      (⟨[]⟩ : OldCategory D Sc cutoff) →ₗ[k] CoefficientPowerQuotient (k := k) D cutoff L :=
  (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).symm.toLinearMap.comp
    (moduleUnitCoefficient D Sc cutoff (coefficientPowerVacuum D Sc cutoff L) i ⟨[]⟩
      (height D cutoff i) (topSlot D cutoff i hN))

private theorem emptyInverse_even :
    (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).symm.toLinearMap ∈ parity (R := k)
      ((coefficientPowerVacuum D Sc cutoff L).obj (⟨[]⟩ : OldCategory D Sc cutoff))
      (coefficientPowerSpace (k := k) D cutoff L) 0 := by
  let e := coefficientPowerVacuumEmptyEquiv D Sc cutoff L
  let eIso : coefficientPowerSpace (k := k) D cutoff L ≅
      (coefficientPowerVacuum D Sc cutoff L).obj (⟨[]⟩ : OldCategory D Sc cutoff) := {
    hom := e.toLinearMap
    inv := e.symm.toLinearMap
    hom_inv_id := by apply LinearMap.ext; intro x; exact e.symm_apply_apply x
    inv_hom_id := by apply LinearMap.ext; intro x; exact e.apply_symm_apply x }
  have he : eIso.hom ∈ parity (R := k) (coefficientPowerSpace (k := k) D cutoff L)
      ((coefficientPowerVacuum D Sc cutoff L).obj (⟨[]⟩ : OldCategory D Sc cutoff)) 0 := by
    apply SVec.mem_parityHom_of_apply_mem
    intro p x hx
    change e x ∈ ((coefficientPowerVacuum D Sc cutoff L).obj
      (⟨[]⟩ : OldCategory D Sc cutoff)).part (p + 0)
    simpa only [add_zero] using coefficientPowerVacuumEmptyEquiv_mem D Sc cutoff L hx
  exact Supercategory.inv_mem eIso he

/-- The normalized A/T-valued functional retains the prescribed top-row
parity. In particular odd coefficients cannot pass through it unsigned. -/
theorem functional_mem (i : I) (hN : 0 < cutoff i) :
    functional D Sc cutoff L i hN ∈ parity (R := k)
      (mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L) ⟨[]⟩)
      (coefficientPowerSpace (k := k) D cutoff L) ((cutoff i - 1) • D.parity i) := by
  apply SVec.mem_parityHom_of_apply_mem
  intro q x hx
  have hc := SVec.apply_mem_part
    (moduleUnitCoefficient_mem D Sc cutoff (coefficientPowerVacuum D Sc cutoff L) i ⟨[]⟩
      (height D cutoff i) (topSlot D cutoff i hN)) hx
  have h := SVec.apply_mem_part (emptyInverse_even D Sc cutoff L) hc
  change (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).symm
    (moduleUnitCoefficient D Sc cutoff (coefficientPowerVacuum D Sc cutoff L) i ⟨[]⟩
      (height D cutoff i) (topSlot D cutoff i hN) x) ∈
        (coefficientPowerSpace (k := k) D cutoff L).part (q + (cutoff i - 1) • D.parity i)
  change (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).symm
    (moduleUnitCoefficient D Sc cutoff (coefficientPowerVacuum D Sc cutoff L) i ⟨[]⟩
      (height D cutoff i) (topSlot D cutoff i hN) x) ∈
        (coefficientPowerSpace (k := k) D cutoff L).part
          (q + (cutoff i - 1) • D.parity i + 0) at h
  simpa only [add_zero] using h

/-- The exact normalized extraction window as an identity on every
coefficient vector of literal A/T, for both moving parities. -/
theorem functional_dot_window (i : I) (hN : 0 < cutoff i)
    (a : ℕ) (ha : a < cutoff i) (z : CoefficientPowerQuotient (k := k) D cutoff L) :
    functional D Sc cutoff L i hN
      (((inductionDot D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
        ((append D Sc cutoff i).obj ⟨[]⟩)) ^ a) (unit D Sc cutoff L i z)) =
      if a + 1 = cutoff i then z else 0 := by
  let e := coefficientPowerVacuumEmptyEquiv D Sc cutoff L
  let c := moduleUnitCoefficient D Sc cutoff (coefficientPowerVacuum D Sc cutoff L)
    i ⟨[]⟩ (height D cutoff i) (topSlot D cutoff i hN)
  let dot : Module.End k (mateTargetSpace D Sc cutoff i
      (coefficientPowerVacuum D Sc cutoff L) ⟨[]⟩) :=
    inductionDot D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
      ((append D Sc cutoff i).obj ⟨[]⟩)
  let u0 : (coefficientPowerVacuum D Sc cutoff L).obj (⟨[]⟩ : OldCategory D Sc cutoff) →ₗ[k]
      mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L) ⟨[]⟩ :=
    (((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app
      (coefficientPowerVacuum D Sc cutoff L)).total ⟨[]⟩)
  have he : (a = cutoff i - 1) ↔ a + 1 = cutoff i := by omega
  have h := moduleUnitCoefficient_dot_window D Sc cutoff (coefficientPowerVacuum D Sc cutoff L)
    i ⟨[]⟩ (height D cutoff i) (topSlot D cutoff i hN) a
    (by simpa only [VacuumCoefficient.count] using ha) (e z)
  change c ((dot ^ a) (u0 (e z))) = if a = cutoff i - 1 then e z else 0 at h
  change e.symm (c ((dot ^ a) (u0 (e z)))) = _
  by_cases hh : a + 1 = cutoff i
  · have hv : c ((dot ^ a) (u0 (e z))) = e z := by
      simpa only [ite_eq_left (he.mpr hh)] using h
    simpa only [ite_eq_left hh] using (congrArg e.symm hv).trans (e.symm_apply_apply z)
  · have hv : c ((dot ^ a) (u0 (e z))) = 0 := by
      simpa only [ite_eq_right (fun hEq => hh (he.mp hEq))] using h
    simpa only [ite_eq_right hh] using (congrArg e.symm hv).trans (map_zero e.symm)

/-- The even empty-component unit retains the full coefficient action,
with its original multiplication order, including odd coefficients. -/
theorem empty_coefficient_action
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (x : CoefficientPowerQuotient (k := k) D cutoff L) :
    (coefficientPowerVacuum D Sc cutoff L).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
      (coefficientEndomorphism D Sc cutoff [] a)
        (coefficientPowerVacuumEmptyEquiv D Sc cutoff L x) =
      coefficientPowerVacuumEmptyEquiv D Sc cutoff L
        ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a * x) := by
  let J := powerCoefficientEmbedding D Sc cutoff
  let R := liftedPowerRegular (k := k) D cutoff L
  let s := powerCoefficientStar (k := k) D cutoff
  have h := LinearMap.congr_fun (BalancedInduction.unit_naturality J R.toFunctor
    (show s ⟶ s from a)) x
  exact h

private theorem empty_coefficient_decode
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (x : (coefficientPowerVacuum D Sc cutoff L).obj (⟨[]⟩ : OldCategory D Sc cutoff)) :
    (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).symm
      ((coefficientPowerVacuum D Sc cutoff L).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
        (coefficientEndomorphism D Sc cutoff [] a) x) =
      (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a *
        (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).symm x := by
  let e := coefficientPowerVacuumEmptyEquiv D Sc cutoff L
  have h := empty_coefficient_action D Sc cutoff L a (e.symm x)
  rw [e.apply_symm_apply] at h
  change (coefficientPowerVacuum D Sc cutoff L).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
    (coefficientEndomorphism D Sc cutoff [] a) x =
    e ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a *
      e.symm x) at h
  have h' := congrArg e.symm h
  rw [e.symm_apply_apply] at h'
  exact h'

/-- The full A/T-superlinearity of the actual inverse row. The
coefficient acts in its original left order, with the top-row Koszul sign. -/
theorem functional_coefficient (i : I) (hN : 0 < cutoff i) {q : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff q)
    (z : mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L) ⟨[]⟩) :
    functional D Sc cutoff L i hN
      ((SVec.toLinearMap (((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj
          (coefficientPowerVacuum D Sc cutoff L))).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
            (coefficientEndomorphism D Sc cutoff [] a))) z) =
      koszulSign ((cutoff i - 1) • D.parity i) q •
        ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a *
          functional D Sc cutoff L i hN z) := by
  let M := coefficientPowerVacuum D Sc cutoff L
  let T := (BalancedInduction.restriction (append D Sc cutoff i)).obj
    ((BalancedInduction.induction (append D Sc cutoff i)).obj M)
  let f : (⟨[]⟩ : OldCategory D Sc cutoff) ⟶ ⟨[]⟩ := coefficientEndomorphism D Sc cutoff [] a
  let e := coefficientPowerVacuumEmptyEquiv D Sc cutoff L
  let row := moduleUnitCoefficient D Sc cutoff M i ⟨[]⟩
    (height D cutoff i) (topSlot D cutoff i hN)
  let K : ℤ := koszulSign ((cutoff i - 1) • D.parity i) q
  have hf : f ∈ parity (R := k) (⟨[]⟩ : OldCategory D Sc cutoff) ⟨[]⟩ q :=
    coefficientEndomorphism_mem D Sc cutoff [] ha
  have h := LinearMap.congr_fun (moduleUnitCoefficient_end_naturality D Sc cutoff M
    i ⟨[]⟩ (height D cutoff i) (topSlot D cutoff i hN) f hf) z
  change row ((SVec.toLinearMap (T.map (X := ⟨[]⟩) (Y := ⟨[]⟩) f)) z) =
    K • (M.map (X := ⟨[]⟩) (Y := ⟨[]⟩) f (row z)) at h
  have hd := empty_coefficient_decode D Sc cutoff L a (row z)
  change e.symm (M.map (X := ⟨[]⟩) (Y := ⟨[]⟩) f (row z)) =
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a *
      e.symm (row z) at hd
  change e.symm (row ((SVec.toLinearMap (T.map (X := ⟨[]⟩) (Y := ⟨[]⟩) f)) z)) =
    K • ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a *
      e.symm (row z))
  calc
    _ = e.symm (K • M.map (X := ⟨[]⟩) (Y := ⟨[]⟩) f (row z)) := congrArg e.symm h
    _ = K • e.symm (M.map (X := ⟨[]⟩) (Y := ⟨[]⟩) f (row z)) := by rw [map_zsmul]
    _ = _ := congrArg (fun w : CoefficientPowerQuotient (k := k) D cutoff L => K • w) hd

end OddMath.QuiverHecke.ELV.PowerVacuumCoefficient
end

end

section

/-! # One-strand moments on the literal coefficient-power vacuum

The coefficient-extraction input of `SwappedVacuumNonpositiveBubbles.md`,
§§2–4, is evaluated on the regular A/T old vacuum. The literal one-strand
cyclotomic relation determines its higher moments; no relation or extractor
is supplied as an additional hypothesis.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.PowerVacuumCoefficient
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- The actual coend generator at the chosen vacuum vector, linear in
the complete one-strand old Hom, including exterior coefficients. -/
def rawVector (i : I) : Old D Sc cutoff [i] [i] →ₗ[k]
    mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L) ⟨[]⟩ :=
  let J := append D Sc cutoff i
  let M := coefficientPowerVacuum D Sc cutoff L
  let w : OldCategory D Sc cutoff := ⟨[]⟩
  (BalancedInduction.inclusion J M.toFunctor (J.obj w) w).comp
    ((TensorProduct.mk k (J.obj w ⟶ J.obj w) (M.obj w)).flip
      (coefficientPowerVacuumEmptyEquiv D Sc cutoff L 1))

/-- The prescribed inverse row evaluated on literal one-strand old arrows. -/
def upperFunctional (i : I) (hN : 0 < cutoff i) :
    Old D Sc cutoff [i] [i] →ₗ[k] CoefficientPowerQuotient (k := k) D cutoff L :=
  (functional D Sc cutoff L i hN).comp (rawVector D Sc cutoff L i)

/-- Coefficient-left raw moments of the actual power vacuum. -/
def rawMoment (i : I) (hN : 0 < cutoff i)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    CoefficientPowerQuotient (k := k) D cutoff L :=
  upperFunctional D Sc cutoff L i hN (singleClass D Sc cutoff i a n)

/-- The actual one-strand relation determines higher raw moments in its
original coefficient order. -/
theorem rawMoment_recurrence (i : I) (hN : 0 < cutoff i)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (m : ℕ) :
    (∑ j : Fin (cutoff i + 1), rawMoment D Sc cutoff L i hN
      (a * singleCoefficient D cutoff i j) (j.val + m)) = 0 := by
  have h := congrArg (upperFunctional D Sc cutoff L i hN)
    (single_recurrence D Sc cutoff i a m)
  simpa only [map_sum, map_zero, rawMoment] using h

/-- Signed higher moments on the ordinary unit of the same power vacuum. -/
def signedMoment (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    CoefficientPowerQuotient (k := k) D cutoff L :=
  functional D Sc cutoff L i hN
    ((inductionDot D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
      ((append D Sc cutoff i).obj ⟨[]⟩) ^ n) (unit D Sc cutoff L i 1))

/-- At every exponent the existing signed dot differs from the literal
raw monomial by exactly its triangular power scalar. -/
theorem signedMoment_rawMoment (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    signedMoment D Sc cutoff L i hN n =
      inductionUnitDotSign (k := k) (D.parity i) n • rawMoment D Sc cutoff L i hN 1 n := by
  have h := inductionDot_iterate_unit D Sc cutoff i
    (coefficientPowerVacuum D Sc cutoff L) (⟨[]⟩ : OldCategory D Sc cutoff) n
      (coefficientPowerVacuumEmptyEquiv D Sc cutoff L 1)
  rw [← Module.End.pow_apply] at h
  have hu := adjunctionUnit_total_apply D Sc cutoff i
    (coefficientPowerVacuum D Sc cutoff L) (⟨[]⟩ : OldCategory D Sc cutoff)
      (coefficientPowerVacuumEmptyEquiv D Sc cutoff L 1)
  change (unit D Sc cutoff L i) 1 = _ at hu
  rw [← hu] at h
  have hv := congrArg (functional D Sc cutoff L i hN) h
  rw [map_smul] at hv
  exact hv

/-- The same involutive triangular scalar recovers the raw moment from
its signed-dot moment at every exponent. -/
theorem rawMoment_signedMoment (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    rawMoment D Sc cutoff L i hN 1 n =
      inductionUnitDotSign (k := k) (D.parity i) n • signedMoment D Sc cutoff L i hN n := by
  rw [signedMoment_rawMoment]
  simp only [smul_smul, inductionUnitDotSign, Supercategory.sign_mul_self, one_smul]

/-- The low raw scalar window follows from the prescribed inverse row
and the actual signed-dot power comparison. -/
theorem rawMoment_one_window (i : I) (hN : 0 < cutoff i) (n : ℕ) (hn : n < cutoff i) :
    rawMoment D Sc cutoff L i hN 1 n =
      inductionUnitDotSign (k := k) (D.parity i) n •
        (if n + 1 = cutoff i then 1 else 0) := by
  rw [rawMoment_signedMoment]
  have h := functional_dot_window D Sc cutoff L i hN n hn
    (1 : CoefficientPowerQuotient (k := k) D cutoff L)
  change signedMoment D Sc cutoff L i hN n = _ at h
  rw [h]

private theorem singleClass_postcompose (i : I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    (show End ((append D Sc cutoff i).obj (⟨[]⟩ : OldCategory D Sc cutoff)) from
      singleClass D Sc cutoff i 1 n) ≫
      ((append D Sc cutoff i).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
        (coefficientEndomorphism D Sc cutoff [] a)) = singleClass D Sc cutoff i a n := by
  change oldComp D Sc cutoff [i] [i] [i]
    ((ideal D Sc cutoff [i] [i]).mkQ (singleTerm D Sc cutoff i 1 n))
    ((ideal D Sc cutoff [i] [i]).mkQ
      (rightContext D Sc cutoff [i] [] [] (ELVPScalar.scalar D Sc cutoff [] a))) = _
  rw [oldComp_mk, ELVPScalar.rightContext_scalar]
  simp only [List.nil_append]
  congr 1
  change BoxProd.tmulHom (X := obj D Sc cutoff [i]) (Y := obj D Sc cutoff [i])
    (𝟙 _) (dotE D Sc [i] 0 ^ n) ≫
    BoxProd.tmulHom (X := obj D Sc cutoff [i]) (Y := obj D Sc cutoff [i]) a (𝟙 _) = _
  dsimp only [obj, elvQuotientObj, coefficientObj]
  rw [BoxProd.tmulHom_comp_tmulHom_eq]
  simp only [proj_id, ↓reduceIte, one_ne_zero, Category.id_comp, Limits.zero_comp,
    BoxProd.tmulHom_def, TensorProduct.zero_tmul, Category.comp_id, add_zero]

/-- Raw higher moments retain the full inverse row's coefficient sign
and the original left multiplication order in literal A/T. -/
theorem rawMoment_coefficient (i : I) (hN : 0 < cutoff i) (n : ℕ) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    rawMoment D Sc cutoff L i hN a n =
      koszulSign ((cutoff i - 1) • D.parity i) p •
        ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a *
          rawMoment D Sc cutoff L i hN 1 n) := by
  have h := functional_coefficient D Sc cutoff L i hN ha
    (rawVector D Sc cutoff L i (singleClass D Sc cutoff i 1 n))
  change functional D Sc cutoff L i hN
    (BalancedInduction.postcompose (append D Sc cutoff i)
      (coefficientPowerVacuum D Sc cutoff L).toFunctor
      ((append D Sc cutoff i).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
        (coefficientEndomorphism D Sc cutoff [] a))
      (BalancedInduction.tensor (append D Sc cutoff i)
        (coefficientPowerVacuum D Sc cutoff L).toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)
        (singleClass D Sc cutoff i 1 n) (coefficientPowerVacuumEmptyEquiv D Sc cutoff L 1))) = _ at h
  rw [BalancedInduction.postcompose_tensor, singleClass_postcompose] at h
  exact h

/-- The actual monic relation expressed in scalar raw moments on A/T.
The coefficients remain on their proved left side, with the top-row sign. -/
theorem rawMoment_one_recurrence (i : I) (hN : 0 < cutoff i) (m : ℕ) :
    (∑ j : Fin (cutoff i + 1),
      koszulSign ((cutoff i - 1) • D.parity i)
        ((cutoff i : ZMod 2) * D.parity i - j.val • D.parity i) •
      ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        (singleCoefficient D cutoff i j) * rawMoment D Sc cutoff L i hN 1 (j.val + m))) = 0 := by
  calc
    _ = ∑ j : Fin (cutoff i + 1), rawMoment D Sc cutoff L i hN
        (singleCoefficient D cutoff i j) (j.val + m) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (rawMoment_coefficient D Sc cutoff L i hN (j.val + m)
        (singleCoefficient_mem D cutoff i j)).symm
    _ = 0 := by
      simpa only [one_mul] using rawMoment_recurrence D Sc cutoff L i hN 1 m

end OddMath.QuiverHecke.ELV.PowerVacuumCoefficient
end

end

section

/-! # Ordered odd remainder coefficients on the power vacuum

The parity conversion in `SwappedVacuumNonpositiveBubbles.md`, §2,
relates the actual inverse-row moments to the ordered monic remainder
recurrence. Coefficient order and the top inverse-row sign are retained.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.PowerVacuumCoefficient
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private theorem sign_natCast (n : ℕ) : sign k (n : ZMod 2) = (-1 : k) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add, Nat.cast_one, sign_add, ih, sign_one, pow_succ]

/-- The parity correction from the actual signed inverse row to the
ordinary coefficient of the top monic remainder, for an odd moving colour. -/
def ordinaryMomentSign (i : I) (n : ℕ) : k :=
  CyclotomicCrossingTensor.inductionUnitDotSign (k := k) 1 (cutoff i - 1) *
    sign k (((cutoff i - 1 : ℕ) : ZMod 2) * ((n + (cutoff i - 1) : ℕ) : ZMod 2))

/-- Ordinary remainder moments obtained from the actual row; they are not
introduced as independently prescribed coefficient values. -/
def ordinaryMoment (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    CoefficientPowerQuotient (k := k) D cutoff L :=
  ordinaryMomentSign (k := k) cutoff i n • rawMoment D Sc cutoff L i hN 1 n

private theorem ordinaryMomentSign_shift (i : I) (j m : ℕ) :
    ordinaryMomentSign (k := k) cutoff i (j + m) =
      ordinaryMomentSign (k := k) cutoff i (cutoff i + m) *
        sign k (((cutoff i - 1 : ℕ) : ZMod 2) * ((cutoff i : ZMod 2) - j)) := by
  unfold ordinaryMomentSign
  rw [mul_assoc, ← sign_add]
  congr 2
  push_cast
  ring_nf
  simp only [ZMod.neg_eq_self_mod_two, show (2 : ZMod 2) = 0 from rfl, mul_zero, add_zero]

/-- The corrected moments satisfy the literal ordered monic recurrence.
In shifted indexing this is equation (6) of the written reservoir calculation. -/
theorem ordinaryMoment_recurrence (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) (m : ℕ) :
    (∑ j : Fin (cutoff i + 1),
      (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        (singleCoefficient D cutoff i j) * ordinaryMoment D Sc cutoff L i hN (j.val + m)) = 0 := by
  have h := rawMoment_one_recurrence D Sc cutoff L i hN m
  rw [hi] at h
  simp only [nsmul_eq_mul, mul_one] at h
  have hs := congrArg (fun z : CoefficientPowerQuotient (k := k) D cutoff L =>
    ordinaryMomentSign (k := k) cutoff i (cutoff i + m) • z) h
  rw [smul_zero, Finset.smul_sum] at hs
  calc
    _ = ∑ j : Fin (cutoff i + 1),
        ordinaryMomentSign (k := k) cutoff i (cutoff i + m) •
          (koszulSign (((cutoff i - 1 : ℕ) : ZMod 2)) ((cutoff i : ZMod 2) - j.val) •
            ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
              (singleCoefficient D cutoff i j) * rawMoment D Sc cutoff L i hN 1 (j.val + m))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [ordinaryMoment, mul_smul_comm, ordinaryMomentSign_shift (k := k) cutoff i
        j.val m, mul_smul, koszulSign_smul (R := k)]
    _ = 0 := hs

/-- The corrected row is the ordinary top-coefficient window on all
low monomials, with value one at the top. -/
theorem ordinaryMoment_window (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) (n : ℕ) (hn : n < cutoff i) :
    ordinaryMoment D Sc cutoff L i hN n = if n + 1 = cutoff i then 1 else 0 := by
  rw [ordinaryMoment, rawMoment_one_window D Sc cutoff L i hN n hn]
  by_cases ht : n + 1 = cutoff i
  · have he : n = cutoff i - 1 := by omega
    subst n
    have hp : (((cutoff i - 1 : ℕ) : ZMod 2) *
        ((cutoff i - 1 + (cutoff i - 1) : ℕ) : ZMod 2)) = 0 := by
      push_cast
      rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, mul_zero]
    simp only [ordinaryMomentSign, hi, hp, Supercategory.sign_zero, mul_one, ite_eq_left ht,
      smul_smul, inductionUnitDotSign, Supercategory.sign_mul_self, one_smul]
  · simp only [ite_eq_right ht, smul_zero]

/-- The sequence of ordinary top remainders at exponents N−1+l. -/
def remainder (i : I) (hN : 0 < cutoff i) (l : ℕ) :
    CoefficientPowerQuotient (k := k) D cutoff L :=
  ordinaryMoment D Sc cutoff L i hN (cutoff i - 1 + l)

theorem remainder_zero (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) :
    remainder D Sc cutoff L i hN 0 = 1 := by
  have h := ordinaryMoment_window D Sc cutoff L i hi hN (cutoff i - 1) (by omega)
  have ht : cutoff i - 1 + 1 = cutoff i := by omega
  simpa only [remainder, Nat.add_zero, ite_eq_left ht] using h

/-- The complete ordered remainder recurrence; terms with a negative
shift are zero by the proved low window, rather than negative dot powers. -/
theorem remainder_recurrence (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) (l : ℕ) (hl : 0 < l) :
    (∑ j : Fin (cutoff i + 1),
      (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        (singleCoefficient D cutoff i j) *
          (if cutoff i - j.val ≤ l then remainder D Sc cutoff L i hN (l - (cutoff i - j.val))
           else 0)) = 0 := by
  calc
    _ = ∑ j : Fin (cutoff i + 1),
        (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
          (singleCoefficient D cutoff i j) * ordinaryMoment D Sc cutoff L i hN (j.val + (l - 1)) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      by_cases hj : cutoff i - j.val ≤ l
      · rw [ite_eq_left hj, remainder]
        congr 1
        have hv := j.isLt
        omega
      · rw [ite_eq_right hj]
        have hv := j.isLt
        have he := ordinaryMoment_window D Sc cutoff L i hi hN (j.val + (l - 1)) (by omega)
        have ht : ¬ j.val + (l - 1) + 1 = cutoff i := by omega
        simpa only [ite_eq_right ht] using he.symm
    _ = 0 := ordinaryMoment_recurrence D Sc cutoff L i hi hN (l - 1)

private theorem chi_mem_coefficientIdeal (i : I) (hi : D.parity i = 1)
    (r : ℕ) (hr : cutoff i / 2 < r) :
    SKM.SYM.elvChi D k ⟨i, hi⟩ r ∈ SKM.SYM.elvCoefficientIdeal D k cutoff := by
  have he : r = (r - 1) + 1 := by omega
  rw [he, SKM.SYM.elvChi]
  apply TwoSidedIdeal.subset_span
  apply Or.inl
  refine ⟨i, r - 1, ?_, rfl⟩
  have hzero : ¬ D.parity i = 0 := by rw [hi]; decide
  simp only [SKM.SYM.elvElementaryRank, ite_eq_right hzero]
  omega

/-- Every coefficient beyond the odd cutoff vanishes in literal A/T.
At an even cutoff the first odd tail is the defining δχ relation. -/
theorem odd_coefficient_tail (i : I) (hi : D.parity i = 1)
    (n : ℕ) (hn : cutoff i < n) :
    coefficientPowerQuotientMap (k := k) D cutoff L
      (SKM.SYM.elvCoefficient D k ⟨i, hi⟩ n) = 0 := by
  apply (coefficientPowerQuotientMap_eq_zero_iff D cutoff L _).mpr
  apply TwoSidedIdeal.mem_sup_left
  unfold SKM.SYM.elvCoefficient
  split_ifs with hn2
  · exact chi_mem_coefficientIdeal D cutoff i hi (n / 2) (by omega)
  · by_cases hr : cutoff i / 2 < n / 2
    · exact (SKM.SYM.elvCoefficientIdeal D k cutoff).mul_mem_left _ _
        (chi_mem_coefficientIdeal D cutoff i hi (n / 2) hr)
    · have hN : cutoff i % 2 = 0 := by omega
      have he : n / 2 = cutoff i / 2 := by omega
      rw [he]
      exact TwoSidedIdeal.subset_span (Or.inr ⟨⟨i, hi⟩, hN, rfl⟩)

private theorem coeff_monomial_mul {A : Type u} [Semiring A]
    (n l : ℕ) (a : A) (f : PowerSeries A) :
    PowerSeries.coeff l (PowerSeries.monomial n a * f) =
      if n ≤ l then a * PowerSeries.coeff (l - n) f else 0 := by
  change MvPowerSeries.coeff (Finsupp.single () l)
    (MvPowerSeries.monomial (Finsupp.single () n) a * f) = _
  rw [MvPowerSeries.coeff_monomial_mul]
  simp only [Finsupp.single_le_single, ← Finsupp.single_tsub]
  rfl

/-- The reversed literal monic relation, with its original coefficient
order, as a finite formal series on the actual power quotient. -/
def remainderPolynomial (i : I) : PowerSeries (CoefficientPowerQuotient (k := k) D cutoff L) :=
  ∑ j : Fin (cutoff i + 1), PowerSeries.monomial (cutoff i - j.val)
    ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
      (singleCoefficient D cutoff i j))

/-- The complete series of actual ordinary top remainders. -/
def remainderSeries (i : I) (hN : 0 < cutoff i) :
    PowerSeries (CoefficientPowerQuotient (k := k) D cutoff L) :=
  PowerSeries.mk (remainder D Sc cutoff L i hN)

/-- The ordered monic recurrence is a literal power-series inverse
identity on A/T, at every coefficient. The coefficient ring is not made
commutative and no coefficient is inverted. -/
theorem remainderPolynomial_mul_remainderSeries (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) :
    remainderPolynomial D cutoff L i * remainderSeries D Sc cutoff L i hN = 1 := by
  classical
  apply PowerSeries.ext
  intro l
  simp only [remainderPolynomial, remainderSeries, Finset.sum_mul, map_sum,
    coeff_monomial_mul, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  by_cases hl : l = 0
  · subst l
    rw [ite_eq_left rfl]
    rw [Finset.sum_eq_single (Fin.last (cutoff i))]
    · simp only [Fin.val_last, Nat.sub_self, le_refl, ↓reduceIte,
        singleCoefficient_top, map_one, remainder_zero D Sc cutoff L i hi hN, mul_one]
    · intro j _ hj
      have hne : j.val ≠ cutoff i := by
        intro h
        apply hj
        exact Fin.ext h
      have hv := j.isLt
      rw [ite_eq_right (by omega : ¬ cutoff i - j.val ≤ 0)]
    · simp
  · rw [ite_eq_right hl]
    simpa only [mul_ite, mul_zero] using remainder_recurrence D Sc cutoff L i hi hN l (by omega)

include Sc in
/-- The reversed monic relation has constant coefficient one. -/
theorem remainderPolynomial_constantCoeff (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) :
    PowerSeries.constantCoeff (remainderPolynomial (k := k) D cutoff L i) = 1 := by
  have h := congrArg PowerSeries.constantCoeff
    (remainderPolynomial_mul_remainderSeries D Sc cutoff L i hi hN)
  rw [map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply
    (φ := remainderSeries D Sc cutoff L i hN), remainderSeries, PowerSeries.coeff_mk,
      remainder_zero D Sc cutoff L i hi hN, mul_one, map_one] at h
  exact h

/-- The actual remainder series is the formal inverse with unit constant
coefficient. This is derived from the old relation and the actual inverse row. -/
theorem remainderSeries_eq_invOfUnit (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) :
    remainderSeries D Sc cutoff L i hN =
      PowerSeries.invOfUnit (remainderPolynomial D cutoff L i) 1 := by
  have hC : PowerSeries.constantCoeff (remainderPolynomial (k := k) D cutoff L i) =
      ((1 : (CoefficientPowerQuotient (k := k) D cutoff L)ˣ) : _) :=
    remainderPolynomial_constantCoeff D Sc cutoff L i hi hN
  calc
    _ = (PowerSeries.invOfUnit (remainderPolynomial D cutoff L i) 1 *
        remainderPolynomial D cutoff L i) * remainderSeries D Sc cutoff L i hN := by
      rw [PowerSeries.invOfUnit_mul _ _ hC, one_mul]
    _ = _ := by
      rw [mul_assoc, remainderPolynomial_mul_remainderSeries D Sc cutoff L i hi hN, mul_one]

private theorem choose_two_add (a b : ℕ) :
    (a + b).choose 2 = a.choose 2 + a * b + b.choose 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h1 : (a + b + 1).choose 2 = (a + b) + (a + b).choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ (a + b) 1
    have h2 : (b + 1).choose 2 = b + b.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ b 1
    rw [Nat.add_succ, h1, ih, h2]
    ring

private theorem triangular_ordinary_sign (i : I) (l : ℕ) :
    sign k (((cutoff i - 1 + l).choose 2 : ℕ) : ZMod 2) =
      sign k ((l.choose 2 : ℕ) : ZMod 2) *
        ordinaryMomentSign (k := k) cutoff i (cutoff i - 1 + l) := by
  unfold ordinaryMomentSign
  simp only [inductionUnitDotSign, nsmul_eq_mul, mul_one, ← Supercategory.sign_add]
  congr 1
  rw [choose_two_add]
  push_cast
  ring_nf
  simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, add_zero]

/-- All higher signed moments have the exact ordinary-remainder sign
in equation (5), including the sign of the extracted odd coefficient. -/
theorem signedMoment_remainder (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) (l : ℕ) :
    signedMoment D Sc cutoff L i hN (cutoff i - 1 + l) =
      sign k ((l.choose 2 : ℕ) : ZMod 2) • remainder D Sc cutoff L i hN l := by
  rw [signedMoment_rawMoment]
  simp only [hi, remainder, ordinaryMoment, inductionUnitDotSign,
    nsmul_eq_mul, mul_one, smul_smul]
  rw [triangular_ordinary_sign (k := k) cutoff i l]

end OddMath.QuiverHecke.ELV.PowerVacuumCoefficient
end

end

section

/-! # Even and odd series of the literal power-vacuum remainders

The closed series of `SwappedVacuumNonpositiveBubbles.md`, §2 (7),
come from the actual monic remainder series. Polynomial series operations
are performed in the commutative polynomial algebra before mapping to A/T.
The latter retains its original ring and exterior coefficient order.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.PowerVacuumCoefficient
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private theorem sign_natCast_2 (n : ℕ) : sign k (n : ZMod 2) = (-1 : k) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add, Nat.cast_one, sign_add, ih, sign_one, pow_succ]

private theorem reversed_negative_one_power (N n : ℕ) (hn : n ≤ N) :
    (-1 : k) ^ (N * (N - n + 1)) = (-1 : k) ^ (N * n) := by
  have hp : ((N * (N - n + 1) : ℕ) : ZMod 2) = ((N * n : ℕ) : ZMod 2) := by
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hn, Nat.cast_one, Nat.cast_mul]
    rcases parity_eq_zero_or_one (N : ZMod 2) with hN | hN <;> rw [hN] <;>
      rcases parity_eq_zero_or_one (n : ZMod 2) with hn | hn <;> rw [hn] <;> decide
  rw [← sign_natCast_2, ← sign_natCast_2, hp]

private theorem odd_reversed_coefficient (i : I) (hi : D.parity i = 1)
    (n : ℕ) (hn : n ≤ cutoff i) :
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
      (singleCoefficient D cutoff i ⟨cutoff i - n, by omega⟩) =
      (-1 : k) ^ (cutoff i * n) • coefficientPowerQuotientMap (k := k) D cutoff L
        (SKM.SYM.elvCoefficient D k ⟨i, hi⟩ n) := by
  unfold singleCoefficient
  rw [dite_eq_left hi, SKM.SYM.elvMonicCoefficient, map_smul, map_smul]
  rw [show cutoff i - (cutoff i - n) = n by omega,
    reversed_negative_one_power (k := k) (cutoff i) n hn]
  rfl

/-- At every degree the reversed actual monic relation has exactly the
ordered odd coefficient. The proved cutoff tail supplies the large degrees. -/
theorem odd_remainderPolynomial_coeff (i : I) (hi : D.parity i = 1) (n : ℕ) :
    PowerSeries.coeff n (remainderPolynomial (k := k) D cutoff L i) =
      (-1 : k) ^ (cutoff i * n) • coefficientPowerQuotientMap D cutoff L
        (SKM.SYM.elvCoefficient D k ⟨i, hi⟩ n) := by
  classical
  rw [remainderPolynomial, map_sum]
  by_cases hn : n ≤ cutoff i
  · let j : Fin (cutoff i + 1) := ⟨cutoff i - n, by omega⟩
    rw [Finset.sum_eq_single j]
    · rw [PowerSeries.coeff_monomial, ite_eq_left (by dsimp [j]; omega)]
      exact odd_reversed_coefficient D cutoff L i hi n hn
    · intro b _ hb
      rw [PowerSeries.coeff_monomial, ite_eq_right]
      intro he
      apply hb
      apply Fin.ext
      have hv := b.isLt
      dsimp [j]
      omega
    · simp
  · rw [odd_coefficient_tail D cutoff L i hi n (by omega), smul_zero]
    apply Finset.sum_eq_zero
    intro j _
    rw [PowerSeries.coeff_monomial, ite_eq_right (by have hv := j.isLt; omega)]

/-- Polynomial coefficient evaluation in literal A/T. Series expansion
and rescaling are performed before applying this map. -/
def polynomialToPower : MvPolynomial (I × ℕ) k →ₐ[k] CoefficientPowerQuotient (k := k) D cutoff L :=
  (coefficientPowerQuotientMap D cutoff L).comp (SKM.SYM.polynomialInclude D k)

private theorem polynomial_generatorCoeff (i : I) (hi : D.parity i = 1) (n : ℕ) :
    polynomialToPower (k := k) D cutoff L (PowerSeries.coeff n (SKM.SYM.generatorSeries k i)) =
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.elvChi D k ⟨i, hi⟩ n) := by
  cases n with
  | zero => simp [SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff, SKM.SYM.elvChi]
  | succ n =>
    simp [SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff, SKM.SYM.elvChi,
      polynomialToPower, AlgHom.comp_apply]

/-- The even-power elementary series, expanded in the commutative
universal polynomial algebra and then evaluated in literal A/T. -/
def elementaryEvenSeries (i : I) : PowerSeries (CoefficientPowerQuotient (k := k) D cutoff L) :=
  PowerSeries.map (polynomialToPower D cutoff L).toRingHom
    (PowerSeries.expand 2 (by decide) (SKM.SYM.generatorSeries k i))

/-- Its coefficient formula retains the actual odd elementary coefficients. -/
theorem elementaryEvenSeries_coeff (i : I) (hi : D.parity i = 1) (n : ℕ) :
    PowerSeries.coeff n (elementaryEvenSeries (k := k) D cutoff L i) =
      if n % 2 = 0 then coefficientPowerQuotientMap D cutoff L
        (SKM.SYM.elvChi D k ⟨i, hi⟩ (n / 2)) else 0 := by
  rw [elementaryEvenSeries, PowerSeries.coeff_map, PowerSeries.coeff_expand]
  by_cases hn : n % 2 = 0
  · rw [ite_eq_left ((Nat.dvd_iff_mod_eq_zero).mpr hn), ite_eq_left hn]
    exact polynomial_generatorCoeff D cutoff L i hi (n / 2)
  · rw [ite_eq_right (fun h => hn (Nat.dvd_iff_mod_eq_zero.mp h)), ite_eq_right hn, map_zero]

private theorem coeff_mul_monomial {A : Type u} [Semiring A]
    (n l : ℕ) (a : A) (f : PowerSeries A) :
    PowerSeries.coeff l (f * PowerSeries.monomial n a) =
      if n ≤ l then PowerSeries.coeff (l - n) f * a else 0 := by
  change MvPowerSeries.coeff (Finsupp.single () l)
    (f * MvPowerSeries.monomial (Finsupp.single () n) a) = _
  rw [MvPowerSeries.coeff_mul_monomial]
  simp only [Finsupp.single_le_single, ← Finsupp.single_tsub]
  rfl

private theorem chi_commute_delta (i : I) (hi : D.parity i = 1) (n : ℕ) :
    Commute (coefficientPowerQuotientMap (k := k) D cutoff L (SKM.SYM.elvChi D k ⟨i, hi⟩ n))
      (coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) := by
  cases n with
  | zero => simp [SKM.SYM.elvChi]
  | succ n =>
    exact (SKM.SYM.e_commute_all D k i n (SKM.SYM.delta D k ⟨i, hi⟩)).map
      (coefficientPowerQuotientMap D cutoff L).toRingHom

/-- The exact linear exterior factor in the odd reversed monic relation. -/
def oddLinearTerm (i : I) (hi : D.parity i = 1) :
    PowerSeries (CoefficientPowerQuotient (k := k) D cutoff L) :=
  PowerSeries.monomial 1 (((-1 : k) ^ cutoff i) •
    coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩))

/-- The literal reversed odd monic polynomial factors as C(w²)(1+sδw),
including the even-cutoff top exterior relation through its proved tail. -/
theorem remainderPolynomial_factor (i : I) (hi : D.parity i = 1) :
    remainderPolynomial (k := k) D cutoff L i =
      elementaryEvenSeries D cutoff L i * (1 + oddLinearTerm D cutoff L i hi) := by
  apply PowerSeries.ext
  intro n
  rw [odd_remainderPolynomial_coeff D cutoff L i hi n, mul_add, mul_one, map_add,
    oddLinearTerm, coeff_mul_monomial, elementaryEvenSeries_coeff D cutoff L i hi n]
  by_cases hz : n = 0
  · subst n
    simp [SKM.SYM.elvCoefficient, SKM.SYM.elvChi]
  · rw [ite_eq_left (by omega : 1 ≤ n), elementaryEvenSeries_coeff D cutoff L i hi (n - 1)]
    by_cases hn : n % 2 = 0
    · have hn1 : ¬ (n - 1) % 2 = 0 := by omega
      have hs : (-1 : k) ^ (cutoff i * n) = 1 :=
        ((even_iff_two_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr hn) : Even n).mul_left (cutoff i)).neg_one_pow
      rw [SKM.SYM.elvCoefficient]
      simp only [ite_eq_left hn, ite_eq_right hn1]
      rw [hs, one_smul, zero_mul, add_zero]
    · have hn1 : (n - 1) % 2 = 0 := by omega
      have hodd : Odd n := Nat.odd_iff.mpr (by omega)
      have hs : (-1 : k) ^ (cutoff i * n) = (-1 : k) ^ cutoff i := by
        rw [← sign_natCast_2, Nat.cast_mul, ZMod.natCast_eq_one_iff_odd.mpr hodd,
          mul_one, sign_natCast_2]
      have hd : (n - 1) / 2 = n / 2 := by omega
      rw [SKM.SYM.elvCoefficient]
      simp only [ite_eq_right hn, ite_eq_left hn1]
      rw [hd, hs, map_mul, zero_add, mul_smul_comm, (chi_commute_delta D cutoff L i hi (n / 2)).eq]

/-- The exterior linear term squares to zero before any series inversion. -/
theorem oddLinearTerm_mul_self (i : I) (hi : D.parity i = 1) :
    oddLinearTerm (k := k) D cutoff L i hi * oddLinearTerm D cutoff L i hi = 0 := by
  unfold oddLinearTerm
  rw [PowerSeries.monomial_mul_monomial]
  have hz : (((-1 : k) ^ cutoff i) • coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
      (((-1 : k) ^ cutoff i) • coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, ← pow_two, ← map_pow, SKM.SYM.delta_sq,
      map_zero, smul_zero, smul_zero]
  rw [hz, map_zero]

private theorem generatorSeries_constantCoeff (i : I) :
    PowerSeries.constantCoeff (SKM.SYM.generatorSeries k i) =
      ((1 : (MvPolynomial (I × ℕ) k)ˣ) : _) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff]

/-- The inverse elementary even series is constructed over the universal
commutative polynomial algebra before evaluation on literal A/T. -/
def elementaryEvenInverse (i : I) : PowerSeries (CoefficientPowerQuotient (k := k) D cutoff L) :=
  PowerSeries.map (polynomialToPower D cutoff L).toRingHom
    (PowerSeries.expand 2 (by decide) (PowerSeries.invOfUnit (SKM.SYM.generatorSeries k i) 1))

theorem elementaryEvenSeries_mul_inverse (i : I) :
    elementaryEvenSeries (k := k) D cutoff L i * elementaryEvenInverse D cutoff L i = 1 := by
  unfold elementaryEvenSeries elementaryEvenInverse
  rw [← map_mul, ← map_mul, PowerSeries.mul_invOfUnit _ _ (generatorSeries_constantCoeff (k := k) i),
    map_one, map_one]

/-- The complete actual remainder series has its original exterior linear
factor on the left of the mapped inverse elementary series. -/
theorem remainderSeries_factor (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) :
    remainderSeries D Sc cutoff L i hN =
      (1 - oddLinearTerm D cutoff L i hi) * elementaryEvenInverse D cutoff L i := by
  have hlin : (1 + oddLinearTerm (k := k) D cutoff L i hi) *
      (1 - oddLinearTerm D cutoff L i hi) = 1 := by
    simp only [mul_sub, add_mul, mul_one, one_mul, oddLinearTerm_mul_self D cutoff L i hi,
      add_zero, add_sub_cancel_right]
  have hprod : remainderPolynomial (k := k) D cutoff L i *
      ((1 - oddLinearTerm D cutoff L i hi) * elementaryEvenInverse D cutoff L i) = 1 := by
    rw [remainderPolynomial_factor D cutoff L i hi, mul_assoc,
      ← mul_assoc (1 + oddLinearTerm D cutoff L i hi), hlin, one_mul,
      elementaryEvenSeries_mul_inverse D cutoff L i]
  have hC : PowerSeries.constantCoeff (remainderPolynomial (k := k) D cutoff L i) =
      ((1 : (CoefficientPowerQuotient (k := k) D cutoff L)ˣ) : _) :=
    remainderPolynomial_constantCoeff D Sc cutoff L i hi hN
  calc
    _ = remainderSeries D Sc cutoff L i hN *
        (remainderPolynomial D cutoff L i *
          ((1 - oddLinearTerm D cutoff L i hi) * elementaryEvenInverse D cutoff L i)) := by
      rw [hprod, mul_one]
    _ = _ := by
      rw [← mul_assoc, remainderSeries_eq_invOfUnit D Sc cutoff L i hi hN,
        PowerSeries.invOfUnit_mul _ _ hC, one_mul]

private theorem elementaryEvenInverse_even (i : I) (r : ℕ) :
    PowerSeries.coeff (2 * r) (elementaryEvenInverse (k := k) D cutoff L i) =
      polynomialToPower D cutoff L (PowerSeries.coeff r
        (PowerSeries.invOfUnit (SKM.SYM.generatorSeries k i) 1)) := by
  rw [elementaryEvenInverse, PowerSeries.coeff_map, PowerSeries.coeff_expand_mul]
  rfl

private theorem elementaryEvenInverse_odd (i : I) (r : ℕ) :
    PowerSeries.coeff (2 * r + 1) (elementaryEvenInverse (k := k) D cutoff L i) = 0 := by
  have hn : ¬ 2 ∣ 2 * r + 1 := by
    intro h
    have hm := Nat.dvd_iff_mod_eq_zero.mp h
    omega
  rw [elementaryEvenInverse, PowerSeries.coeff_map,
    PowerSeries.coeff_expand_of_not_dvd 2 (by decide) _ hn, map_zero]

private theorem coeff_monomial_mul_2 {A : Type u} [Semiring A]
    (n l : ℕ) (a : A) (f : PowerSeries A) :
    PowerSeries.coeff l (PowerSeries.monomial n a * f) =
      if n ≤ l then a * PowerSeries.coeff (l - n) f else 0 := by
  change MvPowerSeries.coeff (Finsupp.single () l)
    (MvPowerSeries.monomial (Finsupp.single () n) a * f) = _
  rw [MvPowerSeries.coeff_monomial_mul]
  simp only [Finsupp.single_le_single, ← Finsupp.single_tsub]
  rfl

private theorem oddLinearTerm_mul_coeff_succ (i : I) (hi : D.parity i = 1) (n : ℕ) :
    PowerSeries.coeff (n + 1)
      (oddLinearTerm (k := k) D cutoff L i hi * elementaryEvenInverse D cutoff L i) =
      (((-1 : k) ^ cutoff i) • coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
        PowerSeries.coeff n (elementaryEvenInverse D cutoff L i) := by
  rw [oddLinearTerm, coeff_monomial_mul_2, ite_eq_left (by omega : 1 ≤ n + 1), Nat.add_sub_cancel]

private theorem oddLinearTerm_mul_even (i : I) (hi : D.parity i = 1) (r : ℕ) :
    PowerSeries.coeff (2 * r)
      (oddLinearTerm (k := k) D cutoff L i hi * elementaryEvenInverse D cutoff L i) = 0 := by
  cases r with
  | zero => rw [mul_zero, oddLinearTerm, coeff_monomial_mul_2, ite_eq_right (by decide : ¬ 1 ≤ 0)]
  | succ r =>
    rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega,
      oddLinearTerm_mul_coeff_succ, elementaryEvenInverse_odd, mul_zero]

/-- Even ordinary remainder coefficients are the mapped coefficients of
1/C(w²). The statement concerns the constructed inverse-row remainder. -/
theorem remainder_even (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    remainder D Sc cutoff L i hN (2 * r) =
      polynomialToPower (k := k) D cutoff L (PowerSeries.coeff r
        (PowerSeries.invOfUnit (SKM.SYM.generatorSeries k i) 1)) := by
  have h := congrArg (PowerSeries.coeff (2 * r)) (remainderSeries_factor D Sc cutoff L i hi hN)
  rw [remainderSeries, PowerSeries.coeff_mk, sub_mul, one_mul, map_sub,
    elementaryEvenInverse_even, oddLinearTerm_mul_even, sub_zero] at h
  exact h

/-- Odd ordinary remainder coefficients retain the original left exterior
factor and the sign (−1)^(N+1). -/
theorem remainder_odd (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    remainder D Sc cutoff L i hN (2 * r + 1) =
      (-1 : k) ^ (cutoff i + 1) •
        (coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩) *
          polynomialToPower D cutoff L (PowerSeries.coeff r
            (PowerSeries.invOfUnit (SKM.SYM.generatorSeries k i) 1))) := by
  have h := congrArg (PowerSeries.coeff (2 * r + 1)) (remainderSeries_factor D Sc cutoff L i hi hN)
  rw [remainderSeries, PowerSeries.coeff_mk, sub_mul, one_mul, map_sub,
    elementaryEvenInverse_odd, oddLinearTerm_mul_coeff_succ, elementaryEvenInverse_even,
    zero_sub, smul_mul_assoc] at h
  rw [pow_succ, mul_neg, mul_one]
  exact h.trans (neg_smul ((-1 : k) ^ cutoff i)
    (coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩) *
      polynomialToPower D cutoff L (PowerSeries.coeff r
        (PowerSeries.invOfUnit (SKM.SYM.generatorSeries k i) 1)))).symm

private theorem rescale_inverse (i : I) :
    PowerSeries.rescale (-1 : MvPolynomial (I × ℕ) k)
      (PowerSeries.invOfUnit (SKM.SYM.generatorSeries k i) 1) =
      PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1 := by
  let A := PowerSeries.rescale (-1 : MvPolynomial (I × ℕ) k) (SKM.SYM.generatorSeries k i)
  let B := PowerSeries.rescale (-1 : MvPolynomial (I × ℕ) k)
    (PowerSeries.invOfUnit (SKM.SYM.generatorSeries k i) 1)
  have hAB : A * B = 1 := by
    change PowerSeries.rescale (-1 : MvPolynomial (I × ℕ) k) _ *
      PowerSeries.rescale (-1 : MvPolynomial (I × ℕ) k) _ = 1
    rw [← map_mul, PowerSeries.mul_invOfUnit _ _ (generatorSeries_constantCoeff (k := k) i), map_one]
  have hA : PowerSeries.constantCoeff A = ((1 : (MvPolynomial (I × ℕ) k)ˣ) : _) := by
    change PowerSeries.constantCoeff (PowerSeries.rescale (-1 : MvPolynomial (I × ℕ) k) _) = _
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, generatorSeries_constantCoeff]
  calc
    B = (PowerSeries.invOfUnit A 1 * A) * B := by rw [PowerSeries.invOfUnit_mul _ _ hA, one_mul]
    _ = PowerSeries.invOfUnit A 1 := by rw [mul_assoc, hAB, mul_one]

/-- The literal coefficient of 1/C(−z), formed in the commutative
polynomial algebra and then mapped to the actual coefficient power quotient. -/
def completeCoefficient (i : I) (r : ℕ) : CoefficientPowerQuotient (k := k) D cutoff L :=
  polynomialToPower D cutoff L (PowerSeries.coeff r (PowerSeries.invOfUnit
    (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1))

private theorem completeCoefficient_eq (i : I) (r : ℕ) :
    completeCoefficient (k := k) D cutoff L i r =
      (-1 : k) ^ r • polynomialToPower D cutoff L
        (PowerSeries.coeff r (PowerSeries.invOfUnit (SKM.SYM.generatorSeries k i) 1)) := by
  rw [completeCoefficient, ← rescale_inverse (k := k) i, PowerSeries.coeff_rescale]
  have hs : (-1 : MvPolynomial (I × ℕ) k) ^ r =
      (-1 : k) ^ r • (1 : MvPolynomial (I × ℕ) k) := by
    rw [Algebra.smul_def, mul_one, map_pow, map_neg, map_one]
  rw [hs, smul_mul_assoc, one_mul, map_smul]

private theorem choose_even_parity (r : ℕ) :
    (((2 * r).choose 2 : ℕ) : ZMod 2) = (r : ZMod 2) := by
  by_cases hr : r = 0
  · subst r
    simp
  · have he : (2 * r).choose 2 = r * (2 * r - 1) := by
      rw [Nat.choose_two_right]
      rw [show 2 * r * (2 * r - 1) = (r * (2 * r - 1)) * 2 by ring, Nat.mul_div_cancel]
      omega
    rw [he, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 2 * r), Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one]
    simp only [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_sub,
      show -(1 : ZMod 2) = 1 from rfl, mul_one]

private theorem choose_odd_parity (r : ℕ) :
    (((2 * r + 1).choose 2 : ℕ) : ZMod 2) = (r : ZMod 2) := by
  have h : (2 * r + 1).choose 2 = 2 * r + (2 * r).choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ (2 * r) 1
  rw [h, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, choose_even_parity]
  simp only [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]

/-- Every even-index normalized reservoir moment is the actual mapped
coefficient of 1/C(−z), as in equation (7) of the written proof. -/
theorem signedMoment_even (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    signedMoment D Sc cutoff L i hN (cutoff i - 1 + 2 * r) =
      completeCoefficient D cutoff L i r := by
  rw [signedMoment_remainder D Sc cutoff L i hi hN, choose_even_parity,
    remainder_even D Sc cutoff L i hi hN, sign_natCast_2]
  exact (completeCoefficient_eq D cutoff L i r).symm

/-- Every odd-index normalized reservoir moment retains its independent
exterior generator on the left, with the prescribed sign (−1)^(N+1). -/
theorem signedMoment_odd (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    signedMoment D Sc cutoff L i hN (cutoff i - 1 + (2 * r + 1)) =
      (-1 : k) ^ (cutoff i + 1) •
        (coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩) *
          completeCoefficient D cutoff L i r) := by
  rw [signedMoment_remainder D Sc cutoff L i hi hN, choose_odd_parity,
    remainder_odd D Sc cutoff L i hi hN, sign_natCast_2, completeCoefficient_eq]
  simp only [mul_smul_comm, smul_smul]
  rw [mul_comm ((-1 : k) ^ r) ((-1 : k) ^ (cutoff i + 1))]

end OddMath.QuiverHecke.ELV.PowerVacuumCoefficient
end

end

section

/-! # Full moment maps on the literal coefficient-power vacuum

The all-vector interpretation of the scalar reservoir series in
`SwappedVacuumNonpositiveBubbles.md`, §2. The actual ordinary unit,
signed induction dot and prescribed inverse row define the maps.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.PowerVacuumCoefficient
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private abbrev coefficientProjection :=
  (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
private abbrev target (i : I) := mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L) ⟨[]⟩
private def dot (i : I) : Module.End k (target D Sc cutoff L i) :=
  inductionDot D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
    ((append D Sc cutoff i).obj ⟨[]⟩)
private def outputCoefficient (i : I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    Module.End k (target D Sc cutoff L i) :=
  SVec.toLinearMap (((BalancedInduction.restriction (append D Sc cutoff i)).obj
    ((BalancedInduction.induction (append D Sc cutoff i)).obj
      (coefficientPowerVacuum D Sc cutoff L))).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
        (coefficientEndomorphism D Sc cutoff [] a))

/-- The actual signed n-th-dot moment on every input vector of literal A/T. -/
def momentMap (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    Module.End k (CoefficientPowerQuotient (k := k) D cutoff L) :=
  (functional D Sc cutoff L i hN).comp
    ((dot D Sc cutoff L i ^ n).comp (unit D Sc cutoff L i))

private theorem unit_eq (i : I) (z : CoefficientPowerQuotient (k := k) D cutoff L) :
    unit D Sc cutoff L i z = BalancedInduction.unit (append D Sc cutoff i)
      (coefficientPowerVacuum D Sc cutoff L).toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)
        (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z) := by
  exact adjunctionUnit_total_apply D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
    (⟨[]⟩ : OldCategory D Sc cutoff) (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z)

private theorem unit_coefficient (i : I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (z : CoefficientPowerQuotient (k := k) D cutoff L) :
    outputCoefficient D Sc cutoff L i a (unit D Sc cutoff L i z) =
      unit D Sc cutoff L i (coefficientProjection D cutoff L a * z) := by
  let M := coefficientPowerVacuum D Sc cutoff L
  let J := append D Sc cutoff i
  let f : (⟨[]⟩ : OldCategory D Sc cutoff) ⟶ ⟨[]⟩ := coefficientEndomorphism D Sc cutoff [] a
  have h := LinearMap.congr_fun (BalancedInduction.unit_naturality J M.toFunctor f)
    (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z)
  simp only [LinearMap.comp_apply] at h
  change outputCoefficient D Sc cutoff L i a
    (BalancedInduction.unit J M.toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)
      (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z)) =
    BalancedInduction.unit J M.toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)
      ((coefficientPowerVacuum D Sc cutoff L).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
        (coefficientEndomorphism D Sc cutoff [] a) (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z)) at h
  rw [empty_coefficient_action D Sc cutoff L a z] at h
  simpa only [unit_eq] using h

private theorem scalar_commuting_power {V : Type u} [AddCommGroup V] [Module k V]
    (d a : Module.End k V) (s : k) (h : d.comp a = s • (a.comp d)) (n : ℕ) :
    (d ^ n).comp a = s ^ n • (a.comp (d ^ n)) := by
  have h' : d.comp a = a.comp (s • d) := by simpa only [LinearMap.comp_smul] using h
  have hp := Module.End.commute_pow_left_of_commute h' n
  simpa only [smul_pow, LinearMap.comp_smul] using hp

private theorem sign_nsmul (p : ZMod 2) (n : ℕ) : sign k (n • p) = sign k p ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, sign_add, ih, pow_succ]

private theorem dot_pow_coefficient (i : I) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) (n : ℕ) :
    (dot D Sc cutoff L i ^ n).comp (outputCoefficient D Sc cutoff L i a) =
      koszulSign (n • D.parity i) p •
        ((outputCoefficient D Sc cutoff L i a).comp (dot D Sc cutoff L i ^ n)) := by
  let M := coefficientPowerVacuum D Sc cutoff L
  let J := append D Sc cutoff i
  let f : J.obj (⟨[]⟩ : OldCategory D Sc cutoff) ⟶ J.obj ⟨[]⟩ :=
    J.map (X := ⟨[]⟩) (Y := ⟨[]⟩) (coefficientEndomorphism D Sc cutoff [] a)
  have hf : f ∈ parity (R := k) _ _ p :=
    IsSuperfunctor.map_mem (F := J) (coefficientEndomorphism_mem D Sc cutoff [] ha)
  have h := (BalancedInduction.transformLinear_supernatural
    (oldAppendDot_supernatural D Sc cutoff i) M).naturality hf
  change (dot D Sc cutoff L i).comp (outputCoefficient D Sc cutoff L i a) =
    sign k (D.parity i * p) •
      ((outputCoefficient D Sc cutoff L i a).comp (dot D Sc cutoff L i)) at h
  have hp := scalar_commuting_power (dot D Sc cutoff L i) (outputCoefficient D Sc cutoff L i a)
    (sign k (D.parity i * p)) h n
  rw [← sign_nsmul] at hp
  have he : n • (D.parity i * p) = (n • D.parity i) * p := by
    simp only [nsmul_eq_mul]
    ring
  rw [he, ← koszulSign_smul (R := k)] at hp
  exact hp

/-- Full coefficient superlinearity of every higher moment map, with
its total parity and the original left coefficient order. -/
theorem momentMap_coefficient (i : I) (hN : 0 < cutoff i) (n : ℕ) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    momentMap D Sc cutoff L i hN n (coefficientProjection D cutoff L a) =
      koszulSign ((n + (cutoff i - 1)) • D.parity i) p •
        (coefficientProjection D cutoff L a * signedMoment D Sc cutoff L i hN n) := by
  have hu := unit_coefficient D Sc cutoff L i a (1 : CoefficientPowerQuotient (k := k) D cutoff L)
  rw [mul_one] at hu
  have hd := LinearMap.congr_fun (dot_pow_coefficient D Sc cutoff L i ha n)
    (unit D Sc cutoff L i 1)
  have h := congrArg (functional D Sc cutoff L i hN) hd
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h
  have hcap := functional_coefficient D Sc cutoff L i hN ha
    ((dot D Sc cutoff L i ^ n) (unit D Sc cutoff L i 1))
  change functional D Sc cutoff L i hN
    (outputCoefficient D Sc cutoff L i a ((dot D Sc cutoff L i ^ n) (unit D Sc cutoff L i 1))) =
    koszulSign ((cutoff i - 1) • D.parity i) p •
      (coefficientProjection D cutoff L a * signedMoment D Sc cutoff L i hN n) at hcap
  rw [map_zsmul, hcap] at h
  rw [smul_smul, ← koszulSign_add_left, ← add_nsmul] at h
  change functional D Sc cutoff L i hN
    ((dot D Sc cutoff L i ^ n) (outputCoefficient D Sc cutoff L i a (unit D Sc cutoff L i 1))) = _ at h
  rw [hu] at h
  exact h

private theorem unit_apply_mem (i : I) {p : ZMod 2}
    {z : CoefficientPowerQuotient (k := k) D cutoff L}
    (hz : z ∈ coefficientPowerParity D cutoff L p) :
    unit D Sc cutoff L i z ∈ (target D Sc cutoff L i).part p := by
  rw [unit_eq]
  have h := SVec.apply_mem_part (BalancedInduction.unit_mem (append D Sc cutoff i)
    (coefficientPowerVacuum D Sc cutoff L) (⟨[]⟩ : OldCategory D Sc cutoff))
      (coefficientPowerVacuumEmptyEquiv_mem D Sc cutoff L hz)
  change BalancedInduction.unit (append D Sc cutoff i)
    (coefficientPowerVacuum D Sc cutoff L).toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)
      (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z) ∈
        (target D Sc cutoff L i).part (p + 0) at h
  simpa only [add_zero] using h

private theorem dot_pow_apply_mem (i : I) {p : ZMod 2}
    {z : target D Sc cutoff L i} (hz : z ∈ (target D Sc cutoff L i).part p) (n : ℕ) :
    (dot D Sc cutoff L i ^ n) z ∈ (target D Sc cutoff L i).part (p + n • D.parity i) := by
  induction n with
  | zero => simpa only [pow_zero, Module.End.one_apply, zero_nsmul, add_zero] using hz
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := SVec.apply_mem_part (BalancedInduction.transformLinear_mem
      (oldAppendDot_supernatural D Sc cutoff i) (coefficientPowerVacuum D Sc cutoff L)
        ((append D Sc cutoff i).obj (⟨[]⟩ : OldCategory D Sc cutoff))) ih
    change dot D Sc cutoff L i ((dot D Sc cutoff L i ^ n) z) ∈
      (target D Sc cutoff L i).part ((p + n • D.parity i) + D.parity i) at h
    simpa only [succ_nsmul, add_assoc] using h

/-- The actual full moment map retains the total parity of its chosen
inverse row and all n signed dots. -/
theorem momentMap_mem (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    momentMap D Sc cutoff L i hN n ∈ parity (R := k)
      (coefficientPowerSpace D cutoff L) (coefficientPowerSpace D cutoff L)
        ((n + (cutoff i - 1)) • D.parity i) := by
  apply SVec.mem_parityHom_of_apply_mem
  intro p z hz
  have hu := unit_apply_mem D Sc cutoff L i hz
  have hd := dot_pow_apply_mem D Sc cutoff L i hu n
  have h := SVec.apply_mem_part (functional_mem D Sc cutoff L i hN) hd
  change momentMap D Sc cutoff L i hN n z ∈
    (coefficientPowerSpace D cutoff L).part (p + ((n + (cutoff i - 1)) • D.parity i))
  change momentMap D Sc cutoff L i hN n z ∈
    (coefficientPowerSpace D cutoff L).part ((p + n • D.parity i) + (cutoff i - 1) • D.parity i) at h
  simpa only [add_nsmul, add_assoc] using h

private theorem homogeneous_lift {p : ZMod 2}
    {z : CoefficientPowerQuotient (k := k) D cutoff L}
    (hz : z ∈ coefficientPowerParity D cutoff L p) :
    ∃ a ∈ SKM.SYM.elvCoefficientParity D cutoff p, coefficientProjection D cutoff L a = z := by
  obtain ⟨a, rfl⟩ := RingCon.mkₐ_surjective (α := k)
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon z
  refine ⟨GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) p a,
    (DirectSum.decompose (SKM.SYM.elvCoefficientParity D cutoff) a p).property, ?_⟩
  rw [← coefficientPowerSpace_projection D cutoff L p a]
  exact (SVec.mem_part_iff _).mp hz

private theorem homogeneous_comm {p q : ZMod 2}
    {a b : CoefficientPowerQuotient (k := k) D cutoff L}
    (ha : a ∈ coefficientPowerParity D cutoff L p)
    (hb : b ∈ coefficientPowerParity D cutoff L q) :
    a * b = koszulSign p q • (b * a) := by
  obtain ⟨a0, ha0, ea⟩ := homogeneous_lift D cutoff L ha
  obtain ⟨b0, hb0, eb⟩ := homogeneous_lift D cutoff L hb
  rw [← ea, ← eb]
  have h := congrArg (coefficientProjection D cutoff L) (ELVPScalar.elv_comm D cutoff ha0 hb0)
  simpa only [map_mul, map_zsmul] using h

/-- Every actual higher moment on every coefficient vector is the original
left multiplication by its proved scalar value on 1. No bubble-value
hypothesis or ordinary commutativity of A/T is used. -/
theorem momentMap_apply (i : I) (hN : 0 < cutoff i) (n : ℕ)
    (z : CoefficientPowerQuotient (k := k) D cutoff L) :
    momentMap D Sc cutoff L i hN n z = signedMoment D Sc cutoff L i hN n * z := by
  have hvalue : signedMoment D Sc cutoff L i hN n ∈
      coefficientPowerParity D cutoff L ((n + (cutoff i - 1)) • D.parity i) := by
    have h := SVec.apply_mem_part (momentMap_mem D Sc cutoff L i hN n)
      (SetLike.one_mem_graded (coefficientPowerParity (k := k) D cutoff L))
    change signedMoment D Sc cutoff L i hN n ∈ coefficientPowerParity D cutoff L
      (0 + ((n + (cutoff i - 1)) • D.parity i)) at h
    simpa only [zero_add] using h
  have hh {p : ZMod 2} {a : CoefficientPowerQuotient (k := k) D cutoff L}
      (ha : a ∈ coefficientPowerParity D cutoff L p) :
      momentMap D Sc cutoff L i hN n a = signedMoment D Sc cutoff L i hN n * a := by
    obtain ⟨b, hb, rfl⟩ := homogeneous_lift D cutoff L ha
    have h := momentMap_coefficient D Sc cutoff L i hN n hb
    have hc := homogeneous_comm D cutoff L (coefficientPowerQuotient_mem D cutoff L hb) hvalue
    have hs : koszulSign ((n + (cutoff i - 1)) • D.parity i) p *
        koszulSign p ((n + (cutoff i - 1)) • D.parity i) = 1 := by
      rw [koszulSign_comm p _, koszulSign_mul_self]
    rw [hc, smul_smul, hs, one_smul] at h
    exact h
  have hz : z = (coefficientPowerSpace D cutoff L).proj 0 z +
      (coefficientPowerSpace D cutoff L).proj 1 z :=
    ((coefficientPowerSpace D cutoff L).proj_apply_add z).symm
  calc
    _ = momentMap D Sc cutoff L i hN n
        ((coefficientPowerSpace D cutoff L).proj 0 z + (coefficientPowerSpace D cutoff L).proj 1 z) :=
      congrArg (momentMap D Sc cutoff L i hN n) hz
    _ = _ := by
      rw [map_add, hh ((coefficientPowerSpace D cutoff L).proj_mem_part 0 z),
        hh ((coefficientPowerSpace D cutoff L).proj_mem_part 1 z), ← mul_add, ← hz]

/-- The same all-vector identity as an endomorphism equality, for use
when whiskering the source bubble map through a chosen word functor. -/
theorem momentMap_eq_mulLeft (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    momentMap D Sc cutoff L i hN n = LinearMap.mulLeft k (signedMoment D Sc cutoff L i hN n) := by
  apply LinearMap.ext
  intro z
  exact momentMap_apply D Sc cutoff L i hN n z

/-- The complete even-index odd-colour reservoir series, as literal
endomorphisms on every vector of the actual power quotient. -/
theorem momentMap_even (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    momentMap D Sc cutoff L i hN (cutoff i - 1 + 2 * r) =
      LinearMap.mulLeft k (completeCoefficient D cutoff L i r) := by
  rw [momentMap_eq_mulLeft, signedMoment_even D Sc cutoff L i hi hN r]

/-- The complete odd-index reservoir series as literal endomorphisms,
retaining the original left exterior coefficient. -/
theorem momentMap_odd (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    momentMap D Sc cutoff L i hN (cutoff i - 1 + (2 * r + 1)) =
      LinearMap.mulLeft k ((-1 : k) ^ (cutoff i + 1) •
        (coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩) *
          completeCoefficient D cutoff L i r)) := by
  rw [momentMap_eq_mulLeft, signedMoment_odd D Sc cutoff L i hi hN r]

end OddMath.QuiverHecke.ELV.PowerVacuumCoefficient
end

end

section

/-! # Full coefficient endomorphisms of old supermodules

The source-word coefficient action required by `SwappedVacuumCoordinates.md`,
§6, consists of genuine supermodule maps. Its odd components retain their
parity and their signed balanced-induction tensor formula.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def coefficientHomLinear (v : List I) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
      End (⟨v⟩ : OldCategory D Sc cutoff) :=
  (ideal D Sc cutoff v v).mkQ.comp (ELVPScalar.scalar D Sc cutoff v)

private def evaluateCoefficient (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (v : OldCategory D Sc cutoff) : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
      End (M.obj v) :=
  (M.toFunctor.mapLinearMap k).comp (coefficientHomLinear D Sc cutoff v.word)

private def coefficientComponent (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (p : ZMod 2) (v : OldCategory D Sc cutoff) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k] End (M.obj v) :=
  (evaluateCoefficient D Sc cutoff M v).comp
    (GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) p)

private theorem component_mem (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (p : ZMod 2) (v : OldCategory D Sc cutoff) :
    coefficientComponent D Sc cutoff M p v a ∈ parity (R := k) (M.obj v) (M.obj v) p :=
  M.map_mem (coefficientEndomorphism_mem D Sc cutoff v.word
    (DirectSum.decompose (SKM.SYM.elvCoefficientParity D cutoff) a p).property)

private theorem component_naturality (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (p : ZMod 2)
    {v w : OldCategory D Sc cutoff} {q : ZMod 2} (f : v ⟶ w)
    (hf : f ∈ parity (R := k) v w q) :
    M.map f ≫ coefficientComponent D Sc cutoff M p w a =
      koszulSign p q • (coefficientComponent D Sc cutoff M p v a ≫ M.map f) := by
  let a0 := GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) p a
  have ha0 : a0 ∈ SKM.SYM.elvCoefficientParity D cutoff p :=
    (DirectSum.decompose (SKM.SYM.elvCoefficientParity D cutoff) a p).property
  have h := congrArg M.toFunctor.map
    (coefficientEndomorphism_slide D Sc cutoff ha0 v.word w.word f)
  rw [twist_of_mem p hf, Linear.comp_smul, M.toFunctor.map_smul] at h
  rw [koszulSign_smul (R := k)]
  simp only [Functor.map_comp] at h
  change M.map f ≫ coefficientComponent D Sc cutoff M p w a =
    sign k (p * q) • (coefficientComponent D Sc cutoff M p v a ≫ M.map f) at h
  exact h

/-- The full coefficient action as genuine old-supermodule maps, including
its inhomogeneous elements and both homogeneous components. -/
private def coefficientModuleLinear (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k] End M where
  toFun a := Superfunctor.homMk {
    app p v := coefficientComponent D Sc cutoff M p v a
    app_mem := component_mem D Sc cutoff M a
    naturality := fun p _ _ _ f hf => component_naturality D Sc cutoff M a p f hf }
  map_add' a b := by
    apply Superfunctor.hom_ext
    intro p v
    exact (coefficientComponent D Sc cutoff M p v).map_add a b
  map_smul' r a := by
    apply Superfunctor.hom_ext
    intro p v
    exact (coefficientComponent D Sc cutoff M p v).map_smul r a

private theorem coefficient_projections_add (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) 0 a +
      GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) 1 a = a := by
  refine DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cutoff) (by simp) ?_ ?_ a
  · intro p a
    rcases parity_eq_zero_or_one p with rfl | rfl
    · simp only [GradedAlgebra.proj_apply,
        DirectSum.decompose_of_mem_same _ a.property,
        DirectSum.decompose_of_mem_ne _ a.property (by decide : (0 : ZMod 2) ≠ 1), add_zero]
    · simp only [GradedAlgebra.proj_apply,
        DirectSum.decompose_of_mem_same _ a.property,
        DirectSum.decompose_of_mem_ne _ a.property (by decide : (1 : ZMod 2) ≠ 0), zero_add]
  · intro a b ha hb
    simpa only [map_add, add_add_add_comm] using congrArg₂ (· + ·) ha hb

/-- Total evaluation is exactly the original coefficient endomorphism
of the old category, with no reversed or unsigned replacement. -/
private theorem coefficientModuleLinear_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (v : OldCategory D Sc cutoff) :
    (coefficientModuleLinear D Sc cutoff M a).total v =
      M.map (X := v) (Y := v) (coefficientEndomorphism D Sc cutoff v.word a) := by
  change evaluateCoefficient D Sc cutoff M v
      (GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) 0 a) +
    evaluateCoefficient D Sc cutoff M v
      (GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) 1 a) = _
  rw [← map_add, coefficient_projections_add]
  rfl

private theorem module_hom_ext_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (f g : End M)
    (h : ∀ v, f.total v = g.total v) : f = g := by
  apply Superfunctor.hom_ext_parity
  · intro v
    have hh := congrArg (proj (R := k) 0) (h v)
    simpa only [SuperNatTrans.total, map_add, proj_of_mem (f.app_mem 0 v),
      proj_of_mem_ne (f.app_mem 1 v) (by decide : (1 : ZMod 2) ≠ 0),
      proj_of_mem (g.app_mem 0 v), proj_of_mem_ne (g.app_mem 1 v) (by decide : (1 : ZMod 2) ≠ 0),
      add_zero] using hh
  · intro v
    have hh := congrArg (proj (R := k) 1) (h v)
    simpa only [SuperNatTrans.total, map_add, proj_of_mem (f.app_mem 1 v),
      proj_of_mem_ne (f.app_mem 0 v) (by decide : (0 : ZMod 2) ≠ 1),
      proj_of_mem (g.app_mem 1 v), proj_of_mem_ne (g.app_mem 0 v) (by decide : (0 : ZMod 2) ≠ 1),
      zero_add] using hh

private theorem coefficient_one (v : OldCategory D Sc cutoff) :
    coefficientEndomorphism D Sc cutoff v.word (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) =
      (𝟙 v : v ⟶ v) := rfl

private theorem coefficient_comp (v : OldCategory D Sc cutoff)
    (a b : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (coefficientEndomorphism D Sc cutoff v.word b : v ⟶ v) ≫
      coefficientEndomorphism D Sc cutoff v.word a = coefficientEndomorphism D Sc cutoff v.word (a * b) :=
  coefficientEndomorphism_comp D Sc cutoff v.word b a

/-- The genuine coefficient action on old supermodule endomorphisms is
an algebra map in the original multiplication order. -/
def coefficientModuleAction (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₐ[k] End M :=
  AlgHom.ofLinearMap (coefficientModuleLinear D Sc cutoff M) (by
    apply module_hom_ext_total D Sc cutoff M
    intro v
    rw [coefficientModuleLinear_total, coefficient_one]
    change M.toFunctor.map (𝟙 v) = (𝟙 M : End M).total v
    rw [M.toFunctor.map_id]
    exact (SuperNatTrans.id_total M.toFunctor v).symm) (by
    intro a b
    apply module_hom_ext_total D Sc cutoff M
    intro v
    rw [End.mul_def, Superfunctor.comp_total, coefficientModuleLinear_total,
      coefficientModuleLinear_total, coefficientModuleLinear_total, ← M.toFunctor.map_comp,
      coefficient_comp])

/-- Total evaluation is the original coefficient action on every old word. -/
theorem coefficientModuleAction_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (v : OldCategory D Sc cutoff) :
    (coefficientModuleAction D Sc cutoff M a).total v =
      M.map (X := v) (Y := v) (coefficientEndomorphism D Sc cutoff v.word a) :=
  coefficientModuleLinear_total D Sc cutoff M a v

private theorem coefficientModuleAction_zero
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (ha : KillsCoefficient D Sc cutoff M a) : coefficientModuleAction D Sc cutoff M a = 0 := by
  apply module_hom_ext_total D Sc cutoff M
  intro v
  rw [coefficientModuleAction_total]
  change M.map (X := v) (Y := v) (coefficientEndomorphism D Sc cutoff v.word a) = 0 + 0
  rw [add_zero]
  exact ha v.word

variable (L : I × ℕ → ℕ)

private theorem power_le_action_kernel
    (M : CoefficientPowerModules D Sc cutoff (elementaryCoefficients (k := k) D cutoff) L) :
    coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L ≤
      TwoSidedIdeal.ofRingCon (RingCon.ker
        (coefficientModuleAction D Sc cutoff M.obj).toRingHom) := by
  intro a ha
  change coefficientModuleAction D Sc cutoff M.obj a = coefficientModuleAction D Sc cutoff M.obj 0
  rw [map_zero]
  exact coefficientModuleAction_zero D Sc cutoff M.obj a
    ((mem_coefficientAnnihilator D Sc cutoff M.obj a).mp (M.property ha))

/-- The literal A/T action by supermodule maps on every T-annihilated old module. -/
def powerModuleCoefficientAction
    (M : CoefficientPowerModules D Sc cutoff (elementaryCoefficients (k := k) D cutoff) L) :
    CoefficientPowerQuotient (k := k) D cutoff L →ₐ[k] End M.obj :=
  RingCon.liftₐ _ (coefficientModuleAction D Sc cutoff M.obj)
    (TwoSidedIdeal.ringCon_le_iff.mp (power_le_action_kernel D Sc cutoff L M))

/-- The quotient action evaluates on coefficient representatives without changing maps. -/
@[simp] theorem powerModuleCoefficientAction_mk
    (M : CoefficientPowerModules D Sc cutoff (elementaryCoefficients (k := k) D cutoff) L)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    powerModuleCoefficientAction D Sc cutoff L M
      ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a) =
        coefficientModuleAction D Sc cutoff M.obj a := rfl

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Reservoir moments of an even moving colour on the power vacuum

The even-colour counterpart of `ELVCoefficientPowerOddSeries`
(`SwappedVacuumNonpositiveBubbles.md`, §2). For `D.parity i = 0` the signed
and raw moments agree, the actual one-strand relation is the reversed series
`E(-w) = Σₙ (-1)ⁿ eₙ wⁿ` (truncated by the cutoff relations of A/T), and the
higher reservoir moments are the coefficients of `1/E(-w)`:
`signedMoment (N - 1 + r) = completeCoefficient r`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.PowerVacuumCoefficient
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private theorem coeff_monomial_mul_even {A : Type u} [Semiring A]
    (n l : ℕ) (a : A) (f : PowerSeries A) :
    PowerSeries.coeff l (PowerSeries.monomial n a * f) =
      if n ≤ l then a * PowerSeries.coeff (l - n) f else 0 := by
  change MvPowerSeries.coeff (Finsupp.single () l)
    (MvPowerSeries.monomial (Finsupp.single () n) a * f) = _
  rw [MvPowerSeries.coeff_monomial_mul]
  simp only [Finsupp.single_le_single, ← Finsupp.single_tsub]
  rfl

/-- For an even colour the triangular dot sign is trivial. -/
theorem even_signedMoment_rawMoment (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i) (n : ℕ) :
    signedMoment D Sc cutoff L i hN n = rawMoment D Sc cutoff L i hN 1 n := by
  rw [signedMoment_rawMoment, hi]
  simp only [inductionUnitDotSign, smul_zero, Supercategory.sign_zero, one_smul]

/-- The actual one-strand relation, with no Koszul sign for an even colour. -/
theorem even_rawMoment_recurrence (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i) (m : ℕ) :
    (∑ j : Fin (cutoff i + 1),
      (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        (singleCoefficient D cutoff i j) * rawMoment D Sc cutoff L i hN 1 (j.val + m)) = 0 := by
  have h := rawMoment_one_recurrence D Sc cutoff L i hN m
  rw [hi] at h
  simpa only [smul_zero, mul_zero, sub_zero, koszulSign_zero_left, one_smul] using h

/-- The low window of the actual even inverse row. -/
theorem even_rawMoment_window (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i)
    (n : ℕ) (hn : n < cutoff i) :
    rawMoment D Sc cutoff L i hN 1 n = if n + 1 = cutoff i then 1 else 0 := by
  rw [rawMoment_one_window D Sc cutoff L i hN n hn, hi]
  simp only [inductionUnitDotSign, smul_zero, Supercategory.sign_zero, one_smul]

/-- The even-colour top remainders at exponents N−1+l. -/
def evenRemainder (i : I) (hN : 0 < cutoff i) (l : ℕ) :
    CoefficientPowerQuotient (k := k) D cutoff L :=
  rawMoment D Sc cutoff L i hN 1 (cutoff i - 1 + l)

/-- Their complete series. -/
def evenRemainderSeries (i : I) (hN : 0 < cutoff i) :
    PowerSeries (CoefficientPowerQuotient (k := k) D cutoff L) :=
  PowerSeries.mk (evenRemainder D Sc cutoff L i hN)

theorem evenRemainder_zero (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i) :
    evenRemainder D Sc cutoff L i hN 0 = 1 := by
  have h := even_rawMoment_window D Sc cutoff L i hi hN (cutoff i - 1) (by omega)
  have ht : cutoff i - 1 + 1 = cutoff i := by omega
  simpa only [evenRemainder, Nat.add_zero, ite_eq_left ht] using h

theorem evenRemainder_recurrence (i : I) (hi : D.parity i = 0)
    (hN : 0 < cutoff i) (l : ℕ) (hl : 0 < l) :
    (∑ j : Fin (cutoff i + 1),
      (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        (singleCoefficient D cutoff i j) *
          (if cutoff i - j.val ≤ l then evenRemainder D Sc cutoff L i hN (l - (cutoff i - j.val))
           else 0)) = 0 := by
  calc
    _ = ∑ j : Fin (cutoff i + 1),
        (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
          (singleCoefficient D cutoff i j) * rawMoment D Sc cutoff L i hN 1 (j.val + (l - 1)) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      by_cases hj : cutoff i - j.val ≤ l
      · rw [ite_eq_left hj, evenRemainder]
        congr 1
        have hv := j.isLt
        omega
      · rw [ite_eq_right hj]
        have hv := j.isLt
        have he := even_rawMoment_window D Sc cutoff L i hi hN (j.val + (l - 1)) (by omega)
        have ht : ¬ j.val + (l - 1) + 1 = cutoff i := by omega
        simpa only [ite_eq_right ht] using he.symm
    _ = 0 := even_rawMoment_recurrence D Sc cutoff L i hi hN (l - 1)

/-- The reversed monic relation inverts the actual even remainder series. -/
theorem remainderPolynomial_mul_evenRemainderSeries (i : I) (hi : D.parity i = 0)
    (hN : 0 < cutoff i) :
    remainderPolynomial D cutoff L i * evenRemainderSeries D Sc cutoff L i hN = 1 := by
  classical
  apply PowerSeries.ext
  intro l
  simp only [remainderPolynomial, evenRemainderSeries, Finset.sum_mul, map_sum,
    coeff_monomial_mul_even, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  by_cases hl : l = 0
  · subst l
    rw [ite_eq_left rfl]
    rw [Finset.sum_eq_single (Fin.last (cutoff i))]
    · simp only [Fin.val_last, Nat.sub_self, le_refl, ↓reduceIte,
        singleCoefficient_top, map_one, evenRemainder_zero D Sc cutoff L i hi hN, mul_one]
    · intro j _ hj
      have hne : j.val ≠ cutoff i := by
        intro h
        apply hj
        exact Fin.ext h
      have hv := j.isLt
      rw [ite_eq_right (by omega : ¬ cutoff i - j.val ≤ 0)]
    · simp
  · rw [ite_eq_right hl]
    simpa only [mul_ite, mul_zero] using evenRemainder_recurrence D Sc cutoff L i hi hN l (by omega)

private theorem even_reversed_coefficient (i : I) (hi : D.parity i = 0)
    (n : ℕ) (hn : n ≤ cutoff i) :
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
      (singleCoefficient D cutoff i ⟨cutoff i - n, by omega⟩) =
      (-1 : k) ^ n • coefficientPowerQuotientMap (k := k) D cutoff L
        (SKM.SYM.evenCyclotomicCoefficient D k i n) := by
  have h1 : ¬ D.parity i = 1 := by rw [hi]; decide
  unfold singleCoefficient
  rw [dite_eq_right h1, SKM.SYM.evenMonicCoefficient, map_smul, map_smul]
  rw [show cutoff i - (cutoff i - n) = n by omega]
  rfl

private theorem even_coefficient_tail (i : I) (hi : D.parity i = 0)
    (n : ℕ) (hn : cutoff i < n) :
    coefficientPowerQuotientMap (k := k) D cutoff L
      (SKM.SYM.evenCyclotomicCoefficient D k i n) = 0 := by
  apply (coefficientPowerQuotientMap_eq_zero_iff D cutoff L _).mpr
  apply TwoSidedIdeal.mem_sup_left
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  apply TwoSidedIdeal.subset_span
  refine Or.inl ⟨i, r, ?_, rfl⟩
  rw [SKM.SYM.elvElementaryRank, ite_eq_left hi]
  omega

private theorem polynomial_generatorCoeff_even (i : I) (n : ℕ) :
    polynomialToPower (k := k) D cutoff L (PowerSeries.coeff n (SKM.SYM.generatorSeries k i)) =
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.evenCyclotomicCoefficient D k i n) := by
  cases n with
  | zero =>
    simp [SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff, SKM.SYM.evenCyclotomicCoefficient]
  | succ n =>
    simp [SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff, SKM.SYM.evenCyclotomicCoefficient,
      polynomialToPower, AlgHom.comp_apply]

/-- For an even colour the reversed actual monic relation is the mapped
series `E(-w)` of the commutative polynomial algebra; the coefficients beyond
the cutoff vanish by the defining relations of A/T. -/
theorem even_remainderPolynomial (i : I) (hi : D.parity i = 0) :
    remainderPolynomial (k := k) D cutoff L i =
      PowerSeries.map (polynomialToPower D cutoff L).toRingHom
        (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) := by
  classical
  apply PowerSeries.ext
  intro n
  have hs : (-1 : MvPolynomial (I × ℕ) k) ^ n =
      (-1 : k) ^ n • (1 : MvPolynomial (I × ℕ) k) := by
    rw [Algebra.smul_def, mul_one, map_pow, map_neg, map_one]
  have hr : PowerSeries.coeff n (PowerSeries.map (polynomialToPower (k := k) D cutoff L).toRingHom
      (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i))) =
      (-1 : k) ^ n • coefficientPowerQuotientMap D cutoff L
        (SKM.SYM.evenCyclotomicCoefficient D k i n) := by
    rw [PowerSeries.coeff_map, PowerSeries.coeff_rescale, hs, smul_mul_assoc, one_mul]
    change polynomialToPower (k := k) D cutoff L _ = _
    rw [map_smul, polynomial_generatorCoeff_even]
  rw [hr, remainderPolynomial, map_sum]
  by_cases hn : n ≤ cutoff i
  · let j : Fin (cutoff i + 1) := ⟨cutoff i - n, by omega⟩
    rw [Finset.sum_eq_single j]
    · rw [PowerSeries.coeff_monomial, ite_eq_left (by dsimp [j]; omega)]
      exact even_reversed_coefficient D cutoff L i hi n hn
    · intro b _ hb
      rw [PowerSeries.coeff_monomial, ite_eq_right]
      intro he
      apply hb
      apply Fin.ext
      have hv := b.isLt
      dsimp [j]
      omega
    · simp
  · rw [even_coefficient_tail D cutoff L i hi n (by omega), smul_zero]
    apply Finset.sum_eq_zero
    intro j _
    rw [PowerSeries.coeff_monomial, ite_eq_right (by have hv := j.isLt; omega)]

private theorem rescaled_generator_constantCoeff (i : I) :
    PowerSeries.constantCoeff (PowerSeries.rescale (-1 : MvPolynomial (I × ℕ) k)
      (SKM.SYM.generatorSeries k i)) = ((1 : (MvPolynomial (I × ℕ) k)ˣ) : _) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
    one_mul]
  simp [SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff]

/-- The actual even remainder series is the mapped inverse of `E(-w)`. -/
theorem evenRemainderSeries_eq (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i) :
    evenRemainderSeries D Sc cutoff L i hN =
      PowerSeries.map (polynomialToPower D cutoff L).toRingHom
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1) := by
  have hQP : PowerSeries.map (polynomialToPower (k := k) D cutoff L).toRingHom
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1) *
      remainderPolynomial D cutoff L i = 1 := by
    rw [even_remainderPolynomial D cutoff L i hi, ← map_mul,
      PowerSeries.invOfUnit_mul _ _ (rescaled_generator_constantCoeff (k := k) i), map_one]
  calc
    _ = (PowerSeries.map (polynomialToPower (k := k) D cutoff L).toRingHom
          (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1) *
        remainderPolynomial D cutoff L i) * evenRemainderSeries D Sc cutoff L i hN := by
      rw [hQP, one_mul]
    _ = _ := by
      rw [mul_assoc, remainderPolynomial_mul_evenRemainderSeries D Sc cutoff L i hi hN, mul_one]

/-- Every higher reservoir moment of an even colour is the actual mapped
coefficient of `1/E(-z)`. -/
theorem even_colour_signedMoment (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i) (r : ℕ) :
    signedMoment D Sc cutoff L i hN (cutoff i - 1 + r) =
      completeCoefficient D cutoff L i r := by
  rw [even_signedMoment_rawMoment D Sc cutoff L i hi hN]
  have h := congrArg (PowerSeries.coeff r) (evenRemainderSeries_eq D Sc cutoff L i hi hN)
  rw [evenRemainderSeries, PowerSeries.coeff_mk, PowerSeries.coeff_map] at h
  exact h

end OddMath.QuiverHecke.ELV.PowerVacuumCoefficient
end

end
