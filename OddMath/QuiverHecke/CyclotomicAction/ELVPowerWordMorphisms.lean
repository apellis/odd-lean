import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordYoneda
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform

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
