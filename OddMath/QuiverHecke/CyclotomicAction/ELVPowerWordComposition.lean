import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContexts
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates

/-! # Signed composition in the full regular-power word chart

SwappedVacuumCoordinates §§4–5: the super-opposite composition sign in the
old-Hom word chart is retained before combining it with the signed half-turn.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordComposition
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (s t u : List I)

/-- Signed old-Hom maps retain scalar multiplication. -/
theorem fromArrow_smul (a : k)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    PowerWordMorphisms.fromArrow D Sc cutoff L s t (a • g) =
      a • PowerWordMorphisms.fromArrow D Sc cutoff L s t g := by
  unfold PowerWordMorphisms.fromArrow
  rw [map_smul]
  exact (PowerWordYoneda.homEquiv D Sc cutoff L s (powerWordObject D Sc cutoff L t)).symm.map_smul a _

private theorem evaluate_fromArrow
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    PowerWordYoneda.evaluate D Sc cutoff L s (powerWordObject D Sc cutoff L t)
      (PowerWordMorphisms.fromArrow D Sc cutoff L s t g) =
    powerWordGenerator D Sc cutoff L t (OldCategory.mk s) g :=
  PowerWordYoneda.evaluate_fromElement D Sc cutoff L s (powerWordObject D Sc cutoff L t) _

/-- Whole-map super-opposite composition, on every full coefficient vector. -/
theorem fromArrow_comp {p q : ZMod 2}
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s)
    (f : (OldCategory.mk u : OldCategory D Sc cutoff) ⟶ OldCategory.mk t)
    (hg : g ∈ parity (R := k) _ _ p) (hf : f ∈ parity (R := k) _ _ q) :
    PowerWordMorphisms.fromArrow D Sc cutoff L s t g ≫
        PowerWordMorphisms.fromArrow D Sc cutoff L t u f =
      sign k (p * q) • PowerWordMorphisms.fromArrow D Sc cutoff L s u (f ≫ g) := by
  apply (PowerWordYoneda.homEquiv D Sc cutoff L s (powerWordObject D Sc cutoff L u)).injective
  rw [map_smul]
  change PowerWordYoneda.evaluate D Sc cutoff L s (powerWordObject D Sc cutoff L u) _ =
    sign k (p * q) • PowerWordYoneda.evaluate D Sc cutoff L s (powerWordObject D Sc cutoff L u) _
  rw [evaluate_fromArrow]
  change _ + _ = _
  dsimp only [PowerWordYoneda.unitVector, powerWordObject] at ⊢
  erw [PowerWordMorphisms.composition_generator, PowerWordMorphisms.composition_generator]
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl
  · simp [proj_of_mem hg, proj_of_mem hf,
      proj_of_mem_ne (p := 1) hg (by decide), proj_of_mem_ne (p := 1) hf (by decide),
      Supercategory.sign]
  · simp [proj_of_mem hg, proj_of_mem hf,
      proj_of_mem_ne (p := 1) hg (by decide), proj_of_mem_ne (p := 0) hf (by decide),
      Supercategory.sign]
  · simp [proj_of_mem hg, proj_of_mem hf,
      proj_of_mem_ne (p := 0) hg (by decide), proj_of_mem_ne (p := 1) hf (by decide),
      Supercategory.sign]
  · simp [proj_of_mem hg, proj_of_mem hf,
      proj_of_mem_ne (p := 0) hg (by decide), proj_of_mem_ne (p := 0) hf (by decide),
      Supercategory.sign]

/-- The half-turn followed by the literal old quotient retains total
coefficient-plus-affine parity. -/
theorem halfTurnOldHom_mem {s t : List I} {p : ZMod 2}
    {f : coefficientObj D Sc s ⟶ coefficientObj D Sc t}
    (hf : f ∈ parity (R := k) _ _ p) :
    halfTurnOldHom D Sc cutoff s t f ∈ parity (R := k) _ _ p := by
  apply Submodule.mem_map_of_mem
  exact elvQuotientMap_mem D (parameterTwist D Sc) cutoff (htCoef_mem_parity D Sc hf)

/-- Full source arrows act in the actual word-module chart at twisted
parameters. This map is not yet identified with the chosen weight action. -/
def sourceMap (s t : List I) :
    (coefficientObj D Sc s ⟶ coefficientObj D Sc t) →ₗ[k]
      (powerWordModule D (parameterTwist D Sc) cutoff L s.reverse ⟶
        powerWordModule D (parameterTwist D Sc) cutoff L t.reverse) :=
  (PowerWordYoneda.homEquiv D (parameterTwist D Sc) cutoff L s.reverse
    (powerWordObject D (parameterTwist D Sc) cutoff L t.reverse)).symm.toLinearMap.comp
    ((powerWordGenerator D (parameterTwist D Sc) cutoff L t.reverse (OldCategory.mk s.reverse)).comp
      (halfTurnOldHom D Sc cutoff s t))

theorem sourceMap_apply (s t : List I) (f : coefficientObj D Sc s ⟶ coefficientObj D Sc t) :
    sourceMap D Sc cutoff L s t f =
      PowerWordMorphisms.fromArrow D (parameterTwist D Sc) cutoff L s.reverse t.reverse
        (halfTurnOldHom D Sc cutoff s t f) := rfl

/-- The two super-opposite signs match, so source chronological composition
is ordinary composition of the actual word module maps. -/
theorem sourceMap_comp_homogeneous {s t u : List I} {p q : ZMod 2}
    {f : coefficientObj D Sc s ⟶ coefficientObj D Sc t}
    {g : coefficientObj D Sc t ⟶ coefficientObj D Sc u}
    (hf : f ∈ parity (R := k) _ _ p) (hg : g ∈ parity (R := k) _ _ q) :
    sourceMap D Sc cutoff L s u (f ≫ g) =
      sourceMap D Sc cutoff L s t f ≫ sourceMap D Sc cutoff L t u g := by
  rw [sourceMap_apply, sourceMap_apply, sourceMap_apply, halfTurnOldHom_comp D Sc cutoff hf hg,
    fromArrow_smul, ← SKM.sign_eq_zsign]
  exact (fromArrow_comp D (parameterTwist D Sc) cutoff L s.reverse t.reverse u.reverse _ _
    (halfTurnOldHom_mem D Sc cutoff hf) (halfTurnOldHom_mem D Sc cutoff hg)).symm

/-- Ordinary source composition for arbitrary full coefficient arrows,
including both parity components of each input. -/
theorem sourceMap_comp {s t u : List I}
    (f : coefficientObj D Sc s ⟶ coefficientObj D Sc t)
    (g : coefficientObj D Sc t ⟶ coefficientObj D Sc u) :
    sourceMap D Sc cutoff L s u (f ≫ g) =
      sourceMap D Sc cutoff L s t f ≫ sourceMap D Sc cutoff L t u g := by
  revert g
  refine Supercategory.induction_on (R := k)
    (P := fun f => ∀ g : coefficientObj D Sc t ⟶ coefficientObj D Sc u,
      sourceMap D Sc cutoff L s u (f ≫ g) =
        sourceMap D Sc cutoff L s t f ≫ sourceMap D Sc cutoff L t u g) f ?_ ?_ ?_
  · intro g
    simp only [Limits.zero_comp, map_zero]
  · intro p f hf g
    refine Supercategory.induction_on (R := k)
      (P := fun g => sourceMap D Sc cutoff L s u (f ≫ g) =
        sourceMap D Sc cutoff L s t f ≫ sourceMap D Sc cutoff L t u g) g ?_ ?_ ?_
    · simp only [Limits.comp_zero, map_zero]
    · intro q g hg
      exact sourceMap_comp_homogeneous D Sc cutoff L hf hg
    · intro g h ihg ihh
      simp only [Preadditive.comp_add, map_add, ihg, ihh]
  · intro f h ihf ihh g
    simp only [Preadditive.add_comp, map_add, ihf g, ihh g]

/-- Evaluating this module map at the word unit recovers the previously
computed coordinate in the actual module. It is not a chosen weight-action
identification. -/
theorem sourceMap_evaluate (s t : List I)
    (f : coefficientObj D Sc s ⟶ coefficientObj D Sc t) :
    PowerWordYoneda.homEquiv D (parameterTwist D Sc) cutoff L s.reverse
      (powerWordObject D (parameterTwist D Sc) cutoff L t.reverse)
      (sourceMap D Sc cutoff L s t f) = powerWordHalfTurnCoordinate D Sc cutoff L s t f := by
  change (PowerWordYoneda.homEquiv D (parameterTwist D Sc) cutoff L s.reverse
    (powerWordObject D (parameterTwist D Sc) cutoff L t.reverse))
      ((PowerWordYoneda.homEquiv D (parameterTwist D Sc) cutoff L s.reverse
        (powerWordObject D (parameterTwist D Sc) cutoff L t.reverse)).symm
        (powerWordGenerator D (parameterTwist D Sc) cutoff L t.reverse (OldCategory.mk s.reverse)
          (halfTurnOldHom D Sc cutoff s t f))) = _
  rw [LinearEquiv.apply_symm_apply, powerWordHalfTurnCoordinate_eq]
  rfl

end OddMath.QuiverHecke.ELVOld.PowerWordComposition
