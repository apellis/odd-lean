import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContexts
import OddMath.QuiverHecke.HalfTurn.OldQuotient

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

end OddMath.QuiverHecke.ELVOld.PowerWordComposition
