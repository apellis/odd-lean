import OddMath.QuiverHecke.SwappedAssembly.Sigma.BendSeriesAlgebra
import OddMath.SKM.RouquierHomBendMonomials

/-! # Evaluation of ordered mixed-bend monomials

The inverse-probe monomials of `SwappedHomInversion.md` §3 (4)–(6)
are evaluated through the prescribed bend functor. This interface
keeps endomorphism multiplication in its chronological convention and
connects ring inverse powers to the specified probe automorphism.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory OddMath.SKM

variable {A C C' : Type*} [Category A] [Preadditive A]
  [Category C] [Preadditive C] [Category C'] [Preadditive C']

/-- Evaluation preserves the exact integral automorphism exponent used
by the central residual comparison. -/
theorem bend_map_aut_zpow (F : A ⥤ C) {U : A} (x : Aut U) (z : ℤ) :
    F.map (x^z).hom = (Functor.mapAut U F x ^ z).hom :=
  congrArg Iso.hom (map_zpow (Functor.mapAut U F) x z)

/-- The evaluated ring inverse is the map of the specified automorphism's
inverse, without selecting an unrelated inverse endomorphism. -/
theorem bendFunctor_inverse (F : A ⥤ C) [F.Additive] {U : A} (x : Aut U) :
    Ring.inverse (bendFunctorEnd F U (Aut.toEnd U x)) =
      bendFunctorEnd F U (autInverseEnd x) := by
  have hx : IsUnit (Aut.toEnd U x) := ⟨(Aut.unitsEndEquivAut U).symm x, rfl⟩
  apply bend_inverse_eq (hx.map (bendFunctorEnd F U).toMonoidHom)
  change F.map x.inv ≫ F.map x.hom = 𝟙 (F.obj U)
  rw [← F.map_comp, x.inv_hom_id, F.map_id]

/-- Ordered inverse powers and reservoir powers evaluate to the literal
unit–dots–cap composite. The reservoir power is chronologically first. -/
theorem bend_evaluated_monomial (F : A ⥤ C) [F.Additive]
    (L : C ⥤ C') [L.Additive] {U : A} {X Y : C}
    (a : X ⟶ F.obj U) (b : F.obj U ⟶ Y)
    (x : Aut U) (y : End U) (n r : ℕ) :
    bendInsertion (L.map a) (L.map b)
      (Ring.inverse (bendFunctorEnd (F ⋙ L) U (Aut.toEnd U x)) ^ n *
        bendFunctorEnd (F ⋙ L) U y ^ r) =
      L.map (a ≫ F.map (y^r) ≫ F.map (autInverseEnd x ^ n) ≫ b) := by
  rw [bendFunctor_inverse, ← map_pow, ← map_pow, ← map_mul]
  dsimp only [bendInsertion, bendFunctorEnd]
  simp only [End.mul_def, Functor.comp_map, Functor.map_comp, Category.assoc]

end OddMath.QuiverHecke.SwappedAssembly
