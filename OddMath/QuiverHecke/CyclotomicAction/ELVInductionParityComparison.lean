import OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity

/-! # Canonical parity transport of induction and its actual counit

The source comparison is the image of the actual vector parity isomorphism
under restriction and balanced induction. Its tensor formula twists the
kernel arrow, including all coefficient parity. Counit naturality proves
the whole module-map comparison independently of any representative basis.
This supplies the categorical transport used in DeformedMatrixComparison
(3), (5); the concrete shifted old-Hom source must still be identified with
the corresponding restricted representable module.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (A : C ⥤ D) [A.Additive] [A.Linear k] [IsSuperfunctor k A]

/-- Canonical whole-module source transport, built from actual parity and
the existing restriction/induction functors. -/
def adjunctionParitySourceIso (N : Superfunctor k D (SVec k)) :
    (induction A).obj ((restriction A).obj N) ≅
      (induction A).obj ((restriction A).obj (supermoduleParityObj N)) :=
  ((restriction A ⋙ induction A).mapIso (supermoduleParityIso N)).symm

/-- The actual counit at the parity-shifted module, transported on source
and output by the canonical isomorphisms, equals the original actual counit.
This is a whole supernatural module-map equality, including odd inputs. -/
theorem adjunctionParitySourceIso_counit
    (N : Superfunctor k D (SVec k)) :
    (adjunctionParitySourceIso A N).hom ≫
      (adjunctionCounit A).app (supermoduleParityObj N) ≫
        (supermoduleParityIso N).hom =
      (adjunctionCounit A).app N := by
  have hn := (adjunctionCounit A).naturality (supermoduleParityIso N).hom
  simp only [Functor.id_map] at hn
  change (restriction A ⋙ induction A).map (supermoduleParityIso N).inv ≫
      ((adjunctionCounit A).app (supermoduleParityObj N) ≫
        (supermoduleParityIso N).hom) = (adjunctionCounit A).app N
  rw [← hn, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

end OddMath.QuiverHecke.ELVOld.BalancedInduction
