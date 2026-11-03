import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionRelations

/-! # Braid relations under balanced induction

Brundan–Ellis Definition 1.5: two source transformations of the same
parity induce the braid on every module, retaining the superopposite
composition signs. This is used by both the old append and the changing
content-category induction grids.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
/-- A braid of homogeneous source transformations induces the whole module braid. -/
theorem transformComponent_braid
    {k C A : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    (T : C ⥤ A) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    {p : ZMod 2} {α β : ∀ s, T.obj s ⟶ T.obj s}
    (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β)
    (hb : ∀ s, α s ≫ β s ≫ α s = β s ≫ α s ≫ β s)
    (M : Superfunctor k C (SVec k)) :
    transformComponent hα M ≫ transformComponent hβ M ≫ transformComponent hα M =
      transformComponent hβ M ≫ transformComponent hα M ≫ transformComponent hβ M := by
  have he : (fun s => (α s ≫ β s) ≫ α s) =
      (fun s => (β s ≫ α s) ≫ β s) := by
    funext s
    simpa only [Category.assoc] using hb s
  have ht : transformComponent ((hα.comp hβ).comp hα) M =
      transformComponent ((hβ.comp hα).comp hβ) M := by
    congr 1
  rw [transformComponent_comp, transformComponent_comp,
    Linear.comp_smul, Linear.comp_smul,
    transformComponent_comp, transformComponent_comp]
  exact congrArg (fun f => _ • (_ • f)) ht

end OddMath.QuiverHecke.ELVOld.BalancedInduction
