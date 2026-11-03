import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionRelations

/-! # The old braid on direct triple induction

Brundan–Ellis Definition 1.5: the literal old prefix and suffix crossings
induce the braid on every balanced triple-append module. The superopposite
composition signs on the two three-crossing paths agree. Comparison with
three separately chosen induction functors remains a separate step.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open BalancedInduction
universe u
private theorem transformComponent_braid
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

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (i : I)

local notation "J" => append D Sc cutoff i

/-- Induce the physical prefix crossing after appending the third strand. -/
def oldTriplePrefixCross (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    End ((induction ((J ⋙ J) ⋙ J)).obj M) :=
  transformComponent ((equalCross_supernatural D Sc cutoff i).whiskerRight J) M

/-- Induce the physical suffix crossing at the already appended old word. -/
def oldTripleSuffixCross (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    End ((induction ((J ⋙ J) ⋙ J)).obj M) :=
  transformComponent ((equalCross_supernatural D Sc cutoff i).whiskerLeft J) M

/-- The whole balanced-module braid for the independent old crossings. -/
theorem oldTripleCross_braid (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    oldTriplePrefixCross D Sc cutoff i M ≫ oldTripleSuffixCross D Sc cutoff i M ≫
        oldTriplePrefixCross D Sc cutoff i M =
      oldTripleSuffixCross D Sc cutoff i M ≫ oldTriplePrefixCross D Sc cutoff i M ≫
        oldTripleSuffixCross D Sc cutoff i M := by
  exact transformComponent_braid ((J ⋙ J) ⋙ J)
    ((equalCross_supernatural D Sc cutoff i).whiskerRight J)
    ((equalCross_supernatural D Sc cutoff i).whiskerLeft J)
    (equalCrossComponent_braid D Sc cutoff i) M

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
